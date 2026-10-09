-- Prove2me | Definitions.Def_StatComplexityDM_Estimation_Process
-- name    : StatComplexityDM_Estimation_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:37.034984+00:00
-- url     : https://prove2.me/theorems/62666c15-c148-4976-afcc-172323705bb2
-- title:
--   Appendix A.3.1, pp. 75–76 — online density process, log-loss regret, and Hellinger estimation error
-- statement:
--   Let $X$ be a finite covariate set, $Y$ a finite outcome set, $I$ a finite expert index set, and $T$ the number of rounds. At round $t$, expert $i$ supplies an outcome law $g_{i,t}(\cdot\mid x;h_{<t})$ for each covariate $x$, and the learner supplies $\widehat g_t(\cdot\mid x;h_{<t})$. Both depend only on the past history. Nature chooses the next covariate using an arbitrary history-dependent vector $c_t(\cdot\mid h_{<t})$.
--
--   For a true expert $i^\star$, realizability gives the complete-history law
--   $$
--   P(h)=\prod_{t=0}^{T-1}c_t(x_t\mid h_{<t})\,g_{i^\star,t}(y_t\mid x_t;h_{<t}).
--   $$
--   Log loss is $-\log q(y\mid x)$, and log-loss regret subtracts the minimum cumulative expert loss. Hellinger estimation error is
--   $$
--   \mathrm{Est}_{\mathrm H}(h)=\sum_{t=0}^{T-1}\sum_{x\in X}c_t(x\mid h_{<t})D_{\mathrm H}^2\!\left(\widehat g_t(\cdot\mid x;h_{<t}),g_{i^\star,t}(\cdot\mid x;h_{<t})\right).
--   $$
--
--   The file also defines predictable masked versions for (103). A mask depends on the history before the current round.
--
--   **Formalization Note** Alphabets and the expert class are finite, and rounds are 0-based. Squared Hellinger distance uses the published FoundationsRL definition with no factor of $1/2$. PositiveOnSupport requires the learner and every expert to assign positive density to observed outcomes on histories of positive probability, avoiding the real-valued convention $\log 0=0$.
-- source:
--   arXiv:2112.13487v3, Appendix A.3.1, (99)–(100), Assumption A.1, pp. 75–76

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_StatComplexityDM_Estimation_Sequential

namespace StatComplexityDM.Estimation

open FoundationsRL.GeneralDM

/-- The expert class of A.3.1: each expert predicts an outcome distribution after seeing
the past, but before seeing the current covariate. -/
abbrev Experts (I X Y : Type*) (T : ℕ) :=
  I → (t : Fin T) → Hist (X × Y) t.val → X → Y → ℝ

/-- An arbitrary online density estimator. -/
abbrev Predictor (X Y : Type*) (T : ℕ) :=
  (t : Fin T) → Hist (X × Y) t.val → X → Y → ℝ

/-- Nature's adaptive distribution for the next covariate. -/
abbrev ContextKernel (X Y : Type*) (T : ℕ) :=
  (t : Fin T) → Hist (X × Y) t.val → X → ℝ

def IsExperts {I X Y : Type*} [Fintype Y] {T : ℕ}
    (g : Experts I X Y T) : Prop :=
  ∀ i t h x, StatComplexityDM.LowerBound.IsDist (g i t h x)

def IsPredictor {X Y : Type*} [Fintype Y] {T : ℕ}
    (ghat : Predictor X Y T) : Prop :=
  ∀ t h x, StatComplexityDM.LowerBound.IsDist (ghat t h x)

def IsContextKernel {X Y : Type*} [Fintype X] {T : ℕ}
    (ctx : ContextKernel X Y T) : Prop :=
  ∀ t h, StatComplexityDM.LowerBound.IsDist (ctx t h)

/-- The joint law of the history under realizability, Assumption A.1. -/
def law {I X Y : Type*} {T : ℕ} (ctx : ContextKernel X Y T)
    (g : Experts I X Y T) (istar : I) (h : Hist (X × Y) T) : ℝ :=
  ∏ t, ctx t (histPrefix h t) (h t).1 *
    g istar t (histPrefix h t) (h t).1 (h t).2

/-- Conditional squared Hellinger estimation error (100). Its inner sum averages
the *next covariate* under `ctx`, conditional on the preceding history. -/
noncomputable def estH {I X Y : Type*} [Fintype X] [Fintype Y] {T : ℕ}
    (ctx : ContextKernel X Y T) (ghat : Predictor X Y T)
    (g : Experts I X Y T) (istar : I) (h : Hist (X × Y) T) : ℝ :=
  ∑ t, ∑ x, ctx t (histPrefix h t) x *
    hellingerSq (ghat t (histPrefix h t) x) (g istar t (histPrefix h t) x)

/-- Logarithmic loss (99), used at positive predicted probability. -/
noncomputable def logLoss {X Y : Type*} (q : X → Y → ℝ) (x : X) (y : Y) : ℝ :=
  -Real.log (q x y)

/-- Log-loss regret (99) against the best expert in the finite class. -/
noncomputable def regKL {I X Y : Type*} [Fintype I] [Nonempty I] {T : ℕ}
    (ghat : Predictor X Y T) (g : Experts I X Y T)
    (h : Hist (X × Y) T) : ℝ :=
  (∑ t, logLoss (ghat t (histPrefix h t)) (h t).1 (h t).2) -
    (Finset.univ : Finset I).inf' Finset.univ_nonempty
      (fun i => ∑ t, logLoss (g i t (histPrefix h t)) (h t).1 (h t).2)

/-- Positivity of the densities on complete histories with positive probability.
It excludes Lean's junk value `Real.log 0 = 0` on every observed sample. -/
def PositiveOnSupport {I X Y : Type*} {T : ℕ}
    (ctx : ContextKernel X Y T) (ghat : Predictor X Y T)
    (g : Experts I X Y T) (istar : I) : Prop :=
  ∀ h : Hist (X × Y) T, 0 < law ctx g istar h →
    ∀ i t,
      0 < g i t (histPrefix h t) (h t).1 (h t).2 ∧
      0 < ghat t (histPrefix h t) (h t).1 (h t).2

/-- The predictable, Boolean-masked version of (100). -/
noncomputable def maskedEstH {I X Y : Type*} [Fintype X] [Fintype Y] {T : ℕ}
    (ctx : ContextKernel X Y T) (ghat : Predictor X Y T)
    (g : Experts I X Y T) (istar : I)
    (mask : (t : Fin T) → Hist (X × Y) t.val → Bool)
    (h : Hist (X × Y) T) : ℝ :=
  ∑ t, if mask t (histPrefix h t) then
    ∑ x, ctx t (histPrefix h t) x *
      hellingerSq (ghat t (histPrefix h t) x) (g istar t (histPrefix h t) x)
    else 0

/-- The realized, Boolean-masked log-loss gap to the true expert in (103). -/
noncomputable def maskedGap {I X Y : Type*} {T : ℕ}
    (ghat : Predictor X Y T) (g : Experts I X Y T) (istar : I)
    (mask : (t : Fin T) → Hist (X × Y) t.val → Bool)
    (h : Hist (X × Y) T) : ℝ :=
  ∑ t, if mask t (histPrefix h t) then
    logLoss (ghat t (histPrefix h t)) (h t).1 (h t).2 -
      logLoss (g istar t (histPrefix h t)) (h t).1 (h t).2
    else 0

end StatComplexityDM.Estimation


