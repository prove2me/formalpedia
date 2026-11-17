-- Prove2me | Definitions.Def_FairReplay_Supplement_Qthr
-- name    : FairReplay_Supplement_Qthr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:45:59.331195+00:00
-- url     : https://prove2.me/theorems/35945da2-73d1-4de7-935b-d94c89bc3b25
-- title:
--   Composite thresholded problem and $Q_{\mathrm{thr}}$
-- statement:
--   The **composite thresholded problem** (49) asks, from four-way replay rounds, to distinguish
--   $$H_0:\ |p_{1,u}-p_{1,v}|\le\tau\qquad\text{from}\qquad H_1:\ |p_{1,u}-p_{1,v}|\ge\tau+d,$$
--   uniformly over all old and new thresholds in $[0,1]$. A tester is correct at level $\delta$ if it rejects with probability at most $\delta$ under every instance of $H_0$ and fails to reject with probability at most $\delta$ under every instance of $H_1$.
--
--   In the P18 family (old thresholds $(p,p)$, boundary-null new thresholds $(p+s+\tau,p+s)$, alternative $(p+s+\tau+d,p+s)$), two optimal null expected round counts are defined:
--
--   1. $Q_{\mathrm{thr}}^{\mathrm{pair}}$, over testers that are $\delta$-correct for the boundary null against the alternative;
--   2. $Q_{\mathrm{thr}}^{\mathrm{comp}}$, over testers correct for the whole composite problem, with the expectation under the boundary null.
--
--   **Formalization Note** The paper writes $Q_{\mathrm{thr}}(\tau,d,\delta)$ without a displayed definition; both readings are bounded in Theorem 10.5. Infima are in $[0,\infty]$; non-stopping counts as an error under $H_1$.
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.5, eqs. (49), (51), p.16 (PDF p.18)

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_FairReplay_IsDeltaCorrect
import Definitions.Def_FairReplay_expectedRounds
import Definitions.Def_FairReplay_optRounds
import Definitions.Def_FairReplay_Supplement_fourWayEnv

open MeasureTheory

namespace FairReplay.Supplement

/-- **Correctness for the composite thresholded problem** (Sah, Zhang, Lian, *Testing Fairness of
Evolving Software under Uncertainty*, STOC 2027 submission, manuscript of 2026-11-03,
sha256 e23940a0…, Theorem 10.5, eq. (49), p.16 (PDF p.18)):
`H0 : |p1,u − p1,v| ≤ τ, H1 : |p1,u − p1,v| ≥ τ + d`.

A four-way tester `(π, T, ψ)` is correct at level `δ` for this problem if, for all old thresholds and
new thresholds in `[0, 1]`, it stops and rejects with probability at most `δ` whenever the new
endpoint gap is at most `τ`, and fails to stop-and-reject with probability at most `δ` whenever the
gap is at least `τ + d`.

**Formalization Note** The stopping time is named `T` (the paper's `τ` is the tolerance here). A run
that never stops counts as an error under `H1`. -/
def IsThrCompositeCorrect (τ d δ : ℝ) (π : BanditAlgorithm.BanditPolicy 1)
    (T : (ℕ → Fin 1 × ℝ) → ℕ∞) (ψ : (ℕ → Fin 1 × ℝ) → Bool) : Prop :=
  (∀ old new : Fin 2 → ℝ, (∀ j, old j ∈ Set.Icc (0 : ℝ) 1) → (∀ j, new j ∈ Set.Icc (0 : ℝ) 1) →
      |new 0 - new 1| ≤ τ →
      BanditAlgorithm.banditTrajMeasure (fourWayEnv old new) π {ω | T ω < ⊤ ∧ ψ ω = true} ≤
        ENNReal.ofReal δ) ∧
  (∀ old new : Fin 2 → ℝ, (∀ j, old j ∈ Set.Icc (0 : ℝ) 1) → (∀ j, new j ∈ Set.Icc (0 : ℝ) 1) →
      τ + d ≤ |new 0 - new 1| →
      BanditAlgorithm.banditTrajMeasure (fourWayEnv old new) π {ω | ¬ (T ω < ⊤ ∧ ψ ω = true)} ≤
        ENNReal.ofReal δ)

/-- **`Q_thr` for the boundary pair** (Theorem 10.5, eq. (51), p.16): the optimal null expected
number of four-way rounds over testers that are δ-correct for the P18 boundary null (old `(p, p)`,
new `(p + s + τ, p + s)`) against the alternative (new `(p + s + τ + d, p + s)`).

**Formalization Note** The paper gives no displayed definition of `Q_thr`; this and `QthrComp`
are the two natural readings, and Theorem 10.5's `Θ` statement bounds both. -/
noncomputable def QthrPair (p s τ d δ : ℝ) : ENNReal :=
  optRounds δ (fourWayEnv ![p, p] ![p + s + τ, p + s]) (fourWayEnv ![p, p] ![p + s + τ + d, p + s])

/-- **`Q_thr` for the composite problem** (Theorem 10.5, eqs. (49), (51), p.16): the infimum of the
expected number of rounds under the P18 boundary null over all four-way testers that are correct at
level `δ` for the whole composite problem (49). The infimum is in `[0, ∞]`. -/
noncomputable def QthrComp (p s τ d δ : ℝ) : ENNReal :=
  ⨅ (π : BanditAlgorithm.BanditPolicy 1) (T : (ℕ → Fin 1 × ℝ) → ℕ∞)
    (ψ : (ℕ → Fin 1 × ℝ) → Bool) (hT : BanditAlgorithm.IsBanditStoppingTime T)
    (_ : Measurable[hT.measurableSpace] ψ) (_ : IsThrCompositeCorrect τ d δ π T ψ),
    expectedRounds (fourWayEnv ![p, p] ![p + s + τ, p + s]) π T

end FairReplay.Supplement


