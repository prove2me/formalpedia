-- Prove2me | Definitions.Def_StatComplexityDM_LowerBound_History
-- name    : StatComplexityDM_LowerBound_History
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:20:46.909625+00:00
-- url     : https://prove2.me/theorems/3bd9566c-7d10-4502-bddf-3a508634c4f1
-- title:
--   §2, p. 9; Theorem 3.2, p. 12; App. C.1.3, p. 90 — adaptive history law P^{M,p}, expected regret, average play p_M, V(M), C(T) and C_T
-- statement:
--   An **algorithm** for horizon $T$ is a sequence of kernels $p^{(1)},\dots,p^{(T)}$: after the history $\mathcal H^{(t-1)}=((\pi^{(1)},y^{(1)}),\dots,(\pi^{(t-1)},y^{(t-1)}))$ it plays a probability vector $p^{(t)}(\cdot\mid\mathcal H^{(t-1)})$ on $\Pi$. Under model $M$, the **law of the history** is
--
--   $$
--   \mathbb P^{M,p}(h)=\prod_{t=1}^T p^{(t)}(\pi_t\mid h_{<t})\,M(\pi_t)(y_t),\qquad h=((\pi_t,y_t))_{t=1}^T .
--   $$
--
--   The **expected regret** is $\mathbb E^{M,p}[\mathrm{Reg}_{\mathrm{DM}}]=\mathbb E^{M,p}\bigl[\sum_{t=1}^T\mathbb E_{\pi\sim p^{(t)}(\cdot\mid\mathcal H^{(t-1)})}[g^M(\pi)]\bigr]$ with $g^M(\pi)=f^M(\pi_M)-f^M(\pi)$, as in (1). The **average play** is $p_M=\mathbb E^{M,p}\bigl[\frac1T\sum_{t=1}^T p^{(t)}(\cdot\mid\mathcal H^{(t-1)})\bigr]\in\Delta(\Pi)$.
--
--   For events $A\subseteq\mathcal Y$, the **density ratio** of the class is $V(\mathcal M)=\sup_{M,M'\in\mathcal M}\sup_{\pi}\sup_A \frac{M(A\mid\pi)}{M'(A\mid\pi)}\vee e$, and the one-sided ratio is $V^{\bar M}(\mathcal M)=\sup_{M\in\mathcal M}\sup_\pi\sup_A\frac{\bar M(A\mid\pi)}{M(A\mid\pi)}$; both may be $+\infty$. The constants are
--
--   $$
--   C(T)=2^{11}\log\bigl(2T\wedge V(\mathcal M)\bigr),\qquad C_T=2^{8}\log\bigl(2T\wedge (V^{\bar M}(\mathcal M)\vee e)\bigr).
--   $$
--
--   These are the stochastic process and constants of Theorem 3.2 and its proof.
--
--   **Formalization Note** Decisions $\Pi$ and joint reward–observation outcomes $\mathcal R\times\mathcal O$ are finite alphabets (the finite-alphabet case of the paper's measurable setting, §2, p. 9); models and algorithm kernels are probability vectors and expectations are finite sums. Rounds are 0-based (`Fin T`). An event ratio with zero denominator is $+\infty$ when its numerator is positive and $0$ when both vanish. The cutoff $\vee e$ in $C_T$ is not printed on p. 90; it is the hypothesis $V\ge e$ of Lemma A.13 (98), p. 73, from which the page derives $C_T$, and without it $C_T\to0$ as $V^{\bar M}(\mathcal M)\to1$ and the history bound is false. Since $V^{\bar M}(\mathcal M)\vee e\le V(\mathcal M)$, it still gives $8C_T\le C(T)$.
-- source:
--   arXiv:2112.13487v3, §2, p. 9; (1), p. 5; Theorem 3.2, p. 12; App. C.1.3, proof of Theorem 3.2, p. 90; Lemma A.13 (98), p. 73

import Mathlib
import Definitions.Def_StatComplexityDM_LowerBound_Core
import Definitions.Def_FoundationsRL_GeneralDM_Divergences

namespace StatComplexityDM.LowerBound

open FoundationsRL.GeneralDM

/-- Histories of `t` decision–outcome pairs (§2, p. 9). -/
abbrev History (S Y : Type*) (t : ℕ) := Fin t → S × Y

/-- An adaptive decision kernel indexed by its past (§2, p. 9). -/
def IsAlgorithm {S Y : Type*} [Fintype S] {T : ℕ}
    (alg : (t : Fin T) → History S Y t.val → S → ℝ) : Prop :=
  ∀ t h, IsDist (alg t h)

/-- The past visible at round `t` of a complete history. -/
def historyPrefix {S Y : Type*} {T : ℕ} (h : History S Y T) (t : Fin T) : History S Y t.val :=
  fun i => h ⟨i.val, Nat.lt_trans i.isLt t.isLt⟩

/-- The law `P^{M,p}` of the full adaptive history (§2, p. 9). -/
noncomputable def histLaw {S Y : Type*} {T : ℕ} (m : S → Y → ℝ)
    (alg : (t : Fin T) → History S Y t.val → S → ℝ) (h : History S Y T) : ℝ :=
  ∏ t : Fin T, alg t (historyPrefix h t) (h t).1 * m (h t).1 (h t).2

/-- The mean-reward gap `g^M(π)` of (12), p. 12. -/
noncomputable def rewardGap {S Y : Type*} [Fintype S] [Fintype Y] (rew : Y → ℝ)
    (piStar : (S → Y → ℝ) → S) (m : S → Y → ℝ) (π : S) : ℝ :=
  fM rew m (piStar m) - fM rew m π

/-- Expected decision-distribution regret (1), pp. 5, 90, under the adaptive history law. -/
noncomputable def expRegret {S Y : Type*} [Fintype S] [Fintype Y] {T : ℕ}
    (rew : Y → ℝ) (piStar : (S → Y → ℝ) → S) (m : S → Y → ℝ)
    (alg : (t : Fin T) → History S Y t.val → S → ℝ) : ℝ :=
  ∑ h : History S Y T, histLaw m alg h *
    ∑ t : Fin T, ∑ π : S, alg t (historyPrefix h t) π * rewardGap rew piStar m π

/-- The expected average play distribution `p_M` in App. C.1.3, p. 90. -/
noncomputable def avgPlay {S Y : Type*} [Fintype S] [Fintype Y] {T : ℕ}
    (m : S → Y → ℝ) (alg : (t : Fin T) → History S Y t.val → S → ℝ) (π : S) : ℝ :=
  (1 / (T : ℝ)) * ∑ h : History S Y T,
    histLaw m alg h * ∑ t : Fin T, alg t (historyPrefix h t) π

/-- An event probability in a finite outcome alphabet. -/
noncomputable def eventMass {Y : Type*} (P : Y → ℝ) (A : Finset Y) : ℝ :=
  ∑ y ∈ A, P y

/-- Event likelihood ratio, with positive mass over zero mass valued `+∞`. -/
noncomputable def eventRatio {Y : Type*} (P Q : Y → ℝ) (A : Finset Y) : ENNReal :=
  if eventMass Q A = 0 then
    if eventMass P A = 0 then 0 else ⊤
  else ENNReal.ofReal (eventMass P A / eventMass Q A)

/-- The class-wide density ratio `V(M)` of p. 12, including the lower cutoff `e`. -/
noncomputable def densityRatio {S Y : Type*} [DecidableEq Y]
    (𝓜 : Set (S → Y → ℝ)) : ENNReal :=
  (ENNReal.ofReal (Real.exp 1)) ⊔
    ⨆ m ∈ 𝓜, ⨆ m' ∈ 𝓜, ⨆ π : S, ⨆ A : Finset Y, eventRatio (m π) (m' π) A

/-- The one-sided ratio `V^{M̄}(M)` of App. C.1.3, p. 90. -/
noncomputable def relativeDensityRatio {S Y : Type*} [DecidableEq Y]
    (𝓜 : Set (S → Y → ℝ)) (mbar : S → Y → ℝ) : ENNReal :=
  ⨆ m ∈ 𝓜, ⨆ π : S, ⨆ A : Finset Y, eventRatio (mbar π) (m π) A

/-- The theorem's `C(T) = 2¹¹ log(2T ∧ V(M))` (Theorem 3.2, p. 12). -/
noncomputable def regretConstant {S Y : Type*} [DecidableEq Y] (𝓜 : Set (S → Y → ℝ))
    (T : ℕ) : ℝ :=
  (2 : ℝ) ^ 11 * Real.log ((min ((2 * T : ℕ) : ENNReal) (densityRatio 𝓜)).toReal)

/-- The proof's `C_T = 2⁸(log(2T) ∧ log(V^{M̄}(M) ∨ e))`, p. 90. The cutoff `∨ e` is the
hypothesis `V ≥ e` of Lemma A.13 (98), p. 73, through which the page obtains `C_T`; without it
`C_T → 0` as `V^{M̄}(M) → 1` and the bound fails. -/
noncomputable def historyConstant {S Y : Type*} [DecidableEq Y] (𝓜 : Set (S → Y → ℝ))
    (mbar : S → Y → ℝ) (T : ℕ) : ℝ :=
  (2 : ℝ) ^ 8 * Real.log ((min ((2 * T : ℕ) : ENNReal)
    (relativeDensityRatio 𝓜 mbar ⊔ ENNReal.ofReal (Real.exp 1))).toReal)

end StatComplexityDM.LowerBound


