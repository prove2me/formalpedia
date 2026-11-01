-- Prove2me | Definitions.Def_DRBatchBandit_Estimator
-- name    : DRBatchBandit_Estimator
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:11.810042+00:00
-- url     : https://prove2.me/theorems/1bcd0054-e775-4370-aaba-d9faeb8cc19e
-- title:
--   Self-normalized estimator $\hat Q_{\mathrm{DRO}}$ (Definition 4) and the learned policy $\hat\pi_{\mathrm{DRO}}$ of (4)
-- statement:
--   Let $\{(X_i,A_i,Y_i)\}_{i=1}^n$ be observed data, with $Y_i=Y_i(A_i)$, and $\delta>0$. Definition 4 (p.12) sets
--   $$W_i(\pi,\alpha)=\frac{\mathbf 1\{\pi(X_i)=A_i\}}{\pi_0(A_i\mid X_i)}\exp(-Y_i(A_i)/\alpha),\qquad S_n^\pi=\frac1n\sum_{i=1}^n\frac{\mathbf 1\{\pi(X_i)=A_i\}}{\pi_0(A_i\mid X_i)},$$
--   $$\hat W_n(\pi,\alpha)=\frac{1}{nS_n^\pi}\sum_{i=1}^nW_i(\pi,\alpha),\qquad \hat\phi_n(\pi,\alpha)=-\alpha\log\hat W_n(\pi,\alpha)-\alpha\delta,$$
--   and the distributionally robust value estimator
--   $$\hat Q_{\mathrm{DRO}}(\pi)=\sup_{\alpha\ge0}\hat\phi_n(\pi,\alpha).$$
--   The learned policy (4), p.15, is any $\hat\pi_{\mathrm{DRO}}\in\arg\max_{\pi\in\Pi}\hat Q_{\mathrm{DRO}}(\pi)$. A **DRO learner** maps every data set to such a maximizer.
--
--   **Formalization Note** The supremum is over $\alpha>0$; Remark 2 (p.11) defines the $\alpha=0$ value as the right limit, so the supremum is unchanged. When $S_n^\pi=0$ (no sample with $\pi(X_i)=A_i$) the paper leaves $\hat W_n$ undefined; Lean's $1/0=0$ gives $\hat W_n=0$ and $\hat Q_{\mathrm{DRO}}(\pi)=0$. The family $\hat\phi_n(\pi,\cdot)$ is bounded above by $\max_i|Y_i|$, so the real supremum is the paper's.
-- source:
--   Si, Zhang, Zhou & Blanchet, Distributionally Robust Batch Contextual Bandits, arXiv:2006.05630v7, Definition 4 p.12 (W_i, S_n^π, Ŵ_n, φ̂_n, Q̂_DRO); (4) p.15 (π̂_DRO). PDF sha256 ac485985feb75d33b603f06f5a5d93c52077877db7be11de3d71107c7c374b02

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Setting

open MeasureTheory

namespace DRBatchBandit

open OfflinePolicyLearning.Regret

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

/-- The inverse-propensity weight `1{π(x) = a} / π₀(a | x)` of an observed triple
`o = (x, a, y)` (arXiv:2006.05630v7, Definition 4, p.12). -/
noncomputable def ipw (M : Model X d) (π : X → Fin d) (o : Obs X d) : ℝ :=
  if π o.1 = o.2.1 then 1 / M.e o.1 o.2.1 else 0

/-- Definition 4 (arXiv:2006.05630v7, p.12): `S_n^π = (1/n) ∑ᵢ 1{π(Xᵢ) = Aᵢ} / π₀(Aᵢ | Xᵢ)`. -/
noncomputable def Sn (M : Model X d) {n : ℕ} (D : Fin n → Obs X d) (π : X → Fin d) : ℝ :=
  (1 / n : ℝ) * ∑ i, ipw M π (D i)

/-- Definition 4 (arXiv:2006.05630v7, p.12): `Ŵ_n(π, α) = (1/(n S_n^π)) ∑ᵢ Wᵢ(π, α)` with
`Wᵢ(π, α) = 1{π(Xᵢ) = Aᵢ} / π₀(Aᵢ | Xᵢ) · exp(−Yᵢ(Aᵢ)/α)`.

**Formalization Note.** When `S_n^π = 0` (no sample with `π(Xᵢ) = Aᵢ`) Lean's `1/0 = 0` gives
`Ŵ_n = 0`; the paper is silent on this case. -/
noncomputable def What (M : Model X d) {n : ℕ} (D : Fin n → Obs X d) (π : X → Fin d) (α : ℝ) : ℝ :=
  1 / (n * Sn M D π) * ∑ i, ipw M π (D i) * Real.exp (-(D i).2.2 / α)

/-- Definition 4 (arXiv:2006.05630v7, p.12): the empirical dual objective
`φ̂_n(π, α) = −α log Ŵ_n(π, α) − αδ`. -/
noncomputable def phiHat (M : Model X d) (δ : ℝ) {n : ℕ} (D : Fin n → Obs X d) (π : X → Fin d)
    (α : ℝ) : ℝ :=
  -α * Real.log (What M D π α) - α * δ

/-- Definition 4, item 1 (arXiv:2006.05630v7, p.12): the distributionally robust value estimator
`Q̂_DRO(π) = sup_{α ≥ 0} φ̂_n(π, α)`.

**Formalization Note.** The supremum is over `α > 0`; the value at `α = 0` is defined by
Remark 2 (p.11) as the right limit (the essential infimum), so it does not change the supremum.
The family is bounded above by `maxᵢ |Yᵢ|` when `δ ≥ 0`, so the real supremum is the paper's. -/
noncomputable def QhatDRO (M : Model X d) (δ : ℝ) {n : ℕ} (D : Fin n → Obs X d)
    (π : X → Fin d) : ℝ :=
  ⨆ α : Set.Ioi (0 : ℝ), phiHat M δ D π α

/-- (4) (arXiv:2006.05630v7, p.15): `π̂_DRO ∈ argmax_{π ∈ Π} Q̂_DRO(π)`. A learner maps every
observed data set `D` to a policy of `Π` maximizing `Q̂_DRO` on `D`. -/
def IsDROLearner (M : Model X d) (δ : ℝ) (Pol : Set (X → Fin d)) {n : ℕ}
    (πhat : (Fin n → Obs X d) → X → Fin d) : Prop :=
  ∀ D, πhat D ∈ Pol ∧ ∀ π ∈ Pol, QhatDRO M δ D π ≤ QhatDRO M δ D (πhat D)

end DRBatchBandit


