-- Prove2me | Definitions.Def_DRBatchBandit_RobustValue
-- name    : DRBatchBandit_RobustValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:17.326144+00:00
-- url     : https://prove2.me/theorems/8cf80a17-741d-41dd-bf57-e0dba136fdd0
-- title:
--   KL uncertainty set $\mathcal U_{P_0}(\delta)$, robust value $Q_{\mathrm{DRO}}$ and robust regret $R_{\mathrm{DRO}}$ (Definitions 2–3)
-- statement:
--   This file fixes the distributionally robust objects of §2.3 of Si, Zhang, Zhou and Blanchet.
--
--   **Data-generating law.** There are $d$ actions $a^1,\dots,a^d$ and a context space $\mathcal X$ with a $\sigma$-algebra. A draw consists of the context $X$, the potential rewards $(Y(a^1),\dots,Y(a^d))\in\mathbb R^d$ and the logged action $A$. Write $\mathbf P_0$ for the law of $(X,Y(a^1),\dots,Y(a^d))$ on $\mathcal X\times\mathbb R^d$ (§2.1, p.8); it does not involve $A$.
--
--   **KL ball** (p.10). For a probability measure $\mathbf P$ on the same space, $D(\mathbf P\|\mathbf P_0)=\int\log\big(\tfrac{d\mathbf P}{d\mathbf P_0}\big)\,d\mathbf P$, and
--   $$\mathcal U_{\mathbf P_0}(\delta)=\{\mathbf P\ll\mathbf P_0:\ D(\mathbf P\|\mathbf P_0)\le\delta\}.$$
--
--   **Robust value** (Definition 2, p.10). For a policy $\pi:\mathcal X\to\{a^1,\dots,a^d\}$,
--   $$Q_{\mathrm{DRO}}(\pi)=\inf_{\mathbf P\in\mathcal U_{\mathbf P_0}(\delta)}\mathbf E_{\mathbf P}[Y(\pi(X))].$$
--
--   **Robust regret** (Definition 3, p.10). For a policy class $\Pi$,
--   $$R_{\mathrm{DRO}}(\pi)=\max_{\pi'\in\Pi}Q_{\mathrm{DRO}}(\pi')-Q_{\mathrm{DRO}}(\pi).$$
--
--   These are the quantities Theorem 2 bounds.
--
--   **Formalization Note** The model is the published `OfflinePolicyLearning.Regret.Model` (feature law `PX`, reward kernel `κY`, logging kernel `κA`); $\mathbf P_0$ is `PX ⊗ₘ κY`. Ball members are required to be probability measures (Mathlib's `klDiv` coincides with $\int\log(d\mathbf P/d\mathbf P_0)\,d\mathbf P$ on probability measures). $Q_{\mathrm{DRO}}$ is a real infimum over the ball, which contains $\mathbf P_0$; it is bounded below under Assumption 1.3. The maximum over $\Pi$ is a supremum over `Pol`, equal to the maximum when it is attained (the paper notes on p.10 that its results extend to the supremum).
-- source:
--   Si, Zhang, Zhou & Blanchet, Distributionally Robust Batch Contextual Bandits, arXiv:2006.05630v7, §2.1 p.8 (P₀); §2.3 p.10 (KL divergence, 𝒰_{P₀}(δ), Definition 2, Definition 3). PDF sha256 ac485985feb75d33b603f06f5a5d93c52077877db7be11de3d71107c7c374b02

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Setting

open MeasureTheory ProbabilityTheory InformationTheory

namespace DRBatchBandit

open OfflinePolicyLearning.Regret

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

/-- The underlying distribution `P₀` of the context and the potential rewards
`(X, Y(a¹), …, Y(a^d))` on `𝒳 × ∏ⱼ 𝒴ⱼ` (Si, Zhang, Zhou & Blanchet, *Distributionally Robust
Batch Contextual Bandits*, arXiv:2006.05630v7, §2.1, p.8).

**Formalization Note.** Actions are `Fin d` (0-based) and the reward vector is a point of
`Fin d → ℝ`. `P₀` is the feature law `M.PX` composed with the conditional law `M.κY` of the
reward vector; it does not involve the logged action `A`. -/
noncomputable def P0 (M : Model X d) : Measure (X × (Fin d → ℝ)) := M.PX ⊗ₘ M.κY

/-- The distributional uncertainty set `𝒰_{P₀}(δ) = {P ≪ P₀ | D(P‖P₀) ≤ δ}` (arXiv:2006.05630v7,
§2.3, p.10), with `D(P‖P₀) = ∫ log(dP/dP₀) dP` the Kullback–Leibler divergence.

**Formalization Note.** The elements are probability measures on `𝒳 × ∏ⱼ 𝒴ⱼ`; Mathlib's
`klDiv` (which adds `P₀(univ) − P(univ)`) agrees with `∫ log(dP/dP₀) dP` on probability
measures. The radius is compared through `ENNReal.ofReal δ`. -/
def klBall (M : Model X d) (δ : ℝ) : Set (Measure (X × (Fin d → ℝ))) :=
  {P | IsProbabilityMeasure P ∧ P ≪ P0 M ∧ klDiv P (P0 M) ≤ ENNReal.ofReal δ}

/-- Definition 2 (arXiv:2006.05630v7, p.10): the distributionally robust value function
`Q_DRO(π) = inf_{P ∈ 𝒰_{P₀}(δ)} E_P[Y(π(X))]`.

**Formalization Note.** A real infimum over the (nonempty: it contains `P₀`) ball; it is bounded
below by `0` under bounded rewards (Assumption 1.3). -/
noncomputable def QDRO (M : Model X d) (δ : ℝ) (π : X → Fin d) : ℝ :=
  ⨅ P : klBall M δ, ∫ z, z.2 (π z.1) ∂(P : Measure (X × (Fin d → ℝ)))

/-- Definition 3 (arXiv:2006.05630v7, p.10): the distributionally robust regret
`R_DRO(π) = max_{π' ∈ Π} Q_DRO(π') − Q_DRO(π)`.

**Formalization Note.** The maximum over `Π` is written as a supremum over `Pol` (equal to the
maximum when it is attained; the paper says its results extend to the supremum, p.10). -/
noncomputable def RDRO (M : Model X d) (δ : ℝ) (Pol : Set (X → Fin d)) (π : X → Fin d) : ℝ :=
  (⨆ π' : Pol, QDRO M δ π'.1) - QDRO M δ π

end DRBatchBandit


