-- Prove2me | Definitions.Def_LimitedPriceChanges_AlgorithmI_DataBasedOptimization
-- name    : LimitedPriceChanges_AlgorithmI_DataBasedOptimization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:00.360987+00:00
-- url     : https://prove2.me/theorems/acb4ead4-80cb-4196-b2ce-8a9a0acaab2c
-- title:
--   p. 7 and pp. 20–21 — the data-based optimization problem: G*(z), price and level selections, and Assumption A
-- statement:
--   This file sets up the general parametric optimization problem of Appendix B, on which both the estimation-to-profit transfer (Theorem B1) and the model of §2 rest.
--
--   **The problem.** An objective $G(p,y,\mathbf z)$ depends on a continuous decision $p\in\mathcal P=[p^l,p^h]$, a discrete decision $y\in\mathcal Y$ (a nonempty finite set of nonnegative integers) and a parameter $\mathbf z$ in a normed space; $\mathcal Z$ is a set of admissible parameters.
--
--   **Selections.** A *price selection* is a function $p^*_y(\mathbf z')$ such that, for every $y\in\mathcal Y$ and $\mathbf z'\in\mathcal Z$, $p^*_y(\mathbf z')\in\mathcal P$ and
--   $$
--   G(p,y,\mathbf z')\le G\big(p^*_y(\mathbf z'),y,\mathbf z'\big)\quad\text{for all }p\in\mathcal P,
--   $$
--   i.e. $p^*_y(\mathbf z')$ is an optimal solution of $\max_{p\in\mathcal P}G(p,y,\mathbf z')$. A *level selection* $\hat y(\mathbf z')\in\mathcal Y$ maximizes $y\mapsto G(p^*_y(\mathbf z'),y,\mathbf z')$ over $\mathcal Y$, i.e. $\hat y(\mathbf z')\in\mathcal Y^*(\mathbf z')$, the set of optimal discrete decisions under $\mathbf z'$. The optimal value is the finite maximum
--   $$
--   G^*(\mathbf z)=\max_{y\in\mathcal Y}G\big(p^*_y(\mathbf z),y,\mathbf z\big),
--   $$
--   which equals $\max_{(p,y)\in\mathcal P\times\mathcal Y}G(p,y,\mathbf z)$ for a price selection.
--
--   **Assumption A** (Regularity Conditions) at the true parameter $\mathbf z$, for the price selection $p^*$:
--
--   1. (i) for every $y\in\mathcal Y$ there is $\delta>0$ such that $G(p^*_y(\mathbf z),y,\mathbf z)<G^*(\mathbf z)$ implies $G(p^*_y(\mathbf z),y,\mathbf z)<G^*(\mathbf z)-\delta$; and for every $p\in\mathcal P$, $y\in\mathcal Y$ there are $c_1,K_1>0$ with $|G(p,y,\mathbf z')-G(p,y,\mathbf z)|\le K_1\|\mathbf z'-\mathbf z\|$ for all $\mathbf z'\in\mathcal Z$ with $\|\mathbf z'-\mathbf z\|<c_1$;
--   2. (ii) there are $c,M>0$ such that for every $y\in\mathcal Y$ and every $\mathbf z'\in\mathcal Z$ with $\|\mathbf z'-\mathbf z\|<c$, the map $p\mapsto G(p,y,\mathbf z')$ is twice differentiable on $\mathcal P$ with second derivative bounded in absolute value by $M$;
--   3. (iii) for every $y\in\mathcal Y$, $p^*_y(\mathbf z)$ lies in the interior $(p^l,p^h)$ of $\mathcal P$, and there are $c_2,K_2>0$ with $|p^*_y(\mathbf z')-p^*_y(\mathbf z)|\le K_2\|\mathbf z'-\mathbf z\|$ for all $\mathbf z'\in\mathcal Z$ with $\|\mathbf z'-\mathbf z\|<c_2$.
--
--   These are the hypotheses under which a good parameter estimate yields a near-optimal plug-in decision.
--
--   **Formalization Note** The continuous decision is scalar ($r_1=1$) and the discrete decision a natural number ($r_2=1$), the setting of §2. The derivatives in (ii) are one-sided derivatives within $[p^l,p^h]$. In (ii) the bound $M$ and radius $c$ are uniform over $y$ and over $\mathbf z'$ near $\mathbf z$, which is how the proof of Theorem B1 uses them (the constant $K_{19}$ in (13)). All perturbed parameters range over $\mathcal Z$. The printed (iii) asks for "an optimal solution $p^*_y(\mathbf z)$ … locally Lipschitz around $\mathbf z$"; this is the function $p^*$, required to be optimal at every $\mathbf z'\in\mathcal Z$.
-- source:
--   Chen, Chao and Wang, Data-Based Dynamic Pricing and Inventory Control with Censored Demand and Limited Price Changes, SSRN 2700747 (revision of 2020-02-10), p. 6 (G*, p*_y), p. 7 (Assumption A), pp. 20–21 (Appendix B, 𝒫*_y(z), 𝒴*(z))

import Mathlib

namespace LimitedPriceChanges.AlgorithmI

/-! # The data-based optimization problem of Appendix B

Chen, Chao and Wang, *Data-Based Dynamic Pricing and Inventory Control with Censored Demand and
Limited Price Changes*, SSRN 2700747 (revision of 2020-02-10), p. 7 (Assumption A) and
pp. 20–21 (Appendix B).

An objective `G p y z` of a continuous decision `p ∈ 𝒫 = [pl, ph]`, a discrete decision
`y ∈ 𝒴` (a nonempty finite set of naturals) and a parameter `z` in a normed space. The price
selection `pstar y z` is the function `p*_y(z)` of Assumption A(iii); `optValue` is
`G*(z) = max_{y ∈ 𝒴} G(p*_y(z), y, z)`, which is the maximum of `G(·, ·, z)` over `𝒫 × 𝒴`
whenever `pstar` is a price selection. -/

variable {E : Type*} [NormedAddCommGroup E]

/-- `G*(z) = max_{y ∈ 𝒴} G(p*_y(z), y, z)`, a finite maximum (no real `sSup`). -/
noncomputable def optValue (Y : Finset ℕ) (hY : Y.Nonempty) (G : ℝ → ℕ → E → ℝ)
    (pstar : ℕ → E → ℝ) (z : E) : ℝ :=
  Y.sup' hY (fun y => G (pstar y z) y z)

/-- `pstar` is a price selection on `𝒵`: for every `y ∈ 𝒴` and every `z' ∈ 𝒵`, `pstar y z'`
lies in `𝒫 = [pl, ph]` and maximizes `p ↦ G(p, y, z')` over `𝒫`, i.e. it is an optimal
solution `p*_y(z')` of `max_{p ∈ 𝒫} G(p, y, z')` (p. 6). -/
def IsPriceSelection (pl ph : ℝ) (Y : Finset ℕ) (Z : Set E) (G : ℝ → ℕ → E → ℝ)
    (pstar : ℕ → E → ℝ) : Prop :=
  ∀ y ∈ Y, ∀ z' ∈ Z, pstar y z' ∈ Set.Icc pl ph ∧
    ∀ p ∈ Set.Icc pl ph, G p y z' ≤ G (pstar y z') y z'

/-- `ysel` selects an optimal order-up-to level on `𝒵`: for every `z' ∈ 𝒵`, `ysel z' ∈ 𝒴`
maximizes `y ↦ G(p*_y(z'), y, z') = max_{p ∈ 𝒫} G(p, y, z')` over `𝒴`, i.e.
`ysel z' ∈ 𝒴*(z')` (p. 21). -/
def IsLevelSelection (Y : Finset ℕ) (Z : Set E) (G : ℝ → ℕ → E → ℝ) (pstar : ℕ → E → ℝ)
    (ysel : E → ℕ) : Prop :=
  ∀ z' ∈ Z, ysel z' ∈ Y ∧ ∀ y ∈ Y, G (pstar y z') y z' ≤ G (pstar (ysel z') z') (ysel z') z'

/-- **Assumption A** (Regularity Conditions), p. 7, at the true parameter `z`, for the price
selection `pstar`. All perturbed parameters `z'` range over `𝒵`.
* (i) for every `p ∈ 𝒫`, `y ∈ 𝒴` there is a gap `δ > 0`: if `G(p*_y(z), y, z) < G*(z)` then
  `G(p*_y(z), y, z) < G*(z) − δ`; and there are `c₁, K₁ > 0` with
  `|G(p, y, z') − G(p, y, z)| ≤ K₁‖z' − z‖` whenever `‖z' − z‖ < c₁`;
* (ii) there are `c, M > 0` such that for every `y ∈ 𝒴` and every `z' ∈ 𝒵` with `‖z' − z‖ < c`,
  `p ↦ G(p, y, z')` is twice differentiable on `𝒫` with second derivative bounded by `M`;
* (iii) for every `y ∈ 𝒴`, `p*_y(z)` lies in the interior `(pl, ph)` of `𝒫`, and there are
  `c₂, K₂ > 0` with `|p*_y(z') − p*_y(z)| ≤ K₂‖z' − z‖` whenever `‖z' − z‖ < c₂`. -/
structure AssumptionA (pl ph : ℝ) (Y : Finset ℕ) (hY : Y.Nonempty) (Z : Set E)
    (G : ℝ → ℕ → E → ℝ) (pstar : ℕ → E → ℝ) (z : E) : Prop where
  gap : ∀ y ∈ Y, ∃ δ : ℝ, 0 < δ ∧
    (G (pstar y z) y z < optValue Y hY G pstar z →
      G (pstar y z) y z < optValue Y hY G pstar z - δ)
  lipschitz_G : ∀ p ∈ Set.Icc pl ph, ∀ y ∈ Y, ∃ c₁ K₁ : ℝ, 0 < c₁ ∧ 0 < K₁ ∧
    ∀ z' ∈ Z, ‖z' - z‖ < c₁ → |G p y z' - G p y z| ≤ K₁ * ‖z' - z‖
  second_deriv : ∃ c M : ℝ, 0 < c ∧ 0 < M ∧ ∀ y ∈ Y, ∀ z' ∈ Z, ‖z' - z‖ < c →
    DifferentiableOn ℝ (fun p => G p y z') (Set.Icc pl ph) ∧
    DifferentiableOn ℝ (derivWithin (fun p => G p y z') (Set.Icc pl ph)) (Set.Icc pl ph) ∧
    ∀ p ∈ Set.Icc pl ph,
      |derivWithin (derivWithin (fun p => G p y z') (Set.Icc pl ph)) (Set.Icc pl ph) p| ≤ M
  interior : ∀ y ∈ Y, pstar y z ∈ Set.Ioo pl ph
  lipschitz_pstar : ∀ y ∈ Y, ∃ c₂ K₂ : ℝ, 0 < c₂ ∧ 0 < K₂ ∧
    ∀ z' ∈ Z, ‖z' - z‖ < c₂ → |pstar y z' - pstar y z| ≤ K₂ * ‖z' - z‖

end LimitedPriceChanges.AlgorithmI


