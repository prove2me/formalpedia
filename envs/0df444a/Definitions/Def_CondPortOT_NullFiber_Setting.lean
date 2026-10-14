-- Prove2me | Definitions.Def_CondPortOT_NullFiber_Setting
-- name    : CondPortOT_NullFiber_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:28.951928+00:00
-- url     : https://prove2.me/theorems/b3ffdb37-2845-48ae-a7ee-6a3a9c77d1f0
-- title:
--   pp. 7–11, 18–19 — ground cost, empirical measure, fiber, conditional expectation, 𝔹_ρ, worst-case values, ρ_max, κ, d, ℐ₁, Assumption 2.4, BoundaryRegular, the LP of Proposition 4.3
-- statement:
--   This file fixes the model of Nguyen, Zhang, Wang, Blanchet, Delage and Ye for conditional portfolio decisions under optimal-transport ambiguity, in the setting of §4.1 (a fiber of positive radius).
--
--   Let $\mathcal X$ (covariates) and $\mathcal Y$ (returns) be Polish spaces with their Borel $\sigma$-algebras, and let $(\hat x_i,\hat y_i)$, $i\in[N]$, be $N\ge 1$ samples (repetitions allowed). The objects are:
--
--   1. **Ground cost.** For cost functions $\mathbb D_{\mathcal X}$ on $\mathcal X\times\mathcal X$ and $\mathbb D_{\mathcal Y}$ on $\mathcal Y\times\mathcal Y$, the separable cost $\mathbb D((x,y),(x',y'))=\mathbb D_{\mathcal X}(x,x')+\mathbb D_{\mathcal Y}(y,y')$, valued in $[0,\infty]$.
--   2. **Empirical distribution** $\widehat{\mathbb P}=N^{-1}\sum_{i\in[N]}\delta_{(\hat x_i,\hat y_i)}$.
--   3. **Neighbourhood and fiber.** $\mathcal N_\gamma(x_0)=\{x\in\mathcal X:\mathbb D_{\mathcal X}(x,x_0)\le\gamma\}$ and the fiber set $\mathcal N_\gamma(x_0)\times\mathcal Y$.
--   4. **Conditional expectation** of a loss $\ell:\mathcal Y\to\mathbb R$ on a set $S$: $\mathbb E_{\mathbb Q}[\ell(Y)\mid S]=\mathbb E_{\mathbb Q}[\ell(Y)\mathbb 1_S]/\mathbb Q(S)$, the numerator being $\int\ell^+-\int\ell^-$ in the extended reals.
--   5. **Ambiguity set** $\mathbb B_\rho=\{\mathbb Q\in\mathcal M(\mathcal X\times\mathcal Y):\mathbb W(\mathbb Q,\widehat{\mathbb P})\le\rho\}$, with $\mathbb W$ the optimal transport cost for $\mathbb D$.
--   6. **Worst-case conditional losses**
--   $$\sup_{\mathbb Q\in\mathbb B_\rho,\ \mathbb Q(X\in\mathcal N_\gamma(x_0))>0}\mathbb E_{\mathbb Q}[\ell(Y)\mid X\in\mathcal N_\gamma(x_0)],\qquad \sup_{\mathbb Q\in\mathbb B_\rho,\ \mathbb Q(X\in\mathcal N_\gamma(x_0))\ge\varepsilon}\mathbb E_{\mathbb Q}[\ell(Y)\mid X\in\mathcal N_\gamma(x_0)].$$
--   7. **Maximal budget** $\rho_{\max}(x_0,\gamma)=\inf\{\mathbb W(\mathbb Q,\widehat{\mathbb P}):\mathbb Q\in\mathcal M(\mathcal X\times\mathcal Y),\ \mathbb Q(X\in\mathcal N_\gamma(x_0))=0\}$.
--   8. **Projection and boundary costs** $\kappa_i=\inf_{x\in\mathcal N_\gamma(x_0)}\mathbb D_{\mathcal X}(x,\hat x_i)$ and $d_i=\inf_{x\in\partial\mathcal N_\gamma(x_0)}\mathbb D_{\mathcal X}(x,\hat x_i)$, and the index set $\mathcal I_1=\{i:\hat x_i\in\mathcal N_\gamma(x_0)\}$ (its complement is $\mathcal I_2$).
--   9. **Assumption 2.4.** (i) $\mathbb D_{\mathcal X},\mathbb D_{\mathcal Y}$ are symmetric, non-negative and continuous, and $\mathbb D((x,y),(x',y'))=0$ iff $(x,y)=(x',y')$; (ii) every $\hat x_i$ has a unique projection onto $\mathcal N_\gamma(x_0)$; (iii) for every boundary point $x$ of $\mathcal N_\gamma(x_0)$ and every $r>0$ there is $x'\notin\mathcal N_\gamma(x_0)$ with $\mathbb D_{\mathcal X}(x',x)\le r$.
--   10. **Boundary regularity** (an addition, see below): $\partial\mathcal N_\gamma(x_0)\neq\emptyset$; for $i\in\mathcal I_1$, $d_i=\inf_{x\notin\mathcal N_\gamma(x_0)}\mathbb D_{\mathcal X}(x,\hat x_i)$; for $i\in\mathcal I_2$, $d_i=\kappa_i$.
--   11. **The LP values of Proposition 4.3**: the set of numbers $N^{-1}\sum_{i\in\mathcal I_1}p_i$ over $p\in[0,1]^N$ with $N^{-1}\sum_{i\in\mathcal I_1}d_i(1-p_i)\le\rho$.
--
--   These objects are shared by every statement of the mission about the regime $\gamma>0$, $\rho<\rho_{\max}(x_0,\gamma)$.
--
--   **Formalization Note** The index set $[N]$ is `Fin N`. The paper's "min" in Definition 2.1, (7) and (14) is taken as an infimum (`transportCost`, `sInf`); attainment is stated only where a result asserts it. The transport cost is the published `RWPI.SqrtLasso.transportCost` (an infimum of lower Lebesgue integrals over couplings with first marginal $\mathbb Q$ and second marginal $\widehat{\mathbb P}$), and the expectation is the published `ModelRiskOT.Duality.extIntegral`, never the Bochner integral (which would be $0$ for a non-integrable loss). The ball uses `ENNReal.ofReal ρ`, so statements carry $\rho\ge0$ (the paper's $\rho\in\mathbb R_+$). The conditional expectation multiplies by $\mathbb Q(S)^{-1}$ computed in $\mathbb R$, which is $0$ when $\mathbb Q(S)=0$; the worst-case values only range over $\mathbb Q$ with positive or at least $\varepsilon$ fiber mass. The boundary $\partial$ is the topological `frontier` in $\mathcal X$. `BoundaryRegular` is not in the paper: its proofs (pp. 45–51) use that leaving the fiber from $\hat x_i\in\mathcal N_\gamma(x_0)$ costs $d_i$ in the limit, which does not follow from Assumption 2.4 for a general continuous cost; it holds when $\mathbb D_{\mathcal X}$ is a norm distance. `ℐ₁` is defined with classical decidability. Identical copies of the core definitions appear in the sibling missions of this paper (namespaces `CondPortOT.<Tag>`).
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, pp. 7–11 (§2, Definition 2.1, Assumption 2.4, (7)), pp. 17–19 (§4.1, ρ_max, (13), (14), Proposition 4.3)

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_CondPortOT_BigRadius_Setting
import Definitions.Def_CondPortOT_SingDual_Setting
import Definitions.Def_CondPortOT_SingUninf_Setting

namespace CondPortOT.NullFiber

open MeasureTheory

/-- Assumption 2.4 (Regularity conditions), pp. 10–11. -/
structure Assumption24 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) (x0 : X) (γ : ℝ) {N : ℕ} (xh : Fin N → X) : Prop where
  /-- (i) `𝔻_𝒳` is symmetric. -/
  symm_X : ∀ x x' : X, DX x x' = DX x' x
  /-- (i) `𝔻_𝒴` is symmetric. -/
  symm_Y : ∀ y y' : Y, DY y y' = DY y' y
  /-- (i) `𝔻_𝒳` is non-negative. -/
  nonneg_X : ∀ x x' : X, 0 ≤ DX x x'
  /-- (i) `𝔻_𝒴` is non-negative. -/
  nonneg_Y : ∀ y y' : Y, 0 ≤ DY y y'
  /-- (i) `𝔻_𝒳` is continuous on `𝒳 × 𝒳`. -/
  cont_X : Continuous (fun p : X × X => DX p.1 p.2)
  /-- (i) `𝔻_𝒴` is continuous on `𝒴 × 𝒴`. -/
  cont_Y : Continuous (fun p : Y × Y => DY p.1 p.2)
  /-- (i) `𝔻((x, y), (x', y')) = 0` if and only if `(x, y) = (x', y')`. -/
  eq_zero_iff : ∀ (x x' : X) (y y' : Y), DX x x' + DY y y' = 0 ↔ (x, y) = (x', y')
  /-- (ii) every `x̂ᵢ` has a unique projection onto `𝒩_γ(x₀)` under `𝔻_𝒳`. -/
  proj : ∀ i : Fin N, ∃! xp : X,
    xp ∈ CondPortOT.SingUninf.nbhd DX x0 γ ∧ ∀ x ∈ CondPortOT.SingUninf.nbhd DX x0 γ, DX xp (xh i) ≤ DX x (xh i)
  /-- (iii) every boundary point of `𝒩_γ(x₀)` has points outside `𝒩_γ(x₀)` at any cost `r > 0`. -/
  vicinity : ∀ x ∈ frontier (CondPortOT.SingUninf.nbhd DX x0 γ), ∀ r : ℝ, 0 < r →
    ∃ x' ∉ CondPortOT.SingUninf.nbhd DX x0 γ, DX x' x ≤ r

open Classical in

/-- The feasible values of the linear program of Proposition 4.3:
`{N⁻¹ Σ_{i ∈ ℐ₁} pᵢ : p ∈ [0, 1]ᴺ, N⁻¹ Σ_{i ∈ ℐ₁} dᵢ (1 − pᵢ) ≤ ρ}`. -/
def knapsackSet {X : Type*} [TopologicalSpace X] (DX : X → X → ℝ) (x0 : X) (γ : ℝ) {N : ℕ}
    (xh : Fin N → X) (ρ : ℝ) : Set ℝ :=
  {r | ∃ p : Fin N → ℝ, (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) ∧
    (N : ℝ)⁻¹ * ∑ i ∈ CondPortOT.BigRadius.I1 DX x0 γ xh, CondPortOT.BigRadius.bdDist DX x0 γ xh i * (1 - p i) ≤ ρ ∧
    r = (N : ℝ)⁻¹ * ∑ i ∈ CondPortOT.BigRadius.I1 DX x0 γ xh, p i}

end CondPortOT.NullFiber


