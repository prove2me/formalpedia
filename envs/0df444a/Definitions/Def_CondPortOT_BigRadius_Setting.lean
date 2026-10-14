-- Prove2me | Definitions.Def_CondPortOT_BigRadius_Setting
-- name    : CondPortOT_BigRadius_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:05.840994+00:00
-- url     : https://prove2.me/theorems/1fd2755b-07b4-49ee-b7cf-d70f06dfa0fd
-- title:
--   pp. 10–11, 18 — Assumption 2.4, ρ_max, boundary distances d_i, index set ℐ₁, BoundaryRegular (γ > 0)
-- statement:
--   This file adds to the shared model of Nguyen, Zhang, Wang, Blanchet, Delage and Ye the objects of §4.1, where the fiber has radius $\gamma>0$. The model itself (ground cost $\mathbb D=\mathbb D_{\mathcal X}+\mathbb D_{\mathcal Y}$, empirical distribution $\hat{\mathbb P}=N^{-1}\sum_{i\in[N]}\delta_{(\hat x_i,\hat y_i)}$, neighbourhood $\mathcal N_\gamma(x_0)=\{x\in\mathcal X:\mathbb D_{\mathcal X}(x,x_0)\le\gamma\}$, fiber set $\mathcal N_\gamma(x_0)\times\mathcal Y$, optimal transport ball $\mathbb B_\rho$, conditional expectation and projection costs $\kappa_i$) is imported from `CondPortOT.SingUninf.Setting`.
--
--   Let $\mathcal X,\mathcal Y$ be topological spaces with ground costs $\mathbb D_{\mathcal X}$, $\mathbb D_{\mathcal Y}$, a centre $x_0\in\mathcal X$, a radius $\gamma$ and samples $(\hat x_i,\hat y_i)$, $i\in[N]$.
--
--   1. **Assumption 2.4** (pp. 10–11). (i) $\mathbb D_{\mathcal X}$ and $\mathbb D_{\mathcal Y}$ are symmetric, non-negative and continuous on $\mathcal X\times\mathcal X$ and $\mathcal Y\times\mathcal Y$, and $\mathbb D_{\mathcal X}(x,x')+\mathbb D_{\mathcal Y}(y,y')=0$ if and only if $(x,y)=(x',y')$; (ii) every $\hat x_i$ has a unique minimiser of $\mathbb D_{\mathcal X}(\cdot,\hat x_i)$ over $\mathcal N_\gamma(x_0)$; (iii) for every $x\in\partial\mathcal N_\gamma(x_0)$ and every $r>0$ there is $x'\in\mathcal X\setminus\mathcal N_\gamma(x_0)$ with $\mathbb D_{\mathcal X}(x',x)\le r$.
--   2. **Maximum radius** (p. 18).
--   $$\rho_{\max}(x_0,\gamma)=\inf\Big\{\mathbb W(\mathbb Q,\hat{\mathbb P}):\ \mathbb Q\in\mathcal M(\mathcal X\times\mathcal Y),\ \mathbb Q(X\in\mathcal N_\gamma(x_0))=0\Big\}\in[0,\infty],$$
--   the least transport budget that moves all the mass out of the fiber.
--   3. **Boundary distances** (display (14), p. 18). $d_i=\inf_{x\in\partial\mathcal N_\gamma(x_0)}\mathbb D_{\mathcal X}(x,\hat x_i)$.
--   4. **Samples inside the fiber** (display (13), p. 18). $\mathcal I_1=\{i\in[N]:\hat x_i\in\mathcal N_\gamma(x_0)\}$; its complement is $\mathcal I_2$.
--   5. **Boundary regularity** (not in the paper). $\partial\mathcal N_\gamma(x_0)\neq\emptyset$; for $i\in\mathcal I_1$, $d_i$ is the greatest lower bound of $\{\mathbb D_{\mathcal X}(x,\hat x_i):x\notin\mathcal N_\gamma(x_0)\}$, so leaving the fiber from $\hat x_i$ costs exactly $d_i$ in the limit; and for $i\in\mathcal I_2$, $d_i=\kappa_i$, as stated on p. 18.
--
--   These objects enter Propositions 4.1–4.3 and Theorem 4.4: $\rho_{\max}=N^{-1}\sum_{i\in\mathcal I_1}d_i$ is Proposition 4.1, and $\rho>\rho_{\max}$ is the regime of Proposition 4.2.
--
--   **Formalization Note** $[N]$ is `Fin N` and $\mathcal I_1$ is a `Finset` built with classical decidability. $d_i$ is a real infimum (`sInf`), which is the paper's "min" whenever that minimum exists; on an empty boundary it would be $0$, which `BoundaryRegular` excludes. The boundary $\partial$ is the topological frontier in $\mathcal X$. $\rho_{\max}$ is $[0,\infty]$-valued, with the infimum of the empty set equal to $+\infty$. `BoundaryRegular` mentions only $\mathbb D_{\mathcal X}$, $x_0$, $\gamma$ and the samples, never a measure or a loss; it holds when $\mathbb D_{\mathcal X}$ is a norm distance, and Proposition 4.1 is false without it for a general continuous cost (a non-monotone $\mathbb D_{\mathcal X}(x,x')=h(|x-x'|)$ lets a sample leave the fiber more cheaply than $d_i$). Assumption 2.4 is stated here with the same content as in the other files of the series; only the field names differ.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, pp. 10–11 (Assumption 2.4) and p. 18 (ρ_max, displays (13), (14))

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_CondPortOT_SingUninf_Setting

namespace CondPortOT.BigRadius

open MeasureTheory RWPI.SqrtLasso ModelRiskOT.Duality

/-- Assumption 2.4 (Regularity conditions), pp. 10–11. -/
structure Assumption24 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) (x0 : X) (γ : ℝ) {N : ℕ} (xh : Fin N → X) : Prop where
  /-- (i) `𝔻_𝒳` is symmetric. -/
  symmX : ∀ x x', DX x x' = DX x' x
  /-- (i) `𝔻_𝒴` is symmetric. -/
  symmY : ∀ y y', DY y y' = DY y' y
  /-- (i) `𝔻_𝒳` is non-negative. -/
  nonnegX : ∀ x x', 0 ≤ DX x x'
  /-- (i) `𝔻_𝒴` is non-negative. -/
  nonnegY : ∀ y y', 0 ≤ DY y y'
  /-- (i) `𝔻_𝒳` is continuous on `𝒳 × 𝒳`. -/
  contX : Continuous (fun p : X × X => DX p.1 p.2)
  /-- (i) `𝔻_𝒴` is continuous on `𝒴 × 𝒴`. -/
  contY : Continuous (fun p : Y × Y => DY p.1 p.2)
  /-- (i) `𝔻((x, y), (x', y')) = 0` iff `(x, y) = (x', y')`. -/
  eq_zero_iff : ∀ x x' y y', DX x x' + DY y y' = 0 ↔ (x, y) = (x', y')
  /-- (ii) every `x̂ᵢ` has a unique projection onto `𝒩_γ(x₀)` under `𝔻_𝒳`. -/
  proj : ∀ i, ∃! xp, xp ∈ CondPortOT.SingUninf.nbhd DX x0 γ ∧ ∀ x ∈ CondPortOT.SingUninf.nbhd DX x0 γ, DX xp (xh i) ≤ DX x (xh i)
  /-- (iii) every boundary point of `𝒩_γ(x₀)` has points outside `𝒩_γ(x₀)` arbitrarily close. -/
  vicinity : ∀ x ∈ frontier (CondPortOT.SingUninf.nbhd DX x0 γ), ∀ r : ℝ, 0 < r → ∃ x' ∉ CondPortOT.SingUninf.nbhd DX x0 γ, DX x' x ≤ r

/-- `ρ_max(x₀, γ) = inf {W(ℚ, ℙ̂) : ℚ ∈ ℳ(𝒳 × 𝒴), ℚ(X ∈ 𝒩_γ(x₀)) = 0}`, p. 18. -/
noncomputable def rhoMax {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (xh : Fin N → X) (yh : Fin N → Y) (x0 : X)
    (γ : ℝ) : ENNReal :=
  ⨅ (Q : Measure (X × Y)) (_ : IsProbabilityMeasure Q ∧ Q (CondPortOT.SingUninf.fiber DX x0 γ) = 0),
    transportCost (CondPortOT.SingUninf.groundCost DX DY) Q (CondPortOT.SingUninf.empirical xh yh)

/-- `dᵢ = inf_{x ∈ ∂𝒩_γ(x₀)} 𝔻_𝒳(x, x̂ᵢ)`, display (14), p. 18; `∂` is the frontier in `𝒳`. -/
noncomputable def bdDist {X : Type*} [TopologicalSpace X] (DX : X → X → ℝ) (x0 : X) (γ : ℝ)
    {N : ℕ} (xh : Fin N → X) (i : Fin N) : ℝ :=
  sInf ((fun x => DX x (xh i)) '' frontier (CondPortOT.SingUninf.nbhd DX x0 γ))

open Classical in
/-- The index set `ℐ₁ = {i ∈ [N] : x̂ᵢ ∈ 𝒩_γ(x₀)}`, display (13), p. 18. -/
noncomputable def I1 {X : Type*} (DX : X → X → ℝ) (x0 : X) (γ : ℝ) {N : ℕ} (xh : Fin N → X) :
    Finset (Fin N) :=
  Finset.univ.filter (fun i => xh i ∈ CondPortOT.SingUninf.nbhd DX x0 γ)

/-- Disclosed regularity predicate (not in the paper): the boundary of `𝒩_γ(x₀)` is nonempty,
leaving the fiber from a sample inside it costs exactly `dᵢ` in the limit, and for a sample
outside it `dᵢ = κᵢ` (stated on p. 18). Holds when `𝔻_𝒳` is a norm distance. -/
structure BoundaryRegular {X : Type*} [TopologicalSpace X] (DX : X → X → ℝ) (x0 : X) (γ : ℝ)
    {N : ℕ} (xh : Fin N → X) : Prop where
  frontier_nonempty : (frontier (CondPortOT.SingUninf.nbhd DX x0 γ)).Nonempty
  exit_cost : ∀ i ∈ I1 DX x0 γ xh,
    IsGLB ((fun x => DX x (xh i)) '' (CondPortOT.SingUninf.nbhd DX x0 γ)ᶜ) (bdDist DX x0 γ xh i)
  enter_cost : ∀ i ∉ I1 DX x0 γ xh, bdDist DX x0 γ xh i = CondPortOT.SingUninf.kappa DX x0 γ xh i

end CondPortOT.BigRadius


