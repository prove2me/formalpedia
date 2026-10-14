-- Prove2me | Definitions.Def_CondPortOT_SingDual_Setting
-- name    : CondPortOT_SingDual_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:07.617979+00:00
-- url     : https://prove2.me/theorems/28a34a67-9505-4544-91bc-68c7e2b954e7
-- title:
--   pp. 8, 10–11, 36, 41 — Assumption 2.4, worst-case value of (4), ρ_min, inner supremum of Proposition A.5 and its dual
-- statement:
--   This file adds to the shared model of Nguyen, Zhang, Wang, Blanchet, Delage and Ye the objects of problem (4) with a fiber-mass requirement $\varepsilon>0$ and of the dual reformulation of §3.2. The model itself (ground cost $\mathbb D=\mathbb D_{\mathcal X}+\mathbb D_{\mathcal Y}$, empirical distribution $\hat{\mathbb P}=N^{-1}\sum_{i\in[N]}\delta_{(\hat x_i,\hat y_i)}$, neighbourhood $\mathcal N_\gamma(x_0)=\{x\in\mathcal X:\mathbb D_{\mathcal X}(x,x_0)\le\gamma\}$, fiber set $\mathcal N_\gamma(x_0)\times\mathcal Y$, optimal transport ball $\mathbb B_\rho=\{\mathbb Q:\mathbb W(\mathbb Q,\hat{\mathbb P})\le\rho\}$, conditional expectation and projection costs $\kappa_i$) is imported from `CondPortOT.SingUninf.Setting`. A loss $\ell:\mathcal Y\to\mathbb R$ stands for $y\mapsto\ell(y,\alpha,\beta)$ at a fixed decision.
--
--   1. **Assumption 2.4** (pp. 10–11). (i) $\mathbb D_{\mathcal X}$ and $\mathbb D_{\mathcal Y}$ are symmetric, non-negative and continuous, and $\mathbb D_{\mathcal X}(x,x')+\mathbb D_{\mathcal Y}(y,y')=0$ if and only if $(x,y)=(x',y')$; (ii) every $\hat x_i$ has a unique minimiser of $\mathbb D_{\mathcal X}(\cdot,\hat x_i)$ over $\mathcal N_\gamma(x_0)$; (iii) for every $x\in\partial\mathcal N_\gamma(x_0)$ and $r>0$ there is $x'\notin\mathcal N_\gamma(x_0)$ with $\mathbb D_{\mathcal X}(x',x)\le r$.
--   2. **Worst-case conditional expected loss** (problem (4), p. 8). For $\varepsilon>0$,
--   $$\sup\Big\{\mathbb E_{\mathbb Q}[\ell(Y)\mid X\in\mathcal N_\gamma(x_0)]:\ \mathbb Q\in\mathbb B_\rho,\ \mathbb Q(X\in\mathcal N_\gamma(x_0))\ge\varepsilon\Big\}\in[-\infty,+\infty].$$
--   3. **Minimum radius** (display (8), p. 11). $\rho_{\min}(x_0,\gamma,\varepsilon)=\inf\{\mathbb W(\mathbb Q,\hat{\mathbb P}):\ \mathbb Q\in\mathcal M(\mathcal X\times\mathcal Y),\ \mathbb Q(X\in\mathcal N_\gamma(x_0))\ge\varepsilon\}\in[0,\infty]$.
--   4. **Inner problem for fixed weights** (Proposition A.5, p. 36). For a weight vector $\upsilon$,
--   $$\sup\Big\{(N\varepsilon)^{-1}\sum_{i\in[N]}\upsilon_i\,\mathbb E_{\mu_0^i}[\ell(Y)]:\ \mu_0^i\in\mathcal M(\mathcal Y),\ \sum_{i\in[N]}\upsilon_i\big(\mathbb D_{\mathcal X}(x_0,\hat x_i)+\mathbb E_{\mu_0^i}[\mathbb D_{\mathcal Y}(Y,\hat y_i)]\big)\le N\rho\Big\}.$$
--   5. **Its dual** (proof of Theorem 3.2, p. 41).
--   $$\inf\Big\{\lambda_1\Big(N\rho-\sum_{i\in[N]}\upsilon_i\mathbb D_{\mathcal X}(x_0,\hat x_i)\Big)+\sum_{i\in[N]}\theta_i:\ \lambda_1\ge0,\ \theta\in\mathbb R^N,\ \upsilon_i\mathbb D_{\mathcal Y}(y,\hat y_i)\lambda_1+\theta_i\ge(N\varepsilon)^{-1}\upsilon_i\ell(y)\ \ \forall y\in\mathcal Y,\ i\in[N]\Big\}.$$
--
--   These objects carry Theorem 3.2 and its milestones: the feasibility threshold $\rho_{\min}$, the representation of the worst case as an outer supremum over $\upsilon$ of the inner problem, and the duality between the inner problem and its dual.
--
--   **Formalization Note** The worst-case value and both inner problems are suprema/infima in $[-\infty,+\infty]$ (`EReal`): an empty supremum is $-\infty$ and an empty infimum is $+\infty$. The worst-case value is meant for $\varepsilon>0$: for $\varepsilon\le0$ the mass constraint, written `ENNReal.ofReal ε ≤ ℚ(fiber)`, is vacuous and measures with null fiber mass would enter at the junk conditional expectation $0$; every statement carries $\varepsilon>0$. Expectations of $\ell$ use the published `ModelRiskOT.Duality.extIntegral` ($\int\ell^+-\int\ell^-$ with $\infty-\infty=-\infty$), so no integrability of $\ell$ is assumed, and $\mathbb E_{\mu_0^i}[\mathbb D_{\mathcal Y}(Y,\hat y_i)]$ is a lower Lebesgue integral in $[0,\infty]$. In the inner constraint, $\upsilon_i$, $\mathbb D_{\mathcal X}$ and $N\rho$ enter through `ENNReal.ofReal` (negative values read as $0$); the statements using it restrict $\upsilon\in[0,1]^N$, carry Assumption 2.4 (non-negative costs) and force $\rho>0$. $\rho_{\min}$ is $[0,\infty]$-valued, with the infimum of the empty set (e.g. $\varepsilon>1$) equal to $+\infty$. Assumption 2.4 is stated here with the same content as in the other files of the series; only the field names differ.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, p. 8 (problem (4)), pp. 10–11 (Assumption 2.4, display (8)), p. 36 (Proposition A.5), p. 41 (proof of Theorem 3.2)

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_CondPortOT_SingUninf_Setting

namespace CondPortOT.SingDual

open MeasureTheory

/-- Assumption 2.4 (Regularity conditions), pp. 10–11. -/
structure Assumption24 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) (x0 : X) (γ : ℝ) {N : ℕ} (xh : Fin N → X) : Prop where
  /-- (i) `𝔻_𝒳` is symmetric. -/
  symm_X : ∀ x x', DX x x' = DX x' x
  /-- (i) `𝔻_𝒴` is symmetric. -/
  symm_Y : ∀ y y', DY y y' = DY y' y
  /-- (i) `𝔻_𝒳` is non-negative. -/
  nonneg_X : ∀ x x', 0 ≤ DX x x'
  /-- (i) `𝔻_𝒴` is non-negative. -/
  nonneg_Y : ∀ y y', 0 ≤ DY y y'
  /-- (i) `𝔻_𝒳` is continuous on `𝒳 × 𝒳`. -/
  cont_X : Continuous (fun p : X × X => DX p.1 p.2)
  /-- (i) `𝔻_𝒴` is continuous on `𝒴 × 𝒴`. -/
  cont_Y : Continuous (fun p : Y × Y => DY p.1 p.2)
  /-- (i) `𝔻((x, y), (x', y')) = 0` if and only if `(x, y) = (x', y')`. -/
  zero_iff : ∀ x x' y y', DX x x' + DY y y' = 0 ↔ (x, y) = (x', y')
  /-- (ii) every `x̂ᵢ` has a unique projection onto `𝒩_γ(x₀)` under `𝔻_𝒳`. -/
  proj : ∀ i, ∃! xp, xp ∈ CondPortOT.SingUninf.nbhd DX x0 γ ∧ ∀ x ∈ CondPortOT.SingUninf.nbhd DX x0 γ, DX xp (xh i) ≤ DX x (xh i)
  /-- (iii) every boundary point of `𝒩_γ(x₀)` has points outside `𝒩_γ(x₀)` at arbitrarily small cost. -/
  vicinity : ∀ x ∈ frontier (CondPortOT.SingUninf.nbhd DX x0 γ), ∀ r : ℝ, 0 < r → ∃ x' ∉ CondPortOT.SingUninf.nbhd DX x0 γ, DX x' x ≤ r

/-- The worst-case conditional expected loss
`sup {E_ℚ[ℓ(Y) | X ∈ 𝒩_γ(x₀)] : ℚ ∈ 𝔹_ρ, ℚ(X ∈ 𝒩_γ(x₀)) ≥ ε}` of problem (4), p. 8. -/
noncomputable def worstCaseGe {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (xh : Fin N → X) (yh : Fin N → Y) (x0 : X)
    (γ ρ ε : ℝ) (L : Y → ℝ) : EReal :=
  ⨆ (Q : Measure (X × Y)) (_ : CondPortOT.SingUninf.InBall DX DY xh yh ρ Q ∧ ENNReal.ofReal ε ≤ Q (CondPortOT.SingUninf.fiber DX x0 γ)),
    CondPortOT.SingUninf.condExp Q (CondPortOT.SingUninf.fiber DX x0 γ) L

/-- The minimum radius `ρ_min(x₀, γ, ε) = inf {W(ℚ, ℙ̂) : ℚ ∈ ℳ(𝒳 × 𝒴), ℚ(X ∈ 𝒩_γ(x₀)) ≥ ε}`,
display (8), p. 11. -/
noncomputable def rhoMin {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (xh : Fin N → X) (yh : Fin N → Y) (x0 : X)
    (γ ε : ℝ) : ENNReal :=
  ⨅ (Q : Measure (X × Y)) (_ : IsProbabilityMeasure Q ∧ ENNReal.ofReal ε ≤ Q (CondPortOT.SingUninf.fiber DX x0 γ)),
    RWPI.SqrtLasso.transportCost (CondPortOT.SingUninf.groundCost DX DY) Q (CondPortOT.SingUninf.empirical xh yh)

/-- For a fixed weight vector `υ`, the inner supremum of Proposition A.5 (p. 36):
the supremum over `μ₀ⁱ ∈ ℳ(𝒴)` of `(Nε)⁻¹ Σᵢ υᵢ E_{μ₀ⁱ}[ℓ(Y)]` subject to
`Σᵢ υᵢ (𝔻_𝒳(x₀, x̂ᵢ) + E_{μ₀ⁱ}[𝔻_𝒴(Y, ŷᵢ)]) ≤ Nρ`. -/
noncomputable def innerSup {X Y : Type*} [MeasurableSpace Y] (DX : X → X → ℝ) (DY : Y → Y → ℝ)
    {N : ℕ} (xh : Fin N → X) (yh : Fin N → Y) (x0 : X) (ρ ε : ℝ) (L : Y → ℝ) (υ : Fin N → ℝ) :
    EReal :=
  ⨆ (μ : Fin N → Measure Y)
    (_ : (∀ i, IsProbabilityMeasure (μ i)) ∧
      ∑ i, ENNReal.ofReal (υ i) *
          (ENNReal.ofReal (DX x0 (xh i)) + ∫⁻ y, ENNReal.ofReal (DY y (yh i)) ∂(μ i)) ≤
        ENNReal.ofReal (N * ρ)),
    (((N * ε)⁻¹ : ℝ) : EReal) *
      ∑ i, ((υ i : ℝ) : EReal) * ModelRiskOT.Duality.extIntegral (μ i) (fun y => (L y : EReal))

/-- For a fixed weight vector `υ`, the moment-problem dual of `innerSup` (proof of Theorem 3.2,
p. 41): the infimum of `λ₁ (Nρ − Σᵢ υᵢ 𝔻_𝒳(x₀, x̂ᵢ)) + Σᵢ θᵢ` over `λ₁ ≥ 0`, `θ ∈ ℝᴺ` with
`υᵢ 𝔻_𝒴(y, ŷᵢ) λ₁ + θᵢ ≥ (Nε)⁻¹ υᵢ ℓ(y)` for all `y ∈ 𝒴`, `i ∈ [N]`. -/
noncomputable def innerDual {X Y : Type*} (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ}
    (xh : Fin N → X) (yh : Fin N → Y) (x0 : X) (ρ ε : ℝ) (L : Y → ℝ) (υ : Fin N → ℝ) : EReal :=
  ⨅ (l1 : ℝ) (_ : 0 ≤ l1) (θ : Fin N → ℝ)
    (_ : ∀ i y, (N * ε)⁻¹ * υ i * L y ≤ υ i * DY y (yh i) * l1 + θ i),
    ((l1 * (N * ρ - ∑ i, υ i * DX x0 (xh i)) + ∑ i, θ i : ℝ) : EReal)

end CondPortOT.SingDual


