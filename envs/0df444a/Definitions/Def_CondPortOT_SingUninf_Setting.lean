-- Prove2me | Definitions.Def_CondPortOT_SingUninf_Setting
-- name    : CondPortOT_SingUninf_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:45.867049+00:00
-- url     : https://prove2.me/theorems/5f67ffef-9dc0-4147-8ad9-7f4dce5d0be5
-- title:
--   pp. 7–11, 14 — ground cost, empirical measure, fiber, conditional expectation, OT ball, κ, Assumption 2.4, worst-case value with positive fiber mass, NotIsolated
-- statement:
--   This file fixes the model of Nguyen, Zhang, Wang, Blanchet, Delage and Ye for the conditional portfolio problem.
--
--   Let $\mathcal X$ (covariates) and $\mathcal Y$ (asset returns) be Polish spaces with their Borel $\sigma$-algebras, and let $\mathbb D_{\mathcal X}:\mathcal X\times\mathcal X\to\mathbb R$, $\mathbb D_{\mathcal Y}:\mathcal Y\times\mathcal Y\to\mathbb R$ be ground costs. The data are $N$ samples $(\widehat x_i,\widehat y_i)\in\mathcal X\times\mathcal Y$, $i\in[N]$.
--
--   1. **Ground cost.** $\mathbb D((x,y),(x',y'))=\mathbb D_{\mathcal X}(x,x')+\mathbb D_{\mathcal Y}(y,y')$, viewed as a $[0,\infty]$-valued cost.
--   2. **Empirical measure.** $\widehat{\mathbb P}=\frac1N\sum_{i\in[N]}\delta_{(\widehat x_i,\widehat y_i)}$.
--   3. **Optimal transport ball.** $\mathbb B_\rho=\{\mathbb Q\in\mathcal M(\mathcal X\times\mathcal Y): W(\mathbb Q,\widehat{\mathbb P})\le\rho\}$, where $W$ is the optimal transport cost of Definition 2.1 with ground cost $\mathbb D$ (the infimum of $\mathbb E_\pi[\mathbb D]$ over couplings $\pi$ of $\mathbb Q$ and $\widehat{\mathbb P}$).
--   4. **Fiber.** $\mathcal N_\gamma(x_0)=\{x\in\mathcal X:\mathbb D_{\mathcal X}(x,x_0)\le\gamma\}$ and the fiber set $\mathcal N_\gamma(x_0)\times\mathcal Y$.
--   5. **Conditional expectation.** For a set $S$ with $0<\mathbb Q(S)$, $$\mathbb E_{\mathbb Q}[\ell(Y)\mid S]=\frac{\mathbb E_{\mathbb Q}[\ell(Y)\mathbb 1_S]}{\mathbb Q(S)},$$ where the numerator is the extended integral $\int\ell^+\,d\mathbb Q|_S-\int\ell^-\,d\mathbb Q|_S\in[-\infty,+\infty]$.
--   6. **Projection cost.** $\kappa_i=\inf_{x\in\mathcal N_\gamma(x_0)}\mathbb D_{\mathcal X}(x,\widehat x_i)$, display (7).
--   7. **Assumption 2.4.** (i) $\mathbb D_{\mathcal X}$, $\mathbb D_{\mathcal Y}$ are symmetric, non-negative and continuous, and $\mathbb D((x,y),(x',y'))=0$ iff $(x,y)=(x',y')$; (ii) each $\widehat x_i$ has a unique projection onto $\mathcal N_\gamma(x_0)$ under $\mathbb D_{\mathcal X}$; (iii) for every boundary point $x$ of $\mathcal N_\gamma(x_0)$ and every $r>0$ there is $x'\notin\mathcal N_\gamma(x_0)$ with $\mathbb D_{\mathcal X}(x',x)\le r$.
--   8. **Worst-case value with positive fiber mass.** $$\sup_{\mathbb Q\in\mathbb B_\rho,\ \mathbb Q(X\in\mathcal N_\gamma(x_0))>0}\mathbb E_{\mathbb Q}[\ell(Y)\mid X\in\mathcal N_\gamma(x_0)],$$ a value in $[-\infty,+\infty]$.
--   9. **Non-isolated centre.** $x_0$ is *not isolated* for $\mathbb D_{\mathcal X}$ if for every $r>0$ there is $x\ne x_0$ with $\mathbb D_{\mathcal X}(x,x_0)\le r$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Samples are indexed by `Fin N` (the paper's $[N]$). The transport cost reuses the published `RWPI.SqrtLasso.transportCost` (an infimum over couplings with first marginal $\mathbb Q$ and second marginal $\widehat{\mathbb P}$; the paper's "min" is not built in), and the extended integral reuses `ModelRiskOT.Duality.extIntegral` (with $\infty-\infty=-\infty$), so no integrability of $\ell$ is assumed. The radius enters as `ENNReal.ofReal ρ`, which is $0$ for $\rho<0$; every statement carries $\rho\ge0$ or $\rho>0$. The conditional expectation is a junk value when $\mathbb Q(S)=0$; the worst-case value only ranges over $\mathbb Q$ with positive fiber mass. The boundary $\partial$ in Assumption 2.4(iii) is the topological frontier in $\mathcal X$. The predicate "not isolated" is an addition to the paper, used at $\gamma=0$ (see the goal theorem).
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, pp. 7–11 (Definition 2.1, §2.1, (4), Assumption 2.4, (7)) and p. 14 (§3.1)

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral

namespace CondPortOT.SingUninf

open MeasureTheory

/-- The separable ground cost `𝔻((x, y), (x', y')) = 𝔻_𝒳(x, x') + 𝔻_𝒴(y, y')` of Assumption 2.4(i),
as a `[0, ∞]`-valued cost on `𝒳 × 𝒴`. -/
noncomputable def groundCost {X Y : Type*} (DX : X → X → ℝ) (DY : Y → Y → ℝ) :
    X × Y → X × Y → ENNReal :=
  fun z z' => ENNReal.ofReal (DX z.1 z'.1 + DY z.2 z'.2)

/-- The empirical measure `ℙ̂ = N⁻¹ ∑_{i ∈ [N]} δ_{(x̂ᵢ, ŷᵢ)}` (p. 8). -/
noncomputable def empirical {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {N : ℕ}
    (xh : Fin N → X) (yh : Fin N → Y) : Measure (X × Y) :=
  (N : ENNReal)⁻¹ • ∑ i, Measure.dirac (xh i, yh i)

/-- The neighborhood `𝒩_γ(x₀) = {x ∈ 𝒳 : 𝔻_𝒳(x, x₀) ≤ γ}` (p. 9). -/
def nbhd {X : Type*} (DX : X → X → ℝ) (x0 : X) (γ : ℝ) : Set X :=
  {x | DX x x0 ≤ γ}

/-- The fiber set `𝒩_γ(x₀) × 𝒴` (p. 9). -/
def fiber {X Y : Type*} (DX : X → X → ℝ) (x0 : X) (γ : ℝ) : Set (X × Y) :=
  nbhd DX x0 γ ×ˢ Set.univ

/-- The conditional expectation `E_ℚ[ℓ(Y) | (X, Y) ∈ S] = E_ℚ[ℓ(Y) 𝟙_S] / ℚ(S)` (p. 9), with the
numerator the extended integral `∫ ℓ⁺ − ∫ ℓ⁻` in `EReal`. Only meaningful when `0 < ℚ(S) < ∞`. -/
noncomputable def condExp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (Q : Measure (X × Y)) (S : Set (X × Y)) (L : Y → ℝ) : EReal :=
  (((Q S).toReal⁻¹ : ℝ) : EReal) *
    ModelRiskOT.Duality.extIntegral (Q.restrict S) (fun p => (L p.2 : EReal))

/-- Membership in the optimal-transport ball `𝔹_ρ = {ℚ ∈ ℳ(𝒳 × 𝒴) : W(ℚ, ℙ̂) ≤ ρ}` (p. 8). -/
def InBall {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (xh : Fin N → X) (yh : Fin N → Y) (ρ : ℝ)
    (Q : Measure (X × Y)) : Prop :=
  IsProbabilityMeasure Q ∧
    RWPI.SqrtLasso.transportCost (groundCost DX DY) Q (empirical xh yh) ≤ ENNReal.ofReal ρ

/-- `κᵢ = inf_{x ∈ 𝒩_γ(x₀)} 𝔻_𝒳(x, x̂ᵢ)`, the cost of moving `x̂ᵢ` into the neighborhood (7). -/
noncomputable def kappa {X : Type*} (DX : X → X → ℝ) (x0 : X) (γ : ℝ) {N : ℕ} (xh : Fin N → X)
    (i : Fin N) : ℝ :=
  sInf ((fun x => DX x (xh i)) '' nbhd DX x0 γ)

/-- Assumption 2.4 (Regularity conditions), pp. 10–11. -/
structure Assumption24 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) (x0 : X) (γ : ℝ) {N : ℕ} (xh : Fin N → X) : Prop where
  /-- (i) `𝔻_𝒳` is symmetric. -/
  DX_symm : ∀ x x' : X, DX x x' = DX x' x
  /-- (i) `𝔻_𝒴` is symmetric. -/
  DY_symm : ∀ y y' : Y, DY y y' = DY y' y
  /-- (i) `𝔻_𝒳` is non-negative. -/
  DX_nonneg : ∀ x x' : X, 0 ≤ DX x x'
  /-- (i) `𝔻_𝒴` is non-negative. -/
  DY_nonneg : ∀ y y' : Y, 0 ≤ DY y y'
  /-- (i) `𝔻_𝒳` is continuous on `𝒳 × 𝒳`. -/
  DX_cont : Continuous (fun p : X × X => DX p.1 p.2)
  /-- (i) `𝔻_𝒴` is continuous on `𝒴 × 𝒴`. -/
  DY_cont : Continuous (fun p : Y × Y => DY p.1 p.2)
  /-- (i) `𝔻((x, y), (x', y')) = 0` if and only if `(x, y) = (x', y')`. -/
  cost_eq_zero_iff : ∀ (x x' : X) (y y' : Y), DX x x' + DY y y' = 0 ↔ (x, y) = (x', y')
  /-- (ii) Every `x̂ᵢ` has a unique projection onto `𝒩_γ(x₀)` under `𝔻_𝒳`. -/
  proj : ∀ i, ∃! xp : X, xp ∈ nbhd DX x0 γ ∧ ∀ x ∈ nbhd DX x0 γ, DX xp (xh i) ≤ DX x (xh i)
  /-- (iii) Every boundary point of `𝒩_γ(x₀)` has points outside `𝒩_γ(x₀)` at arbitrarily small cost. -/
  vicinity : ∀ x ∈ frontier (nbhd DX x0 γ), ∀ r : ℝ, 0 < r →
    ∃ x' : X, x' ∉ nbhd DX x0 γ ∧ DX x' x ≤ r

/-- The worst-case conditional expected loss with only positive fiber mass required:
`sup {E_ℚ[ℓ(Y) | X ∈ 𝒩_γ(x₀)] : ℚ ∈ 𝔹_ρ, ℚ(X ∈ 𝒩_γ(x₀)) > 0}` (p. 14 for γ = 0, p. 18 for γ > 0). -/
noncomputable def worstCasePos {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (xh : Fin N → X) (yh : Fin N → Y) (x0 : X) (γ ρ : ℝ)
    (L : Y → ℝ) : EReal :=
  ⨆ (Q : Measure (X × Y)) (_ : InBall DX DY xh yh ρ Q ∧ 0 < Q (fiber DX x0 γ)),
    condExp Q (fiber DX x0 γ) L

/-- Disclosed addition H1: `x₀` is not isolated for `𝔻_𝒳`, i.e. there are points `x ≠ x₀` at
arbitrarily small cost from `x₀`. This is Assumption 2.4(iii) at `γ = 0` with the boundary of `{x₀}`
taken in the ambient space. -/
def NotIsolated {X : Type*} (DX : X → X → ℝ) (x0 : X) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ x : X, x ≠ x0 ∧ DX x x0 ≤ r

end CondPortOT.SingUninf


