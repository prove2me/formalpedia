-- Prove2me | Definitions.Def_MaxSpectralRisk_Duality_Setting
-- name    : MaxSpectralRisk_Duality_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:35.511992+00:00
-- url     : https://prove2.me/theorems/2d9e03cc-0533-40d4-ac94-8f343ac666f0
-- title:
--   §2–§3, pp. 4–10 — spectral functions σ, γσ, Γσ, F←, R_{π,σ}, ES, g_α (1), V_σ (3), C^β (5), Φ_{C^β}, D_σ, A.1–A.4, H, D_H, K_π
-- statement:
--   The objects of the maximum spectral measure problem of Ghossoub, Hall and Saunders.
--
--   Let $\mathcal X,\mathcal Y$ be Polish spaces with their Borel $\sigma$-algebras, $\mathcal W=\mathcal X\times\mathcal Y$, $\mu,\nu$ probability measures on $\mathcal X,\mathcal Y$, and $\Pi(\mu,\nu)$ the set of probability measures on $\mathcal W$ with marginals $\mu$ and $\nu$ (the published `MongeKantorovichYao.transferencePlans`).
--
--   1. **Spectral function.** A function $\sigma:[0,1)\to\mathbb R_+$ that is nonnegative, increasing, right-continuous, bounded and satisfies $\int_0^1\sigma(u)\,du=1$.
--   2. **The measures $\gamma_\sigma$ and $\Gamma_\sigma$.** $\gamma_\sigma$ is the measure on $[0,1)$ with distribution function $\sigma$, so $\gamma_\sigma((a,b])=\sigma(b)-\sigma(a)$ and $\gamma_\sigma(\{0\})=\sigma(0)=z_0$; and $d\Gamma_\sigma(u)=(1-u)\,d\gamma_\sigma(u)$.
--   3. **Quantile, spectral risk measure, Expected Shortfall.** For a probability measure $\pi$ on $\mathcal W$,
--   $$F^{\leftarrow}_{L,\pi}(\alpha)=\inf\{x\in\mathbb R:\pi(L\le x)\ge\alpha\},\qquad R_{\pi,\sigma}(L)=\int_0^1F^{\leftarrow}_{L,\pi}(u)\sigma(u)\,du,$$
--   $\mathrm{ES}_{\alpha,\pi}(L)=(1-\alpha)^{-1}\int_\alpha^1F^{\leftarrow}_{L,\pi}(u)\,du$ and $g_\alpha(b,\pi)=b+(1-\alpha)^{-1}\mathbb E_\pi[(L-b)_+]$ (1).
--   4. **Primal value (3).** $V_\sigma(\mu,\nu)=\sup_{\pi\in\Pi(\mu,\nu)}R_{\pi,\sigma}(L)$.
--   5. **Dual value.** For measurable $\beta$, $C^\beta(x,y)=\int_0^1\max(L(x,y)-\beta(u),0)\,d\gamma_\sigma(u)$ (5); $\Phi_{C^\beta}$ is the set of $(\varphi,\psi)\in\mathcal L^1(\mu)\times\mathcal L^1(\nu)$ with $\varphi(x)+\psi(y)\ge C^\beta(x,y)$ for $\mu$-a.e. $x$ and $\nu$-a.e. $y$; and
--   $$D_\sigma(\mu,\nu)=\inf_{\beta\in\mathcal L^1(\gamma_\sigma),\,(\varphi,\psi)\in\Phi_{C^\beta}}\int_0^1\beta\,d\Gamma_\sigma+\int\varphi\,d\mu+\int\psi\,d\nu.$$
--   6. **Assumptions.** A.1: $L$ is upper semicontinuous. A.2: $L(x,y)\le A(x)+B(y)$ for $\mu$-a.e. $x$ and $\nu$-a.e. $y$, with lower semicontinuous $A\in\mathcal L^1(\mu)$, $B\in\mathcal L^1(\nu)$. A.3: $L(x,y)\ge a(x)+b(y)$ likewise, with upper semicontinuous $a\in\mathcal L^1(\mu)$, $b\in\mathcal L^1(\nu)$. A.4: $\sigma$ is bounded and right-continuous.
--   7. **Auxiliary functionals (pp. 9–10).** $H(\pi,\beta)=\int_0^1\beta(u)+(1-u)^{-1}\mathbb E_\pi[(L-\beta(u))_+]\,d\Gamma_\sigma(u)\in\mathbb R\cup\{\infty\}$; $\mathcal D_H=\{\beta\in\mathcal L^1(\Gamma_\sigma):H(\pi,\beta)<\infty\ \forall\pi\in\Pi(\mu,\nu)\}$; and $K_\pi=\inf_\beta\int_0^1 g_u(\beta(u),\pi)\,d\Gamma_\sigma(u)$ over Borel measurable $\beta$.
--
--   These are the objects of the strong duality theorem $V_\sigma=D_\sigma$ (Theorem 1) and of every milestone of the mission.
--
--   **Formalization Note.** A spectral function is a Mathlib `StieltjesFunction` on $\mathbb R$ (monotone, right-continuous) that vanishes on $(-\infty,0)$ and has $\int_0^1\sigma=1$: nonnegativity follows, boundedness on $[0,1)$ follows from monotonicity, and every bounded increasing right-continuous $\sigma$ on $[0,1)$ extends this way, so A.4 is built in; values on $[1,\infty)$ never enter. $\gamma_\sigma$ is the Stieltjes measure restricted to $[0,1)$, and $\Gamma_\sigma$ is defined by the density $1-u$ against $\gamma_\sigma$ (the paper's distribution-function description of $\Gamma_\sigma$ is posed as a milestone). $V_\sigma$, $D_\sigma$, $H$, $K_\pi$ take values in the extended reals; $H$ and $K_\pi$ are $+\infty$ when their integrand is not integrable, which is the paper's $\mathbb R\cup\{\infty\}$ convention since these integrands are bounded below by integrable functions. "For $\mu$-a.e. $x$ and $\nu$-a.e. $y$" means: off $N\times\mathcal Y\cup\mathcal X\times N'$ with $\mu(N)=\nu(N')=0$; a $(\mu\otimes\nu)$-a.e. reading would be strictly weaker and would break weak duality. The quantile is restated locally rather than imported from `RiskFunctionals_AVaR_QuantileFunction`.
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, pp. 4–10, (1), (3), (5), Definition 1, A.1–A.4, footnote 4, Remark 1, definitions of H and D_H (p. 10), K_π in Lemma 4 (p. 9)

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs

namespace MaxSpectralRisk.Duality

open MeasureTheory

/-- §2.2, p. 5 and A.4, p. 7: a bounded, right-continuous spectral function
`σ : [0, 1) → ℝ₊`, increasing with `∫₀¹ σ = 1`. It is encoded as a Stieltjes function on `ℝ`
(monotone and right-continuous) that vanishes on `(-∞, 0)`; nonnegativity follows, and boundedness
on `[0, 1)` follows from monotonicity (`σ u ≤ σ 1`). Values on `[1, ∞)` are never used. -/
structure SpectralFunction where
  /-- σ, extended by `0` to the left of `0`. -/
  toStieltjes : StieltjesFunction ℝ
  /-- σ vanishes to the left of `0` (Remark 1, p. 9: `γσ({0}) = σ(0)`). -/
  eq_zero_of_neg : ∀ u : ℝ, u < 0 → toStieltjes u = 0
  /-- `∫₀¹ σ(u) du = 1`. -/
  integral_eq_one : ∫ u in (0 : ℝ)..1, toStieltjes u = 1

instance : CoeFun SpectralFunction (fun _ => ℝ → ℝ) := ⟨fun sig => sig.toStieltjes⟩

/-- p. 6 and footnote 4: `γσ`, the measure with distribution function `σ` on `[0, 1)`, so that
`γσ((a, b]) = σ(b) - σ(a)` and `γσ({0}) = σ(0) = z₀` (Remark 1). -/
noncomputable def gam (sig : SpectralFunction) : Measure ℝ :=
  sig.toStieltjes.measure.restrict (Set.Ico 0 1)

/-- p. 6: `Γσ`, given by `dΓσ(u) = (1 - u) dγσ(u)`. -/
noncomputable def Gam (sig : SpectralFunction) : Measure ℝ :=
  (gam sig).withDensity (fun u => ENNReal.ofReal (1 - u))

/-- p. 5: the generalized inverse distribution function
`F←_{L,π}(α) = inf {x ∈ ℝ : π(L ≤ x) ≥ α}`, meaningful for `α ∈ (0, 1)`. -/
noncomputable def quantile {W : Type*} [MeasurableSpace W] (π : Measure W) (L : W → ℝ)
    (α : ℝ) : ℝ :=
  sInf {x : ℝ | α ≤ π.real {p | L p ≤ x}}

/-- §2.2, p. 5: the spectral risk measure `R_{π,σ}(L) = ∫₀¹ F←_{L,π}(u) σ(u) du`. -/
noncomputable def specRisk {W : Type*} [MeasurableSpace W] (sig : SpectralFunction)
    (π : Measure W) (L : W → ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, quantile π L u * sig u

/-- p. 5: Expected Shortfall `ES_{α,π}(L) = (1 - α)⁻¹ ∫_α^1 F←_{L,π}(u) du`, for `α ∈ [0, 1)`. -/
noncomputable def ES {W : Type*} [MeasurableSpace W] (α : ℝ) (π : Measure W) (L : W → ℝ) : ℝ :=
  (1 - α)⁻¹ * ∫ u in α..1, quantile π L u

/-- (1), p. 5: `g_α(b, π) = b + (1 - α)⁻¹ E_π[(L - b)₊]`. -/
noncomputable def g {W : Type*} [MeasurableSpace W] (α b : ℝ) (π : Measure W) (L : W → ℝ) : ℝ :=
  b + (1 - α)⁻¹ * ∫ p, max (L p - b) 0 ∂π

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Definition 1 and (3), p. 6: the Maximum Spectral Measure
`V_σ(µ, ν) = sup_{π ∈ Π(µ, ν)} R_{π,σ}(L)`, valued in the extended reals. -/
noncomputable def V (sig : SpectralFunction) (L : X × Y → ℝ) (μ : Measure X) (ν : Measure Y) :
    EReal :=
  ⨆ π ∈ MongeKantorovichYao.transferencePlans μ ν, ((specRisk sig π L : ℝ) : EReal)

/-- (5), p. 7: `C^β(x, y) = ∫₀¹ max(L(x, y) - β(u), 0) dγσ(u)`. -/
noncomputable def Cbeta (sig : SpectralFunction) (L : X × Y → ℝ) (β : ℝ → ℝ) (x : X) (y : Y) :
    ℝ :=
  ∫ u, max (L (x, y) - β u) 0 ∂(gam sig)

/-- "for µ-a.e. x ∈ X and ν-a.e. y ∈ Y" (pp. 7): `P x y` holds off `N × Y ∪ X × N'` for some
`µ`-null `N` and `ν`-null `N'`. -/
def AERect (μ : Measure X) (ν : Measure Y) (P : X → Y → Prop) : Prop :=
  ∃ N : Set X, μ N = 0 ∧ ∃ N' : Set Y, ν N' = 0 ∧ ∀ x ∉ N, ∀ y ∉ N', P x y

/-- p. 7: `Φ_{C^β}`, the pairs `(φ, ψ) ∈ L¹(µ) × L¹(ν)` with `φ(x) + ψ(y) ≥ C^β(x, y)` for
`µ`-a.e. `x` and `ν`-a.e. `y`. -/
def PhiC (sig : SpectralFunction) (L : X × Y → ℝ) (μ : Measure X) (ν : Measure Y)
    (β : ℝ → ℝ) : Set ((X → ℝ) × (Y → ℝ)) :=
  {φψ | Integrable φψ.1 μ ∧ Integrable φψ.2 ν ∧
    AERect μ ν (fun x y => Cbeta sig L β x y ≤ φψ.1 x + φψ.2 y)}

/-- p. 7: the dual value
`D_σ(µ, ν) = inf_{β ∈ L¹(γσ), (φ, ψ) ∈ Φ_{C^β}} ∫₀¹ β dΓσ + ∫ φ dµ + ∫ ψ dν`. -/
noncomputable def D (sig : SpectralFunction) (L : X × Y → ℝ) (μ : Measure X) (ν : Measure Y) :
    EReal :=
  ⨅ (β : ℝ → ℝ) (_ : Integrable β (gam sig)) (φψ ∈ PhiC sig L μ ν β),
    (((∫ u, β u ∂(Gam sig)) + (∫ x, φψ.1 x ∂μ) + (∫ y, φψ.2 y ∂ν) : ℝ) : EReal)

/-- Assumptions A.1–A.3, p. 7 (A.4 is built into `SpectralFunction`). -/
structure Assumptions [TopologicalSpace X] [TopologicalSpace Y] (L : X × Y → ℝ) (μ : Measure X)
    (ν : Measure Y) : Prop where
  /-- A.1: `L` is upper semicontinuous. -/
  usc : UpperSemicontinuous L
  /-- A.2: `L(x, y) ≤ A(x) + B(y)` for µ-a.e. `x`, ν-a.e. `y`, with `A ∈ L¹(µ)`, `B ∈ L¹(ν)`
  lower semicontinuous. -/
  upper_bound : ∃ (A : X → ℝ) (B : Y → ℝ), LowerSemicontinuous A ∧ Integrable A μ ∧
    LowerSemicontinuous B ∧ Integrable B ν ∧ AERect μ ν (fun x y => L (x, y) ≤ A x + B y)
  /-- A.3: `L(x, y) ≥ a(x) + b(y)` for µ-a.e. `x`, ν-a.e. `y`, with `a ∈ L¹(µ)`, `b ∈ L¹(ν)`
  upper semicontinuous. -/
  lower_bound : ∃ (a : X → ℝ) (b : Y → ℝ), UpperSemicontinuous a ∧ Integrable a μ ∧
    UpperSemicontinuous b ∧ Integrable b ν ∧ AERect μ ν (fun x y => a x + b y ≤ L (x, y))

/-- The integral of `f` against `m`, extended by `+∞` when `f` is not `m`-integrable. Used for
integrands bounded below by an integrable function (the values on p. 9–10 lie in `ℝ ∪ {∞}`). -/
noncomputable def extIntegral (f : ℝ → ℝ) (m : Measure ℝ) : EReal :=
  open Classical in
  if Integrable f m then (((∫ u, f u ∂m) : ℝ) : EReal) else ⊤

/-- p. 10: `H(π, β) = ∫₀¹ β(u) + (1 - u)⁻¹ E_π[(L(X, Y) - β(u))₊] dΓσ(u)` in `ℝ ∪ {∞}`. -/
noncomputable def H (sig : SpectralFunction) (L : X × Y → ℝ) (π : Measure (X × Y))
    (β : ℝ → ℝ) : EReal :=
  extIntegral (fun u => β u + (1 - u)⁻¹ * ∫ p, max (L p - β u) 0 ∂π) (Gam sig)

/-- p. 10: `D_H = {β ∈ L¹(Γσ) : ∀ π ∈ Π(µ, ν), H(π, β) < ∞}`. -/
def DH (sig : SpectralFunction) (L : X × Y → ℝ) (μ : Measure X) (ν : Measure Y) :
    Set (ℝ → ℝ) :=
  {β | Integrable β (Gam sig) ∧
    ∀ π ∈ MongeKantorovichYao.transferencePlans μ ν, H sig L π β < ⊤}

/-- Lemma 4, p. 9: `K_π = inf_{β ∈ L⁰} ∫₀¹ g_u(β(u), π) dΓσ(u)`, the infimum over Borel
measurable `β`. -/
noncomputable def K (sig : SpectralFunction) (L : X × Y → ℝ) (π : Measure (X × Y)) : EReal :=
  ⨅ (β : ℝ → ℝ) (_ : Measurable β), extIntegral (fun u => g u (β u) π L) (Gam sig)

end MaxSpectralRisk.Duality


