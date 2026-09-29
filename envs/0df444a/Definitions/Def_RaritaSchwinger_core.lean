-- Prove2me | Definitions.Def_RaritaSchwinger_core
-- name    : RaritaSchwinger_core
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T11:08:01.939339+00:00
-- url     : https://prove2.me/theorems/aa6a4ce5-f8bc-4176-aaf3-fa4e634fec4c
-- title:
--   Rarita–Schwinger field: $\gamma_5$, $\sigma^{\mu\nu}$, $\gamma^{\mu\nu\rho}$, $\epsilon^{\mu\kappa\rho\nu}$ and the free field equations
-- statement:
--   The objects of the free Rarita–Schwinger theory in $3+1$ dimensions, built on the Minkowski metric $\eta=\mathrm{diag}(1,-1,-1,-1)$ and an arbitrary quadruple of complex $4\times4$ matrices $\gamma^\mu$ (from `DiracAlgebra_core`), with the partial derivative $\partial_\rho$ and scalar plane waves from `DiracEquation_fields`.
--
--   1. A **vector-spinor field** $\psi$ assigns to every $x\in\mathbb R^4$ and every lower vector index $\mu$ a spinor $\psi_\mu(x)\in\mathbb C^4$; $\psi_\nu$ also denotes the spinor field $x\mapsto\psi_\nu(x)$.
--   2. Lowered gamma matrices $\gamma_\kappa=\eta_{\kappa\kappa}\gamma^\kappa$, the chirality matrix $\gamma_5=i\gamma_0\gamma_1\gamma_2\gamma_3$, and the spin matrices $\sigma^{\mu\nu}=\frac i2(\gamma^\mu\gamma^\nu-\gamma^\nu\gamma^\mu)$.
--   3. The antisymmetrized triple product
--   $$\gamma^{\mu\nu\rho}=\tfrac16\bigl(\gamma^\mu\gamma^\nu\gamma^\rho-\gamma^\mu\gamma^\rho\gamma^\nu-\gamma^\nu\gamma^\mu\gamma^\rho+\gamma^\nu\gamma^\rho\gamma^\mu+\gamma^\rho\gamma^\mu\gamma^\nu-\gamma^\rho\gamma^\nu\gamma^\mu\bigr).$$
--   4. The Levi-Civita symbol $\epsilon^{\mu\kappa\rho\nu}$: the sign of the permutation $(\mu,\kappa,\rho,\nu)$ of $(0,1,2,3)$, zero when two indices coincide; $\epsilon^{0123}=+1$.
--   5. The gamma trace $\gamma^\mu\psi_\mu(x)$, the divergence $\partial^\mu\psi_\mu(x)=\sum_\mu\eta^{\mu\mu}\partial_\mu\psi_\mu(x)$, and the Dirac operator on a component, $\gamma^\nu\partial_\nu\psi_\mu(x)$.
--   6. The **massive Rarita–Schwinger equation** with mass $m$: for all $x$ and $\mu$,
--   $$\sum_{\kappa,\rho,\nu}\epsilon^{\mu\kappa\rho\nu}\gamma_5\gamma_\kappa\,\partial_\rho\psi_\nu(x)-i m\sum_\nu\sigma^{\mu\nu}\psi_\nu(x)=0.$$
--   7. The **massless Rarita–Schwinger equation**: for all $x$ and $\mu$, $\sum_{\nu,\rho}\gamma^{\mu\nu\rho}\partial_\nu\psi_\rho(x)=0$.
--   8. The vector-spinor plane wave $\psi_\nu(x)=u_\nu\,e^{i p_\mu x^\mu}$ with polarization $u=(u_\nu)\in(\mathbb C^4)^4$ and real covector $p$.
--
--   These are the notions the mission's theorems are phrased in.
--
--   **Formalization Note** The partial derivative is a Fréchet derivative in a coordinate direction and equals $0$ where the field is not differentiable; the field equations carry no regularity condition, so each theorem adds one.
-- source:
--   "Rarita–Schwinger equation", Wikipedia, revision oldid=1362709293, https://en.wikipedia.org/w/index.php?title=Rarita%E2%80%93Schwinger_equation&oldid=1362709293; lead section (massive equation, $\sigma^{\mu\nu}$, $\gamma_5$) and section 'Massless equation and gauge invariance' ($\gamma^{\mu\nu\rho}$, massless equation).

import Definitions.Def_DiracEquation_fields

namespace RaritaSchwinger

open Matrix DiracEquation

/-- A vector-spinor field `ψ_μ(x)` on `ℝ⁴`: for every spacetime point `x` and every (lower)
vector index `μ`, a four-component Dirac spinor `ψ x μ`. -/
abbrev VectorSpinorField := (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℂ)

/-- The `ν`-th vector component `ψ_ν` of a vector-spinor field, viewed as a spinor field. -/
def comp (psi : VectorSpinorField) (nu : Fin 4) : (Fin 4 → ℝ) → (Fin 4 → ℂ) :=
  fun x => psi x nu

/-- The gamma matrices with lowered index, `γ_κ = η_{κλ} γ^λ = η_{κκ} γ^κ`. -/
noncomputable def gammaLower (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (kappa : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  eta kappa kappa • g kappa

/-- The chirality matrix `γ₅ = i γ₀ γ₁ γ₂ γ₃` (built from the lowered gamma matrices). -/
noncomputable def gamma5 (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Complex.I • (gammaLower g 0 * gammaLower g 1 * gammaLower g 2 * gammaLower g 3)

/-- The spin matrices `σ^{μν} = (i/2) [γ^μ, γ^ν]`. -/
noncomputable def sigma (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (mu nu : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  (Complex.I / 2) • (g mu * g nu - g nu * g mu)

/-- The antisymmetrized product `γ^{μνρ} = γ^{[μ} γ^ν γ^{ρ]}`, with unit-weight
antisymmetrization (the signed sum over the six orderings, divided by `3! = 6`). -/
noncomputable def gamma3 (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (mu nu rho : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 6 : ℂ) • (g mu * g nu * g rho - g mu * g rho * g nu - g nu * g mu * g rho
    + g nu * g rho * g mu + g rho * g mu * g nu - g rho * g nu * g mu)

/-- The Levi-Civita symbol `ε^{μκρν}`, normalized by `ε^{0123} = +1`: it is the determinant of
the matrix whose rows are the standard basis vectors `e_μ, e_κ, e_ρ, e_ν`, hence the sign of the
permutation `(μ, κ, ρ, ν)` of `(0, 1, 2, 3)`, and `0` if two indices coincide. -/
noncomputable def levi (mu kappa rho nu : Fin 4) : ℂ :=
  (Matrix.of ![(Pi.single mu 1 : Fin 4 → ℂ), Pi.single kappa 1, Pi.single rho 1,
    Pi.single nu 1]).det

/-- The gamma trace `γ^μ ψ_μ` of a vector-spinor field at the point `x`. -/
noncomputable def gammaTrace (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (psi : VectorSpinorField)
    (x : Fin 4 → ℝ) : Fin 4 → ℂ :=
  ∑ mu, (g mu).mulVec (psi x mu)

/-- The divergence `∂^μ ψ_μ = η^{μν} ∂_ν ψ_μ` of a vector-spinor field at the point `x`. -/
noncomputable def divergence (psi : VectorSpinorField) (x : Fin 4 → ℝ) : Fin 4 → ℂ :=
  ∑ mu, eta mu mu • pd (comp psi mu) mu x

/-- The Dirac operator `γ^ν ∂_ν` applied to the `μ`-th component: `γ^ν ∂_ν ψ_μ` at `x`. -/
noncomputable def diracOperator (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (psi : VectorSpinorField)
    (mu : Fin 4) (x : Fin 4 → ℝ) : Fin 4 → ℂ :=
  ∑ nu, (g nu).mulVec (pd (comp psi mu) nu x)

/-- `IsMassiveRSSolution g m ψ`: the vector-spinor field `ψ` satisfies the massive free
Rarita–Schwinger equation `(ε^{μκρν} γ₅ γ_κ ∂_ρ - i m σ^{μν}) ψ_ν = 0` at every point and for
every free index `μ` (summation over `κ, ρ, ν`). -/
def IsMassiveRSSolution (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (m : ℝ)
    (psi : VectorSpinorField) : Prop :=
  ∀ x mu,
    (∑ kappa, ∑ rho, ∑ nu,
        levi mu kappa rho nu • (gamma5 g * gammaLower g kappa).mulVec (pd (comp psi nu) rho x))
      - (Complex.I * (m : ℂ)) • ∑ nu, (sigma g mu nu).mulVec (psi x nu) = 0

/-- `IsMasslessRSSolution g ψ`: the vector-spinor field `ψ` satisfies the massless
Rarita–Schwinger equation `γ^{μνρ} ∂_ν ψ_ρ = 0` at every point and for every free index `μ`
(summation over `ν, ρ`). -/
def IsMasslessRSSolution (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (psi : VectorSpinorField) :
    Prop :=
  ∀ x mu, ∑ nu, ∑ rho, (gamma3 g mu nu rho).mulVec (pd (comp psi rho) nu x) = 0

/-- The vector-spinor plane wave `ψ_ν(x) = u_ν e^{i p_μ x^μ}` with polarization `u = (u_ν)`. -/
noncomputable def vectorSpinorPlaneWave (p : Fin 4 → ℝ) (u : Fin 4 → Fin 4 → ℂ) :
    VectorSpinorField :=
  fun x nu => planeWave p (u nu) x

end RaritaSchwinger


