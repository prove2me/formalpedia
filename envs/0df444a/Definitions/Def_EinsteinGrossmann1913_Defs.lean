-- Prove2me | Definitions.Def_EinsteinGrossmann1913_Defs
-- name    : EinsteinGrossmann1913_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:22:50.48329+00:00
-- url     : https://prove2.me/theorems/806baf05-9dd1-42f0-bedb-094728d1aced
-- title:
--   Entwurf theory (1913): fundamental tensor, gravitational stress-energy, field operators
-- statement:
--   Coordinate definitions for Part I, §§4–5 of the Einstein–Grossmann *Entwurf* (1913).
--
--   Space-time is described in one global chart: a point is $x=(x_1,x_2,x_3,x_4)\in\mathbb R^4$, where $x_4$ is the time coordinate. The gravitational field is the **fundamental tensor** $g_{\mu\nu}(x)$, the coefficients of $ds^2=\sum_{\mu\nu}g_{\mu\nu}\,dx_\mu dx_\nu$. Standing assumptions (*IsMetricField*): every $g_{\mu\nu}$ is twice continuously differentiable, $g_{\mu\nu}=g_{\nu\mu}$, and $g=\det(g_{\mu\nu})<0$ everywhere. From $g$ one forms the reciprocal tensor $\gamma_{\mu\nu}$ (the inverse matrix) and $\sqrt{-g}$.
--
--   The file defines:
--
--   1. the coordinate partial derivative $\partial f/\partial x_i$;
--   2. lowering of indices, $T_{\mu\nu}=\sum_{\alpha\beta}g_{\mu\alpha}g_{\nu\beta}\Theta_{\alpha\beta}$;
--   3. eq. (13), the contravariant stress-energy tensor of the gravitational field,
--   $$-2\kappa\,\vartheta_{\mu\nu}=\sum_{\alpha\beta\tau\rho}\Big(\gamma_{\alpha\mu}\gamma_{\beta\nu}\frac{\partial g_{\tau\rho}}{\partial x_\alpha}\frac{\partial\gamma_{\tau\rho}}{\partial x_\beta}-\tfrac12\gamma_{\mu\nu}\gamma_{\alpha\beta}\frac{\partial g_{\tau\rho}}{\partial x_\alpha}\frac{\partial\gamma_{\tau\rho}}{\partial x_\beta}\Big);$$
--   4. eq. (14), its covariant counterpart
--   $$-2\kappa\,t_{\mu\nu}=\sum_{\tau\rho}\frac{\partial g_{\tau\rho}}{\partial x_\mu}\frac{\partial\gamma_{\tau\rho}}{\partial x_\nu}-\tfrac12\sum_{\alpha\beta\tau\rho}g_{\mu\nu}\gamma_{\alpha\beta}\frac{\partial g_{\tau\rho}}{\partial x_\alpha}\frac{\partial\gamma_{\tau\rho}}{\partial x_\beta};$$
--   5. eqs. (15), (16), the differential operators
--   $$\Delta_{\mu\nu}(\gamma)=\sum_{\alpha\beta}\frac{1}{\sqrt{-g}}\frac{\partial}{\partial x_\alpha}\Big(\gamma_{\alpha\beta}\sqrt{-g}\,\frac{\partial\gamma_{\mu\nu}}{\partial x_\beta}\Big)-\sum_{\alpha\beta\tau\rho}\gamma_{\alpha\beta}g_{\tau\rho}\frac{\partial\gamma_{\mu\tau}}{\partial x_\alpha}\frac{\partial\gamma_{\nu\rho}}{\partial x_\beta},$$
--   $$D_{\mu\nu}(g)=\sum_{\alpha\beta}\frac{1}{\sqrt{-g}}\frac{\partial}{\partial x_\alpha}\Big(\gamma_{\alpha\beta}\sqrt{-g}\,\frac{\partial g_{\mu\nu}}{\partial x_\beta}\Big)-\sum_{\alpha\beta\tau\rho}\gamma_{\alpha\beta}\gamma_{\tau\rho}\frac{\partial g_{\mu\tau}}{\partial x_\alpha}\frac{\partial g_{\nu\rho}}{\partial x_\beta};$$
--   6. eq. (10), the energy-momentum law of a material process with contravariant stress-energy tensor $\Theta_{\mu\nu}$,
--   $$\sum_{\mu\nu}\frac{\partial}{\partial x_\nu}\big(\sqrt{-g}\,g_{\sigma\mu}\Theta_{\mu\nu}\big)-\tfrac12\sum_{\mu\nu}\sqrt{-g}\,\frac{\partial g_{\mu\nu}}{\partial x_\sigma}\Theta_{\mu\nu}=0\qquad(\sigma=1,2,3,4),$$
--   and eq. (20), its covariant form for a covariant tensor $T_{\mu\nu}$,
--   $$\sum_{\mu\nu}\frac{\partial}{\partial x_\nu}\big(\sqrt{-g}\,\gamma_{\mu\nu}T_{\mu\sigma}\big)+\tfrac12\sum_{\mu\nu}\sqrt{-g}\,\frac{\partial \gamma_{\mu\nu}}{\partial x_\sigma}T_{\mu\nu}=0;$$
--   7. eq. (18), the Entwurf gravitational field equations $\Delta_{\mu\nu}(\gamma)=\kappa(\Theta_{\mu\nu}+\vartheta_{\mu\nu})$, and eq. (21), their covariant form $-D_{\mu\nu}(g)=\kappa(t_{\mu\nu}+T_{\mu\nu})$.
--
--   These are the objects in which every statement of the mission is phrased.
--
--   **Formalization Note** Partial derivatives are Fréchet derivatives along coordinate directions (value $0$ where a function is not differentiable). In eq. (14) the source writes a single $\sum_{\alpha\beta\tau\rho}$ in front of both terms; the first term does not contain $\alpha,\beta$, and, following the convention used throughout the paper, the sum over $\alpha,\beta$ is taken only in the term where these indices occur (this is the reading under which $t_{\mu\nu}$ is the index-lowered form of $\vartheta_{\mu\nu}$, as the source states).
-- source:
--   A. Einstein and M. Grossmann, "Entwurf einer verallgemeinerten Relativitätstheorie und einer Theorie der Gravitation", B. G. Teubner, Leipzig und Berlin 1913 (Separatabdruck aus Zeitschrift für Mathematik und Physik 62), Part I (Physikalischer Teil, A. Einstein), §4 (eq. (10)) and §5 (eqs. (13)–(18), (20), (21)), pp. 10–17.

import Mathlib

/-!
# Einstein–Grossmann 1913 ("Entwurf") — coordinate definitions

A. Einstein and M. Grossmann, *Entwurf einer verallgemeinerten Relativitätstheorie
und einer Theorie der Gravitation*, Teubner, Leipzig und Berlin 1913
(Separatabdruck aus Zeitschrift für Mathematik und Physik 62).

Everything is written in a single global chart: a point of space-time is
`x : Fin 4 → ℝ` (the source's `x₁, x₂, x₃, x₄`, with `x₄` the time coordinate,
here index `3`). A two-index field is a matrix-valued function `x ↦ (A x μ ν)`.
All index sums run over the four values of every index that actually occurs in
the summand (the source's convention).
-/

namespace EinsteinGrossmann1913

/-- Coordinate space `ℝ⁴`, points `x = (x₁, x₂, x₃, x₄)`. -/
abbrev Coord := Fin 4 → ℝ

/-- A two-index field on space-time: `A x μ ν = A_{μν}(x)`. -/
abbrev Field2 := Coord → Matrix (Fin 4) (Fin 4) ℝ

/-- The coordinate partial derivative `∂f/∂x_i` at `x`, in `n` variables
(Fréchet derivative applied to the `i`-th unit vector). -/
noncomputable def pd {n : ℕ} (i : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- Standing assumptions on the fundamental tensor `g_{μν}` (the coefficients of
`ds² = Σ g_{μν} dx_μ dx_ν`): every component is twice continuously differentiable,
`g_{μν} = g_{νμ}`, and the determinant `g = |g_{μν}|` is negative at every point, so
that `√(-g)` is a positive real number. -/
structure IsMetricField (g : Field2) : Prop where
  contDiff : ∀ μ ν : Fin 4, ContDiff ℝ 2 (fun x => g x μ ν)
  symm : ∀ (x : Coord) (μ ν : Fin 4), g x μ ν = g x ν μ
  det_neg : ∀ x : Coord, (g x).det < 0

/-- The reciprocal contravariant tensor `γ_{μν}`: the inverse matrix of `g_{μν}`. -/
noncomputable def gamma (g : Field2) : Field2 := fun x => (g x)⁻¹

/-- `√(-g)`, where `g = det (g_{μν})`. -/
noncomputable def sqrtNegDet (g : Field2) (x : Coord) : ℝ := Real.sqrt (-(g x).det)

/-- Lowering both indices of a contravariant field:
`T_{μν} = Σ_{αβ} g_{μα} g_{νβ} Θ_{αβ}` (p. 17, before eq. (20)). -/
noncomputable def lowerIndices (g Θ : Field2) : Field2 := fun x => Matrix.of fun μ ν =>
  ∑ α : Fin 4, ∑ β : Fin 4, g x μ α * g x ν β * Θ x α β

/-- Eq. (13): the contravariant stress-energy tensor `ϑ_{μν}` of the gravitational
field, defined by
`-2κ ϑ_{μν} = Σ_{αβτρ} (γ_{αμ} γ_{βν} ∂g_{τρ}/∂x_α ∂γ_{τρ}/∂x_β
               - ½ γ_{μν} γ_{αβ} ∂g_{τρ}/∂x_α ∂γ_{τρ}/∂x_β)`. -/
noncomputable def gravStressEnergy (κ : ℝ) (g : Field2) : Field2 := fun x => Matrix.of fun μ ν =>
  -(1 / (2 * κ)) * ∑ α : Fin 4, ∑ β : Fin 4, ∑ τ : Fin 4, ∑ ρ : Fin 4,
    (gamma g x α μ * gamma g x β ν * pd α (fun y => g y τ ρ) x * pd β (fun y => gamma g y τ ρ) x
      - (1 / 2) * gamma g x μ ν * gamma g x α β * pd α (fun y => g y τ ρ) x
          * pd β (fun y => gamma g y τ ρ) x)

/-- Eq. (14): the covariant stress-energy tensor `t_{μν}` of the gravitational field,
`-2κ t_{μν} = Σ_{τρ} ∂g_{τρ}/∂x_μ ∂γ_{τρ}/∂x_ν
             - ½ Σ_{αβτρ} g_{μν} γ_{αβ} ∂g_{τρ}/∂x_α ∂γ_{τρ}/∂x_β`. -/
noncomputable def gravStressEnergyCov (κ : ℝ) (g : Field2) : Field2 := fun x => Matrix.of fun μ ν =>
  -(1 / (2 * κ)) *
    ((∑ τ : Fin 4, ∑ ρ : Fin 4, pd μ (fun y => g y τ ρ) x * pd ν (fun y => gamma g y τ ρ) x)
      - (1 / 2) * ∑ α : Fin 4, ∑ β : Fin 4, ∑ τ : Fin 4, ∑ ρ : Fin 4,
          g x μ ν * gamma g x α β * pd α (fun y => g y τ ρ) x * pd β (fun y => gamma g y τ ρ) x)

/-- Eq. (15): the differential operator `Δ_{μν}(γ)`,
`Δ_{μν}(γ) = Σ_{αβ} (1/√(-g)) ∂/∂x_α (γ_{αβ} √(-g) ∂γ_{μν}/∂x_β)
            - Σ_{αβτρ} γ_{αβ} g_{τρ} ∂γ_{μτ}/∂x_α ∂γ_{νρ}/∂x_β`. -/
noncomputable def entwurfDelta (g : Field2) : Field2 := fun x => Matrix.of fun μ ν =>
  (∑ α : Fin 4, ∑ β : Fin 4, (1 / sqrtNegDet g x) *
      pd α (fun y => gamma g y α β * sqrtNegDet g y * pd β (fun z => gamma g z μ ν) y) x)
    - ∑ α : Fin 4, ∑ β : Fin 4, ∑ τ : Fin 4, ∑ ρ : Fin 4,
        gamma g x α β * g x τ ρ * pd α (fun y => gamma g y μ τ) x * pd β (fun y => gamma g y ν ρ) x

/-- Eq. (16): the differential operator `D_{μν}(g)`,
`D_{μν}(g) = Σ_{αβ} (1/√(-g)) ∂/∂x_α (γ_{αβ} √(-g) ∂g_{μν}/∂x_β)
            - Σ_{αβτρ} γ_{αβ} γ_{τρ} ∂g_{μτ}/∂x_α ∂g_{νρ}/∂x_β`. -/
noncomputable def entwurfD (g : Field2) : Field2 := fun x => Matrix.of fun μ ν =>
  (∑ α : Fin 4, ∑ β : Fin 4, (1 / sqrtNegDet g x) *
      pd α (fun y => gamma g y α β * sqrtNegDet g y * pd β (fun z => g z μ ν) y) x)
    - ∑ α : Fin 4, ∑ β : Fin 4, ∑ τ : Fin 4, ∑ ρ : Fin 4,
        gamma g x α β * gamma g x τ ρ * pd α (fun y => g y μ τ) x * pd β (fun y => g y ν ρ) x

/-- Left-hand side of eq. (10) for the index `σ` at the point `x`:
`Σ_{μν} ∂/∂x_ν (√(-g) g_{σμ} Θ_{μν}) - ½ Σ_{μν} √(-g) ∂g_{μν}/∂x_σ Θ_{μν}`. -/
noncomputable def matterConservationLHS (g Θ : Field2) (σ : Fin 4) (x : Coord) : ℝ :=
  (∑ μ : Fin 4, ∑ ν : Fin 4, pd ν (fun y => sqrtNegDet g y * g y σ μ * Θ y μ ν) x)
    - (1 / 2) * ∑ μ : Fin 4, ∑ ν : Fin 4,
        sqrtNegDet g x * pd σ (fun y => g y μ ν) x * Θ x μ ν

/-- Eq. (10), the energy-momentum law for a material process with contravariant
stress-energy tensor `Θ_{μν}`: the left-hand side above vanishes for `σ = 1, 2, 3, 4`
at every point. -/
def MatterConservation (g Θ : Field2) : Prop :=
  ∀ (σ : Fin 4) (x : Coord), matterConservationLHS g Θ σ x = 0

/-- Left-hand side of eq. (20) for the index `σ` at the point `x`, for a covariant
tensor `T_{μν}`:
`Σ_{μν} ∂/∂x_ν (√(-g) γ_{μν} T_{μσ}) + ½ Σ_{μν} √(-g) ∂γ_{μν}/∂x_σ T_{μν}`. -/
noncomputable def matterConservationCovLHS (g T : Field2) (σ : Fin 4) (x : Coord) : ℝ :=
  (∑ μ : Fin 4, ∑ ν : Fin 4, pd ν (fun y => sqrtNegDet g y * gamma g y μ ν * T y μ σ) x)
    + (1 / 2) * ∑ μ : Fin 4, ∑ ν : Fin 4,
        sqrtNegDet g x * pd σ (fun y => gamma g y μ ν) x * T x μ ν

/-- Eq. (20), the covariant form of the energy-momentum law: the left-hand side
above vanishes for `σ = 1, 2, 3, 4` at every point. -/
def MatterConservationCov (g T : Field2) : Prop :=
  ∀ (σ : Fin 4) (x : Coord), matterConservationCovLHS g T σ x = 0

/-- Eq. (18), the gravitational field equations of the Entwurf theory:
`Δ_{μν}(γ) = κ (Θ_{μν} + ϑ_{μν})` for all `μ, ν` at every point. -/
def EntwurfFieldEquations (κ : ℝ) (g Θ : Field2) : Prop :=
  ∀ (x : Coord) (μ ν : Fin 4),
    entwurfDelta g x μ ν = κ * (Θ x μ ν + gravStressEnergy κ g x μ ν)

/-- Eq. (21), the covariant form of the field equations:
`-D_{μν}(g) = κ (t_{μν} + T_{μν})` for all `μ, ν` at every point. -/
def EntwurfFieldEquationsCov (κ : ℝ) (g T : Field2) : Prop :=
  ∀ (x : Coord) (μ ν : Fin 4),
    -entwurfD g x μ ν = κ * (gravStressEnergyCov κ g x μ ν + T x μ ν)

end EinsteinGrossmann1913


