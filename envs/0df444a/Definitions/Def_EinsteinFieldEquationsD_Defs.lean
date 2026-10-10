-- Prove2me | Definitions.Def_EinsteinFieldEquationsD_Defs
-- name    : EinsteinFieldEquationsD_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:10:53.679989+00:00
-- url     : https://prove2.me/theorems/abd24765-a526-403a-8914-2e69d2a8d7ab
-- title:
--   Einstein field equations in coordinates (MTW convention, $D$ dimensions)
-- statement:
--   Coordinate-level definitions for the Einstein field equations in $D$ spacetime dimensions, following the Misner–Thorne–Wheeler $(+\,+\,+)$ sign convention used by the source.
--
--   Everything is written in a single coordinate chart: a point is $x\in\mathbb{R}^D$ and a covariant 2-tensor field is a matrix-valued function $x\mapsto T_{ab}(x)$. A **metric on an open set $U$** is a field $g$ whose components are $C^\infty$ on $U$ and which is symmetric and nondegenerate at every point of $U$. From it one builds
--
--   $$\Gamma^c_{ab}=\tfrac12 g^{cs}(\partial_a g_{sb}+\partial_b g_{sa}-\partial_s g_{ab}),\qquad R^\mu{}_{\alpha\beta\gamma}=\Gamma^\mu_{\alpha\gamma,\beta}-\Gamma^\mu_{\alpha\beta,\gamma}+\Gamma^\mu_{\sigma\beta}\Gamma^\sigma_{\gamma\alpha}-\Gamma^\mu_{\sigma\gamma}\Gamma^\sigma_{\beta\alpha},$$
--
--   $$R_{\mu\nu}=R^\alpha{}_{\mu\alpha\nu},\qquad R=g^{\mu\nu}R_{\mu\nu},\qquad G_{\mu\nu}=R_{\mu\nu}-\tfrac12 R g_{\mu\nu},$$
--
--   together with the covariant derivative and divergence of 2-tensors, the covariant derivative of the Riemann tensor, the field equations $G_{\mu\nu}+\Lambda g_{\mu\nu}=\kappa T_{\mu\nu}$ on $U$, the Einstein gravitational constant $\kappa=8\pi G/c^4$, the vacuum stress–energy tensor $T^{(\mathrm{vac})}_{\mu\nu}=-(\Lambda/\kappa)g_{\mu\nu}$, the perfect-fluid tensor $(\rho+p)u_\mu u_\nu+p\,g_{\mu\nu}$, and the Minkowski metric $\operatorname{diag}(-1,1,1,1)$.
-- source:
--   Wikipedia, "Einstein field equations", revision oldid=1374672993, https://en.wikipedia.org/w/index.php?title=Einstein_field_equations&oldid=1374672993; sections 'Mathematical form', 'Sign convention', 'Cosmological constant', 'Features', 'Vacuum field equations'

import Mathlib

/-!
# Einstein field equations — coordinate definitions

All objects are written in a single coordinate chart: points of spacetime are
points `x : Fin D → ℝ` of an open subset `U ⊆ ℝ^D`, and a covariant 2-tensor
field is a matrix-valued function `x ↦ (T x a b)`. Curvature follows the
Misner–Thorne–Wheeler `(+ + +)` sign convention.
-/

open scoped ContDiff

namespace EinsteinFieldEquationsD

/-- Coordinate space `ℝ^D`. -/
abbrev Coord (D : ℕ) := Fin D → ℝ

/-- A covariant 2-tensor field in coordinates: `T x a b = T_{ab}(x)`. -/
abbrev Tensor2 (D : ℕ) := Coord D → Matrix (Fin D) (Fin D) ℝ

variable {D : ℕ}

/-- The coordinate partial derivative `∂_a f (x)`. -/
noncomputable def partialDeriv (a : Fin D) (f : Coord D → ℝ) (x : Coord D) : ℝ :=
  fderiv ℝ f x (Pi.single a 1)

/-- `g` is a smooth pseudo-Riemannian metric on the open set `U`: every component
`g_{ab}` is `C^∞` on `U`, and at every point of `U` the matrix `g_{ab}(x)` is
symmetric and nondegenerate. -/
structure IsMetricOn (g : Tensor2 D) (U : Set (Coord D)) : Prop where
  isOpen : IsOpen U
  smooth : ∀ a b, ContDiffOn ℝ ∞ (fun x => g x a b) U
  symm : ∀ x ∈ U, ∀ a b, g x a b = g x b a
  nondegenerate : ∀ x ∈ U, (g x).det ≠ 0

/-- The inverse metric `g^{ab}(x)` (matrix inverse of `g_{ab}(x)`). -/
noncomputable def invMetric (g : Tensor2 D) : Tensor2 D := fun x => (g x)⁻¹

/-- Christoffel symbols of the Levi-Civita connection:
`Γ^c_{ab} = ½ g^{cs} (∂_a g_{sb} + ∂_b g_{sa} − ∂_s g_{ab})`. -/
noncomputable def christoffel (g : Tensor2 D) (x : Coord D) (c a b : Fin D) : ℝ :=
  (1 / 2 : ℝ) * ∑ s, invMetric g x c s *
    (partialDeriv a (fun y => g y s b) x + partialDeriv b (fun y => g y s a) x
      - partialDeriv s (fun y => g y a b) x)

/-- Riemann curvature tensor (MTW convention, `[S2] = +1`):
`R^m_{abc} = ∂_b Γ^m_{ac} − ∂_c Γ^m_{ab} + Γ^m_{sb} Γ^s_{ca} − Γ^m_{sc} Γ^s_{ba}`. -/
noncomputable def riemann (g : Tensor2 D) (x : Coord D) (m a b c : Fin D) : ℝ :=
  partialDeriv b (fun y => christoffel g y m a c) x
    - partialDeriv c (fun y => christoffel g y m a b) x
    + ∑ s, (christoffel g x m s b * christoffel g x s c a
      - christoffel g x m s c * christoffel g x s b a)

/-- Ricci tensor (`[S2][S3] = +1`): `R_{ab} = R^c_{acb}`. -/
noncomputable def ricci (g : Tensor2 D) : Tensor2 D :=
  fun x a b => ∑ c, riemann g x c a c b

/-- Scalar curvature `R = g^{ab} R_{ab}`. -/
noncomputable def scalarCurvature (g : Tensor2 D) (x : Coord D) : ℝ :=
  ∑ a, ∑ b, invMetric g x a b * ricci g x a b

/-- Einstein tensor `G_{ab} = R_{ab} − ½ R g_{ab}`. -/
noncomputable def einsteinTensor (g : Tensor2 D) : Tensor2 D :=
  fun x a b => ricci g x a b - (1 / 2 : ℝ) * scalarCurvature g x * g x a b

/-- Trace of a covariant 2-tensor with respect to the metric: `T = g^{ab} T_{ab}`. -/
noncomputable def metricTrace (g T : Tensor2 D) (x : Coord D) : ℝ :=
  ∑ a, ∑ b, invMetric g x a b * T x a b

/-- Covariant derivative of a covariant 2-tensor:
`∇_l T_{ab} = ∂_l T_{ab} − Γ^s_{la} T_{sb} − Γ^s_{lb} T_{as}`. -/
noncomputable def covDeriv2 (g T : Tensor2 D) (x : Coord D) (l a b : Fin D) : ℝ :=
  partialDeriv l (fun y => T y a b) x
    - ∑ s, (christoffel g x s l a * T x s b + christoffel g x s l b * T x a s)

/-- Covariant divergence on the second index, `(∇·T)_a = g^{bl} ∇_l T_{ab}`
(the index-lowered form of `∇_b T^{ab}`). -/
noncomputable def divergence (g T : Tensor2 D) (x : Coord D) (a : Fin D) : ℝ :=
  ∑ b, ∑ l, invMetric g x b l * covDeriv2 g T x l a b

/-- Covariant derivative of the `(1,3)` Riemann tensor:
`∇_e R^m_{abc} = ∂_e R^m_{abc} + Γ^m_{es} R^s_{abc} − Γ^s_{ea} R^m_{sbc}
 − Γ^s_{eb} R^m_{asc} − Γ^s_{ec} R^m_{abs}`. -/
noncomputable def covDerivRiemann (g : Tensor2 D) (x : Coord D) (e m a b c : Fin D) : ℝ :=
  partialDeriv e (fun y => riemann g y m a b c) x
    + ∑ s, (christoffel g x m e s * riemann g x s a b c
      - christoffel g x s e a * riemann g x m s b c
      - christoffel g x s e b * riemann g x m a s c
      - christoffel g x s e c * riemann g x m a b s)

/-- The Einstein field equations with cosmological constant `Λ` and coupling `κ`
hold on `U`: `G_{ab} + Λ g_{ab} = κ T_{ab}` at every point of `U`. -/
def EinsteinFieldEquationsOn (g T : Tensor2 D) (Λ κ : ℝ) (U : Set (Coord D)) : Prop :=
  ∀ x ∈ U, ∀ a b, einsteinTensor g x a b + Λ * g x a b = κ * T x a b

/-- The Einstein gravitational constant `κ = 8πG / c⁴`. -/
noncomputable def einsteinGravitationalConstant (G c : ℝ) : ℝ :=
  8 * Real.pi * G / c ^ 4

/-- The vacuum stress–energy tensor of the cosmological constant:
`T^{(vac)}_{ab} = −(Λ/κ) g_{ab}`. -/
noncomputable def vacuumStressEnergy (g : Tensor2 D) (Λ κ : ℝ) : Tensor2 D :=
  fun x a b => -(Λ / κ) * g x a b

/-- Perfect-fluid stress–energy tensor with energy density `ρ`, isotropic pressure
`p` and (covariant) velocity field `u`: `T_{ab} = (ρ + p) u_a u_b + p g_{ab}`. -/
def perfectFluid (g : Tensor2 D) (ρ p : ℝ) (u : Coord D → Fin D → ℝ) : Tensor2 D :=
  fun x a b => (ρ + p) * u x a * u x b + p * g x a b

/-- The Minkowski metric in MTW signature `(− + + +)`: `η = diag(−1, 1, 1, 1)`. -/
def minkowskiMetric : Tensor2 4 :=
  fun _ => Matrix.diagonal ![-1, 1, 1, 1]

end EinsteinFieldEquationsD


