-- Prove2me | Definitions.Def_efe_geometry
-- name    : efe_geometry
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T23:38:49.349473+00:00
-- url     : https://prove2.me/theorems/d167e613-28df-480a-a986-ac11c00e2bc3
-- title:
--   Coordinate curvature tensors and the Einstein field equations
-- statement:
--   Curvature in a single coordinate chart of a four-dimensional spacetime, and the Einstein field equations.
--
--   A point of spacetime is a quadruple of coordinates $x = (x^0, x^1, x^2, x^3)$, and a $(0,2)$-tensor field assigns to each point a real $4 \times 4$ matrix of components. For a metric $g$ we write $g_{ab}(x)$ for its components and $g^{ab}(x)$ for the entries of the inverse matrix, and $\partial_k$ for the partial derivative along the $k$-th coordinate direction (a Fréchet derivative in that direction).
--
--   The file defines, by the standard formulas,
--
--   $$\Gamma^{a}{}_{bc} = \tfrac12 g^{ad}\left(\partial_b g_{dc} + \partial_c g_{db} - \partial_d g_{bc}\right),$$
--
--   $$R^{a}{}_{bcd} = \partial_c \Gamma^{a}{}_{db} - \partial_d \Gamma^{a}{}_{cb} + \Gamma^{a}{}_{ce}\Gamma^{e}{}_{db} - \Gamma^{a}{}_{de}\Gamma^{e}{}_{cb},$$
--
--   the Ricci tensor $R_{bd} = R^{a}{}_{bad}$, the trace $g^{ab}A_{ab}$ of a $(0,2)$-tensor with respect to $g$, the scalar curvature $R = g^{ab}R_{ab}$, and the Einstein tensor
--
--   $$G_{ab} = R_{ab} - \tfrac12 R\, g_{ab}.$$
--
--   The Einstein field equations at a point $x$, for cosmological constant $\Lambda$, Einstein gravitational constant $\kappa$ and stress–energy tensor $T$, are the assertion
--
--   $$G_{ab}(x) + \Lambda\, g_{ab}(x) = \kappa\, T_{ab}(x) \qquad \text{for all } a, b \in \{0,1,2,3\}.$$
--
--   Finally the covariant divergence of a $(0,2)$-tensor field with respect to the Levi-Civita connection of $g$,
--
--   $$\nabla^{a} A_{ab} = g^{ac}\left(\partial_a A_{cb} - \Gamma^{e}{}_{ac}A_{eb} - \Gamma^{e}{}_{ab}A_{ce}\right).$$
--
--   Sign conventions are those of Misner–Thorne–Wheeler. Two conventions of the ambient formalization should be noted: the matrix inverse returns the zero matrix at a point where the metric is singular, and the derivative operator returns zero where a component function fails to be differentiable, so statements using these definitions carry invertibility and domain hypotheses.
-- source:
--   Wikipedia, "Einstein field equations", https://en.wikipedia.org/wiki/Einstein_field_equations (sections "Mathematical form", "Sign convention", "Features — Conservation of energy and momentum")

import Mathlib

namespace EinsteinFieldEquations

open Finset

/-- Coordinate space of a four-dimensional spacetime chart: a point is the quadruple of its
coordinates `(x⁰, x¹, x², x³)`. -/
abbrev Coord : Type := Fin 4 → ℝ

/-- The components, in a coordinate chart, of a (0,2)-tensor field on spacetime: to each point
it assigns a `4 × 4` real matrix of components. -/
abbrev Tensor2Field : Type := Coord → Matrix (Fin 4) (Fin 4) ℝ

/-- The partial derivative `∂_k f` of a scalar function of the coordinates. -/
noncomputable def partialD (f : Coord → ℝ) (k : Fin 4) (x : Coord) : ℝ :=
  fderiv ℝ f x (Pi.single k 1)

/-- The Christoffel symbols of the second kind of a metric `g`:
`Γᵃ_{bc} = ½ gᵃᵈ (∂_b g_{dc} + ∂_c g_{db} − ∂_d g_{bc})`,
where `gᵃᵈ` are the entries of the inverse matrix of `g x`. -/
noncomputable def christoffel (g : Tensor2Field) (a b c : Fin 4) (x : Coord) : ℝ :=
  (1 / 2 : ℝ) * ∑ d : Fin 4, (g x)⁻¹ a d *
    (partialD (fun y => g y d c) b x + partialD (fun y => g y d b) c x
      - partialD (fun y => g y b c) d x)

/-- The Riemann curvature tensor of `g` in the MTW sign convention:
`Rᵃ_{bcd} = ∂_c Γᵃ_{db} − ∂_d Γᵃ_{cb} + Γᵃ_{ce} Γᵉ_{db} − Γᵃ_{de} Γᵉ_{cb}`. -/
noncomputable def riemann (g : Tensor2Field) (a b c d : Fin 4) (x : Coord) : ℝ :=
  partialD (fun y => christoffel g a d b y) c x
    - partialD (fun y => christoffel g a c b y) d x
    + ∑ e : Fin 4, (christoffel g a c e x * christoffel g e d b x
        - christoffel g a d e x * christoffel g e c b x)

/-- The Ricci curvature tensor, the contraction `R_{bd} = Rᵃ_{bad}` of the Riemann tensor. -/
noncomputable def ricci (g : Tensor2Field) (b d : Fin 4) (x : Coord) : ℝ :=
  ∑ a : Fin 4, riemann g a b a d x

/-- The trace `gᵃᵇ A_{ab}` of a (0,2)-tensor field `A` with respect to the metric `g`. -/
noncomputable def metricTrace (g : Tensor2Field) (A : Tensor2Field) (x : Coord) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, (g x)⁻¹ a b * A x a b

/-- The scalar curvature `R = gᵃᵇ R_{ab}` of `g`. -/
noncomputable def scalarCurvature (g : Tensor2Field) (x : Coord) : ℝ :=
  metricTrace g (fun y => Matrix.of fun b d => ricci g b d y) x

/-- The Einstein tensor `G_{ab} = R_{ab} − ½ R g_{ab}`. -/
noncomputable def einsteinTensor (g : Tensor2Field) (a b : Fin 4) (x : Coord) : ℝ :=
  ricci g a b x - (1 / 2 : ℝ) * scalarCurvature g x * (g x) a b

/-- The Einstein field equations `G_{ab} + Λ g_{ab} = κ T_{ab}` at the point `x`, for the metric
`g`, cosmological constant `Lam`, Einstein gravitational constant `kappa` and stress–energy
tensor `T`. -/
def SatisfiesEFE (g : Tensor2Field) (Lam kappa : ℝ) (T : Tensor2Field) (x : Coord) : Prop :=
  ∀ a b : Fin 4, einsteinTensor g a b x + Lam * (g x) a b = kappa * T x a b

/-- The covariant divergence `∇ᵃ A_{ab} = gᵃᶜ (∂_a A_{cb} − Γᵉ_{ac} A_{eb} − Γᵉ_{ab} A_{ce})` of a
(0,2)-tensor field `A` with respect to the Levi-Civita connection of `g`. -/
noncomputable def covDiv (g : Tensor2Field) (A : Tensor2Field) (b : Fin 4) (x : Coord) : ℝ :=
  ∑ a : Fin 4, ∑ c : Fin 4, (g x)⁻¹ a c *
    (partialD (fun y => A y c b) a x
      - ∑ e : Fin 4, christoffel g e a c x * A x e b
      - ∑ e : Fin 4, christoffel g e a b x * A x c e)

end EinsteinFieldEquations


