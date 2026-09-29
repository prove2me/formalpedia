-- Prove2me | Definitions.Def_TeleparallelGravity_Defs
-- name    : TeleparallelGravity_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T22:30:37.660249+00:00
-- url     : https://prove2.me/theorems/71cd9a74-8d01-4ab2-9f57-9296ebfb18f7
-- title:
--   Teleparallel gravity in coordinates: tetrad, Weitzenböck and Christoffel connections, torsion, contortion, superpotential, Lagrangians
-- statement:
--   Coordinate definitions for teleparallel gravity on $\mathbb R^4$ (Aldrovandi-Pereira-Vu 2004, Section 2).
--
--   - Spacetime is $\mathbb R^4$; $\partial_\nu f(x)$ is the Fréchet derivative of $f$ at $x$ applied to the $\nu$-th coordinate basis vector.
--   - $\eta_{ab}=\mathrm{diag}(+1,-1,-1,-1)$.
--   - A tetrad field is a family of functions $h^a{}_\mu:\mathbb R^4\to\mathbb R$; it is **admissible** (`IsTetrad`) if every component is $C^\infty$ and the matrix $(h^a{}_\mu(x))$ is invertible at every $x$. $h_a{}^\mu$ is the inverse matrix and $h=\det(h^a{}_\mu)$.
--   - Metric (Eq. (4)): $g_{\mu\nu}=\eta_{ab}h^a{}_\mu h^b{}_\nu$, inverse $g^{\mu\nu}$.
--   - Weitzenböck connection (Eq. (5)): $\Gamma^\rho{}_{\mu\nu}=h_a{}^\rho\partial_\nu h^a{}_\mu$; torsion (Eq. (6)): $T^\rho{}_{\mu\nu}=\Gamma^\rho{}_{\nu\mu}-\Gamma^\rho{}_{\mu\nu}$; $T_{\rho\mu\nu}=g_{\rho\alpha}T^\alpha{}_{\mu\nu}$.
--   - Christoffel connection: $\mathring\Gamma^\rho{}_{\mu\nu}=\tfrac12g^{\rho\sigma}(\partial_\mu g_{\sigma\nu}+\partial_\nu g_{\sigma\mu}-\partial_\sigma g_{\mu\nu})$.
--   - Contortion (Eq. (9)): $K^\rho{}_{\mu\nu}=\tfrac12(T_\mu{}^\rho{}_\nu+T_\nu{}^\rho{}_\mu-T^\rho{}_{\mu\nu})$ with $T_\mu{}^\rho{}_\nu=g_{\mu\alpha}g^{\rho\beta}T^\alpha{}_{\beta\nu}$.
--   - Curvature of any connection: $R^\rho{}_{\theta\mu\nu}=\partial_\mu\Gamma^\rho{}_{\theta\nu}-\partial_\nu\Gamma^\rho{}_{\theta\mu}+\Gamma^\rho{}_{\sigma\mu}\Gamma^\sigma{}_{\theta\nu}-\Gamma^\rho{}_{\sigma\nu}\Gamma^\sigma{}_{\theta\mu}$; Ricci $\mathring R_{\theta\nu}=\mathring R^\rho{}_{\theta\rho\nu}$ and scalar $\mathring R=g^{\theta\nu}\mathring R_{\theta\nu}$ of the Christoffel connection.
--   - $T^{\sigma\mu}{}_\sigma=g^{\mu\beta}T^\sigma{}_{\beta\sigma}$, $K^{\mu\nu\rho}=g^{\nu\beta}g^{\rho\gamma}K^\mu{}_{\beta\gamma}$.
--   - Superpotential (Eq. (11)): $S^{\rho\mu\nu}=\tfrac12[K^{\mu\nu\rho}-g^{\rho\nu}T^{\sigma\mu}{}_\sigma+g^{\rho\mu}T^{\sigma\nu}{}_\sigma]$.
--   - Teleparallel Lagrangian (Eq. (10)): $\mathcal L_G=\frac{c^4h}{16\pi G}S^{\rho\mu\nu}T_{\rho\mu\nu}$; Einstein-Hilbert Lagrangian: $\mathcal L_{EH}=-\frac{c^4}{16\pi G}\sqrt{-\det g}\,\mathring R$.
--   - Gauge picture: $h^a{}_\mu=\partial_\mu x^a+B^a{}_\mu$ (Eq. (3)) and $F^a{}_{\mu\nu}=\partial_\mu B^a{}_\nu-\partial_\nu B^a{}_\mu$ (Eq. (7)).
-- source:
--   R. Aldrovandi, J. G. Pereira, K. H. Vu, "Selected Topics in Teleparallel Gravity", Brazilian Journal of Physics 34 (2004), no. 4A, 1374-1380, https://doi.org/10.1590/S0103-97332004000700009, Section 2, Eqs. (3)-(11), (15)

import Mathlib

/-!
# Teleparallel gravity: basic objects (coordinate formulation)

Definitions used by the draft Prove2Me mission built from
R. Aldrovandi, J. G. Pereira, K. H. Vu, *Selected Topics in Teleparallel Gravity*,
Braz. J. Phys. 34 (2004) 1374, Section 2 (Eqs. (1)–(11), (15)).

Everything is written in a single global coordinate chart `ℝ⁴`.
Index conventions: `h a μ x` is the tetrad component `h^a_μ(x)`; three-index
connection-type objects `Γ ρ μ ν x` stand for `Γ^ρ_{μν}(x)`.
-/

open scoped ContDiff

namespace TeleparallelGravity

/-- Spacetime points in a global coordinate chart, `x = (x⁰, x¹, x², x³)`. -/
abbrev Spacetime : Type := Fin 4 → ℝ

/-- The Minkowski metric of the tangent spaces, `η_ab = diag(+1, −1, −1, −1)`. -/
def minkowski : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1, -1, -1, -1]

/-- Coordinate partial derivative `∂_ν f (x)`. -/
noncomputable def pd (ν : Fin 4) (f : Spacetime → ℝ) (x : Spacetime) : ℝ :=
  fderiv ℝ f x (Pi.single ν 1)

/-- A tetrad field, stored by components: `h a μ x = h^a_μ(x)`. -/
abbrev TetradField : Type := Fin 4 → Fin 4 → Spacetime → ℝ

/-- The matrix `(h^a_μ(x))_{a,μ}` (rows: tangent index `a`, columns: spacetime index `μ`). -/
def tetradMatrix (h : TetradField) (x : Spacetime) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun a μ => h a μ x

/-- An admissible tetrad: smooth components, invertible at every point. -/
structure IsTetrad (h : TetradField) : Prop where
  smooth : ∀ a μ, ContDiff ℝ ∞ (h a μ)
  nondegenerate : ∀ x, (tetradMatrix h x).det ≠ 0

/-- Inverse tetrad: `invTetrad h x μ a = h_a^μ(x)`. -/
noncomputable def invTetrad (h : TetradField) (x : Spacetime) : Matrix (Fin 4) (Fin 4) ℝ :=
  (tetradMatrix h x)⁻¹

/-- `h = det(h^a_μ)`. -/
noncomputable def tetradDet (h : TetradField) (x : Spacetime) : ℝ :=
  (tetradMatrix h x).det

/-- Eq. (4): the spacetime metric `g_{μν} = η_ab h^a_μ h^b_ν`. -/
def metric (h : TetradField) (x : Spacetime) (μ ν : Fin 4) : ℝ :=
  ∑ a, ∑ b, minkowski a b * h a μ x * h b ν x

/-- Inverse metric `g^{μν}`. -/
noncomputable def invMetric (h : TetradField) (x : Spacetime) : Matrix (Fin 4) (Fin 4) ℝ :=
  (Matrix.of (metric h x))⁻¹

/-- Eq. (5): the Weitzenböck connection `Γ^ρ_{μν} = h_a^ρ ∂_ν h^a_μ`. -/
noncomputable def weitzenbock (h : TetradField) (ρ μ ν : Fin 4) (x : Spacetime) : ℝ :=
  ∑ a, invTetrad h x ρ a * pd ν (h a μ) x

/-- Eq. (6): the Weitzenböck torsion `T^ρ_{μν} = Γ^ρ_{νμ} − Γ^ρ_{μν}`. -/
noncomputable def torsion (h : TetradField) (ρ μ ν : Fin 4) (x : Spacetime) : ℝ :=
  weitzenbock h ρ ν μ x - weitzenbock h ρ μ ν x

/-- Torsion with its upper index lowered: `T_{ρμν} = g_{ρα} T^α_{μν}`. -/
noncomputable def torsionLower (h : TetradField) (ρ μ ν : Fin 4) (x : Spacetime) : ℝ :=
  ∑ α, metric h x ρ α * torsion h α μ ν x

/-- The Christoffel (Levi-Civita) connection of `g`:
`Γ°^ρ_{μν} = ½ g^{ρσ} (∂_μ g_{σν} + ∂_ν g_{σμ} − ∂_σ g_{μν})`. -/
noncomputable def christoffel (h : TetradField) (ρ μ ν : Fin 4) (x : Spacetime) : ℝ :=
  (1 / 2 : ℝ) * ∑ σ, invMetric h x ρ σ *
    (pd μ (fun y => metric h y σ ν) x + pd ν (fun y => metric h y σ μ) x
      - pd σ (fun y => metric h y μ ν) x)

/-- Eq. (9): the contortion `K^ρ_{μν} = ½ (T_μ{}^ρ{}_ν + T_ν{}^ρ{}_μ − T^ρ{}_{μν})`,
where `T_μ{}^ρ{}_ν = g_{μα} g^{ρβ} T^α{}_{βν}`. -/
noncomputable def contortion (h : TetradField) (ρ μ ν : Fin 4) (x : Spacetime) : ℝ :=
  (1 / 2 : ℝ) *
    ((∑ α, ∑ β, metric h x μ α * invMetric h x ρ β * torsion h α β ν x)
      + (∑ α, ∑ β, metric h x ν α * invMetric h x ρ β * torsion h α β μ x)
      - torsion h ρ μ ν x)

/-- Curvature of a linear connection `Γ^ρ_{μν}` (derivative index last):
`R^ρ_{θμν} = ∂_μ Γ^ρ_{θν} − ∂_ν Γ^ρ_{θμ} + Γ^ρ_{σμ} Γ^σ_{θν} − Γ^ρ_{σν} Γ^σ_{θμ}`. -/
noncomputable def curvature (Γ : Fin 4 → Fin 4 → Fin 4 → Spacetime → ℝ)
    (ρ θ μ ν : Fin 4) (x : Spacetime) : ℝ :=
  pd μ (Γ ρ θ ν) x - pd ν (Γ ρ θ μ) x
    + ∑ σ, (Γ ρ σ μ x * Γ σ θ ν x - Γ ρ σ ν x * Γ σ θ μ x)

/-- Ricci tensor of the Christoffel connection, `R°_{θν} = R°^ρ_{θρν}`. -/
noncomputable def ricci (h : TetradField) (θ ν : Fin 4) (x : Spacetime) : ℝ :=
  ∑ ρ, curvature (christoffel h) ρ θ ρ ν x

/-- Scalar curvature of the Christoffel connection, `R° = g^{θν} R°_{θν}`. -/
noncomputable def scalarCurvature (h : TetradField) (x : Spacetime) : ℝ :=
  ∑ θ, ∑ ν, invMetric h x θ ν * ricci h θ ν x

/-- The torsion vector with raised index, `T^{σμ}{}_σ = g^{μβ} T^σ{}_{βσ}`. -/
noncomputable def torsionVectorUp (h : TetradField) (μ : Fin 4) (x : Spacetime) : ℝ :=
  ∑ β, invMetric h x μ β * ∑ σ, torsion h σ β σ x

/-- Contortion with both lower indices raised, `K^{μνρ} = g^{νβ} g^{ργ} K^μ{}_{βγ}`. -/
noncomputable def contortionUp (h : TetradField) (μ ν ρ : Fin 4) (x : Spacetime) : ℝ :=
  ∑ β, ∑ γ, invMetric h x ν β * invMetric h x ρ γ * contortion h μ β γ x

/-- Eq. (11): the superpotential
`S^{ρμν} = ½ [K^{μνρ} − g^{ρν} T^{σμ}{}_σ + g^{ρμ} T^{σν}{}_σ]`. -/
noncomputable def superpotential (h : TetradField) (ρ μ ν : Fin 4) (x : Spacetime) : ℝ :=
  (1 / 2 : ℝ) * (contortionUp h μ ν ρ x - invMetric h x ρ ν * torsionVectorUp h μ x
    + invMetric h x ρ μ * torsionVectorUp h ν x)

/-- Eq. (10): the teleparallel gravitational Lagrangian density
`L_G = (c⁴ h / 16πG) S^{ρμν} T_{ρμν}`. -/
noncomputable def teleparallelLagrangian (c G : ℝ) (h : TetradField) (x : Spacetime) : ℝ :=
  c ^ 4 * tetradDet h x / (16 * Real.pi * G) *
    ∑ ρ, ∑ μ, ∑ ν, superpotential h ρ μ ν x * torsionLower h ρ μ ν x

/-- The Einstein–Hilbert Lagrangian density for signature `(+,−,−,−)`,
`L_EH = −(c⁴ / 16πG) √(−g) R°`, with `g = det(g_{μν})`. -/
noncomputable def einsteinHilbertLagrangian (c G : ℝ) (h : TetradField) (x : Spacetime) : ℝ :=
  -(c ^ 4 / (16 * Real.pi * G)) * Real.sqrt (-(Matrix.of (metric h x)).det) *
    scalarCurvature h x

/-- Eq. (3): the tetrad built from tangent-space coordinates `x^a` and the translational
gauge potential `B^a_μ`: `h^a_μ = ∂_μ x^a + B^a_μ`. -/
noncomputable def tetradOfPotential (xa : Fin 4 → Spacetime → ℝ) (B : TetradField) :
    TetradField :=
  fun a μ y => pd μ (xa a) y + B a μ y

/-- Eq. (7): the translational field strength `F^a_{μν} = ∂_μ B^a_ν − ∂_ν B^a_μ`. -/
noncomputable def fieldStrength (B : TetradField) (a μ ν : Fin 4) (x : Spacetime) : ℝ :=
  pd μ (B a ν) x - pd ν (B a μ) x

end TeleparallelGravity


