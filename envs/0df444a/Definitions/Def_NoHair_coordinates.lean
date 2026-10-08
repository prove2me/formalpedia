-- Prove2me | Definitions.Def_NoHair_coordinates
-- name    : NoHair_coordinates
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-04T18:07:35.108091+00:00
-- url     : https://prove2.me/theorems/fd778b45-df53-4e0d-8926-f7a9b4464d09
-- title:
--   No-hair: coordinate Lorentzian geometry, Einstein–Maxwell equations, Kerr–Newman metric
-- statement:
--   Coordinate-level Lorentzian geometry on $\mathbb R^4$ and the Kerr–Newman family.
--
--   Points of coordinate space are $y=(y^0,y^1,y^2,y^3)=(t,x,y,z)$; index $0$ is time. The Minkowski metric is $\eta=\mathrm{diag}(-1,1,1,1)$ and units are geometrized Gaussian units ($G=c=1$). For a matrix-valued function $g_{\mu\nu}(y)$ (metric components) and an antisymmetric matrix-valued function $F_{\mu\nu}(y)$ (electromagnetic field), with $\partial_k$ the ordinary partial derivative (Fréchet derivative applied to the $k$-th basis vector) and $g^{\mu\nu}$ the inverse matrix:
--
--   1. Christoffel symbols $\Gamma^i_{jk}=\tfrac12 g^{il}(\partial_j g_{lk}+\partial_k g_{lj}-\partial_l g_{jk})$;
--   2. Riemann tensor $R^\rho{}_{\sigma\mu\nu}=\partial_\mu\Gamma^\rho_{\nu\sigma}-\partial_\nu\Gamma^\rho_{\mu\sigma}+\Gamma^\rho_{\mu\lambda}\Gamma^\lambda_{\nu\sigma}-\Gamma^\rho_{\nu\lambda}\Gamma^\lambda_{\mu\sigma}$, Ricci tensor $R_{\sigma\nu}=R^\rho{}_{\sigma\rho\nu}$, scalar curvature $R=g^{\sigma\nu}R_{\sigma\nu}$, Einstein tensor $G_{\mu\nu}=R_{\mu\nu}-\tfrac12 R\,g_{\mu\nu}$;
--   3. the **Einstein–Maxwell system at a point** $y$:
--   $$G_{\mu\nu}=2\Big(F_{\mu\alpha}F_{\nu}{}^{\alpha}-\tfrac14 g_{\mu\nu}F_{\alpha\beta}F^{\alpha\beta}\Big),\qquad \partial_\mu\big(\sqrt{|\det g|}\,F^{\mu\nu}\big)=0,\qquad \partial_{[\lambda}F_{\mu\nu]}=0;$$
--   4. the Hodge dual $(\star F)_{\mu\nu}=\tfrac12\sqrt{|\det g|}\,\varepsilon_{\mu\nu\alpha\beta}F^{\alpha\beta}$ with the Levi-Civita symbol $\varepsilon$.
--
--   **Kerr–Newman in Kerr–Schild coordinates.** For parameters $m,a,e\in\mathbb R$ let $\rho^2=x^2+y^2+z^2$ and let $r\ge0$ be given by $r^2=\tfrac12\big(\rho^2-a^2+\sqrt{(\rho^2-a^2)^2+4a^2z^2}\big)$. With
--   $$k=\Big(1,\ \frac{rx+ay}{r^2+a^2},\ \frac{ry-ax}{r^2+a^2},\ \frac zr\Big),\qquad f=\frac{r^2(2mr-e^2)}{r^4+a^2z^2},$$
--   the Kerr–Newman metric is $g^{KN}_{\mu\nu}=\eta_{\mu\nu}+f\,k_\mu k_\nu$, its potential is $A_\mu=\frac{e\,r^3}{r^4+a^2z^2}k_\mu$ and its field is $F^{KN}_{\mu\nu}=\partial_\mu A_\nu-\partial_\nu A_\mu$. Admissible black-hole parameters are $m>0$, $a^2+e^2\le m^2$; the outer horizon radius is $r_+=m+\sqrt{m^2-a^2-e^2}$ and the Kerr–Newman domain of outer communications is $\{y: r(y)>r_+\}$.
--
--   These are the shared local objects of the mission: the field equations every spacetime in the mission must satisfy, and the explicit model family that the goal theorem asserts is the only possibility.
--
--   **Formalization Note** Coordinate space is `EuclideanSpace ℝ (Fin 4)`; all objects are total functions, so formulas are only meaningful where denominators are nonzero (for Kerr–Newman: $r>0$).
-- source:
--   Wikipedia, "No-hair theorem" (revision oldid=1353599195), https://en.wikipedia.org/w/index.php?title=No-hair_theorem&oldid=1353599195

import Mathlib

/-!
# No-hair mission: coordinate (local) Lorentzian geometry

Everything here is phrased for functions on coordinate space `ℝ⁴ = EuclideanSpace ℝ (Fin 4)`,
with coordinate `0` the time coordinate and the Minkowski metric `η = diag(-1, 1, 1, 1)`.
Units: geometrized Gaussian units `G = c = 1`, so the Einstein–Maxwell equations read
`G_{μν} = 2 (F_{μα} F_ν{}^α - ¼ g_{μν} F_{αβ} F^{αβ})` (i.e. `G = 8π T` with
`T = (1/4π)(…)`).
-/

noncomputable section

open scoped BigOperators

namespace NoHair

/-- Coordinate space `ℝ⁴`; coordinate `0` is time, coordinates `1,2,3` are `x, y, z`. -/
abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- The `μ`-th coordinate basis vector of `ℝ⁴`. -/
def coordBasis (μ : Fin 4) : E4 := EuclideanSpace.single μ 1

/-- Minkowski metric components `η = diag(-1, 1, 1, 1)`. -/
def minkowski : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![-1, 1, 1, 1]

/-- Partial derivative `∂_k f (y)` of a scalar function on coordinate space. -/
def coordPartial (f : E4 → ℝ) (k : Fin 4) (y : E4) : ℝ := fderiv ℝ f y (coordBasis k)

/-- Spatial radius `r = √(x² + y² + z²)` of a point of coordinate space. -/
def spatialRadius (y : E4) : ℝ := Real.sqrt (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2)

/-- Inverse metric components `g^{μν}`. -/
def invMetric (G : E4 → Matrix (Fin 4) (Fin 4) ℝ) (y : E4) : Matrix (Fin 4) (Fin 4) ℝ :=
  (G y)⁻¹

/-- Christoffel symbols `Γ^i_{jk} = ½ g^{il} (∂_j g_{lk} + ∂_k g_{lj} - ∂_l g_{jk})`. -/
def christoffel (G : E4 → Matrix (Fin 4) (Fin 4) ℝ) (y : E4) (i j k : Fin 4) : ℝ :=
  ∑ l, (1 / 2 : ℝ) * invMetric G y i l *
    (coordPartial (fun z => G z l k) j y + coordPartial (fun z => G z l j) k y
      - coordPartial (fun z => G z j k) l y)

/-- Riemann tensor `R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} - ∂_ν Γ^ρ_{μσ} + Γ^ρ_{μλ} Γ^λ_{νσ} - Γ^ρ_{νλ} Γ^λ_{μσ}`. -/
def riemann (G : E4 → Matrix (Fin 4) (Fin 4) ℝ) (y : E4) (ρ σ μ ν : Fin 4) : ℝ :=
  coordPartial (fun z => christoffel G z ρ ν σ) μ y
    - coordPartial (fun z => christoffel G z ρ μ σ) ν y
    + ∑ l, (christoffel G y ρ μ l * christoffel G y l ν σ
      - christoffel G y ρ ν l * christoffel G y l μ σ)

/-- Ricci tensor `R_{σν} = R^ρ_{σρν}`. -/
def ricci (G : E4 → Matrix (Fin 4) (Fin 4) ℝ) (y : E4) (σ ν : Fin 4) : ℝ :=
  ∑ ρ, riemann G y ρ σ ρ ν

/-- Scalar curvature `R = g^{σν} R_{σν}`. -/
def scalarCurvature (G : E4 → Matrix (Fin 4) (Fin 4) ℝ) (y : E4) : ℝ :=
  ∑ σ, ∑ ν, invMetric G y σ ν * ricci G y σ ν

/-- Einstein tensor `G_{μν} = R_{μν} - ½ R g_{μν}`. -/
def einsteinTensor (G : E4 → Matrix (Fin 4) (Fin 4) ℝ) (y : E4) (μ ν : Fin 4) : ℝ :=
  ricci G y μ ν - (1 / 2 : ℝ) * scalarCurvature G y * G y μ ν

/-- Contravariant field strength `F^{αβ} = g^{αμ} g^{βν} F_{μν}`. -/
def raiseBoth (G : E4 → Matrix (Fin 4) (Fin 4) ℝ) (F : E4 → Matrix (Fin 4) (Fin 4) ℝ)
    (y : E4) (α β : Fin 4) : ℝ :=
  ∑ μ, ∑ ν, invMetric G y α μ * invMetric G y β ν * F y μ ν

/-- The (trace-adjusted) Maxwell stress tensor in geometrized Gaussian units, multiplied by `8π`:
`2 (F_{μα} F_ν{}^α - ¼ g_{μν} F_{αβ} F^{αβ})`. -/
def maxwellSource (G : E4 → Matrix (Fin 4) (Fin 4) ℝ) (F : E4 → Matrix (Fin 4) (Fin 4) ℝ)
    (y : E4) (μ ν : Fin 4) : ℝ :=
  2 * ((∑ α, ∑ β, F y μ α * invMetric G y α β * F y ν β)
    - (1 / 4 : ℝ) * G y μ ν * ∑ α, ∑ β, F y α β * raiseBoth G F y α β)

/-- The Einstein–Maxwell system at a point of coordinate space, for metric components `G`
and electromagnetic field components `F` (a 2-form):
1. Einstein equation `G_{μν} = 2 (F_{μα} F_ν{}^α - ¼ g_{μν} F²)`;
2. source-free Maxwell equation `∂_μ (√|det g| F^{μν}) = 0`;
3. Bianchi identity (closedness) `∂_λ F_{μν} + ∂_μ F_{νλ} + ∂_ν F_{λμ} = 0`. -/
def EinsteinMaxwellAt (G : E4 → Matrix (Fin 4) (Fin 4) ℝ) (F : E4 → Matrix (Fin 4) (Fin 4) ℝ)
    (y : E4) : Prop :=
  (∀ μ ν, einsteinTensor G y μ ν = maxwellSource G F y μ ν) ∧
  (∀ ν, ∑ μ, coordPartial
      (fun z => Real.sqrt |(G z).det| * raiseBoth G F z μ ν) μ y = 0) ∧
  (∀ l μ ν, coordPartial (fun z => F z μ ν) l y + coordPartial (fun z => F z ν l) μ y
      + coordPartial (fun z => F z l μ) ν y = 0)

/-- The Levi-Civita symbol `ε_{μναβ}` (sign of the permutation, `0` if an index repeats). -/
def leviCivita (μ ν α β : Fin 4) : ℝ :=
  if h : Function.Bijective ![μ, ν, α, β] then
    ((Equiv.Perm.sign (Equiv.ofBijective _ h) : ℤ) : ℝ)
  else 0

/-- Hodge dual of a 2-form with respect to the metric matrix `g` (at one point):
`(⋆F)_{μν} = ½ √|det g| ε_{μναβ} F^{αβ}`. -/
def hodgeDual (g F : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun μ ν => (1 / 2 : ℝ) * Real.sqrt |g.det| *
    ∑ α, ∑ β, leviCivita μ ν α β * ∑ γ, ∑ δ, g⁻¹ α γ * g⁻¹ β δ * F γ δ

/-! ## The Kerr–Newman family in Kerr–Schild coordinates -/

/-- The Kerr–Schild radial function `r(x,y,z) ≥ 0` for rotation parameter `a`:
the nonnegative root of `(x² + y²)/(r² + a²) + z²/r² = 1`, i.e.
`r² = ½ (ρ² - a² + √((ρ² - a²)² + 4 a² z²))` with `ρ² = x² + y² + z²`. -/
def ksRadius (a : ℝ) (y : E4) : ℝ :=
  let ρ2 := y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2
  Real.sqrt ((ρ2 - a ^ 2 + Real.sqrt ((ρ2 - a ^ 2) ^ 2 + 4 * a ^ 2 * y 3 ^ 2)) / 2)

/-- The Kerr–Schild null covector
`k = (1, (r x + a y)/(r² + a²), (r y - a x)/(r² + a²), z / r)`. -/
def ksNull (a : ℝ) (y : E4) : Fin 4 → ℝ :=
  let r := ksRadius a y
  ![1, (r * y 1 + a * y 2) / (r ^ 2 + a ^ 2), (r * y 2 - a * y 1) / (r ^ 2 + a ^ 2), y 3 / r]

/-- The Kerr–Schild profile `f = r² (2 m r - e²) / (r⁴ + a² z²)`. -/
def ksProfile (m a e : ℝ) (y : E4) : ℝ :=
  let r := ksRadius a y
  r ^ 2 * (2 * m * r - e ^ 2) / (r ^ 4 + a ^ 2 * y 3 ^ 2)

/-- Kerr–Newman metric components in Kerr–Schild coordinates:
`g_{μν} = η_{μν} + f k_μ k_ν` (mass `m`, rotation parameter `a`, charge `e`). -/
def kerrNewmanMetric (m a e : ℝ) (y : E4) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun μ ν => minkowski μ ν + ksProfile m a e y * ksNull a y μ * ksNull a y ν

/-- Kerr–Newman electromagnetic potential `A_μ = e r³ / (r⁴ + a² z²) · k_μ`. -/
def kerrNewmanPotential (a e : ℝ) (y : E4) : Fin 4 → ℝ :=
  let r := ksRadius a y
  fun μ => e * r ^ 3 / (r ^ 4 + a ^ 2 * y 3 ^ 2) * ksNull a y μ

/-- Kerr–Newman electromagnetic field `F_{μν} = ∂_μ A_ν - ∂_ν A_μ`. -/
def kerrNewmanField (a e : ℝ) (y : E4) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun μ ν => coordPartial (fun z => kerrNewmanPotential a e z ν) μ y
    - coordPartial (fun z => kerrNewmanPotential a e z μ) ν y

/-- Admissible black-hole parameters: `m > 0` and `a² + e² ≤ m²`. -/
def IsKerrNewmanBlackHoleParams (m a e : ℝ) : Prop := 0 < m ∧ a ^ 2 + e ^ 2 ≤ m ^ 2

/-- Outer horizon radius `r₊ = m + √(m² - a² - e²)`. -/
def kerrNewmanOuterRadius (m a e : ℝ) : ℝ := m + Real.sqrt (m ^ 2 - a ^ 2 - e ^ 2)

/-- The Kerr–Newman domain of outer communications in Kerr–Schild coordinates: `r > r₊`. -/
def kerrNewmanDOC (m a e : ℝ) : Set E4 := {y | kerrNewmanOuterRadius m a e < ksRadius a y}

end NoHair


