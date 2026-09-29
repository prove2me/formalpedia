-- Prove2me | Definitions.Def_CarrollGR_Defs
-- name    : CarrollGR_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T23:48:53.953605+00:00
-- url     : https://prove2.me/theorems/f1126524-a550-4efb-83b4-2933d44ca93e
-- title:
--   Carroll's GR in coordinates: metric, Christoffel symbols, covariant derivatives, curvature, Schwarzschild and Kruskal
-- statement:
--   This definition file fixes the coordinate language used by the whole *No-Nonsense Introduction to General Relativity* series. Everything is written in one coordinate chart of a four-dimensional spacetime, following S. M. Carroll's notes equation by equation.
--
--   1. **Points and fields.** A point of the chart is $x=(x^0,x^1,x^2,x^3)\in\mathbb R^4$ (`Coord`). A two-index tensor field $T$ (`TensorField2`), such as the metric $g_{\mu\nu}$, assigns a real $4\times4$ matrix to each point; a four-index field (`TensorField4`) assigns an array $T_{\mu\nu\rho\sigma}(x)$. The partial derivative $\partial_\mu f(x)$ (`partialD`) is the derivative of $f$ at $x$ in the $\mu$-th coordinate direction.
--   2. **Minkowski metric** (eq. (3)): $\eta_{\mu\nu}=\operatorname{diag}(-1,1,1,1)$ (`minkowskiEta`). A matrix is *Lorentzian* (`IsLorentzian`) if $P^{\mathsf T}MP=\eta$ for some invertible $P$, i.e. it is a symmetric nondegenerate form of signature $(-+++)$. A field $g$ is a *spacetime metric on an open set* $U$ (`IsSpacetimeMetricOn`) if its components are smooth on $U$ and $g(y)$ is Lorentzian for every $y\in U$.
--   3. **Inverse metric** (eq. (23)): $g^{\mu\nu}$ is the matrix inverse of $g_{\mu\nu}$ (`invMetric`).
--   4. **Christoffel symbols** (eq. (36)):
--   $$\Gamma^\sigma_{\mu\nu}=\tfrac12 g^{\sigma\rho}\left(\partial_\mu g_{\nu\rho}+\partial_\nu g_{\rho\mu}-\partial_\rho g_{\mu\nu}\right).$$
--   5. **Covariant derivatives** (eq. (35)) of two-index tensors with lower or upper indices and of four-index tensors with lower indices (`covDerivLower2`, `covDerivUpper2`, `covDerivLower4`): one $+\Gamma$ term per upper index and one $-\Gamma$ term per lower index.
--   6. **Curvature**: the Riemann tensor (eq. (44))
--   $$R^\sigma{}_{\mu\alpha\beta}=\partial_\alpha\Gamma^\sigma_{\mu\beta}-\partial_\beta\Gamma^\sigma_{\mu\alpha}+\Gamma^\sigma_{\alpha\lambda}\Gamma^\lambda_{\mu\beta}-\Gamma^\sigma_{\beta\lambda}\Gamma^\lambda_{\mu\alpha},$$
--   its all-lower form $R_{\mu\nu\rho\sigma}=g_{\mu\lambda}R^\lambda{}_{\nu\rho\sigma}$, the Ricci tensor $R_{\alpha\beta}=R^\lambda{}_{\alpha\lambda\beta}$ (eq. (45)), the Ricci scalar $R=g^{\mu\nu}R_{\mu\nu}$ (eq. (46)), the Einstein tensor $G_{\mu\nu}=R_{\mu\nu}-\tfrac12Rg_{\mu\nu}$ (eq. (50)) and its raised form $G^{\mu\nu}=g^{\mu\alpha}g^{\nu\beta}G_{\alpha\beta}$.
--   7. **Einstein's equation** (eq. (57)) at a point: $G_{\mu\nu}=8\pi G\,T_{\mu\nu}$ for all $\mu,\nu$ (`EinsteinEq`), with $T=g^{\mu\nu}T_{\mu\nu}$ the trace (`metricTrace`).
--   8. **Changes of coordinates**: the Jacobian matrix $\partial F^a/\partial x^\mu$ (`jacobian`); spherical coordinates (eq. (18)) $(t,r,\theta,\phi)\mapsto(t,r\sin\theta\cos\phi,r\sin\theta\sin\phi,r\cos\theta)$ (`sphericalToCartesian`).
--   9. **Spherically symmetric metrics** (eq. (71)): in coordinates $(t,r,\theta,\phi)$,
--   $$ds^2=-A(r,t)\,dt^2+B(r,t)\,dr^2+r^2(d\theta^2+\sin^2\theta\,d\phi^2)$$
--   (`sphericalMetric A B`), and the **Schwarzschild metric** (eq. (72)), the case $A=1-2Gm/r$, $B=(1-2Gm/r)^{-1}$ (`schwarzschild G m`).
--   10. **Kruskal coordinates** (eqs. (73)–(74)): $u=(r/2Gm-1)^{1/2}e^{r/4Gm}\cosh(t/4Gm)$, $v=(r/2Gm-1)^{1/2}e^{r/4Gm}\sinh(t/4Gm)$, the map $(t,r,\theta,\phi)\mapsto(v,u,\theta,\phi)$, and the Kruskal-form components $\operatorname{diag}(-F,F,r^2,r^2\sin^2\theta)$ with $F=\frac{32(Gm)^3}{r}e^{-r/2Gm}$, written as a function of the values of $r$ and $\theta$.
--
--   These definitions are the shared vocabulary of every statement in the mission; the curvature formulas are transcribed with Carroll's index placement exactly.
--
--   **Formalization Note** All objects are total functions: a derivative at a point where the function is not differentiable is $0$, the inverse of a singular matrix is the zero matrix, and $1/0=0$. Theorems that use these definitions therefore state explicitly the open region (smoothness, nondegeneracy, $r\neq0$, $r\neq2Gm$, $0<\theta<\pi$) on which they are claimed. Coordinates are $x^0=t$ and, in the spherical charts, $x^1=r$, $x^2=\theta$, $x^3=\phi$.
-- source:
--   S. M. Carroll, "A No-Nonsense Introduction to General Relativity" (lecture notes, 2001), uploaded PDF, eqs. (3), (18), (23), (35), (36), (44)–(46), (50), (57), (71)–(74)

import Mathlib

/-!
# Coordinate general relativity after Carroll, "A No-Nonsense Introduction to General Relativity"

All objects are written in a single coordinate chart of a 4-dimensional spacetime.
A point of the chart is `x : Fin 4 → ℝ`, with `x 0 = t`, `x 1`, `x 2`, `x 3` the remaining
coordinates (for the spherical charts of §3 and §6: `x 1 = r`, `x 2 = θ`, `x 3 = φ`).
A (0,2)-tensor field (such as the metric `g_{μν}`) is a function giving at each point the
`4 × 4` matrix of its components.  Partial derivatives are Fréchet derivatives in the
coordinate directions.  Formulas follow Carroll's equation numbers.
-/

open scoped ContDiff

namespace CarrollGR

open Finset

/-- A point `(x⁰, x¹, x², x³)` of a coordinate chart of four-dimensional spacetime. -/
abbrev Coord : Type := Fin 4 → ℝ

/-- The components `T_{μν}(x)` of a two-index tensor field in a chart (e.g. the metric `g_{μν}`). -/
abbrev TensorField2 : Type := Coord → Matrix (Fin 4) (Fin 4) ℝ

/-- The components `T_{μνρσ}(x)` of a four-index tensor field in a chart. -/
abbrev TensorField4 : Type := Coord → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ

/-- The coordinate partial derivative `∂_μ f(x) = ∂f/∂x^μ (x)`. -/
noncomputable def partialD (μ : Fin 4) (f : Coord → ℝ) (x : Coord) : ℝ :=
  fderiv ℝ f x (Pi.single μ 1)

/-- The Minkowski metric `η_{μν} = diag(-1, 1, 1, 1)` (Carroll eq. (3)). -/
def minkowskiEta : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![-1, 1, 1, 1]

/-- A symmetric matrix `M` has Lorentzian signature `(− + + +)`: it is congruent to the
Minkowski metric, i.e. `Pᵀ M P = η` for some invertible matrix `P`. -/
def IsLorentzian (M : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P.det ∧ P.transpose * M * P = minkowskiEta

/-- `g` is a spacetime metric on the open set `U` of the chart: its components are smooth on `U`
and at every point of `U` it is a (symmetric) metric of signature `(− + + +)`. -/
def IsSpacetimeMetricOn (g : TensorField2) (U : Set Coord) : Prop :=
  IsOpen U ∧ (∀ μ ν : Fin 4, ContDiffOn ℝ ∞ (fun y => g y μ ν) U) ∧ ∀ y ∈ U, IsLorentzian (g y)

/-- The inverse metric `g^{μν}(x)`, the matrix inverse of `g_{μν}(x)` (Carroll eq. (23)). -/
noncomputable def invMetric (g : TensorField2) : TensorField2 := fun x => (g x)⁻¹

/-- The Christoffel symbols (Carroll eq. (36)):
`Γ^σ_{μν} = ½ g^{σρ} (∂_μ g_{νρ} + ∂_ν g_{ρμ} − ∂_ρ g_{μν})`. -/
noncomputable def christoffel (g : TensorField2) (σ μ ν : Fin 4) (x : Coord) : ℝ :=
  (1 / 2 : ℝ) * ∑ ρ : Fin 4, invMetric g x σ ρ *
    (partialD μ (fun y => g y ν ρ) x + partialD ν (fun y => g y ρ μ) x
      - partialD ρ (fun y => g y μ ν) x)

/-- The covariant derivative of a two-index tensor with lower indices (Carroll eq. (35)):
`∇_σ T_{μν} = ∂_σ T_{μν} − Γ^λ_{σμ} T_{λν} − Γ^λ_{σν} T_{μλ}`. -/
noncomputable def covDerivLower2 (g T : TensorField2) (σ μ ν : Fin 4) (x : Coord) : ℝ :=
  partialD σ (fun y => T y μ ν) x
    - ∑ l : Fin 4, christoffel g l σ μ x * T x l ν
    - ∑ l : Fin 4, christoffel g l σ ν x * T x μ l

/-- The covariant derivative of a two-index tensor with upper indices (Carroll eq. (35)):
`∇_σ T^{μν} = ∂_σ T^{μν} + Γ^μ_{σλ} T^{λν} + Γ^ν_{σλ} T^{μλ}`. -/
noncomputable def covDerivUpper2 (g T : TensorField2) (σ μ ν : Fin 4) (x : Coord) : ℝ :=
  partialD σ (fun y => T y μ ν) x
    + ∑ l : Fin 4, christoffel g μ σ l x * T x l ν
    + ∑ l : Fin 4, christoffel g ν σ l x * T x μ l

/-- The covariant derivative of a four-index tensor with lower indices (Carroll eq. (35)):
`∇_λ T_{μνρσ} = ∂_λ T_{μνρσ} − Γ^κ_{λμ} T_{κνρσ} − Γ^κ_{λν} T_{μκρσ} − Γ^κ_{λρ} T_{μνκσ}
 − Γ^κ_{λσ} T_{μνρκ}`. -/
noncomputable def covDerivLower4 (g : TensorField2) (T : TensorField4) (l μ ν ρ σ : Fin 4)
    (x : Coord) : ℝ :=
  partialD l (fun y => T y μ ν ρ σ) x
    - ∑ k : Fin 4, christoffel g k l μ x * T x k ν ρ σ
    - ∑ k : Fin 4, christoffel g k l ν x * T x μ k ρ σ
    - ∑ k : Fin 4, christoffel g k l ρ x * T x μ ν k σ
    - ∑ k : Fin 4, christoffel g k l σ x * T x μ ν ρ k

/-- The Riemann curvature tensor (Carroll eq. (44)):
`R^σ_{μαβ} = ∂_α Γ^σ_{μβ} − ∂_β Γ^σ_{μα} + Γ^σ_{αλ} Γ^λ_{μβ} − Γ^σ_{βλ} Γ^λ_{μα}`. -/
noncomputable def riemann (g : TensorField2) (σ μ α β : Fin 4) (x : Coord) : ℝ :=
  partialD α (christoffel g σ μ β) x - partialD β (christoffel g σ μ α) x
    + ∑ l : Fin 4, (christoffel g σ α l x * christoffel g l μ β x
      - christoffel g σ β l x * christoffel g l μ α x)

/-- The Riemann tensor with all indices lowered, `R_{μνρσ} = g_{μλ} R^λ_{νρσ}` (Carroll, before
eq. (47)). -/
noncomputable def riemannLower (g : TensorField2) : TensorField4 :=
  fun x μ ν ρ σ => ∑ l : Fin 4, g x μ l * riemann g l ν ρ σ x

/-- The Ricci tensor `R_{αβ} = R^λ_{αλβ}` (Carroll eq. (45)). -/
noncomputable def ricci (g : TensorField2) (α β : Fin 4) (x : Coord) : ℝ :=
  ∑ l : Fin 4, riemann g l α l β x

/-- The Ricci scalar `R = g^{μν} R_{μν}` (Carroll eq. (46)). -/
noncomputable def ricciScalar (g : TensorField2) (x : Coord) : ℝ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, invMetric g x μ ν * ricci g μ ν x

/-- The Einstein tensor `G_{μν} = R_{μν} − ½ R g_{μν}` (Carroll eq. (50)). -/
noncomputable def einstein (g : TensorField2) (μ ν : Fin 4) (x : Coord) : ℝ :=
  ricci g μ ν x - (1 / 2 : ℝ) * ricciScalar g x * g x μ ν

/-- The Einstein tensor with both indices raised, `G^{μν} = g^{μα} g^{νβ} G_{αβ}`. -/
noncomputable def einsteinUpper (g : TensorField2) : TensorField2 :=
  fun x => Matrix.of fun μ ν =>
    ∑ α : Fin 4, ∑ β : Fin 4, invMetric g x μ α * invMetric g x ν β * einstein g α β x

/-- The trace `T = g^{μν} T_{μν}` of a two-index tensor with respect to the metric `g`. -/
noncomputable def metricTrace (g T : TensorField2) (x : Coord) : ℝ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, invMetric g x μ ν * T x μ ν

/-- Einstein's equation `R_{μν} − ½ R g_{μν} = 8πG T_{μν}` at the point `x` (Carroll eq. (57)),
for the metric `g`, Newton's constant `GN` and energy-momentum tensor `T`. -/
def EinsteinEq (g : TensorField2) (GN : ℝ) (T : TensorField2) (x : Coord) : Prop :=
  ∀ μ ν : Fin 4, einstein g μ ν x = 8 * Real.pi * GN * T x μ ν

/-- The Jacobian matrix `∂F^a/∂x^μ (x)` of a change of coordinates `F` (row `a`, column `μ`). -/
noncomputable def jacobian (F : Coord → Coord) (x : Coord) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun a μ => partialD μ (fun y => F y a) x

/-- Spherical coordinates on space (Carroll eq. (18)):
`(t, r, θ, φ) ↦ (t, r sin θ cos φ, r sin θ sin φ, r cos θ)`. -/
noncomputable def sphericalToCartesian (x : Coord) : Coord :=
  ![x 0, x 1 * Real.sin (x 2) * Real.cos (x 3), x 1 * Real.sin (x 2) * Real.sin (x 3),
    x 1 * Real.cos (x 2)]

/-- The general spherically symmetric metric in spherical coordinates `(t, r, θ, φ)`
(Carroll eq. (71)): `ds² = −A(r,t) dt² + B(r,t) dr² + r² (dθ² + sin²θ dφ²)`. -/
noncomputable def sphericalMetric (A B : ℝ → ℝ → ℝ) : TensorField2 := fun x =>
  Matrix.diagonal ![-A (x 1) (x 0), B (x 1) (x 0), (x 1) ^ 2, (x 1) ^ 2 * Real.sin (x 2) ^ 2]

/-- The Schwarzschild metric (Carroll eq. (72)) with Newton's constant `GN` and mass `m`:
`ds² = −(1 − 2Gm/r) dt² + (1 − 2Gm/r)⁻¹ dr² + r² (dθ² + sin²θ dφ²)`. -/
noncomputable def schwarzschild (GN m : ℝ) : TensorField2 :=
  sphericalMetric (fun r _ => 1 - 2 * GN * m / r) (fun r _ => (1 - 2 * GN * m / r)⁻¹)

/-- The Kruskal coordinate `u` (Carroll eq. (73)):
`u = (r/2Gm − 1)^{1/2} e^{r/4Gm} cosh(t/4Gm)`. -/
noncomputable def kruskalU (GN m t r : ℝ) : ℝ :=
  Real.sqrt (r / (2 * GN * m) - 1) * Real.exp (r / (4 * GN * m)) * Real.cosh (t / (4 * GN * m))

/-- The Kruskal coordinate `v` (Carroll eq. (73)):
`v = (r/2Gm − 1)^{1/2} e^{r/4Gm} sinh(t/4Gm)`. -/
noncomputable def kruskalV (GN m t r : ℝ) : ℝ :=
  Real.sqrt (r / (2 * GN * m) - 1) * Real.exp (r / (4 * GN * m)) * Real.sinh (t / (4 * GN * m))

/-- The change of coordinates `(t, r, θ, φ) ↦ (v, u, θ, φ)` from Schwarzschild to Kruskal
coordinates (Carroll eq. (73)); in Kruskal coordinates `v` is listed first. -/
noncomputable def schwarzschildToKruskal (GN m : ℝ) (x : Coord) : Coord :=
  ![kruskalV GN m (x 0) (x 1), kruskalU GN m (x 0) (x 1), x 2, x 3]

/-- The components of the Schwarzschild metric in Kruskal coordinates `(v, u, θ, φ)`
(Carroll eq. (74)), written as a function of the values of `r` and `θ` at the point:
`diag(−F, F, r², r² sin²θ)` with `F = 32 (Gm)³ / r · e^{−r/2Gm}`. -/
noncomputable def kruskalMetricAt (GN m r θ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal
    ![-(32 * (GN * m) ^ 3 / r * Real.exp (-r / (2 * GN * m))),
      32 * (GN * m) ^ 3 / r * Real.exp (-r / (2 * GN * m)), r ^ 2, r ^ 2 * Real.sin θ ^ 2]

end CarrollGR


