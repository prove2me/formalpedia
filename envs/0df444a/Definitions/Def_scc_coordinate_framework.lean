-- Prove2me | Definitions.Def_scc_coordinate_framework
-- name    : scc_coordinate_framework
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T02:00:20.926553+00:00
-- url     : https://prove2.me/theorems/6701c81c-94f0-40c3-b80f-614f03738d86
-- title:
--   Coordinate framework: Lorentzian metrics, curvature, causal structure and inextendibility
-- statement:
--   This file builds, from nothing, the geometric vocabulary the rest of the mission needs.
--
--   **Framework scope.** Every statement in this proposal is set in a purpose-built *single-chart coordinate framework*, not in abstract Lorentzian geometry. Mathlib contains no Lorentzian geometry whatsoever — no Lorentzian metrics, no affine connection, no Riemann or Ricci curvature, no causal structure, no global hyperbolicity, no maximal globally hyperbolic development — so all of it is defined from scratch in the accompanying definition item. A *spacetime* here is an open subset $U \subseteq \mathbb{R}^4$ together with a field of $4 \times 4$ real matrices $g_{ab}(x)$ of signature $(-,+,+,+)$. This is fully precise and auditable, but it is **strictly less general than the abstract Lorentzian manifolds of the source**: only chart-representable spacetimes, and only chart-representable extensions, are quantified over.
--
--   **Coordinates and derivatives.** A point is an element of $\mathbb{R}^4$ with index $0$ read as time. $\partial_a f$ is the derivative of $f$ in the $a$-th coordinate direction, with the Lean convention that it is $0$ wherever $f$ fails to be differentiable.
--
--   **Signature.** $\eta = \mathrm{diag}(-1,1,1,1)$ is the Minkowski matrix, equation (3.1) of the source. A matrix $A$ is declared Lorentzian when it is congruent to $\eta$, that is $A = P^{\mathsf T}\eta P$ for some invertible $P$; by Sylvester's law of inertia this says exactly that $A$ is symmetric of signature $(-,+,+,+)$.
--
--   **Curvature.** The Christoffel symbols are
--   $$\Gamma^a{}_{bc} = \tfrac12 g^{ad}\big(\partial_b g_{dc} + \partial_c g_{bd} - \partial_d g_{bc}\big),$$
--   the Riemann tensor is
--   $$R^a{}_{bcd} = \partial_c \Gamma^a{}_{db} - \partial_d \Gamma^a{}_{cb} + \Gamma^a{}_{ce}\Gamma^e{}_{db} - \Gamma^a{}_{de}\Gamma^e{}_{cb},$$
--   the Ricci tensor is the trace $R_{bd} = R^a{}_{bad}$, the scalar curvature is $g^{bd}R_{bd}$, and the Kretschmann scalar is $K = R_{abcd}R^{abcd}$. The inverse metric $g^{ab}$ is Mathlib's nonsingular matrix inverse, so it is the zero matrix where $g$ degenerates.
--
--   **Einstein equations.** A metric is a vacuum solution on $U$ when $R_{bd}=0$ throughout $U$ — equation (2.4) of the source in vacuum.
--
--   **Causal structure.** A vector is timelike when $g(v,v)<0$ and causal when it is nonzero with $g(v,v)\le0$. The geodesic equation is equation (2.2) of the source,
--   $$\frac{d^2\gamma^a}{d\tau^2} + \Gamma^a{}_{\sigma\mu}(g)\frac{d\gamma^\sigma}{d\tau}\frac{d\gamma^\mu}{d\tau} = 0,$$
--   with timelike geodesics normalised by $g(\gamma',\gamma')=-1$. Timelike geodesic completeness asks that every timelike geodesic on a bounded interval $[0,T)$ extend to one on $[0,\infty)$; since the parameter-reversal of a geodesic is a geodesic, quantifying over all geodesics captures both time directions.
--
--   **Global hyperbolicity.** An *inextendible* causal curve is one defined on all of $\mathbb{R}$ which, at both ends, eventually leaves every compact subset of $U$. The escape clause is essential: without it, a curve reparametrised to have infinite parameter range while staying inside a compact piece of $U$ would count as inextendible, and the Cauchy condition below would be wrong. A Cauchy hypersurface is a subset met exactly once by every inextendible causal curve, and $(U,g)$ is globally hyperbolic when one exists. $(U,g)$ is time-oriented when it carries a continuous timelike vector field.
--
--   **Inextendibility.** A $C^0$ extension of $(U,g)$ is a triple $(V,h,J)$ with $V$ open, $h$ a *continuous* Lorentzian metric on $V$, and $J : U \to V$ an injective $C^1$ immersion which is an isometry onto its image, $g = (DJ)^{\mathsf T}(h\circ J)(DJ)$, whose image is proper in the strong sense of having nonempty boundary inside $V$. This is the coordinate rendering of the proper isometric embedding $J : \mathcal{M}\to\bar{\mathcal{M}}$ of Section 2.3 of the source. $(U,g)$ is $C^0$-inextendible when no such triple exists — Statement I of Section 2.3 — and $C^2$-inextendible when no such triple with $h$ additionally $C^2$ exists — Statement III.
--
--   **Explicit metrics.** Minkowski (equation (3.1)); Schwarzschild in $(t,r,\theta,\varphi)$ (equation (3.2)) with its exterior $\{r>2M\}$ and interior $\{0<r<2M\}$ taken inside the angular chart $0<\theta<\pi$; Reissner–Nordström with lapse $1-2M/r+e^2/r^2$ and horizon radii $r_\pm = M \pm \sqrt{M^2-e^2}$ (Section 3.3); and the Kasner metrics $-dt^2 + \sum_i t^{2p_i}(dx^i)^2$ on $\{t>0\}$ with the Kasner relations $\sum_i p_i = \sum_i p_i^2 = 1$ (Section 4).
--
--   Every later item is phrased in this vocabulary, so this is the item to audit first: if a definition here is wrong, everything built on it is wrong too.
-- source:
--   Maxime Van de Moortel, "The Strong Cosmic Censorship Conjecture", arXiv:2501.13180v2 [gr-qc], 10 Oct 2025, https://arxiv.org/abs/2501.13180, Sections 2.2–2.4, 3.1–3.3 and 4; equations (2.2), (2.4), (3.1), (3.2); Statements I/II/III of Section 2.3

/-
Coordinate framework for the Strong Cosmic Censorship mission proposal.

Source: Maxime Van de Moortel, "The Strong Cosmic Censorship Conjecture",
arXiv:2501.13180v2 [gr-qc], 10 Oct 2025.

SCOPE NOTE (important, and repeated in every uploaded read-back):
Mathlib currently contains no Lorentzian geometry at all -- no Lorentzian
metrics, no affine connection, no Riemann/Ricci curvature, no causal structure,
no global hyperbolicity, no maximal globally hyperbolic development.  Everything
below is therefore built from scratch, and it is built *in a single coordinate
chart*: a spacetime is an open subset of `ℝ⁴` carrying a matrix-valued metric
field.  This is fully precise and auditable, but it is strictly less general
than the abstract Lorentzian manifolds of the source: statements proved here
concern chart-representable spacetimes only.
-/
import Mathlib

open scoped Matrix
open Set

namespace StrongCosmicCensorship

/-! ## Coordinates and partial derivatives -/

/-- A point of the coordinate spacetime `ℝ^{1+3}`; index `0` is the time coordinate. -/
abbrev Coords := Fin 4 → ℝ

/-- A metric field: a `4 × 4` real matrix attached to each coordinate point. -/
abbrev MetricField := Coords → Matrix (Fin 4) (Fin 4) ℝ

/-- The `a`-th coordinate direction. -/
noncomputable def dir (a : Fin 4) : Coords := Pi.single a 1

/-- The partial derivative `∂ₐ f` of a scalar field, as a Fréchet derivative in
the direction `dir a`.  Junk value `0` where `f` is not differentiable. -/
noncomputable def pd (a : Fin 4) (f : Coords → ℝ) (x : Coords) : ℝ :=
  fderiv ℝ f x (dir a)

/-! ## Signature -/

/-- The Minkowski matrix `diag(-1, 1, 1, 1)`, i.e. the metric (3.1) of the source. -/
def minkowskiMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then -1 else 1)

/-- A matrix has Lorentzian signature `(-,+,+,+)` when it is congruent to
`minkowskiMatrix` (Sylvester's law of inertia). -/
def IsLorentzianMatrix (A : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P.det ∧ A = P.transpose * minkowskiMatrix * P

/-- The inverse metric `g^{ab}`.  Uses the Mathlib nonsingular inverse, so it is
the zero matrix at points where `g` is singular. -/
noncomputable def ginv (g : MetricField) (x : Coords) : Matrix (Fin 4) (Fin 4) ℝ := (g x)⁻¹

/-- `g(u, v)` at the point `x`. -/
noncomputable def gip (g : MetricField) (x : Coords) (u v : Coords) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, g x a b * u a * v b

/-! ## Curvature -/

/-- Christoffel symbols `Γᵃ_{bc} = ½ gᵃᵈ (∂_b g_{dc} + ∂_c g_{bd} - ∂_d g_{bc})`. -/
noncomputable def christoffel (g : MetricField) (a b c : Fin 4) (x : Coords) : ℝ :=
  (1 / 2 : ℝ) * ∑ d : Fin 4, ginv g x a d *
    (pd b (fun y => g y d c) x + pd c (fun y => g y b d) x - pd d (fun y => g y b c) x)

/-- The Riemann tensor
`Rᵃ_{bcd} = ∂_c Γᵃ_{db} - ∂_d Γᵃ_{cb} + Γᵃ_{ce} Γᵉ_{db} - Γᵃ_{de} Γᵉ_{cb}`. -/
noncomputable def riemann (g : MetricField) (a b c d : Fin 4) (x : Coords) : ℝ :=
  pd c (christoffel g a d b) x - pd d (christoffel g a c b) x
    + (∑ e : Fin 4, christoffel g a c e x * christoffel g e d b x)
    - (∑ e : Fin 4, christoffel g a d e x * christoffel g e c b x)

/-- The fully lowered Riemann tensor `R_{abcd} = g_{ae} Rᵉ_{bcd}`. -/
noncomputable def riemannLower (g : MetricField) (a b c d : Fin 4) (x : Coords) : ℝ :=
  ∑ e : Fin 4, g x a e * riemann g e b c d x

/-- The Ricci tensor `R_{bd} = Rᵃ_{bad}`. -/
noncomputable def ricci (g : MetricField) (b d : Fin 4) (x : Coords) : ℝ :=
  ∑ a : Fin 4, riemann g a b a d x

/-- The scalar curvature `R = g^{bd} R_{bd}`. -/
noncomputable def scalarCurvature (g : MetricField) (x : Coords) : ℝ :=
  ∑ b : Fin 4, ∑ d : Fin 4, ginv g x b d * ricci g b d x

/-- The Kretschmann scalar `K = R_{abcd} R^{abcd}`. -/
noncomputable def kretschmann (g : MetricField) (x : Coords) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
    ∑ a' : Fin 4, ∑ b' : Fin 4, ∑ c' : Fin 4, ∑ d' : Fin 4,
      riemannLower g a b c d x * riemannLower g a' b' c' d' x *
        ginv g x a a' * ginv g x b b' * ginv g x c c' * ginv g x d d'

/-! ## Spacetimes -/

/-- A smooth Lorentzian spacetime in a single chart: an open set `U ⊆ ℝ⁴` with a
smooth metric field of signature `(-,+,+,+)` on `U`. -/
structure IsSpacetime (U : Set Coords) (g : MetricField) : Prop where
  isOpen : IsOpen U
  smooth : ∀ a b : Fin 4, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => g x a b) U
  lorentzian : ∀ x ∈ U, IsLorentzianMatrix (g x)

/-- The vacuum Einstein equations `Ric(g) = 0` on `U`, i.e. equation (2.4) of the
source in vacuum. -/
def IsVacuum (U : Set Coords) (g : MetricField) : Prop :=
  ∀ x ∈ U, ∀ b d : Fin 4, ricci g b d x = 0

/-! ## Causal structure -/

/-- A vector `v` is timelike at `x` when `g(v, v) < 0`. -/
def IsTimelikeVec (g : MetricField) (x : Coords) (v : Coords) : Prop := gip g x v v < 0

/-- A vector `v` is causal at `x` when it is nonzero and `g(v, v) ≤ 0`. -/
def IsCausalVec (g : MetricField) (x : Coords) (v : Coords) : Prop :=
  v ≠ 0 ∧ gip g x v v ≤ 0

/-- The coordinate velocity of a curve. -/
noncomputable def vel (γ : ℝ → Coords) (τ : ℝ) : Coords := fun a => deriv (fun s => γ s a) τ

/-- The coordinate acceleration of a curve. -/
noncomputable def acc (γ : ℝ → Coords) (τ : ℝ) : Coords :=
  fun a => deriv (fun s => deriv (fun u => γ u a) s) τ

/-- The geodesic equation (2.2) of the source:
`d²γᵃ/dτ² + Γᵃ_{σμ}(g) dγ^σ/dτ dγ^μ/dτ = 0` on the interval `I`. -/
def IsGeodesicOn (g : MetricField) (I : Set ℝ) (γ : ℝ → Coords) : Prop :=
  ∀ τ ∈ I, ∀ a : Fin 4,
    acc γ τ a + ∑ σ : Fin 4, ∑ μ : Fin 4,
      christoffel g a σ μ (γ τ) * vel γ τ σ * vel γ τ μ = 0

/-- A timelike geodesic of `(U, g)` defined on the interval `I`, normalised by
`g(γ', γ') = -1` as in (2.2). -/
def IsTimelikeGeodesicOn (U : Set Coords) (g : MetricField) (I : Set ℝ) (γ : ℝ → Coords) : Prop :=
  IsGeodesicOn g I γ ∧ (∀ τ ∈ I, γ τ ∈ U) ∧ (∀ τ ∈ I, gip g (γ τ) (vel γ τ) (vel γ τ) = -1)

/-- `(U, g)` is timelike geodesically complete when every timelike geodesic
defined on a bounded interval `[0, T)` extends to a timelike geodesic defined on
all of `[0, ∞)`. -/
def TimelikeGeodesicallyComplete (U : Set Coords) (g : MetricField) : Prop :=
  ∀ (T : ℝ) (γ : ℝ → Coords), 0 < T → IsTimelikeGeodesicOn U g (Ico 0 T) γ →
    ∃ γ' : ℝ → Coords, EqOn γ' γ (Ico 0 T) ∧ IsTimelikeGeodesicOn U g (Ici 0) γ'

/-! ## Global hyperbolicity -/

/-- A causal curve of `(U, g)` on the interval `I`. -/
def IsCausalCurveOn (U : Set Coords) (g : MetricField) (I : Set ℝ) (γ : ℝ → Coords) : Prop :=
  (∀ τ ∈ I, γ τ ∈ U) ∧ (∀ τ ∈ I, DifferentiableAt ℝ γ τ) ∧
    (∀ τ ∈ I, IsCausalVec g (γ τ) (vel γ τ))

/-- An *inextendible* causal curve: a causal curve defined on the whole of `ℝ`
which, at both ends, eventually leaves every compact subset of `U`.  The escape
condition is what rules out curves that are merely reparametrised to have an
infinite parameter range while staying in a compact piece of `U`. -/
def IsInextendibleCausalCurve (U : Set Coords) (g : MetricField) (γ : ℝ → Coords) : Prop :=
  IsCausalCurveOn U g univ γ ∧
    ∀ K : Set Coords, K ⊆ U → IsCompact K → ∃ T : ℝ, ∀ τ : ℝ, T ≤ |τ| → γ τ ∉ K

/-- `Sig` is a Cauchy hypersurface of `(U, g)` when every inextendible causal
curve meets `Sig` exactly once. -/
def IsCauchyHypersurface (U : Set Coords) (g : MetricField) (Sig : Set Coords) : Prop :=
  Sig ⊆ U ∧ ∀ γ : ℝ → Coords, IsInextendibleCausalCurve U g γ → ∃! τ : ℝ, γ τ ∈ Sig

/-- `(U, g)` is globally hyperbolic when it admits a Cauchy hypersurface. -/
def IsGloballyHyperbolic (U : Set Coords) (g : MetricField) : Prop :=
  ∃ Sig : Set Coords, IsCauchyHypersurface U g Sig

/-- `(U, g)` is time-oriented when it carries a continuous timelike vector field. -/
def IsTimeOriented (U : Set Coords) (g : MetricField) : Prop :=
  ∃ X : Coords → Coords, ContinuousOn X U ∧ ∀ x ∈ U, IsTimelikeVec g x (X x)

/-! ## Extendibility -/

/-- The Jacobian matrix of a coordinate map, `(∂ Jᵃ / ∂ x^b)`. -/
noncomputable def jac (J : Coords → Coords) (x : Coords) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun a b => pd b (fun y => J y a) x

/-- `(V, h, J)` is a `C⁰` extension of `(U, g)`: `h` is a *continuous* Lorentzian
metric on the open set `V`, `J : U → V` is an injective immersion which is an
isometry onto its image, and the image is proper in the strong sense that it has
nonempty boundary inside `V`.  This is the coordinate rendering of the proper
isometric embedding `J : M → M̄` discussed in Section 2.3 of the source, and it
is the notion behind Statement I (`C⁰` Strong Cosmic Censorship). -/
structure IsC0Extension (U : Set Coords) (g : MetricField)
    (V : Set Coords) (h : MetricField) (J : Coords → Coords) : Prop where
  isOpen : IsOpen V
  continuous : ∀ a b : Fin 4, ContinuousOn (fun x => h x a b) V
  lorentzian : ∀ x ∈ V, IsLorentzianMatrix (h x)
  mapsTo : MapsTo J U V
  injOn : InjOn J U
  diff : ContDiffOn ℝ 1 J U
  immersion : ∀ x ∈ U, IsUnit (jac J x).det
  isometry : ∀ x ∈ U, g x = (jac J x).transpose * h (J x) * jac J x
  proper : (V ∩ frontier (J '' U)).Nonempty

/-- Statement I of Section 2.3: `(U, g)` admits no `C⁰` extension. -/
def IsC0Inextendible (U : Set Coords) (g : MetricField) : Prop :=
  ∀ (V : Set Coords) (h : MetricField) (J : Coords → Coords), ¬ IsC0Extension U g V h J

/-- `(V, h, J)` is a `C²` extension of `(U, g)`: as `IsC0Extension`, but the
extending metric is required to be twice continuously differentiable. -/
structure IsC2Extension (U : Set Coords) (g : MetricField)
    (V : Set Coords) (h : MetricField) (J : Coords → Coords) : Prop
    extends IsC0Extension U g V h J where
  smooth : ∀ a b : Fin 4, ContDiffOn ℝ 2 (fun x => h x a b) V

/-- Statement III of Section 2.3: `(U, g)` admits no `C²` extension. -/
def IsC2Inextendible (U : Set Coords) (g : MetricField) : Prop :=
  ∀ (V : Set Coords) (h : MetricField) (J : Coords → Coords), ¬ IsC2Extension U g V h J

/-! ## Explicit spacetimes

Coordinates are `x = (t, r, θ, φ)` for the spherically symmetric metrics, and
`x = (t, x¹, x², x³)` for Minkowski and Kasner. -/

/-- Minkowski spacetime, equation (3.1) of the source. -/
def minkowski : MetricField := fun _ => minkowskiMatrix

/-- The Schwarzschild lapse `1 - 2M/r`. -/
noncomputable def schwarzschildLapse (M : ℝ) (r : ℝ) : ℝ := 1 - 2 * M / r

/-- The Schwarzschild metric, equation (3.2) of the source:
`-(1 - 2M/r) dt² + (1 - 2M/r)⁻¹ dr² + r² (dθ² + sin²θ dφ²)`. -/
noncomputable def schwarzschild (M : ℝ) : MetricField := fun x =>
  Matrix.diagonal ![-(schwarzschildLapse M (x 1)), (schwarzschildLapse M (x 1))⁻¹,
    (x 1) ^ 2, (x 1) ^ 2 * Real.sin (x 2) ^ 2]

/-- The Schwarzschild exterior region `{r > 2M}`, with the angular coordinate
restricted to the chart `0 < θ < π`. -/
def schwarzschildExterior (M : ℝ) : Set Coords :=
  {x | 2 * M < x 1 ∧ 0 < x 2 ∧ x 2 < Real.pi}

/-- The Schwarzschild black hole interior `{0 < r < 2M}`. -/
def schwarzschildInterior (M : ℝ) : Set Coords :=
  {x | 0 < x 1 ∧ x 1 < 2 * M ∧ 0 < x 2 ∧ x 2 < Real.pi}

/-- The Reissner–Nordström lapse `1 - 2M/r + e²/r²`, Section 3.3 of the source. -/
noncomputable def rnLapse (M e : ℝ) (r : ℝ) : ℝ := 1 - 2 * M / r + e ^ 2 / r ^ 2

/-- The Reissner–Nordström metric. -/
noncomputable def reissnerNordstrom (M e : ℝ) : MetricField := fun x =>
  Matrix.diagonal ![-(rnLapse M e (x 1)), (rnLapse M e (x 1))⁻¹,
    (x 1) ^ 2, (x 1) ^ 2 * Real.sin (x 2) ^ 2]

/-- The outer (event) horizon radius `r₊ = M + √(M² - e²)`. -/
noncomputable def rnOuterRadius (M e : ℝ) : ℝ := M + Real.sqrt (M ^ 2 - e ^ 2)

/-- The inner (Cauchy) horizon radius `r₋ = M - √(M² - e²)`. -/
noncomputable def rnInnerRadius (M e : ℝ) : ℝ := M - Real.sqrt (M ^ 2 - e ^ 2)

/-- The Kasner metric `-dt² + t^{2p₁} (dx¹)² + t^{2p₂} (dx²)² + t^{2p₃} (dx³)²`,
Section 4 of the source. -/
noncomputable def kasner (p : Fin 3 → ℝ) : MetricField := fun x =>
  Matrix.diagonal ![-1, Real.rpow (x 0) (2 * p 0), Real.rpow (x 0) (2 * p 1),
    Real.rpow (x 0) (2 * p 2)]

/-- The Kasner region `{t > 0}`. -/
def kasnerRegion : Set Coords := {x | 0 < x 0}

/-- The Kasner relations `p₁ + p₂ + p₃ = 1` and `p₁² + p₂² + p₃² = 1`. -/
def KasnerRelations (p : Fin 3 → ℝ) : Prop :=
  (∑ i : Fin 3, p i) = 1 ∧ (∑ i : Fin 3, (p i) ^ 2) = 1

end StrongCosmicCensorship


