-- Prove2me | Definitions.Def_WheelerDeWittSuperspace
-- name    : WheelerDeWittSuperspace
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-05T21:09:38.098344+00:00
-- url     : https://prove2.me/theorems/730707d1-ef2c-4fc6-a874-cbba6fc54f86
-- title:
--   Lattice superspace and the Wheeler–DeWitt operator
-- statement:
--   Lattice model of the configuration space of quantum geometrodynamics. Space is a finite set $X$ of sites; a **configuration** $h$ assigns to every site $x$ the nine components $h_{ab}(x)$ of a spatial metric, all treated as independent real coordinates, and it is **physical** when every $h(x)$ is symmetric positive definite.
--
--   The module defines:
--
--   - the volume density $\sqrt{\det h}$;
--   - the DeWitt supermetric $G_{abcd}=(h_{ac}h_{bd}+h_{ad}h_{bc}-h_{ab}h_{cd})/(2\sqrt{\det h})$ and its inverse $G^{abcd}=\tfrac12\sqrt{\det h}\,(h^{ac}h^{bd}+h^{ad}h^{bc}-2h^{ab}h^{cd})$, the associated quadratic forms and index maps;
--   - the coordinate partial derivatives $\partial_{ab}(x)=\partial/\partial h_{ab}(x)$ as genuine Fréchet derivatives, of complex wavefunctions and of real functions;
--   - the kinetic term $\sum G_{abcd}\,\partial_{ab}\partial_{cd}\Psi$ with the supermetric on the left;
--   - the vacuum Wheeler–DeWitt operator $-2\kappa\hbar^2\,G\,\partial\partial\Psi-\tfrac{\sqrt{\det h}}{2\kappa}(R-2\Lambda)\Psi$ at each site, with a supplied potential $R$ (a lattice scalar curvature, allowed to couple sites);
--   - the Einstein–Hamilton–Jacobi functional;
--   - the classical lattice constraints $H_z=2\kappa\,G_{abcd}(h(z))\,p^{ab}(z)p^{cd}(z)+V_z(h)$ with $V_z=-\tfrac{\sqrt{\det h(z)}}{2\kappa}(R-2\Lambda)$, and the canonical Poisson bracket on $(h,p)$.
--
--   The cell volume is normalized to one. Coupling constants are named `kappa`, `hbar`, `Lam`.
-- source:
--   C. Kiefer, Quantum Geometrodynamics: whence, whither?, Gen. Relativ. Gravit. 41 (2009) 877-901, https://arxiv.org/abs/0812.0295; B. S. DeWitt, Quantum Theory of Gravity I. The Canonical Theory, Phys. Rev. 160 (1967) 1113-1148, https://doi.org/10.1103/PhysRev.160.1113

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

set_option autoImplicit false

namespace WheelerDeWittSuperspace

noncomputable section

open Matrix


/-- Components `h_ab` of a spatial metric at one point, as coordinates on `ℝ⁹`.
All nine entries are independent coordinates; physical metrics are the symmetric
positive-definite ones. -/
abbrev Metric3 := Fin 3 → Fin 3 → ℝ

/-- A configuration: the metric components at each of finitely many spatial sites
(a lattice regularization of a spatial three-geometry). -/
abbrev Config (X : Type*) := X → Metric3

/-- The metric at a site, as a matrix. -/
def metricAt {X : Type*} (h : Config X) (x : X) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of (h x)

/-- Physical configurations: the metric is symmetric positive definite at every site. -/
def IsPhysical {X : Type*} (h : Config X) : Prop :=
  ∀ x, (metricAt h x).PosDef

/-- Volume density `√h` of a matrix metric. -/
def volume (m : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := Real.sqrt m.det

/-- The DeWitt supermetric `G_abcd = (h_ac h_bd + h_ad h_bc - h_ab h_cd) / (2√h)`
(Kiefer, eq. (5)); it pairs two momenta `p^ab`, `p^cd`. -/
def deWitt (m : Matrix (Fin 3) (Fin 3) ℝ) (a b c d : Fin 3) : ℝ :=
  (m a c * m b d + m a d * m b c - m a b * m c d) / (2 * volume m)

/-- The inverse supermetric `G^abcd = √h (h^ac h^bd + h^ad h^bc - 2 h^ab h^cd) / 2`;
it pairs two velocities `k_ab`, `k_cd`. -/
def invDeWitt (m : Matrix (Fin 3) (Fin 3) ℝ) (a b c d : Fin 3) : ℝ :=
  volume m * (m⁻¹ a c * m⁻¹ b d + m⁻¹ a d * m⁻¹ b c - 2 * m⁻¹ a b * m⁻¹ c d) / 2

/-- `G(p,p) = Σ G_abcd p^ab p^cd` on momenta. -/
def superQuad (m p : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ d, deWitt m a b c d * p a b * p c d

/-- Index lowering by the supermetric: `(G p)_ab = Σ G_abcd p^cd`. -/
def superMap (m p : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun a b => ∑ c, ∑ d, deWitt m a b c d * p c d

/-- Index raising by the inverse supermetric: `(G⁻¹ k)^ab = Σ G^abcd k_cd`. -/
def invSuperMap (m k : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun a b => ∑ c, ∑ d, invDeWitt m a b c d * k c d

/-- The supermetric on velocities, `√h (k_ab k^ab - k²)`, written with traces. -/
def velocityQuad (m k : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  volume m * ((m⁻¹ * k * m⁻¹ * k).trace - (m⁻¹ * k).trace ^ 2)

/-- Coordinate direction of `h_ab(x)` in configuration space. -/
def coordDir {X : Type*} [DecidableEq X] (x : X) (a b : Fin 3) : Config X :=
  fun y i j => if y = x ∧ i = a ∧ j = b then 1 else 0

/-- Partial derivative `∂/∂h_ab(x)` of a complex wavefunction (a genuine Fréchet
derivative in a coordinate direction). -/
def partialD {X : Type*} [Fintype X] [DecidableEq X] (Ψ : Config X → ℂ) (x : X) (a b : Fin 3) :
    Config X → ℂ :=
  fun h => fderiv ℝ Ψ h (coordDir x a b)

/-- Partial derivative `∂/∂h_ab(x)` of a real function on configuration space. -/
def partialR {X : Type*} [Fintype X] [DecidableEq X] (S : Config X → ℝ) (x : X) (a b : Fin 3) :
    Config X → ℝ :=
  fun h => fderiv ℝ S h (coordDir x a b)

/-- Kinetic term with the supermetric to the left of both derivatives:
`Σ G_abcd(h(x)) ∂_ab(x) ∂_cd(x) Ψ`. -/
def kinetic {X : Type*} [Fintype X] [DecidableEq X] (Ψ : Config X → ℂ) (h : Config X) (x : X) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d,
    (deWitt (metricAt h x) a b c d : ℂ) * partialD (partialD Ψ x c d) x a b h

/-- The vacuum Wheeler–DeWitt operator at site `x` (Kiefer, eq. (7) with `ρ = 0`):
`-2kappahbar² G ∂∂Ψ - (2kappa)⁻¹ √h (R - 2Lam) Ψ`. The potential `R` is supplied data
(a lattice scalar curvature), allowed to depend on the whole configuration. -/
def wdw {X : Type*} [Fintype X] [DecidableEq X] (kappa hbar Lam : ℝ) (R : Config X → X → ℝ)
    (Ψ : Config X → ℂ) (h : Config X) (x : X) : ℂ :=
  -2 * (kappa : ℂ) * (hbar : ℂ) ^ 2 * kinetic Ψ h x -
    ((2 * kappa)⁻¹ * volume (metricAt h x) * (R h x - 2 * Lam) : ℝ) * Ψ h

/-- The Einstein–Hamilton–Jacobi functional: the classical Hamiltonian constraint
with momenta `p^ab = ∂S/∂h_ab`. -/
def hamiltonJacobi {X : Type*} [Fintype X] [DecidableEq X] (kappa Lam : ℝ) (R : Config X → X → ℝ)
    (S : Config X → ℝ) (h : Config X) (x : X) : ℝ :=
  2 * kappa * (∑ a, ∑ b, ∑ c, ∑ d,
      deWitt (metricAt h x) a b c d * partialR S x a b h * partialR S x c d h) -
    (2 * kappa)⁻¹ * volume (metricAt h x) * (R h x - 2 * Lam)


/-! ### Constraint algebra on the lattice -/

/-- The potential part of the constraint at site `z`: `-(2κ)⁻¹ √h(z) (R(h,z) - 2Λ)`.
It depends on the whole configuration as soon as `R` couples neighbouring sites. -/
def potentialAt {X : Type*} (kappa Lam : ℝ) (R : Config X → X → ℝ) (h : Config X) (z : X) : ℝ :=
  -(2 * kappa)⁻¹ * volume (metricAt h z) * (R h z - 2 * Lam)

/-- Classical phase space: metric components and conjugate momenta at every site. -/
abbrev Phase (X : Type*) := Config X × Config X

/-- The classical lattice Hamiltonian constraint at site `z`:
`2κ G_abcd(h(z)) p^ab(z) p^cd(z) + V_z(h)`. -/
def classicalConstraint {X : Type*} (kappa Lam : ℝ) (R : Config X → X → ℝ) (z : X)
    (w : Phase X) : ℝ :=
  2 * kappa * (∑ a, ∑ b, ∑ c, ∑ d,
      deWitt (metricAt w.1 z) a b c d * w.2 z a b * w.2 z c d) +
    potentialAt kappa Lam R w.1 z

/-- Canonical Poisson bracket on the lattice phase space,
`{F,G} = Σ_{z,a,b} (∂F/∂h_ab(z) ∂G/∂p^ab(z) - ∂F/∂p^ab(z) ∂G/∂h_ab(z))`. -/
def poisson {X : Type*} [Fintype X] [DecidableEq X] (F G : Phase X → ℝ) (w : Phase X) : ℝ :=
  ∑ z, ∑ a, ∑ b,
    (fderiv ℝ F w (coordDir z a b, 0) * fderiv ℝ G w (0, coordDir z a b) -
      fderiv ℝ F w (0, coordDir z a b) * fderiv ℝ G w (coordDir z a b, 0))

end

end WheelerDeWittSuperspace


