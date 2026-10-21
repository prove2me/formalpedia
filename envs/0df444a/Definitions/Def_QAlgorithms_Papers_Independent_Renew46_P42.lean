-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42
-- name    : QAlgorithms_Papers_Independent_Renew46_P42
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T21:20:39.791058+00:00
-- url     : https://prove2.me/theorems/6efcfb6d-c0ff-4c85-8623-a909f8163194
-- title:
--   Definitions for Optics of Nonuniformly Moving Media
-- statement:
--   The objects the formalized statements of *Optics of Nonuniformly Moving Media* (arXiv:physics/9906038) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `V3`
--   - `V4`
--   - `M4`
--   - `dot3`: PDF p.3: Euclidean spatial scalar product.
--   - `length3`: PDF p.3: spatial wave number or speed, not the coordinate-space Pi norm.
--   - `cross3`: PDF p.3: Euclidean cross product with right-handed Cartesian orientation.
--   - `cartesianPartial`: Cartesian coordinate adapter for the pinned accepted Euclidean partial derivative. The conversions preserve every component and basis direction.
--   - `gradient`: Coordinate gradient; the spatial components are Euclidean gradient components.
--   - `curl3`: PDF p.3, (15): curl of a stationary Cartesian flow.
--   - `FirstJetEq`: Equality through first order at zero, including actual differentiability.
--   - `lorentzFactor`: PDF p.4, (22): defined algebraically; every use assumes subluminal flow.
--   - `fourFlow`: PDF p.4, (21): contravariant four-flow.
--   - `minkowskiMetric`: PDF p.4, (32): Minkowski metric of signature +---.
--   - `apply4`: Matrix acting on a covector or vector in fixed Cartesian coordinates.
--   - `gUp`: PDF p.4, (31): contravariant Gordon metric.
--   - `gDown`: PDF p.5, (42): covariant Gordon metric, using eta-lowered four-flow.
--   - `lorentzBoost`: PDF p.4: laboratory coordinates from a local rest frame; identity at zero flow.
--   - `waveCovector`: PDF p.4, (29): covariant wave momentum, including the spatial minus sign.
--   - `spatial`: Spatial projection of a contravariant four-vector.
--   - `rayDispersion`: PDF p.5, (33): dispersion polynomial, without division by c squared.
--   - `rayHamiltonian`: PDF p.5, (34): the constructed positive-comoving-frequency branch.
--   - `rayVelocity`: PDF p.3, (10): first Hamilton equation in laboratory time.
--   - `comovingVelocity`: PDF p.5, (35): continuous identity value is used when u = 0.
--   - `directionalH`: PDF p.5, (37): the directional factor h(zeta) in H = |k| h.
--   - `modifiedVelocity`: PDF p.3, (12): modified ray vector for the exact Hamiltonian family.
--   - `stationaryField`: PDF p.3, (10): Hamiltonian vector field for a stationary uniform-index medium.
--   - `alongField`: Derivative along the actual Hamiltonian vector field, not an assumed force law.
--   - `slowDown`: PDF p.6, (59): retained first-order covariant metric.
--   - `slowUp`: PDF p.6, (60): retained first-order contravariant metric.
--   - `OpticalPatch`: PDF pp.5–6: local optical data in inertial Cartesian spacetime coordinates.
--   - `patchDown`: Local covariant metric constructed from the optical patch.
--   - `patchUp`: Local contravariant metric constructed from the same optical patch.
--   - `christoffel`: Levi-Civita connection computed from metric derivatives, not from ray equations.
--   - `covAcceleration`: Covariant acceleration for a Cartesian-coordinate curve.
--   - `scalarCurvature`: PDF p.6, [31] convention: Ricci contraction of R^a_bcd = partial_c Gamma^a_bd - partial_d Gamma^a_bc + Gamma^a_ec Gamma^e_bd - Gamma^a_ed Gamma^e_bc. This definition uses the connection itself, never the asserted optical formula.
--   - `divergence4`: PDF p.6, (53): Cartesian four-divergence.
--   - `curvatureA`: PDF p.6, first contraction in (52), with the last flow index eta-lowered.
--   - `curvatureB`: PDF p.6, second contraction in (52).
--   - `curvatureC`: PDF p.6, divergence terms in (52).
--   - `endpointAction`: PDF p.6: optical proper-length action on a smooth endpoint congruence.
--   - `massiveLagrangian`: PDF p.6, (49): artificial-mass Lagrangian in laboratory time.
--   - `massiveCovector`: PDF p.5, (46): massive covector computed from a future timelike tangent.
--   - `azimuth`: PDF p.7, (62): cylindrical unit vector in fixed Cartesian spatial coordinates.
--   - `slowVortexPolar`: PDF p.7, (62): nonrelativistic flow, retained as a first-order model.
--   - `axisRadius`: Distance from the z-axis in Cartesian spacetime coordinates.
--   - `vortexGamma`: PDF p.8, (67): relativistic circular-flow Lorentz factor on r > 0.
--   - `vortexSpeed`: PDF p.8, (66): constructed subluminal circular speed.
--   - `circularFlow`: PDF p.8, (65): general stationary axisymmetric circular Cartesian flow.
--   - `vortexFlow`: PDF p.8, (68): spatial Cartesian flow outside the excluded vortex axis.
--   - `vortexFour`: PDF p.8, (68): explicit Cartesian four-flow, retaining the spatial 1/c.
--   - `vortexPressure`: PDF p.8, (70): negative pressure with constant positive rest mass density.
--   - `vortexStress`: PDF p.8, (69): constructed perfect-fluid stress tensor.
--   - `vortexPhase`: PDF p.7, (64): phase as the positive single-circuit magnetic line integral.
--   - `radialF`: PDF p.8, (77): radial eikonal square for any circular speed profile.
--   - `cylindricalSymbol`: PDF p.8, (75): cylindrical eikonal symbol; coordinates z = (t,r,phi).
--   - `separatedPhase`: PDF p.8, (76): separated phase for a specified radial function.
--   - `circularEikonal`: PDF p.8, (76)–(77): actual radial quadrature, not an unrelated assumed solution.
--   - `angularAB`: PDF p.9, (79): shifted angular momentum.
--   - `farRadial`: PDF p.9, (78): retained inverse-radius model, not the full radial symbol.
--   - `farTurningRadius`: PDF p.9, (82): positive square root is used only under a strict radicand guard.
--   - `farAngle`: PDF p.9, (83): signed outgoing trajectory of the retained radial model.
--   - `turningBranch`: PDF p.10, (90): s = 1 or -1; the minus chart excludes n*u = c.
--   - `criticalCubic`: PDF p.10, (94): cubic in the dimensionless critical speed.
--   - `criticalBeta`: PDF p.10, (95): angle of the three-real-root Cardano formula.
--   - `criticalSpeed`: PDF p.10, (95): indices 0,1,2 represent the paper's branches 1,2,3.
--   - `criticalRadius`: PDF p.11, (98): critical turning circle; no global capture predicate.
--   - `scaledEikonal`: PDF pp.11–12, (100): coordinate pullback, with the phase scaling included.
-- source:
--   Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, https://arxiv.org/abs/physics/9906038v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P20
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

/-!
Statements from Leonhardt and Piwnicki, arXiv:physics/9906038v3.
These are classical, nondispersive, geometrical-optics statements. Optical data
are the local principal-symbol data after neglecting derivatives on the optical
wavelength/cycle scale; no quantitative Maxwell approximation is asserted.
Coordinates are x^0 = ct and three Cartesian spatial coordinates. Finite real
coordinate spaces use their usual finite-dimensional calculus; spatial length
is explicitly the Euclidean length, independently of the ambient Pi norm.
-/

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators
open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).
open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

abbrev V3 := Fin 3 → ℝ

abbrev V4 := Fin 4 → ℝ

abbrev M4 := Matrix (Fin 4) (Fin 4) ℝ

/-- PDF p.3: Euclidean spatial scalar product. -/
def dot3 (v w : V3) : ℝ := ∑ i, v i * w i

/-- PDF p.3: spatial wave number or speed, not the coordinate-space Pi norm. -/
def length3 (v : V3) : ℝ := Real.sqrt (dot3 v v)

/-- PDF p.3: Euclidean cross product with right-handed Cartesian orientation. -/
def cross3 (v w : V3) : V3 :=
  ![v 1 * w 2 - v 2 * w 1, v 2 * w 0 - v 0 * w 2,
    v 0 * w 1 - v 1 * w 0]

/-- Cartesian coordinate adapter for the pinned accepted Euclidean partial
 derivative. The conversions preserve every component and basis direction. -/
def cartesianPartial {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (i : Fin d) : ℝ :=
  QAlgorithms.Papers.Independent.Dependency50.P20.coordinatePartial i
    (fun y => f (WithLp.ofLp y)) (WithLp.toLp 2 x)

example {d : ℕ} (x : Fin d → ℝ) (i : Fin d) (a : ℝ) :
    cartesianPartial (fun _ => a) x i = 0 := by
  simp [cartesianPartial, QAlgorithms.Papers.Independent.Dependency50.P20.coordinatePartial]

/-- Coordinate gradient; the spatial components are Euclidean gradient components. -/
def gradient {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => cartesianPartial f x i

/-- PDF p.3, (15): curl of a stationary Cartesian flow. -/
def curl3 (u : V3 → V3) (x : V3) : V3 :=
  ![cartesianPartial (fun y => u y 2) x 1 - cartesianPartial (fun y => u y 1) x 2,
    cartesianPartial (fun y => u y 0) x 2 - cartesianPartial (fun y => u y 2) x 0,
    cartesianPartial (fun y => u y 1) x 0 - cartesianPartial (fun y => u y 0) x 1]

/-- Equality through first order at zero, including actual differentiability. -/
def FirstJetEq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : ℝ → E) : Prop :=
  f 0 = g 0 ∧ ∃ a : E, HasDerivAt f a 0 ∧ HasDerivAt g a 0

/-- PDF p.4, (22): defined algebraically; every use assumes subluminal flow. -/
def lorentzFactor (c : ℝ) (u : V3) : ℝ :=
  1 / Real.sqrt (1 - dot3 u u / c ^ 2)

/-- PDF p.4, (21): contravariant four-flow. -/
def fourFlow (c : ℝ) (u : V3) : V4 :=
  ![lorentzFactor c u, lorentzFactor c u * u 0 / c, lorentzFactor c u * u 1 / c,
    lorentzFactor c u * u 2 / c]

/-- PDF p.4, (32): Minkowski metric of signature +---. -/
def minkowskiMetric : M4 := fun i j => if i = j then (if hi : i = 0 then 1 else -1) else 0

/-- Matrix acting on a covector or vector in fixed Cartesian coordinates. -/
def apply4 (A : M4) (p : V4) : V4 := fun i => ∑ j, A i j * p j

/-- PDF p.4, (31): contravariant Gordon metric. -/
def gUp (c n : ℝ) (u : V3) : M4 :=
  fun i j => minkowskiMetric i j + (n ^ 2 - 1) * fourFlow c u i * fourFlow c u j

/-- PDF p.5, (42): covariant Gordon metric, using eta-lowered four-flow. -/
def gDown (c n : ℝ) (u : V3) : M4 :=
  fun i j => minkowskiMetric i j + (1 / n ^ 2 - 1) *
    apply4 minkowskiMetric (fourFlow c u) i * apply4 minkowskiMetric (fourFlow c u) j

/-- PDF p.4: laboratory coordinates from a local rest frame; identity at zero flow. -/
def lorentzBoost (c : ℝ) (u : V3) : M4 :=
  if u = 0 then 1 else
    fun i j =>
      if hi : i = 0 then (if hj : j = 0 then lorentzFactor c u else lorentzFactor c u * u (j.pred (by omega)) / c)
      else if hj : j = 0 then lorentzFactor c u * u (i.pred (by omega)) / c
      else (if i = j then 1 else 0) + (lorentzFactor c u - 1) *
        u (i.pred (by omega)) * u (j.pred (by omega)) / dot3 u u

/-- PDF p.4, (29): covariant wave momentum, including the spatial minus sign. -/
def waveCovector (c omega : ℝ) (k : V3) : V4 := ![omega / c, -k 0, -k 1, -k 2]

/-- Spatial projection of a contravariant four-vector. -/
def spatial (p : V4) : V3 := ![p 1, p 2, p 3]

/-- PDF p.5, (33): dispersion polynomial, without division by c squared. -/
def rayDispersion (c n : ℝ) (u k : V3) (omega : ℝ) : ℝ :=
  omega ^ 2 - c ^ 2 * dot3 k k +
    (n ^ 2 - 1) * (lorentzFactor c u) ^ 2 * (omega - dot3 u k) ^ 2

/-- PDF p.5, (34): the constructed positive-comoving-frequency branch. -/
def rayHamiltonian (c n : ℝ) (u k : V3) : ℝ :=
  Real.sqrt ((c ^ 2 - dot3 u u) / (n ^ 2 * c ^ 2 - dot3 u u)) *
    Real.sqrt (c ^ 2 * dot3 k k -
      ((n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u)) * (dot3 u k) ^ 2) +
    ((n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u)) * dot3 u k

/-- PDF p.3, (10): first Hamilton equation in laboratory time. -/
def rayVelocity (c n : ℝ) (u k : V3) : V3 :=
  gradient (rayHamiltonian c n u) k

/-- PDF p.5, (35): continuous identity value is used when u = 0. -/
def comovingVelocity (c : ℝ) (u v : V3) : V3 :=
  if u = 0 then v else
    (1 / (lorentzFactor c u * (1 - dot3 u v / c ^ 2))) •
      (v - u + (((lorentzFactor c u - 1) * (dot3 u v - dot3 u u) / dot3 u u)) • u)

/-- PDF p.5, (37): the directional factor h(zeta) in H = |k| h. -/
def directionalH (c n : ℝ) (u : V3) (zeta : ℝ) : ℝ :=
  Real.sqrt ((c ^ 2 - dot3 u u) / (n ^ 2 * c ^ 2 - dot3 u u)) *
    Real.sqrt (c ^ 2 - ((n ^ 2 * c ^ 2 - c ^ 2) /
      (n ^ 2 * c ^ 2 - dot3 u u)) * zeta ^ 2) +
    ((n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u)) * zeta

/-- PDF p.3, (12): modified ray vector for the exact Hamiltonian family. -/
def modifiedVelocity (c n : ℝ) (u k : V3) : V3 :=
  length3 k • rayVelocity c n u k

/-- PDF p.3, (10): Hamiltonian vector field for a stationary uniform-index medium. -/
def stationaryField (c n eps : ℝ) (u : V3 → V3) (z : V3 × V3) : V3 × V3 :=
  (rayVelocity c n (eps • u z.1) z.2,
    -gradient (fun x => rayHamiltonian c n (eps • u x) z.2) z.1)

/-- Derivative along the actual Hamiltonian vector field, not an assumed force law. -/
def alongField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c n eps : ℝ) (u : V3 → V3) (f : V3 × V3 → E) (z : V3 × V3) : E :=
  fderiv ℝ f z (stationaryField c n eps u z)

/-- PDF p.6, (59): retained first-order covariant metric. -/
def slowDown (c n : ℝ) (u : V3) : M4 :=
  fun i j => if hi : i = 0 then
    (if hj : j = 0 then 1 / n ^ 2 else (n ^ 2 - 1) / (n ^ 2 * c) * u (j.pred (by omega)))
  else if hj : j = 0 then (n ^ 2 - 1) / (n ^ 2 * c) * u (i.pred (by omega))
  else minkowskiMetric i j

/-- PDF p.6, (60): retained first-order contravariant metric. -/
def slowUp (c n : ℝ) (u : V3) : M4 :=
  fun i j => if hi : i = 0 then
    (if hj : j = 0 then n ^ 2 else (n ^ 2 - 1) / c * u (j.pred (by omega)))
  else if hj : j = 0 then (n ^ 2 - 1) / c * u (i.pred (by omega))
  else minkowskiMetric i j

/-- PDF pp.5–6: local optical data in inertial Cartesian spacetime coordinates. -/
structure OpticalPatch (c : ℝ) where
  domain : Set V4
  isOpen : IsOpen domain
  index : V4 → ℝ
  flow : V4 → V3
  indexRegular : ContDiffOn ℝ 2 index domain
  flowRegular : ContDiffOn ℝ 2 flow domain
  indexBound : ∀ x ∈ domain, 1 ≤ index x
  flowBound : ∀ x ∈ domain, dot3 (flow x) (flow x) < c ^ 2

/-- Local covariant metric constructed from the optical patch. -/
def patchDown {c : ℝ} (P : OpticalPatch c) (x : V4) : M4 :=
  gDown c (P.index x) (P.flow x)

/-- Local contravariant metric constructed from the same optical patch. -/
def patchUp {c : ℝ} (P : OpticalPatch c) (x : V4) : M4 :=
  gUp c (P.index x) (P.flow x)

/-- Levi-Civita connection computed from metric derivatives, not from ray equations. -/
def christoffel (g gi : V4 → M4) (x : V4) (a b d : Fin 4) : ℝ :=
  (1 / 2) * ∑ e, gi x a e *
    (cartesianPartial (fun y => g y e d) x b + cartesianPartial (fun y => g y e b) x d -
      cartesianPartial (fun y => g y b d) x e)

/-- Covariant acceleration for a Cartesian-coordinate curve. -/
def covAcceleration (g gi : V4 → M4) (q : ℝ → V4) (s : ℝ) : V4 :=
  fun a => deriv (fun t => deriv q t a) s +
    ∑ b, ∑ d, christoffel g gi (q s) a b d * deriv q s b * deriv q s d

/-- PDF p.6, [31] convention: Ricci contraction of
R^a_bcd = partial_c Gamma^a_bd - partial_d Gamma^a_bc
          + Gamma^a_ec Gamma^e_bd - Gamma^a_ed Gamma^e_bc.
This definition uses the connection itself, never the asserted optical formula. -/
def scalarCurvature (g gi : V4 → M4) (x : V4) : ℝ :=
  ∑ b, ∑ d, gi x b d * ∑ a,
    (cartesianPartial (fun y => christoffel g gi y a b d) x a -
      cartesianPartial (fun y => christoffel g gi y a b a) x d +
      ∑ e, (christoffel g gi x a e a * christoffel g gi x e b d -
        christoffel g gi x a e d * christoffel g gi x e b a))

/-- PDF p.6, (53): Cartesian four-divergence. -/
def divergence4 (U : V4 → V4) (x : V4) : ℝ := ∑ i, cartesianPartial (fun y => U y i) x i

/-- PDF p.6, first contraction in (52), with the last flow index eta-lowered. -/
def curvatureA (n : ℝ) (U : V4 → V4) (x : V4) : ℝ :=
  ((n ^ 2 - 1) ^ 2 / (2 * n ^ 2)) * ∑ i, ∑ j, ∑ a,
    (U x i * U x j - minkowskiMetric i j) * cartesianPartial (fun y => U y a) x i *
      cartesianPartial (fun y => apply4 minkowskiMetric (U y) a) x j

/-- PDF p.6, second contraction in (52). -/
def curvatureB (n : ℝ) (U : V4 → V4) (x : V4) : ℝ :=
  ((1 - n ^ 4) / (2 * n ^ 2)) * ∑ i, ∑ j,
    cartesianPartial (fun y => U y j) x i * cartesianPartial (fun y => U y i) x j

/-- PDF p.6, divergence terms in (52). -/
def curvatureC (n : ℝ) (U : V4 → V4) (x : V4) : ℝ :=
  (1 - n ^ 2) * (2 * (∑ i, U x i * cartesianPartial (divergence4 U) x i) +
    (divergence4 U x) ^ 2)

/-- PDF p.6: optical proper-length action on a smooth endpoint congruence. -/
def endpointAction {c : ℝ} (P : OpticalPatch c) (m : ℝ)
    (q : ℝ → V4 → V4) (z : V4) : ℝ :=
  -m * c * ∫ s in (0 : ℝ)..1,
    Real.sqrt (quadratic (patchDown P (q s z)) (deriv (fun t => q t z) s))

/-- PDF p.6, (49): artificial-mass Lagrangian in laboratory time. -/
def massiveLagrangian (c n m : ℝ) (u v : V3) : ℝ :=
  -m * c * Real.sqrt (c ^ 2 - dot3 v v +
    (1 / n ^ 2 - 1) * (lorentzFactor c u) ^ 2 * (c - dot3 u v / c) ^ 2)

/-- PDF p.5, (46): massive covector computed from a future timelike tangent. -/
def massiveCovector (c m : ℝ) (g : M4) (v : V4) : V4 :=
  (m * c / Real.sqrt (quadratic g v)) • apply4 g v

/-- PDF p.7, (62): cylindrical unit vector in fixed Cartesian spatial coordinates. -/
def azimuth (phi : ℝ) : V3 := ![-Real.sin phi, Real.cos phi, 0]

/-- PDF p.7, (62): nonrelativistic flow, retained as a first-order model. -/
def slowVortexPolar (W r phi : ℝ) : V3 := (W / r) • azimuth phi

/-- Distance from the z-axis in Cartesian spacetime coordinates. -/
def axisRadius (x : V4) : ℝ := Real.sqrt (x 1 ^ 2 + x 2 ^ 2)

/-- PDF p.8, (67): relativistic circular-flow Lorentz factor on r > 0. -/
def vortexGamma (c W r : ℝ) : ℝ := Real.sqrt (1 + W ^ 2 / (c ^ 2 * r ^ 2))

/-- PDF p.8, (66): constructed subluminal circular speed. -/
def vortexSpeed (c W r : ℝ) : ℝ := W / (vortexGamma c W r * r)

/-- PDF p.8, (65): general stationary axisymmetric circular Cartesian flow. -/
def circularFlow (u : ℝ → ℝ) (x : V4) : V3 :=
  (u (axisRadius x) / axisRadius x) • ![-x 2, x 1, 0]

/-- PDF p.8, (68): spatial Cartesian flow outside the excluded vortex axis. -/
def vortexFlow (c W : ℝ) (x : V4) : V3 :=
  (vortexSpeed c W (axisRadius x) / axisRadius x) • ![-x 2, x 1, 0]

/-- PDF p.8, (68): explicit Cartesian four-flow, retaining the spatial 1/c. -/
def vortexFour (c W : ℝ) (x : V4) : V4 :=
  ![vortexGamma c W (axisRadius x), -W * x 2 / (c * axisRadius x ^ 2),
    W * x 1 / (c * axisRadius x ^ 2), 0]

/-- PDF p.8, (70): negative pressure with constant positive rest mass density. -/
def vortexPressure (c W rho r : ℝ) : ℝ :=
  rho * c ^ 2 * Real.exp (-W ^ 2 / (2 * c ^ 2 * r ^ 2)) - rho * c ^ 2

/-- PDF p.8, (69): constructed perfect-fluid stress tensor. -/
def vortexStress (c W rho : ℝ) (x : V4) : M4 :=
  fun i j => (rho * c ^ 2 + vortexPressure c W rho (axisRadius x)) *
    vortexFour c W x i * vortexFour c W x j -
      vortexPressure c W rho (axisRadius x) * minkowskiMetric i j

/-- PDF p.7, (64): phase as the positive single-circuit magnetic line integral. -/
def vortexPhase (c n omega W r : ℝ) : ℝ :=
  ((n ^ 2 - 1) * omega / c ^ 2) * ∫ phi in (0 : ℝ)..(2 * Real.pi),
    dot3 (slowVortexPolar W r phi) (r • azimuth phi)

/-- PDF p.8, (77): radial eikonal square for any circular speed profile. -/
def radialF (c n : ℝ) (u : ℝ → ℝ) (r l : ℝ) : ℝ :=
  1 - l ^ 2 / r ^ 2 + (n ^ 2 - 1) / (1 - (u r) ^ 2 / c ^ 2) *
    (1 - u r * l / (c * r)) ^ 2

/-- PDF p.8, (75): cylindrical eikonal symbol; coordinates z = (t,r,phi). -/
def cylindricalSymbol (c n : ℝ) (u : ℝ → ℝ) (S : V3 → ℝ) (z : V3) : ℝ :=
  (cartesianPartial S z 0) ^ 2 - c ^ 2 * ((cartesianPartial S z 1) ^ 2 + (cartesianPartial S z 2 / z 1) ^ 2) +
    (n ^ 2 - 1) / (1 - (u (z 1)) ^ 2 / c ^ 2) *
      (cartesianPartial S z 0 + u (z 1) / z 1 * cartesianPartial S z 2) ^ 2

/-- PDF p.8, (76): separated phase for a specified radial function. -/
def separatedPhase (c omega l : ℝ) (R : ℝ → ℝ) (z : V3) : ℝ :=
  omega / c * (-c * z 0 + l * z 2 + R (z 1))

/-- PDF p.8, (76)–(77): actual radial quadrature, not an unrelated assumed solution. -/
def circularEikonal (c n omega l sigma rBase : ℝ) (u : ℝ → ℝ) (z : V3) : ℝ :=
  omega / c * (-c * z 0 + l * z 2 +
    sigma * ∫ s in rBase..(z 1), Real.sqrt (radialF c n u s l))

/-- PDF p.9, (79): shifted angular momentum. -/
def angularAB (c n W l : ℝ) : ℝ := l + (n ^ 2 - 1) * W / c

/-- PDF p.9, (78): retained inverse-radius model, not the full radial symbol. -/
def farRadial (c n W l r : ℝ) : ℝ :=
  n ^ 2 - (angularAB c n W l) ^ 2 / r ^ 2 +
    (n ^ 2 - 1) * n ^ 2 * W ^ 2 / (c ^ 2 * r ^ 2)

/-- PDF p.9, (82): positive square root is used only under a strict radicand guard. -/
def farTurningRadius (c n W l : ℝ) : ℝ :=
  Real.sqrt ((angularAB c n W l) ^ 2 / n ^ 2 - (n ^ 2 - 1) * W ^ 2 / c ^ 2)

/-- PDF p.9, (83): signed outgoing trajectory of the retained radial model. -/
def farAngle (c n W l phiBase r : ℝ) : ℝ :=
  phiBase + angularAB c n W l / (n * farTurningRadius c n W l) *
    Real.arccos (farTurningRadius c n W l / r)

/-- PDF p.10, (90): s = 1 or -1; the minus chart excludes n*u = c. -/
def turningBranch (c n : ℝ) (u : ℝ → ℝ) (s r : ℝ) : ℝ :=
  r * (n * c + s * u r) / (n * u r + s * c)

/-- PDF p.10, (94): cubic in the dimensionless critical speed. -/
def criticalCubic (n xi : ℝ) : ℝ :=
  (n ^ 2 - 1) * xi ^ 3 + n * xi ^ 2 - 2 * n ^ 2 * xi + n

/-- PDF p.10, (95): angle of the three-real-root Cardano formula. -/
def criticalBeta (n : ℝ) : ℝ :=
  Real.arccos (-(27 - 70 * n ^ 2 + 45 * n ^ 4) /
    (2 * n ^ 2 * (6 * n ^ 2 - 5) * Real.sqrt (6 * n ^ 2 - 5)))

/-- PDF p.10, (95): indices 0,1,2 represent the paper's branches 1,2,3. -/
def criticalSpeed (c n : ℝ) (i : Fin 3) : ℝ :=
  (2 * n * c * Real.sqrt (6 * n ^ 2 - 5) *
    Real.cos ((2 * Real.pi * (i.val : ℝ) + criticalBeta n) / 3) - n * c) /
      (3 * (n ^ 2 - 1))

/-- PDF p.11, (98): critical turning circle; no global capture predicate. -/
def criticalRadius (c W n : ℝ) : ℝ :=
  W / criticalSpeed c n 2 * Real.sqrt (1 - (criticalSpeed c n 2) ^ 2 / c ^ 2)

/-- PDF pp.11–12, (100): coordinate pullback, with the phase scaling included. -/
def scaledEikonal (c W : ℝ) (S : V3 → ℝ) (z : V3) : ℝ :=
  c / W * S ![W / c ^ 2 * z 0, W / c * z 1, z 2]

example : minkowskiMetric 0 0 = 1 ∧ minkowskiMetric 1 1 = -1 := by norm_num [minkowskiMetric]

example (c : ℝ) : lorentzBoost c 0 = 1 := by simp [lorentzBoost]

example (c : ℝ) (v : V3) : comovingVelocity c 0 v = v := by simp [comovingVelocity]

example (n : ℝ) : criticalCubic n 0 = n := by simp [criticalCubic]

example (c n : ℝ) (u : ℝ → ℝ) (r : ℝ) :
    turningBranch c n u 1 r = r * (n * c + u r) / (n * u r + c) := by
  simp [turningBranch]

example (c : ℝ) (u : V3) : gUp c 1 u = minkowskiMetric := by
  ext i j
  simp [gUp]

example (c : ℝ) (u : V3) : gDown c 1 u = minkowskiMetric := by
  ext i j
  simp [gDown]

example (c W r : ℝ) : vortexPressure c W 0 r = 0 := by simp [vortexPressure]

example (c n omega W r : ℝ) : vortexPhase c 1 omega W r = 0 := by
  simp [vortexPhase]

example (c n : ℝ) (u : ℝ → ℝ) (r l : ℝ) :
    radialF c 1 u r l = 1 - l ^ 2 / r ^ 2 := by simp [radialF]

example (c W l : ℝ) : angularAB c 1 W l = l := by simp [angularAB]

example (c n : ℝ) (u v : V3) : massiveLagrangian c n 0 u v = 0 := by
  simp [massiveLagrangian]

example (x : V4) (a b d : Fin 4) :
    christoffel (fun _ => minkowskiMetric) (fun _ => minkowskiMetric) x a b d = 0 := by
  simp [christoffel, cartesianPartial,
    QAlgorithms.Papers.Independent.Dependency50.P20.coordinatePartial]

end

end QAlgorithms.Papers.Independent.Renew46.P42


