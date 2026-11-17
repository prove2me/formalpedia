-- Prove2me | Definitions.Def_N25_CanonicalChartJacobian
-- name    : N25_CanonicalChartJacobian
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:46.723194+00:00
-- url     : https://prove2.me/theorems/c47c7812-2141-4484-935c-07e16e57df17
-- title:
--   Explicit Jacobian and elimination data in characteristics two and three
-- statement:
--   The file defines the reduced canonical equations, gradient rows, six two-by-two Jacobian minors, and singular-point predicates in characteristics $2$ and $3$. It also defines the $x=1$ characteristic-three equations, their bivariate elimination residual and derivatives, projective normalization helpers, and the Jacobian ideal on each affine chart. These formulas are the computational interface for proving good reduction and for reducing point counts to lower-dimensional loci.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalAffineCharts
import Definitions.Def_N25_NormalizedPointPredicates
noncomputable section

/-! Jacobian ideals and the explicit characteristic-two and characteristic-three gradients. -/

namespace MazurProof.RationalPointsN25QuotientSmoothF2

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeil

/-- The canonical quadric after reduction to characteristic two. -/
def canonicalQuadric25CharTwo {K : Type*} [CommRing K]
    (P : Coordinates4 K) : K :=
  P.x * P.z + P.x * P.w + P.y ^ 2 + P.y * P.z + P.z * P.w

/-- The canonical cubic after reduction to characteristic two. -/
def canonicalCubic25CharTwo {K : Type*} [CommRing K]
    (P : Coordinates4 K) : K :=
  P.x ^ 2 * P.w + P.x * P.y * P.z + P.x * P.y * P.w +
    P.x * P.z * P.w + P.y * P.z * P.w + P.z ^ 2 * P.w +
    P.z * P.w ^ 2

/-- The gradient row of the reduced canonical quadric. -/
def canonicalQuadricGradient25CharTwo {K : Type*} [CommRing K]
    (P : Coordinates4 K) : Coordinates4 K :=
  ⟨P.z + P.w, P.z, P.x + P.y + P.w, P.x + P.z⟩

/-- The gradient row of the reduced canonical cubic. -/
def canonicalCubicGradient25CharTwo {K : Type*} [CommRing K]
    (P : Coordinates4 K) : Coordinates4 K :=
  ⟨P.y * P.z + P.y * P.w + P.z * P.w,
    P.x * P.z + P.x * P.w + P.z * P.w,
    P.x * P.y + P.x * P.w + P.y * P.w + P.w ^ 2,
    P.x ^ 2 + P.x * P.y + P.x * P.z + P.y * P.z + P.z ^ 2⟩

/-- The six two-by-two minors of the quadric and cubic gradient rows. -/
structure CanonicalJacobianMinors25 (K : Type*) where
  xy : K
  xz : K
  xw : K
  yz : K
  yw : K
  zw : K

/-- Evaluate the six Jacobian minors at a homogeneous coordinate vector. -/
def canonicalJacobianMinors25CharTwo {K : Type*} [CommRing K]
    (P : Coordinates4 K) : CanonicalJacobianMinors25 K :=
  let q := canonicalQuadricGradient25CharTwo P
  let k := canonicalCubicGradient25CharTwo P
  ⟨q.x * k.y - q.y * k.x,
    q.x * k.z - q.z * k.x,
    q.x * k.w - q.w * k.x,
    q.y * k.z - q.z * k.y,
    q.y * k.w - q.w * k.y,
    q.z * k.w - q.w * k.z⟩

/-- Simultaneous vanishing condition defining a singular point of the
codimension-two complete intersection. -/
def IsCanonicalSingular25CharTwo {K : Type*} [CommRing K]
    (P : Coordinates4 K) : Prop :=
  let M := canonicalJacobianMinors25CharTwo P
  canonicalQuadric25CharTwo P = 0 ∧
    canonicalCubic25CharTwo P = 0 ∧
    M.xy = 0 ∧ M.xz = 0 ∧ M.xw = 0 ∧
    M.yz = 0 ∧ M.yw = 0 ∧ M.zw = 0


end MazurProof.RationalPointsN25QuotientSmoothF2

namespace MazurProof.RationalPointsN25QuotientWeilThreeLinear

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeil

variable {K : Type*} [Field K]

/-- The canonical quadric on the normalized chart `x=1`, written to expose
its coefficient `z-1` of `w`. -/
def canonicalQuadricX25Three (y z w : K) : K :=
  y ^ 2 + y * z - z + (z - 1) * w

/-- The canonical cubic on the normalized chart `x=1`. -/
def canonicalCubicX25Three (y z w : K) : K :=
  w + y * z - y * w - z * w + y * z * w + z ^ 2 * w - z * w ^ 2

/-- The bivariate residual obtained after eliminating `w` from the
quadric-cubic intersection in characteristic three. -/
def canonicalResidualX25Three (y z : K) : K :=
  y ^ 4 * z + y * z ^ 4 + y ^ 3 * z - z ^ 4 +
    y ^ 3 - y ^ 2 + z ^ 2 + z

/-- The quotient multiplying the quadric in the cleared-denominator
elimination identity. -/
def canonicalEliminationMultiplierX25Three (y z w : K) : K :=
  y ^ 2 * z + 2 * y * z ^ 2 + z ^ 3 - z ^ 2 * w -
    2 * y * z + z * w + y + 2 * z - 1


end MazurProof.RationalPointsN25QuotientWeilThreeLinear

namespace MazurProof.RationalPointsN25QuotientSmoothF3

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeil
open MazurProof.RationalPointsN25QuotientKummerThree
open MazurProof.RationalPointsN25QuotientWeilThreeLinear
open MazurProof.RationalPointsN25QuotientKummerThreeProjective

/-- The gradient of the canonical quadric after reducing its coefficients
modulo three.  The coordinate order is `(x,y,z,w)`. -/
def canonicalQuadricGradient25Three {K : Type*} [CommRing K]
    (P : Coordinates4 K) : Coordinates4 K :=
  ⟨-P.z - P.w,
    -P.y + P.z,
    -P.x + P.y + P.w,
    -P.x + P.z⟩

/-- The gradient of the canonical cubic after reducing its coefficients
modulo three, again in coordinate order `(x,y,z,w)`. -/
def canonicalCubicGradient25Three {K : Type*} [CommRing K]
    (P : Coordinates4 K) : Coordinates4 K :=
  ⟨-P.x * P.w + P.y * P.z - P.y * P.w - P.z * P.w,
    P.x * P.z - P.x * P.w + P.z * P.w,
    -P.w ^ 2 - P.x * P.w + P.y * P.w - P.z * P.w + P.x * P.y,
    P.x ^ 2 - P.x * P.y - P.x * P.z + P.y * P.z + P.z ^ 2 + P.z * P.w⟩

/-- The six two-by-two minors of the quadric and cubic gradient rows.  Their
simultaneous vanishing is exactly failure of rank two for this `2 × 4`
Jacobian matrix. -/
structure CanonicalJacobianMinors25Three (K : Type*) where
  xy : K
  xz : K
  xw : K
  yz : K
  yw : K
  zw : K

/-- Evaluate the six characteristic-three Jacobian minors at homogeneous
coordinates. -/
def canonicalJacobianMinors25Three {K : Type*} [CommRing K]
    (P : Coordinates4 K) : CanonicalJacobianMinors25Three K :=
  let q := canonicalQuadricGradient25Three P
  let c := canonicalCubicGradient25Three P
  ⟨q.x * c.y - q.y * c.x,
    q.x * c.z - q.z * c.x,
    q.x * c.w - q.w * c.x,
    q.y * c.z - q.z * c.y,
    q.y * c.w - q.w * c.y,
    q.z * c.w - q.w * c.z⟩

/-- A homogeneous point is singular for the characteristic-three complete
intersection when it lies on both equations and all six Jacobian minors
vanish. -/
def IsCanonicalSingular25Three {K : Type*} [Field K]
    (P : Coordinates4 K) : Prop :=
  let M := canonicalJacobianMinors25Three P
  canonicalQuadric25Three P = 0 ∧
    canonicalCubic25Three P = 0 ∧
    M.xy = 0 ∧ M.xz = 0 ∧ M.xw = 0 ∧
    M.yz = 0 ∧ M.yw = 0 ∧ M.zw = 0

/-! ## The regular residual and its Jacobian identities -/

/-- The `y`-partial derivative of the eliminated residual in characteristic
three.  Terms with coefficient three disappear and `4=1`, `-2=1`. -/
def canonicalResidualYDerivative25Three {K : Type*} [CommRing K]
    (y z : K) : K :=
  y ^ 3 * z + z ^ 4 + y

/-- The `z`-partial derivative of the eliminated residual in characteristic
three. -/
def canonicalResidualZDerivative25Three {K : Type*} [CommRing K]
    (y z : K) : K :=
  y ^ 4 + y ^ 3 + y * z ^ 3 - z ^ 3 - z + 1


end MazurProof.RationalPointsN25QuotientSmoothF3

namespace MazurProof.RationalPointsN25QuotientKummerThreeProjective

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeil

/-- The zero vector in four homogeneous field coordinates. -/
def zeroCoordinatesThree {K : Type*} [Zero K] : Coordinates4 K :=
  ⟨0, 0, 0, 0⟩

/-- Scalar multiplication of four homogeneous coordinates. -/
def scaleCoordinatesThree {K : Type*} [Mul K]
    (a : K) (P : Coordinates4 K) : Coordinates4 K :=
  ⟨a * P.x, a * P.y, a * P.z, a * P.w⟩

/-- Normalize a homogeneous vector by its first nonzero coordinate.  The
zero vector is sent to `wChart`; all uses below separately prove nonvanishing. -/
def normalizeCoordinatesThree {K : Type*} [Field K] [DecidableEq K]
    (P : Coordinates4 K) : NormalizedProjective4 K :=
  if _hx : P.x ≠ 0 then
    .xChart (P.y / P.x) (P.z / P.x) (P.w / P.x)
  else if _hy : P.y ≠ 0 then
    .yChart (P.z / P.y) (P.w / P.y)
  else if _hz : P.z ≠ 0 then
    .zChart (P.w / P.z)
  else .wChart

end MazurProof.RationalPointsN25QuotientKummerThreeProjective

namespace N25

/-- The minors using the three coordinates other than the chart pivot. -/
def canonicalChartJacobianIdeal25
    (K : Type*) [CommRing K] (i : Fin 4) :
    Ideal (CanonicalChartRing25 K i) :=
  Ideal.span
    {m | ∃ j k : Fin 4,
      j ≠ i ∧ k ≠ i ∧ j < k ∧
      m = Ideal.Quotient.mk (canonicalChartIdeal25 K i)
        (canonicalJacobianMinor25 K j k)}

end N25

namespace N25

/-- The four homogeneous partial derivatives of the canonical quadric. -/
def canonicalQuadricGradient25 {K : Type*} [CommRing K] (v : Fin 4 → K) : Fin 4 → K :=
  ![-v 2 - v 3, 2 * v 1 + v 2, -v 0 + v 1 + v 3, -v 0 + v 2]

/-- The four homogeneous partial derivatives of the canonical cubic. -/
def canonicalCubicGradient25 {K : Type*} [CommRing K] (v : Fin 4 → K) : Fin 4 → K :=
  ![2*v 0*v 3+v 1*v 2-v 1*v 3-v 2*v 3,
    v 0*v 2-v 0*v 3+v 2*v 3,
    v 0*v 1-v 0*v 3+v 1*v 3+2*v 2*v 3-(v 3)^2,
    (v 0)^2-v 0*v 1-v 0*v 2+v 1*v 2+(v 2)^2-2*v 2*v 3]

end N25

namespace N25

/-- A four-coordinate record as its coordinate function. -/
def coordinates4Vector25 {K : Type*}
    (P : MazurProof.RationalPointsN25QuotientF2.Coordinates4 K) : Fin 4 → K :=
  ![P.x, P.y, P.z, P.w]

end N25


