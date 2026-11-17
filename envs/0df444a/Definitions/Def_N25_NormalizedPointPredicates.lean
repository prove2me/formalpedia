-- Prove2me | Definitions.Def_N25_NormalizedPointPredicates
-- name    : N25_NormalizedPointPredicates
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:58.970254+00:00
-- url     : https://prove2.me/theorems/a1da939c-a2f6-42bd-afcf-0d5256445f23
-- title:
--   Normalized canonical points in characteristics two and three
-- statement:
--   Defines field-valued homogeneous coordinates for first-nonzero charts and the predicates cutting out the stored canonical level-$25$ quadric–cubic curve in $P^3$ in characteristics $2$ and $3$. The characteristic-two predicate uses standard field operations, while the characteristic-three equations are obtained by base change from the rational model; these predicates support the good-reduction point counts.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_NormalizedProjectiveCoordinates
/-! The field-semantic canonical predicates in characteristics two and three. -/

namespace MazurProof.RationalPointsN25QuotientSmoothF2

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeil

/-- The standard ring operations used to turn a normalized projective chart
into homogeneous coordinates over a characteristic-two field. -/
def fieldBinaryOperations (K : Type*) [Field K] : BinaryRingOperations K where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)

/-- Homogeneous coordinates of a normalized projective point over a field. -/
def normalizedCoordinates25 {K : Type*} [Field K]
    (P : NormalizedProjective4 K) : Coordinates4 K :=
  P.coordinates (fieldBinaryOperations K)

end MazurProof.RationalPointsN25QuotientSmoothF2

namespace MazurProof.RationalPointsN25QuotientBinaryFieldSemantics

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeil
open MazurProof.RationalPointsN25QuotientSmoothF2

/-- The standard field-semantic canonical predicate in characteristic two.
It is stated directly with field equality, so its mathematical type does not
carry the `DecidableEq` instance needed only by executable enumerations. -/
def IsCanonicalNormalizedTwo {K : Type*} [Field K]
    (P : NormalizedProjective4 K) : Prop :=
  let O := fieldBinaryOperations K
  canonicalQuadric25Binary O (normalizedCoordinates25 P) = O.zero ∧
    canonicalCubic25Binary O (normalizedCoordinates25 P) = O.zero

end MazurProof.RationalPointsN25QuotientBinaryFieldSemantics

namespace MazurProof.RationalPointsN25QuotientKummerThree

open MazurProof.RationalPointsN25QuotientF2

variable {K : Type*} [Field K]

/-- The canonical quadric over an arbitrary coefficient field.  This is the
base change of the stored rational equation. -/
def canonicalQuadric25Three (P : Coordinates4 K) : K :=
  -P.x * P.z - P.x * P.w + P.y ^ 2 + P.y * P.z + P.z * P.w

/-- The canonical cubic over an arbitrary coefficient field.  This is the
base change of the stored rational equation. -/
def canonicalCubic25Three (P : Coordinates4 K) : K :=
  P.x ^ 2 * P.w + P.x * P.y * P.z - P.x * P.y * P.w -
    P.x * P.z * P.w + P.y * P.z * P.w + P.z ^ 2 * P.w -
    P.z * P.w ^ 2

end MazurProof.RationalPointsN25QuotientKummerThree

namespace MazurProof.RationalPointsN25QuotientKummerThreeProjective

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeil
open MazurProof.RationalPointsN25QuotientKummerThree

/-- First-nonzero homogeneous coordinates using the zero and one of an
actual field. -/
def normalizedCoordinatesThree {K : Type*} [Field K] :
    NormalizedProjective4 K → Coordinates4 K
  | .xChart y z w => ⟨1, y, z, w⟩
  | .yChart z w => ⟨0, 1, z, w⟩
  | .zChart w => ⟨0, 0, 1, w⟩
  | .wChart => ⟨0, 0, 0, 1⟩

/-- The canonical quadric-cubic equations on a first-nonzero projective
representative over an actual characteristic-three field. -/
def IsCanonicalNormalizedThree {K : Type*} [Field K]
    (P : NormalizedProjective4 K) : Prop :=
  canonicalQuadric25Three (normalizedCoordinatesThree P) = 0 ∧
    canonicalCubic25Three (normalizedCoordinatesThree P) = 0

end MazurProof.RationalPointsN25QuotientKummerThreeProjective


