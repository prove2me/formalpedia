-- Prove2me | Definitions.Def_N25_NormalizedProjectiveCoordinates
-- name    : N25_NormalizedProjectiveCoordinates
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:14.199191+00:00
-- url     : https://prove2.me/theorems/c5886f48-73c4-4084-87e5-941cf4572394
-- title:
--   Executable normalized coordinates in characteristic two
-- statement:
--   Introduces four-coordinate records, a minimal table of binary ring operations, and the four first-nonzero affine charts of $P^3$, together with conversion to homogeneous coordinates and table-driven evaluation of the canonical quadric and cubic. This is a technical, executable carrier for enumerating characteristic-two points.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
/-! First-nonzero-coordinate representatives of projective three-space. -/
namespace MazurProof.RationalPointsN25QuotientF2

/-- Four homogeneous coordinates over a coefficient type. -/
structure Coordinates4 (R : Type*) where
  x : R
  y : R
  z : R
  w : R
deriving DecidableEq, Fintype

end MazurProof.RationalPointsN25QuotientF2

namespace MazurProof.RationalPointsN25QuotientWeil

open MazurProof.RationalPointsN25QuotientF2

/-- Operations needed to evaluate homogeneous equations in characteristic
two.  Additive inverses equal the original element, so subtraction is
represented by the same operation as addition. -/
structure BinaryRingOperations (R : Type*) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R



/-- The four first-nonzero-coordinate charts in projective three-space. -/
inductive NormalizedProjective4 (R : Type*) where
  | xChart (y z w : R)
  | yChart (z w : R)
  | zChart (w : R)
  | wChart
deriving DecidableEq, Fintype

/-- Convert a normalized projective chart value to its four homogeneous
coordinates using the zero and one of the chosen binary field table. -/
def NormalizedProjective4.coordinates {R : Type*}
    (O : BinaryRingOperations R) : NormalizedProjective4 R → Coordinates4 R
  | .xChart y z w => ⟨O.one, y, z, w⟩
  | .yChart z w => ⟨O.zero, O.one, z, w⟩
  | .zChart w => ⟨O.zero, O.zero, O.one, w⟩
  | .wChart => ⟨O.zero, O.zero, O.zero, O.one⟩

/-- The canonical quadric in characteristic two, evaluated using an explicit
binary field table.  Minus signs disappear because every element is its own
additive inverse. -/
def canonicalQuadric25Binary {R : Type*} (O : BinaryRingOperations R)
    (P : Coordinates4 R) : R :=
  O.add
    (O.add
      (O.add (O.mul P.x P.z) (O.mul P.x P.w))
      (O.mul P.y P.y))
    (O.add (O.mul P.y P.z) (O.mul P.z P.w))

/-- The canonical cubic in characteristic two, evaluated using an explicit
binary field table. -/
def canonicalCubic25Binary {R : Type*} (O : BinaryRingOperations R)
    (P : Coordinates4 R) : R :=
  O.add
    (O.add
      (O.add
        (O.add
          (O.add
            (O.add (O.mul (O.mul P.x P.x) P.w)
              (O.mul (O.mul P.x P.y) P.z))
            (O.mul (O.mul P.x P.y) P.w))
          (O.mul (O.mul P.x P.z) P.w))
        (O.mul (O.mul P.y P.z) P.w))
      (O.mul (O.mul P.z P.z) P.w))
    (O.mul P.z (O.mul P.w P.w))

end MazurProof.RationalPointsN25QuotientWeil


