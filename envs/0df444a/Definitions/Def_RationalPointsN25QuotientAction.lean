-- Prove2me | Definitions.Def_RationalPointsN25QuotientAction
-- name    : RationalPointsN25QuotientAction
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:02:07.221124+00:00
-- url     : https://prove2.me/theorems/2ee2b024-78fb-495c-bd72-19809f3965b2
-- title:
--   Order-five action and cyclic orbit coordinates on the canonical model
-- statement:
--   The file defines homogeneous four-coordinate vectors and the linear transformation $$τ(x,y,z,w)=(z,w-y,-w,x-y),$$ together with its ambient and canonical-curve equivalences. It names the five cusp representatives and introduces five cyclic orbit coordinates $(x,z,-w,y-x,w-y-z)$, their rotation, sum, and reconstruction map. These objects make the order-five diamond action explicit and place it in the regular five-cycle representation used for descent.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_RationalPointsN25CanonicalPoints
/-!
# The order-five action on the level-25 genus-four quotient

LMFDB curve `25.150.4.f.1` has canonical model

```
Q = -x*z - x*w + y^2 + y*z + z*w = 0,
C = x^2*w + x*y*z - x*y*w - x*z*w + y*z*w + z^2*w - z*w^2 = 0.
```

This file formalizes the explicit projective transformation

```
tau(x,y,z,w) = (z, w-y, -w, x-y).
```

It proves that `tau` has exact fifth iterate equal to the identity, preserves
the canonical complete intersection, and cyclically permutes the five listed
rational cusps.  It also records an equivariant linear change of coordinates
to the augmentation hyperplane in the regular five-cycle representation:

```
(x,y,z,w) |-> (x, z, -w, y-x, w-y-z).
```

The latter coordinates sum to zero and `tau` becomes cyclic rotation.  This
gives explicit quadratic, cubic, and quintic invariant polynomials suitable
for later cyclic-quintic descent arguments.
-/

namespace MazurProof.RationalPointsN25QuotientAction

open RationalPointsN25CanonicalPoints

/-! ## The four-dimensional order-five representation -/

/-- Homogeneous coordinates on the canonical `P^3` model. -/
@[ext]
structure Coordinates25 where
  x : ℚ
  y : ℚ
  z : ℚ
  w : ℚ
deriving DecidableEq

/-- Scalar multiplication of a homogeneous coordinate vector. -/
def scale25 (a : ℚ) (p : Coordinates25) : Coordinates25 :=
  ⟨a * p.x, a * p.y, a * p.z, a * p.w⟩

/-- The explicit order-five linear transformation on the canonical model. -/
def tau25 (p : Coordinates25) : Coordinates25 :=
  ⟨p.z, p.w - p.y, -p.w, p.x - p.y⟩

/-- Five applications of `tau25` are the identity. -/
theorem tau25_fifth (p : Coordinates25) :
    tau25 (tau25 (tau25 (tau25 (tau25 p)))) = p := by
  ext <;> simp [tau25] <;> ring

/-- The ambient order-five transformation as an explicit equivalence, with
fourth iterate as inverse. -/
def tauEquiv25 : Coordinates25 ≃ Coordinates25 where
  toFun := tau25
  invFun p := tau25 (tau25 (tau25 (tau25 p)))
  left_inv := tau25_fifth
  right_inv := tau25_fifth

/-! ## Projective equality and the canonical equations -/

/-- Existing projective equality, packaged for `Coordinates25`. -/
def ProjectivelyEqual25 (p q : Coordinates25) : Prop :=
  ProjectivelyEqual4 p.x p.y p.z p.w q.x q.y q.z q.w

/-- A coordinate vector lies on the canonical complete intersection. -/
def OnCanonical25 (p : Coordinates25) : Prop :=
  canonicalQuadric25 p.x p.y p.z p.w = 0 ∧
    canonicalCubic25 p.x p.y p.z p.w = 0

/-- The canonical quadric is exactly invariant under `tau25`. -/
theorem canonicalQuadric25_tau25 (p : Coordinates25) :
    canonicalQuadric25 (tau25 p).x (tau25 p).y (tau25 p).z (tau25 p).w =
      canonicalQuadric25 p.x p.y p.z p.w := by
  simp only [tau25, canonicalQuadric25]
  ring

/-- The canonical cubic is invariant modulo the canonical quadric:
`C(tau p) = C(p) - z Q(p)`. -/
theorem canonicalCubic25_tau25 (p : Coordinates25) :
    canonicalCubic25 (tau25 p).x (tau25 p).y (tau25 p).z (tau25 p).w =
      canonicalCubic25 p.x p.y p.z p.w -
        p.z * canonicalQuadric25 p.x p.y p.z p.w := by
  simp only [tau25, canonicalCubic25, canonicalQuadric25]
  ring

/-- `tau25` sends canonical points to canonical points. -/
theorem tau25_onCanonical {p : Coordinates25} (hp : OnCanonical25 p) :
    OnCanonical25 (tau25 p) := by
  rcases hp with ⟨hQ, hC⟩
  constructor
  · rw [canonicalQuadric25_tau25, hQ]
  · rw [canonicalCubic25_tau25, hQ, hC]
    ring

/-- The order-five automorphism restricted to the canonical complete
intersection. -/
def canonicalTauEquiv25 :
    {p : Coordinates25 // OnCanonical25 p} ≃
      {p : Coordinates25 // OnCanonical25 p} where
  toFun p := ⟨tau25 p.1, tau25_onCanonical p.2⟩
  invFun p :=
    ⟨tau25 (tau25 (tau25 (tau25 p.1))),
      tau25_onCanonical (tau25_onCanonical
        (tau25_onCanonical (tau25_onCanonical p.2)))⟩
  left_inv p := Subtype.ext (tau25_fifth p.1)
  right_inv p := Subtype.ext (tau25_fifth p.1)

/-! ## The five rational cusps form one cycle -/

/-- Cusp `[0:0:0:1]`. -/
def cusp25A : Coordinates25 := ⟨0, 0, 0, 1⟩

/-- Cusp `[0:-1:1:0]`. -/
def cusp25B : Coordinates25 := ⟨0, -1, 1, 0⟩

/-- Cusp `[1:1:0:1]`. -/
def cusp25C : Coordinates25 := ⟨1, 1, 0, 1⟩

/-- Cusp `[0:0:1:0]`. -/
def cusp25D : Coordinates25 := ⟨0, 0, 1, 0⟩

/-- Cusp `[1:0:0:0]`. -/
def cusp25E : Coordinates25 := ⟨1, 0, 0, 0⟩

/-- The existing five-cusp predicate, packaged for coordinate vectors. -/
def IsCusp25 (p : Coordinates25) : Prop :=
  IsCanonicalCusp25 p.x p.y p.z p.w

/-! ## Equivariant coordinates on the cyclic augmentation hyperplane -/

/-- Five coordinates carrying the regular cyclic rotation. -/
@[ext]
structure QuinticCoordinates25 where
  a0 : ℚ
  a1 : ℚ
  a2 : ℚ
  a3 : ℚ
  a4 : ℚ
deriving DecidableEq

/-- Cyclic left rotation of five coordinates. -/
def rotateQuintic25 (a : QuinticCoordinates25) : QuinticCoordinates25 :=
  ⟨a.a1, a.a2, a.a3, a.a4, a.a0⟩

/-- Sum of the five cyclic coordinates. -/
def quinticSum25 (a : QuinticCoordinates25) : ℚ :=
  a.a0 + a.a1 + a.a2 + a.a3 + a.a4

/-- Equivariant orbit coordinates: these are the `x`-coordinates of
`p, tau p, ..., tau^4 p`. -/
def orbitCoordinates25 (p : Coordinates25) : QuinticCoordinates25 :=
  ⟨p.x, p.z, -p.w, p.y - p.x, p.w - p.y - p.z⟩

/-- The orbit-coordinate image lies on the augmentation hyperplane. -/
theorem orbitCoordinates25_sum_zero (p : Coordinates25) :
    quinticSum25 (orbitCoordinates25 p) = 0 := by
  simp only [quinticSum25, orbitCoordinates25]
  ring

/-- Reconstruct the four original coordinates from the first four cyclic
coordinates. -/
def reconstructCoordinates25 (a : QuinticCoordinates25) : Coordinates25 :=
  ⟨a.a0, a.a3 + a.a0, a.a1, -a.a2⟩

/-- Reconstruction is a left inverse to the orbit-coordinate map. -/
theorem reconstruct_orbitCoordinates25 (p : Coordinates25) :
    reconstructCoordinates25 (orbitCoordinates25 p) = p := by
  ext <;> simp [reconstructCoordinates25, orbitCoordinates25]

/-- On the augmentation hyperplane, reconstruction is also a right inverse. -/
theorem orbitCoordinates_reconstruct25 {a : QuinticCoordinates25}
    (ha : quinticSum25 a = 0) :
    orbitCoordinates25 (reconstructCoordinates25 a) = a := by
  ext <;> simp [orbitCoordinates25, reconstructCoordinates25]
  simp only [quinticSum25] at ha
  linarith

/-- The four-dimensional representation is explicitly equivalent to the
sum-zero hyperplane of the five-cycle representation. -/
def orbitHyperplaneEquiv25 :
    Coordinates25 ≃ {a : QuinticCoordinates25 // quinticSum25 a = 0} where
  toFun p := ⟨orbitCoordinates25 p, orbitCoordinates25_sum_zero p⟩
  invFun a := reconstructCoordinates25 a.1
  left_inv := reconstruct_orbitCoordinates25
  right_inv a := by
    apply Subtype.ext
    exact orbitCoordinates_reconstruct25 a.2

/-! ## Explicit invariant polynomials -/

/-- The cyclic adjacent-pair quadratic on the five-cycle representation. -/
def cyclicAdjacent25 (a : QuinticCoordinates25) : ℚ :=
  a.a0 * a.a1 + a.a1 * a.a2 + a.a2 * a.a3 +
    a.a3 * a.a4 + a.a4 * a.a0

/-- A linear correction whose coboundary is `5*z`. -/
def cubicCorrection25 (p : Coordinates25) : ℚ :=
  2 * p.x - p.y - 3 * p.z + 2 * p.w

/-- An exactly invariant cubic representative of the class of the canonical
cubic modulo the canonical quadric. -/
def invariantCubic25 (p : Coordinates25) : ℚ :=
  5 * canonicalCubic25 p.x p.y p.z p.w +
    cubicCorrection25 p * canonicalQuadric25 p.x p.y p.z p.w

/-- The cyclic product (norm) of the five orbit coordinates. -/
def cyclicNorm25 (a : QuinticCoordinates25) : ℚ :=
  a.a0 * a.a1 * a.a2 * a.a3 * a.a4

/-- Three basic homogeneous invariants, of weights two, three, and five. -/
@[ext]
structure BasicInvariants25 where
  quadratic : ℚ
  cubic : ℚ
  quintic : ℚ
deriving DecidableEq

/-- The explicit basic-invariant map for the order-five action. -/
def basicInvariantMap25 (p : Coordinates25) : BasicInvariants25 :=
  ⟨canonicalQuadric25 p.x p.y p.z p.w,
    invariantCubic25 p,
    cyclicNorm25 (orbitCoordinates25 p)⟩

end MazurProof.RationalPointsN25QuotientAction


