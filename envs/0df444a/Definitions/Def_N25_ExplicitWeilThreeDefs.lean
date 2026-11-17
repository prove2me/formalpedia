-- Prove2me | Definitions.Def_N25_ExplicitWeilThreeDefs
-- name    : N25_ExplicitWeilThreeDefs
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:00.38084+00:00
-- url     : https://prove2.me/theorems/5b9a0670-31f6-408d-bf6f-bbfdb064205d
-- title:
--   Executable ternary extension fields and signed canonical equations
-- statement:
--   The file defines the three-element coefficient type and its signed arithmetic, a generic ternary operation record, and polynomial-basis carriers for $$𝔽_9=𝔽_3[u]/(u^2+2u+2),\quad 𝔽_{27}=𝔽_3[v]/(v^3+2v+1),\quad 𝔽_{81}=𝔽_3[q]/(q^4+2q^3+2).$$ It supplies their executable addition, negation, multiplication, and inversion tables, together with normalized projective coordinates and signed evaluators for the canonical quadric and cubic. These are the raw computational objects for the characteristic-three counts.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_ExplicitWeil
/-!
# Executable ternary fields for the level-25 local calculation

This file supplies compact polynomial-basis operation tables for

```
F_3,
F_9  = F_3[u]/(u^2 + 2u + 2),
F_27 = F_3[v]/(v^3 + 2v + 1),
F_81 = F_3[q]/(q^4 + 2q^3 + 2).
```

It also evaluates the signed canonical quadric and cubic on normalized
projective representatives.  No large point enumeration belongs here.  The
small fields are counted after linear elimination, while `F_81` is counted
through the order-five Kummer quotient.
-/

namespace MazurProof.RationalPointsN25QuotientWeilThree

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientWeil

/-! ## Prime-field coefficients and signed operations -/

/-- A coefficient of `F_3`, represented by its canonical residue
`0`, `1`, or `2`. -/
inductive Trit where
  | zero
  | one
  | two
deriving DecidableEq

instance : Fintype Trit where
  elems := {.zero, .one, .two}
  complete a := by cases a <;> simp

/-- Addition in the three-element prime field. -/
def tritAdd : Trit → Trit → Trit
  | .zero, b => b
  | a, .zero => a
  | .one, .one => .two
  | .one, .two => .zero
  | .two, .one => .zero
  | .two, .two => .one

/-- Additive inverse in the three-element prime field. -/
def tritNeg : Trit → Trit
  | .zero => .zero
  | .one => .two
  | .two => .one

/-- Multiplication in the three-element prime field. -/
def tritMul : Trit → Trit → Trit
  | .zero, _ => .zero
  | _, .zero => .zero
  | .one, b => b
  | a, .one => a
  | .two, .two => .one

/-- Multiplication of a prime-field coefficient by two. -/
def tritDouble (a : Trit) : Trit :=
  tritAdd a a

/-- The zero, one, addition, negation, and multiplication needed to evaluate
signed equations in an explicit characteristic-three table. -/
structure TernaryRingOperations (R : Type*) where
  zero : R
  one : R
  add : R → R → R
  neg : R → R
  mul : R → R → R

/-- Exponentiation using an explicit multiplication table. -/
def ternaryPow {R : Type*} (O : TernaryRingOperations R) (a : R) : ℕ → R
  | 0 => O.one
  | n + 1 => O.mul (ternaryPow O a n) a

/-- The executable prime-field operation table. -/
def f3Operations : TernaryRingOperations Trit where
  zero := .zero
  one := .one
  add := tritAdd
  neg := tritNeg
  mul := tritMul

/-! ## The quadratic and cubic extensions -/

/-- Polynomial-basis coordinates `c₀+c₁u` for
`F_9=F_3[u]/(u²+2u+2)`. -/
structure F9 where
  c0 : Trit
  c1 : Trit
deriving DecidableEq, Fintype

/-- Coefficientwise addition in `F_9`. -/
def f9Add (a b : F9) : F9 :=
  ⟨tritAdd a.c0 b.c0, tritAdd a.c1 b.c1⟩

/-- Coefficientwise additive inverse in `F_9`. -/
def f9Neg (a : F9) : F9 :=
  ⟨tritNeg a.c0, tritNeg a.c1⟩

/-- Multiplication in `F_9`, reduced with `u²=u+1`. -/
def f9Mul (a b : F9) : F9 :=
  let c0 := tritMul a.c0 b.c0
  let c1 := tritAdd (tritMul a.c0 b.c1) (tritMul a.c1 b.c0)
  let c2 := tritMul a.c1 b.c1
  ⟨tritAdd c0 c2, tritAdd c1 c2⟩

/-- The executable signed operation table on `F_9`. -/
def f9Operations : TernaryRingOperations F9 where
  zero := ⟨.zero, .zero⟩
  one := ⟨.one, .zero⟩
  add := f9Add
  neg := f9Neg
  mul := f9Mul

/-- Polynomial-basis coordinates `c₀+c₁v+c₂v²` for
`F_27=F_3[v]/(v³+2v+1)`. -/
structure F27 where
  c0 : Trit
  c1 : Trit
  c2 : Trit
deriving DecidableEq, Fintype

/-- Coefficientwise addition in `F_27`. -/
def f27Add (a b : F27) : F27 :=
  ⟨tritAdd a.c0 b.c0, tritAdd a.c1 b.c1, tritAdd a.c2 b.c2⟩

/-- Coefficientwise additive inverse in `F_27`. -/
def f27Neg (a : F27) : F27 :=
  ⟨tritNeg a.c0, tritNeg a.c1, tritNeg a.c2⟩

/-- Multiplication in `F_27`, reduced with `v³=v+2` and
`v⁴=v²+2v`. -/
def f27Mul (a b : F27) : F27 :=
  let c0 := tritMul a.c0 b.c0
  let c1 := tritAdd (tritMul a.c0 b.c1) (tritMul a.c1 b.c0)
  let c2 := tritAdd
    (tritAdd (tritMul a.c0 b.c2) (tritMul a.c1 b.c1))
    (tritMul a.c2 b.c0)
  let c3 := tritAdd (tritMul a.c1 b.c2) (tritMul a.c2 b.c1)
  let c4 := tritMul a.c2 b.c2
  ⟨tritAdd c0 (tritDouble c3),
    tritAdd (tritAdd c1 c3) (tritDouble c4),
    tritAdd c2 c4⟩

/-- The executable signed operation table on `F_27`. -/
def f27Operations : TernaryRingOperations F27 where
  zero := ⟨.zero, .zero, .zero⟩
  one := ⟨.one, .zero, .zero⟩
  add := f27Add
  neg := f27Neg
  mul := f27Mul

/-! ## The quartic extension containing the fifth roots of unity -/

/-- Polynomial-basis coordinates `c₀+c₁q+c₂q²+c₃q³` for
`F_81=F_3[q]/(q⁴+2q³+2)`. -/
structure F81 where
  c0 : Trit
  c1 : Trit
  c2 : Trit
  c3 : Trit
deriving DecidableEq, Fintype

/-- Coefficientwise addition in `F_81`. -/
def f81Add (a b : F81) : F81 :=
  ⟨tritAdd a.c0 b.c0, tritAdd a.c1 b.c1,
    tritAdd a.c2 b.c2, tritAdd a.c3 b.c3⟩

/-- Coefficientwise additive inverse in `F_81`. -/
def f81Neg (a : F81) : F81 :=
  ⟨tritNeg a.c0, tritNeg a.c1, tritNeg a.c2, tritNeg a.c3⟩

/-- Multiplication in `F_81`, using
`q⁴=q³+1`, `q⁵=q³+q+1`, and `q⁶=q³+q²+q+1`. -/
def f81Mul (a b : F81) : F81 :=
  let c0 := tritMul a.c0 b.c0
  let c1 := tritAdd (tritMul a.c0 b.c1) (tritMul a.c1 b.c0)
  let c2 := tritAdd
    (tritAdd (tritMul a.c0 b.c2) (tritMul a.c1 b.c1))
    (tritMul a.c2 b.c0)
  let c3 := tritAdd
    (tritAdd (tritAdd (tritMul a.c0 b.c3) (tritMul a.c1 b.c2))
      (tritMul a.c2 b.c1)) (tritMul a.c3 b.c0)
  let c4 := tritAdd
    (tritAdd (tritMul a.c1 b.c3) (tritMul a.c2 b.c2))
    (tritMul a.c3 b.c1)
  let c5 := tritAdd (tritMul a.c2 b.c3) (tritMul a.c3 b.c2)
  let c6 := tritMul a.c3 b.c3
  ⟨tritAdd (tritAdd (tritAdd c0 c4) c5) c6,
    tritAdd (tritAdd c1 c5) c6,
    tritAdd c2 c6,
    tritAdd (tritAdd (tritAdd c3 c4) c5) c6⟩

/-- The executable signed operation table on `F_81`. -/
def f81Operations : TernaryRingOperations F81 where
  zero := ⟨.zero, .zero, .zero, .zero⟩
  one := ⟨.one, .zero, .zero, .zero⟩
  add := f81Add
  neg := f81Neg
  mul := f81Mul

/-- Inversion in `F_81`, using `a⁻¹=a⁷⁹` for nonzero `a`.  The
one-dimensional Kummer fibre evaluator uses this explicit operation. -/
def f81Inv (a : F81) : F81 :=
  ternaryPow f81Operations a 79

/-! ## Signed canonical equations and normalized projective charts -/

/-- Convert a first-nonzero-coordinate chart into homogeneous coordinates
using the zero and one of a ternary table. -/
def ternaryCoordinates {R : Type*} (O : TernaryRingOperations R) :
    NormalizedProjective4 R → Coordinates4 R
  | .xChart y z w => ⟨O.one, y, z, w⟩
  | .yChart z w => ⟨O.zero, O.one, z, w⟩
  | .zChart w => ⟨O.zero, O.zero, O.one, w⟩
  | .wChart => ⟨O.zero, O.zero, O.zero, O.one⟩

/-- The canonical quadric `-xz-xw+y²+yz+zw`, evaluated in a signed
characteristic-three table. -/
def canonicalQuadric25Ternary {R : Type*} (O : TernaryRingOperations R)
    (P : Coordinates4 R) : R :=
  O.add (O.add (O.neg (O.mul P.x P.z)) (O.neg (O.mul P.x P.w)))
    (O.add (O.mul P.y P.y)
      (O.add (O.mul P.y P.z) (O.mul P.z P.w)))

/-- The canonical cubic
`x²w+xyz-xyw-xzw+yzw+z²w-zw²`, evaluated in a signed table. -/
def canonicalCubic25Ternary {R : Type*} (O : TernaryRingOperations R)
    (P : Coordinates4 R) : R :=
  O.add
    (O.add
      (O.add (O.mul (O.mul P.x P.x) P.w)
        (O.mul (O.mul P.x P.y) P.z))
      (O.neg (O.mul (O.mul P.x P.y) P.w)))
    (O.add
      (O.add (O.neg (O.mul (O.mul P.x P.z) P.w))
        (O.mul (O.mul P.y P.z) P.w))
      (O.add (O.mul (O.mul P.z P.z) P.w)
        (O.neg (O.mul P.z (O.mul P.w P.w)))))

/-- A normalized projective chart value satisfying both canonical equations
over the chosen ternary table. -/
def IsCanonicalNormalized25Ternary {R : Type*} [DecidableEq R]
    (O : TernaryRingOperations R) (P : NormalizedProjective4 R) : Prop :=
  let C := ternaryCoordinates O P
  canonicalQuadric25Ternary O C = O.zero ∧
    canonicalCubic25Ternary O C = O.zero

private instance decidableIsCanonicalNormalized25Ternary
    {R : Type*} [DecidableEq R] (O : TernaryRingOperations R) :
    DecidablePred (IsCanonicalNormalized25Ternary O) := fun P => by
  unfold IsCanonicalNormalized25Ternary
  infer_instance

end MazurProof.RationalPointsN25QuotientWeilThree


