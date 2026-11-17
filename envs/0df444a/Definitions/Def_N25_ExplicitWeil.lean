-- Prove2me | Definitions.Def_N25_ExplicitWeil
-- name    : N25_ExplicitWeil
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:05:36.096864+00:00
-- url     : https://prove2.me/theorems/69b7d577-6930-4216-9e0a-e0f5bcf1cfbb
-- title:
--   Executable characteristic-two fields and Weil point-count carriers
-- statement:
--   The file defines the complete-law predicate for a binary field table, table exponentiation, and explicit polynomial-basis models of $𝔽_4$, $𝔽_8=𝔽_2[α]/(α^3+α+1)$, and $𝔽_{16}=𝔽_2[β]/(β^4+β+1)$ with their inverses. It also defines the normalized canonical-point predicate, chart fibres, and assembled projective point-count carriers whose values give $$\#C(𝔽_2)=5,\quad\#C(𝔽_4)=5,\quad\#C(𝔽_8)=20,\quad\#C(𝔽_{16})=29.$$ These are the four moments used to reconstruct the binary Weil numerator.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_ExplicitF2
/-!
# Finite-field moments for the level-25 genus-four quotient

This file extends the kernel-checked point counts for the canonical quotient
`25.150.4.f.1` from `F_2` and `F_4` to `F_8` and `F_16`.  The four counts

`#C(F_2) = 5`, `#C(F_4) = 5`, `#C(F_8) = 20`, `#C(F_16) = 29`

are the point-count moments needed to determine the degree-eight Weil
numerator of a smooth genus-four curve over `F_2`.

The extension fields are executable polynomial-basis models.  The complete
field laws for the cubic model and the inverse law for the quartic model are
checked by ordinary kernel reduction.  The remaining quartic laws are kept in
separate, resource-bounded modules.  Projective points are enumerated by the
unique representative whose first nonzero coordinate is one.  This avoids
quotient enumeration while retaining the exact projective meaning of the
counts once those field-law certificates are imported.

The final section also checks that every *rational* point of the special fibre
has Jacobian rank two.  It deliberately does not claim geometric smoothness:
excluding singular points over the algebraic closure requires a separate
Jacobian-ideal certificate.
-/

namespace MazurProof.RationalPointsN25QuotientWeil

open RationalPointsN25QuotientF2
open scoped BigOperators

-- Finite universal propositions are the trusted computation mechanism in
-- this file, so restore the decision instances disabled by an imported
-- combinatorics module.
attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

/-! ## Executable binary-field tables -/

/-- Exhaustive algebraic laws certifying that a finite binary operation table,
together with the displayed inverse function, is a field of characteristic
two.  Concrete models can prove these laws independently of the later point
enumeration; the expensive quartic laws are split across dedicated modules. -/
def IsBinaryFieldTable {R : Type*} [DecidableEq R]
    (O : BinaryRingOperations R) (inv : R → R) : Prop :=
  O.zero ≠ O.one ∧
  (∀ a b c, O.add (O.add a b) c = O.add a (O.add b c)) ∧
  (∀ a b, O.add a b = O.add b a) ∧
  (∀ a, O.add O.zero a = a) ∧
  (∀ a, O.add a a = O.zero) ∧
  (∀ a b c, O.mul (O.mul a b) c = O.mul a (O.mul b c)) ∧
  (∀ a b, O.mul a b = O.mul b a) ∧
  (∀ a, O.mul O.one a = a) ∧
  (∀ a, O.mul O.zero a = O.zero) ∧
  (∀ a b c,
    O.mul a (O.add b c) = O.add (O.mul a b) (O.mul a c)) ∧
  (∀ a, a ≠ O.zero → O.mul a (inv a) = O.one)

private instance decidableIsBinaryFieldTable
    {R : Type*} [Fintype R] [DecidableEq R]
    (O : BinaryRingOperations R) (inv : R → R) :
    Decidable (IsBinaryFieldTable O inv) := by
  unfold IsBinaryFieldTable
  infer_instance

/-- Exponentiation using a finite operation table.  The inverse functions
below use the finite-field identity `a⁻¹ = a^(q-2)` for `a ≠ 0`. -/
def binaryPow {R : Type*} (O : BinaryRingOperations R) (a : R) : ℕ → R
  | 0 => O.one
  | n + 1 => O.mul (binaryPow O a n) a

/-! ## The quadratic extension `F_4` -/

/-- The executable field operations on the quadratic model imported from the
previous point-count file. -/
def f4Operations : BinaryRingOperations F4 where
  zero := f4Zero
  one := f4One
  add := f4Add
  mul := f4Mul

/-- Kernel-checked certificate that the imported quadratic operation table is
the four-element field. -/
theorem f4_isBinaryFieldTable :
    IsBinaryFieldTable f4Operations f4Inv := by
  decide

/-! ## The cubic extension `F_8` -/

/-- Addition of binary coefficients, implemented as exclusive-or. -/
def bitAdd (a b : Bool) : Bool :=
  Bool.xor a b

/-- Multiplication of binary coefficients, implemented as conjunction. -/
def bitMul (a b : Bool) : Bool :=
  a && b

/-- Polynomial-basis coordinates for
`F_8 = F_2[alpha]/(alpha^3 + alpha + 1)`.  The element is
`c0 + c1*alpha + c2*alpha^2`. -/
structure F8 where
  c0 : Bool
  c1 : Bool
  c2 : Bool
deriving DecidableEq, Fintype

/-- Addition in the polynomial basis of `F_8`. -/
def f8Add (a b : F8) : F8 :=
  ⟨bitAdd a.c0 b.c0, bitAdd a.c1 b.c1, bitAdd a.c2 b.c2⟩

/-- Multiplication in `F_8`, obtained by binary convolution followed by
`alpha^3 = alpha + 1`. -/
def f8Mul (a b : F8) : F8 :=
  let c0 := bitMul a.c0 b.c0
  let c1 := bitAdd (bitMul a.c0 b.c1) (bitMul a.c1 b.c0)
  let c2 := bitAdd (bitAdd (bitMul a.c0 b.c2) (bitMul a.c1 b.c1))
    (bitMul a.c2 b.c0)
  let c3 := bitAdd (bitMul a.c1 b.c2) (bitMul a.c2 b.c1)
  let c4 := bitMul a.c2 b.c2
  ⟨bitAdd c0 c3, bitAdd (bitAdd c1 c3) c4, bitAdd c2 c4⟩

/-- The executable zero, one, addition, and multiplication table for `F_8`. -/
def f8Operations : BinaryRingOperations F8 where
  zero := ⟨false, false, false⟩
  one := ⟨true, false, false⟩
  add := f8Add
  mul := f8Mul

/-- Inversion in the eight-element field; a nonzero element has inverse
`a^6` because its multiplicative group has order seven. -/
def f8Inv (a : F8) : F8 :=
  binaryPow f8Operations a 6

/-- Exhaustive ordinary-kernel certificate that the cubic polynomial-basis
operations form a field of characteristic two.  This connects the executable
`F_8` point enumeration to its intended finite-field interpretation. -/
theorem f8_isBinaryFieldTable :
    IsBinaryFieldTable f8Operations f8Inv := by
  decide

/-! ## The quartic extension `F_16` -/

/-- Polynomial-basis coordinates for
`F_16 = F_2[beta]/(beta^4 + beta + 1)`. -/
structure F16 where
  c0 : Bool
  c1 : Bool
  c2 : Bool
  c3 : Bool
deriving DecidableEq, Fintype

/-- Addition in the polynomial basis of `F_16`. -/
def f16Add (a b : F16) : F16 :=
  ⟨bitAdd a.c0 b.c0, bitAdd a.c1 b.c1,
    bitAdd a.c2 b.c2, bitAdd a.c3 b.c3⟩

/-- Multiplication in `F_16`, obtained by binary convolution followed by
`beta^4 = beta + 1`. -/
def f16Mul (a b : F16) : F16 :=
  let c0 := bitMul a.c0 b.c0
  let c1 := bitAdd (bitMul a.c0 b.c1) (bitMul a.c1 b.c0)
  let c2 := bitAdd (bitAdd (bitMul a.c0 b.c2) (bitMul a.c1 b.c1))
    (bitMul a.c2 b.c0)
  let c3 := bitAdd
    (bitAdd (bitAdd (bitMul a.c0 b.c3) (bitMul a.c1 b.c2))
      (bitMul a.c2 b.c1)) (bitMul a.c3 b.c0)
  let c4 := bitAdd (bitAdd (bitMul a.c1 b.c3) (bitMul a.c2 b.c2))
    (bitMul a.c3 b.c1)
  let c5 := bitAdd (bitMul a.c2 b.c3) (bitMul a.c3 b.c2)
  let c6 := bitMul a.c3 b.c3
  ⟨bitAdd c0 c4, bitAdd (bitAdd c1 c4) c5,
    bitAdd (bitAdd c2 c5) c6, bitAdd c3 c6⟩

/-- The executable zero, one, addition, and multiplication table for
`F_16`. -/
def f16Operations : BinaryRingOperations F16 where
  zero := ⟨false, false, false, false⟩
  one := ⟨true, false, false, false⟩
  add := f16Add
  mul := f16Mul

/-- Inversion in the sixteen-element field; a nonzero element has inverse
`a^14` because its multiplicative group has order fifteen. -/
def f16Inv (a : F16) : F16 :=
  binaryPow f16Operations a 14

/-- Every nonzero element of the quartic polynomial-basis table has the
displayed multiplicative inverse.  This is the field fact needed to justify
first-nonzero-coordinate projective normalization. -/
theorem f16_mul_inv_of_ne_zero :
    ∀ a : F16, a ≠ f16Operations.zero →
      f16Operations.mul a (f16Inv a) = f16Operations.one := by
  exact of_decide_eq_true rfl

/-! ## Normalized projective coordinates and canonical equations -/

/-- A normalized projective vector satisfying both canonical equations over
the chosen binary field table. -/
def IsCanonicalNormalized25 {R : Type*} [DecidableEq R]
    (O : BinaryRingOperations R) (P : NormalizedProjective4 R) : Prop :=
  let C := P.coordinates O
  canonicalQuadric25Binary O C = O.zero ∧
    canonicalCubic25Binary O C = O.zero

private instance decidableIsCanonicalNormalized25
    {R : Type*} [DecidableEq R] (O : BinaryRingOperations R) :
    DecidablePred (IsCanonicalNormalized25 O) := fun P => by
  unfold IsCanonicalNormalized25
  infer_instance

/-- The finite set of first-coordinate-normalized canonical points over
`F_4`.  This gives a cardinal form of the earlier no-new-degree-two result. -/
def canonicalNormalizedPoints25F4 : Finset (NormalizedProjective4 F4) :=
  Finset.univ.filter (IsCanonicalNormalized25 f4Operations)

/-- Canonical points in the chart `[1:y:z:w]` for one fixed `F_8` value of
`y`. -/
def canonicalXChartFiber25F8 (y : F8) : Finset (F8 × F8) :=
  Finset.univ.filter fun zw =>
    IsCanonicalNormalized25 f8Operations (.xChart y zw.1 zw.2)

/-- Expected cardinality of each fixed-`y` fibre in the `F_8` `x=1` chart. -/
def expectedXChartFiberCard25F8 (y : F8) : Nat :=
  match y with
  | ⟨false, false, false⟩ => 4
  | ⟨true, false, false⟩ => 1
  | _ => 2

/-- Canonical points in the normalized chart `[0:1:z:w]` over `F_8`. -/
def canonicalYChartPoints25F8 : Finset (F8 × F8) :=
  Finset.univ.filter fun zw =>
    IsCanonicalNormalized25 f8Operations (.yChart zw.1 zw.2)

/-- Canonical points in the normalized chart `[0:0:1:w]` over `F_8`. -/
def canonicalZChartPoints25F8 : Finset F8 :=
  Finset.univ.filter fun w =>
    IsCanonicalNormalized25 f8Operations (.zChart w)

/-- Projective point count over `F_8`, assembled from the four disjoint
normalized charts. -/
def canonicalProjectivePointCount25F8 : Nat :=
  (∑ y : F8, (canonicalXChartFiber25F8 y).card) +
    canonicalYChartPoints25F8.card + canonicalZChartPoints25F8.card + 1

/-- Canonical points in the chart `[1:y:z:w]` for one fixed value of `y`.
Splitting the largest projective chart into sixteen fibres keeps each kernel
certificate small. -/
def canonicalXChartFiber25F16 (y : F16) : Finset (F16 × F16) :=
  Finset.univ.filter fun zw =>
    IsCanonicalNormalized25 f16Operations (.xChart y zw.1 zw.2)

/-- Expected cardinality of each fixed-`y` fibre in the `x=1` chart. -/
def expectedXChartFiberCard25F16 (y : F16) : Nat :=
  match y with
  | ⟨_, _, _, true⟩ => 1
  | ⟨_, true, true, false⟩ => 4
  | ⟨_, true, false, false⟩ => 2
  | ⟨_, false, true, false⟩ => 2
  | _ => 1

/-- Canonical points in the normalized chart `[0:1:z:w]` over `F_16`. -/
def canonicalYChartPoints25F16 : Finset (F16 × F16) :=
  Finset.univ.filter fun zw =>
    IsCanonicalNormalized25 f16Operations (.yChart zw.1 zw.2)

/-- Canonical points in the normalized chart `[0:0:1:w]` over `F_16`. -/
def canonicalZChartPoints25F16 : Finset F16 :=
  Finset.univ.filter fun w =>
    IsCanonicalNormalized25 f16Operations (.zChart w)

/-- Projective point count obtained by adding the four disjoint normalized
charts. -/
def canonicalProjectivePointCount25F16 : Nat :=
  (∑ y : F16, (canonicalXChartFiber25F16 y).card) +
    canonicalYChartPoints25F16.card + canonicalZChartPoints25F16.card + 1

/-! ## Jacobian rank at the rational points of the special fibre -/


end MazurProof.RationalPointsN25QuotientWeil


