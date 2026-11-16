-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexComputeQuotient
-- name    : liuyao_ca_fd889115_k1_Analysis_ComplexComputeQuotient
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:52:57.434222+00:00
-- url     : https://prove2.me/theorems/49031b2d-7b67-47d9-890b-8e536fd116d9
-- title:
--   Computable analysis · ComplexComputeQuotient · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ComplexComputeQuotient.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexComputeQuotientAlgebra

set_option autoImplicit true

/-!
# The certified represented-complex quotient

`ComplexCompute` remains the executable interval algorithm.  This module forms
the small proof-facing quotient of valid algorithms by overlap equivalence.
It is useful for algebraic normalization: literal interval expressions are
mapped into this quotient, ordinary algebraic rewrites are performed there,
and `Quotient.exact` returns the desired raw equivalence theorem.
-/

namespace ComputableAnalysis
namespace ComplexComputeQuotient

abbrev Certified := ComplexCert

private def certifiedSetoid : Setoid Certified where
  r left right := left.raw.Equiv right.raw
  iseqv := {
    refl := fun value => ComplexCompute.equiv_refl value.raw value.valid
    symm := fun h => ComplexCompute.equiv_symm h
    trans := fun {left middle right} hleft hright =>
      ComplexCompute.equiv_trans left.valid middle.valid right.valid hleft hright }

/-- Valid represented complex values modulo overlap equivalence. -/
def Value := Quotient certifiedSetoid

def ofRaw (raw : ComplexCompute) (valid : raw.Valid) : Value :=
  Quotient.mk certifiedSetoid ⟨raw, valid⟩

def ofQComplex (value : QComplex) : Value :=
  ofRaw (ComplexCompute.ofQComplex value) (ComplexCompute.ofQComplex_valid value)

theorem ofRaw_eq_ofRaw {left right : ComplexCompute}
    {hleft : left.Valid} {hright : right.Valid}
    (h : left.Equiv right) : ofRaw left hleft = ofRaw right hright :=
  Quotient.sound h

theorem equiv_of_ofRaw_eq {left right : ComplexCompute}
    {hleft : left.Valid} {hright : right.Valid}
    (h : ofRaw left hleft = ofRaw right hright) : left.Equiv right :=
  Quotient.exact h

def add (left right : Value) : Value :=
  Quotient.liftOn₂ left right
    (fun left right => ofRaw (ComplexCompute.add left.raw right.raw)
      (ComplexCompute.add_valid left.valid right.valid))
    (by
      intro left right left' right' hleft hright
      apply Quotient.sound
      exact ComplexCompute.add_equiv hleft hright)

def neg (value : Value) : Value :=
  Quotient.liftOn value
    (fun value => ofRaw (ComplexCompute.neg value.raw)
      (ComplexCompute.neg_valid value.valid))
    (by
      intro left right h
      apply Quotient.sound
      exact ComplexCompute.neg_equiv h)

def mul (left right : Value) : Value :=
  Quotient.liftOn₂ left right
    (fun left right => ofRaw (ComplexCompute.mul left.raw right.raw)
      (ComplexCompute.mul_valid left.valid right.valid))
    (by
      intro left right left' right' hleft hright
      apply Quotient.sound
      exact ComplexCompute.mul_equiv left.valid left'.valid right.valid
        right'.valid hleft hright)

def scaleRat (scalar : Rat) (value : Value) : Value :=
  Quotient.liftOn value
    (fun value => ofRaw (ComplexCompute.scaleRat scalar value.raw)
      (ComplexCompute.scaleRat_valid value.valid))
    (by
      intro left right h
      apply Quotient.sound
      exact ComplexCompute.scaleRat_equiv h)

instance : Add Value where add := add
instance : Neg Value where neg := neg
instance : Mul Value where mul := mul
instance : Zero Value where zero := ofQComplex QComplex.zero
instance : One Value where one := ofQComplex QComplex.one

@[simp] theorem ofRaw_add (left right : ComplexCompute)
    (hleft : left.Valid) (hright : right.Valid) :
    ofRaw (ComplexCompute.add left right) (ComplexCompute.add_valid hleft hright) =
      ofRaw left hleft + ofRaw right hright := rfl

@[simp] theorem ofRaw_neg (value : ComplexCompute) (hvalue : value.Valid) :
    ofRaw (ComplexCompute.neg value) (ComplexCompute.neg_valid hvalue) =
      -ofRaw value hvalue := rfl

@[simp] theorem ofRaw_mul (left right : ComplexCompute)
    (hleft : left.Valid) (hright : right.Valid) :
    ofRaw (ComplexCompute.mul left right) (ComplexCompute.mul_valid hleft hright) =
      ofRaw left hleft * ofRaw right hright := rfl

@[simp] theorem ofRaw_scaleRat (scalar : Rat) (value : ComplexCompute)
    (hvalue : value.Valid) :
    ofRaw (ComplexCompute.scaleRat scalar value)
      (ComplexCompute.scaleRat_valid hvalue) =
      scaleRat scalar (ofRaw value hvalue) := rfl

theorem add_comm (left right : Value) : left + right = right + left := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn right ?_
  intro right
  apply Quotient.sound
  exact ComplexCompute.add_comm_equiv left.raw right.raw left.valid right.valid

theorem add_assoc (left middle right : Value) :
    left + middle + right = left + (middle + right) := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn middle ?_
  intro middle
  refine Quotient.inductionOn right ?_
  intro right
  apply Quotient.sound
  exact ComplexCompute.add_assoc_equiv left.raw middle.raw right.raw
    left.valid middle.valid right.valid

theorem add_pairwise (a b c d : Value) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [add_assoc a b (c + d),
    ← add_assoc b c d,
    add_comm b c,
    add_assoc c b d,
    ← add_assoc a c (b + d)]

theorem add_zero (value : Value) : value + 0 = value := by
  refine Quotient.inductionOn value ?_
  intro value
  apply Quotient.sound
  exact ComplexCompute.add_zero_equiv value.raw value.valid

theorem zero_add (value : Value) : 0 + value = value := by
  rw [add_comm, add_zero]

theorem add_neg (value : Value) : value + -value = 0 := by
  refine Quotient.inductionOn value ?_
  intro value
  apply Quotient.sound
  exact ComplexCompute.add_neg_equiv value.raw value.valid

theorem mul_comm (left right : Value) : left * right = right * left := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn right ?_
  intro right
  apply Quotient.sound
  exact ComplexCompute.mul_comm_equiv left.raw right.raw left.valid right.valid

theorem mul_assoc (left middle right : Value) :
    left * middle * right = left * (middle * right) := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn middle ?_
  intro middle
  refine Quotient.inductionOn right ?_
  intro right
  apply Quotient.sound
  exact ComplexCompute.mul_assoc_equiv left.raw middle.raw right.raw
    left.valid middle.valid right.valid

theorem mul_one (value : Value) : value * 1 = value := by
  refine Quotient.inductionOn value ?_
  intro value
  apply Quotient.sound
  exact ComplexCompute.mul_one_equiv value.raw value.valid

theorem one_mul (value : Value) : 1 * value = value := by
  rw [mul_comm, mul_one]

theorem mul_zero (value : Value) : value * 0 = 0 := by
  refine Quotient.inductionOn value ?_
  intro value
  apply Quotient.sound
  exact ComplexCompute.mul_zero_equiv value.raw value.valid

theorem zero_mul (value : Value) : 0 * value = 0 := by
  rw [mul_comm, mul_zero]

theorem mul_add (left middle right : Value) :
    left * (middle + right) = left * middle + left * right := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn middle ?_
  intro middle
  refine Quotient.inductionOn right ?_
  intro right
  apply Quotient.sound
  exact ComplexCompute.mul_add_equiv left.raw middle.raw right.raw
    left.valid middle.valid right.valid

theorem add_mul (left middle right : Value) :
    (left + middle) * right = left * right + middle * right := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn middle ?_
  intro middle
  refine Quotient.inductionOn right ?_
  intro right
  apply Quotient.sound
  exact ComplexCompute.add_mul_equiv left.raw middle.raw right.raw
    left.valid middle.valid right.valid

theorem scaleRat_add (scalar : Rat) (left right : Value) :
    scaleRat scalar (left + right) =
      scaleRat scalar left + scaleRat scalar right := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn right ?_
  intro right
  apply Quotient.sound
  exact ComplexCompute.scaleRat_add_equiv scalar left.raw right.raw
    left.valid right.valid

theorem scaleRat_scaleRat (left right : Rat) (value : Value) :
    scaleRat left (scaleRat right value) =
      scaleRat (left * right) value := by
  refine Quotient.inductionOn value ?_
  intro value
  apply Quotient.sound
  exact ComplexCompute.scaleRat_scaleRat_equiv left right value.raw value.valid

theorem scaleRat_mul (scalar : Rat) (left right : Value) :
    scaleRat scalar (left * right) = scaleRat scalar left * right := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn right ?_
  intro right
  apply Quotient.sound
  exact ComplexCompute.scaleRat_mul_equiv scalar left.raw right.raw
    left.valid right.valid

theorem mul_scaleRat (scalar : Rat) (left right : Value) :
    left * scaleRat scalar right = scaleRat scalar (left * right) := by
  calc
    left * scaleRat scalar right = scaleRat scalar right * left :=
      mul_comm _ _
    _ = scaleRat scalar (right * left) :=
      (scaleRat_mul scalar right left).symm
    _ = scaleRat scalar (left * right) := by
      rw [mul_comm right left]

theorem scaleRat_mul_scaleRat (leftScalar rightScalar : Rat)
    (left right : Value) :
    scaleRat leftScalar left * scaleRat rightScalar right =
      scaleRat (leftScalar * rightScalar) (left * right) := by
  calc
    scaleRat leftScalar left * scaleRat rightScalar right =
        scaleRat leftScalar (left * scaleRat rightScalar right) :=
      (scaleRat_mul leftScalar left (scaleRat rightScalar right)).symm
    _ = scaleRat leftScalar (scaleRat rightScalar (left * right)) := by
      rw [mul_scaleRat]
    _ = scaleRat (leftScalar * rightScalar) (left * right) :=
      scaleRat_scaleRat leftScalar rightScalar (left * right)

theorem add_scaleRat (left right : Rat) (value : Value) :
    scaleRat left value + scaleRat right value =
      scaleRat (left + right) value := by
  refine Quotient.inductionOn value ?_
  intro value
  apply Quotient.sound
  exact ComplexCompute.add_scaleRat_equiv left right value.raw value.valid

theorem scaleRat_zero (scalar : Rat) : scaleRat scalar 0 = 0 := by
  apply Quotient.sound
  exact ComplexCompute.scaleRat_zero_equiv scalar

theorem scaleRat_zeroScalar (value : Value) : scaleRat 0 value = 0 := by
  refine Quotient.inductionOn value ?_
  intro value
  apply Quotient.sound
  exact ComplexCompute.scaleRat_zeroScalar_equiv value.raw value.valid

theorem scaleRat_one (value : Value) : scaleRat 1 value = value := by
  refine Quotient.inductionOn value ?_
  intro value
  apply Quotient.sound
  exact ComplexCompute.scaleRat_one_equiv value.raw value.valid

theorem neg_eq_scaleRat_neg_one (value : Value) :
    -value = scaleRat (-1) value := by
  refine Quotient.inductionOn value ?_
  intro value
  apply Quotient.sound
  exact ComplexCompute.neg_equiv_scaleRat_neg_one value.raw value.valid

theorem neg_add (left right : Value) :
    -(left + right) = -left + -right := by
  rw [neg_eq_scaleRat_neg_one,
    scaleRat_add,
    neg_eq_scaleRat_neg_one,
    neg_eq_scaleRat_neg_one]

theorem neg_scaleRat (scalar : Rat) (value : Value) :
    -(scaleRat scalar value) = scaleRat (-scalar) value := by
  rw [neg_eq_scaleRat_neg_one, scaleRat_scaleRat]
  congr 1
  grind

theorem neg_neg (value : Value) : -(-value) = value := by
  rw [neg_eq_scaleRat_neg_one, neg_eq_scaleRat_neg_one,
    scaleRat_scaleRat]
  have hone : (-1 : Rat) * -1 = 1 := by decide +kernel
  rw [hone, scaleRat_one]

/-- Cancellation pattern used by radial second derivatives: if `q*r=1`,
then `v*r^2*q=v*r`. -/
theorem mul_square_mul_of_mul_eq_one (q reciprocal value : Value)
    (hinverse : q * reciprocal = 1) :
    (value * (reciprocal * reciprocal)) * q = value * reciprocal := by
  calc
    (value * (reciprocal * reciprocal)) * q =
        value * ((reciprocal * reciprocal) * q) :=
      mul_assoc value (reciprocal * reciprocal) q
    _ = value * (reciprocal * (reciprocal * q)) := by
      rw [mul_assoc reciprocal reciprocal q]
    _ = value * (reciprocal * (q * reciprocal)) := by
      rw [mul_comm reciprocal q]
    _ = value * (reciprocal * 1) := by rw [hinverse]
    _ = value * reciprocal := by rw [mul_one]

end ComplexComputeQuotient
end ComputableAnalysis


