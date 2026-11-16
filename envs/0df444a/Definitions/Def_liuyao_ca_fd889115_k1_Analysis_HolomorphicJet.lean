-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_HolomorphicJet
-- name    : liuyao_ca_fd889115_k1_Analysis_HolomorphicJet
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:50:25.608383+00:00
-- url     : https://prove2.me/theorems/f27b45d9-45f4-4be2-afa6-71952fa5c7f6
-- title:
--   Computable analysis · HolomorphicJet · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/HolomorphicJet.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Basic

set_option autoImplicit true

/-!
# Finite rational-complex first jets

A first jet stores the value and proposed complex derivative of a function at
one rational complex point.  The operations below are executable and encode
the algebraic sum, product, reciprocal, and chain rules.  They are the finite
local data carried by the later computable holomorphic-chart evaluator; this
module alone makes no convergence or holomorphicity claim.
-/

namespace ComputableAnalysis

namespace QComplex

/-- Total rational-complex inverse formula.  Its field law requires the
separate nonzero norm certificate below. -/
def inverse (z : QComplex) : QComplex :=
  let n := normSq z
  { re := z.re / n, im := -z.im / n }

theorem mul_inverse_of_normSq_ne_zero (z : QComplex)
    (hnorm : normSq z ≠ 0) :
    mul z (inverse z) = one := by
  have hmap := mul_inv?_eq_one (z := z) hnorm
  simpa [inv?, inverse, hnorm] using hmap

theorem mul_comm_cert (x y : QComplex) : mul x y = mul y x := by
  cases x
  cases y
  simp [mul]
  constructor <;> grind [Rat.mul_comm, Rat.add_comm,
    Rat.sub_eq_add_neg]

theorem one_mul_cert (x : QComplex) : mul one x = x := by
  rw [mul_comm_cert]
  exact mul_one_cert x

theorem add_neg_self_cert (x : QComplex) : add x (neg x) = zero := by
  cases x
  simp [add, neg, zero]
  constructor <;> grind

theorem zero_add_cert (x : QComplex) : add zero x = x := by
  cases x with
  | mk re im =>
      change QComplex.mk (0 + re) (0 + im) = QComplex.mk re im
      rw [Rat.zero_add, Rat.zero_add]

theorem add_zero_cert (x : QComplex) : add x zero = x := by
  cases x with
  | mk re im =>
      change QComplex.mk (re + 0) (im + 0) = QComplex.mk re im
      rw [Rat.add_zero, Rat.add_zero]

theorem add_assoc_cert (x y z : QComplex) :
    add (add x y) z = add x (add y z) := by
  cases x
  cases y
  cases z
  simp [add]
  constructor <;> grind [Rat.add_assoc]

end QComplex

namespace HolomorphicJet

/-- Exact first-order rational-complex data at one chart point. -/
structure FirstJet where
  value : QComplex
  derivative : QComplex
deriving Repr, DecidableEq

theorem FirstJet.extensionality (left right : FirstJet)
    (hvalue : left.value = right.value)
    (hderivative : left.derivative = right.derivative) :
    left = right := by
  cases left
  cases right
  simp_all

def constant (value : QComplex) : FirstJet where
  value := value
  derivative := QComplex.zero

def identity (point : QComplex) : FirstJet where
  value := point
  derivative := QComplex.one

def neg (jet : FirstJet) : FirstJet where
  value := QComplex.neg jet.value
  derivative := QComplex.neg jet.derivative

def add (left right : FirstJet) : FirstJet where
  value := QComplex.add left.value right.value
  derivative := QComplex.add left.derivative right.derivative

def scaleRat (scalar : Rat) (jet : FirstJet) : FirstJet where
  value := QComplex.scaleRat scalar jet.value
  derivative := QComplex.scaleRat scalar jet.derivative

/-- Product rule as an executable operation on first jets. -/
def mul (left right : FirstJet) : FirstJet where
  value := QComplex.mul left.value right.value
  derivative := QComplex.add
    (QComplex.mul left.derivative right.value)
    (QComplex.mul left.value right.derivative)

/-- Chain rule as an executable operation on first jets.  `outer` is the jet
at `inner.value`. -/
def compose (outer inner : FirstJet) : FirstJet where
  value := outer.value
  derivative := QComplex.mul outer.derivative inner.derivative

/-- Reciprocal-rule jet.  The nonzero certificate makes its value an actual
inverse rather than merely a totalized rational expression. -/
def reciprocalOfNonzero (jet : FirstJet)
    (_hnorm : QComplex.normSq jet.value ≠ 0) : FirstJet where
  value := QComplex.inverse jet.value
  derivative := QComplex.neg
    (QComplex.mul
      (QComplex.mul (QComplex.inverse jet.value)
        (QComplex.inverse jet.value))
      jet.derivative)

@[simp] theorem add_value (left right : FirstJet) :
    (add left right).value = QComplex.add left.value right.value := rfl

@[simp] theorem add_derivative (left right : FirstJet) :
    (add left right).derivative =
      QComplex.add left.derivative right.derivative := rfl

@[simp] theorem mul_value (left right : FirstJet) :
    (mul left right).value = QComplex.mul left.value right.value := rfl

@[simp] theorem mul_derivative (left right : FirstJet) :
    (mul left right).derivative = QComplex.add
      (QComplex.mul left.derivative right.value)
      (QComplex.mul left.value right.derivative) := rfl

@[simp] theorem compose_value (outer inner : FirstJet) :
    (compose outer inner).value = outer.value := rfl

@[simp] theorem compose_derivative (outer inner : FirstJet) :
    (compose outer inner).derivative =
      QComplex.mul outer.derivative inner.derivative := rfl

theorem mul_reciprocalOfNonzero (jet : FirstJet)
    (hnorm : QComplex.normSq jet.value ≠ 0) :
    mul jet (reciprocalOfNonzero jet hnorm) =
      constant QComplex.one := by
  apply FirstJet.extensionality
  · exact QComplex.mul_inverse_of_normSq_ne_zero jet.value hnorm
  · simp only [mul, reciprocalOfNonzero, constant]
    let inverse := QComplex.inverse jet.value
    have hinverse : QComplex.mul jet.value inverse = QComplex.one :=
      QComplex.mul_inverse_of_normSq_ne_zero jet.value hnorm
    rw [QComplex.mul_neg_cert]
    have hreassociate :
        QComplex.mul jet.value
            (QComplex.mul (QComplex.mul inverse inverse) jet.derivative) =
          QComplex.mul (QComplex.mul jet.value inverse)
            (QComplex.mul inverse jet.derivative) := by
      rw [← QComplex.mul_assoc_cert,
        ← QComplex.mul_assoc_cert jet.value inverse inverse,
        QComplex.mul_assoc_cert]
    rw [hreassociate, hinverse, QComplex.one_mul_cert,
      QComplex.mul_comm_cert inverse jet.derivative,
      QComplex.add_neg_self_cert]

end HolomorphicJet

end ComputableAnalysis


