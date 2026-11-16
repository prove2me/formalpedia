-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexComputeQuotientRing
-- name    : liuyao_ca_fd889115_k1_Analysis_ComplexComputeQuotientRing
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:53:22.451512+00:00
-- url     : https://prove2.me/theorems/9b485acc-4f7c-4975-8095-2cbf5aeb8e88
-- title:
--   Computable analysis · ComplexComputeQuotientRing · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ComplexComputeQuotientRing.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexComputeQuotient

set_option autoImplicit true

/-!
# Polynomial normalization over certified interval computations

This is only a proof-facing `grind` instance on the existing quotient of
valid raw algorithms. Every ring law comes from the checked finite box
comparisons; no completed real or complex field is introduced.
-/

namespace ComputableAnalysis.ComplexComputeQuotient

def ofRat (q : Rat) : Value := ofQComplex (QComplex.ofRat q)

theorem ofRat_add (a b : Rat) : ofRat (a + b) = ofRat a + ofRat b := by
  apply Quotient.sound
  intro n
  apply (ComplexCompute.compareAt_overlap_iff _ _ n n).2
  simp [ComplexCompute.ofQComplex, ComplexCompute.add,
    QBox.add, QComplex.add, QComplex.ofRat, QBox.Overlaps,
    QComplex.le_def]
  grind

theorem ofRat_neg (a : Rat) : ofRat (-a) = -ofRat a := by
  apply Quotient.sound
  intro n
  apply (ComplexCompute.compareAt_overlap_iff _ _ n n).2
  simp [ComplexCompute.ofQComplex, ComplexCompute.neg,
    QBox.neg, QComplex.ofRat, QBox.Overlaps,
    QComplex.le_def]

private def power (a : Value) : Nat → Value
  | 0 => 1
  | n + 1 => power a n * a

instance : Lean.Grind.CommRing Value where
  natCast := ⟨fun n => ofRat (n : Rat)⟩
  ofNat := fun n => ⟨ofRat (n : Rat)⟩
  intCast := ⟨fun n => ofRat (n : Rat)⟩
  nsmul := ⟨fun n a => ofRat (n : Rat) * a⟩
  zsmul := ⟨fun n a => ofRat (n : Rat) * a⟩
  npow := ⟨power⟩
  sub := fun a b => a + -b
  add_zero := add_zero
  add_comm := add_comm
  add_assoc := add_assoc
  mul_assoc := mul_assoc
  mul_one := mul_one
  one_mul := one_mul
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_comm := mul_comm
  neg_add_cancel := fun a => by rw [add_comm]; exact add_neg a
  sub_eq_add_neg := fun _ _ => rfl
  pow_zero := fun _ => rfl
  pow_succ := fun _ _ => rfl
  ofNat_succ := fun n => by
    change ofRat ((n + 1 : Nat) : Rat) = ofRat (n : Rat) + ofRat 1
    rw [Rat.natCast_add, ofRat_add]
    rfl
  neg_zsmul := fun n a => by
    change ofRat ((-n : Int) : Rat) * a = -(ofRat (n : Rat) * a)
    rw [Rat.intCast_neg, ofRat_neg]
    rw [neg_eq_scaleRat_neg_one, ← scaleRat_mul, ← neg_eq_scaleRat_neg_one]
  zsmul_natCast_eq_nsmul := fun _ _ => rfl
  intCast_ofNat := fun _ => rfl
  intCast_neg := fun n => by
    change ofRat ((-n : Int) : Rat) = -ofRat (n : Rat)
    rw [Rat.intCast_neg, ofRat_neg]

end ComputableAnalysis.ComplexComputeQuotient


