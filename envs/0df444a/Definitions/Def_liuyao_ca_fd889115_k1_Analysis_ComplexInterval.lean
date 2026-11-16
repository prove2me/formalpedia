-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexInterval
-- name    : liuyao_ca_fd889115_k1_Analysis_ComplexInterval
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:52:34.428337+00:00
-- url     : https://prove2.me/theorems/18e02bff-8c4c-46c5-9cd7-3d4cb53269b7
-- title:
--   Computable analysis · ComplexInterval · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ComplexInterval.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexPolynomial
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexMultiplication

set_option autoImplicit true

namespace ComputableAnalysis

namespace QBox

def evalPoly (coeffs : CPoly.Coeffs) (Z : QBox) : QBox :=
  coeffs.foldr (fun c acc => add (point c) (mul Z acc)) zero

theorem add_point (z w : QComplex) :
    add (point z) (point w) = point (QComplex.add z w) := by
  rfl

theorem mul_point (z w : QComplex) :
    mul (point z) (point w) = point (QComplex.mul z w) := by
  simp [mul, mulRealInterval, point, QComplex.mul, min4, max4, minRat, maxRat2]

theorem evalPoly_point (coeffs : CPoly.Coeffs) (z : QComplex) :
    evalPoly coeffs (point z) = point (CPoly.eval coeffs z) := by
  induction coeffs with
  | nil => rfl
  | cons c cs ih =>
      change add (point c) (mul (point z) (evalPoly cs (point z))) =
        point (QComplex.add c (QComplex.mul z (CPoly.eval cs z)))
      rw [ih]
      rw [mul_point, add_point]

/-- The finite Horner evaluator for a rational complex box contains the value
of the polynomial at every rational point enclosed by that box.  This is the
soundness interface needed by root-exclusion and subdivision certificates;
it makes no claim about a global root theorem. -/
theorem evalPoly_contains {coeffs : CPoly.Coeffs} {Z : QBox} {z : QComplex}
    (hzlo : Z.lo <= z) (hzhi : z <= Z.hi) :
    (evalPoly coeffs Z).lo <= CPoly.eval coeffs z /\
      CPoly.eval coeffs z <= (evalPoly coeffs Z).hi := by
  induction coeffs with
  | nil =>
      exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
  | cons c cs ih =>
      change
        (add (point c) (mul Z (evalPoly cs Z))).lo <=
            QComplex.add c (QComplex.mul z (CPoly.eval cs z)) /\
          QComplex.add c (QComplex.mul z (CPoly.eval cs z)) <=
            (add (point c) (mul Z (evalPoly cs Z))).hi
      have htail := ih
      have hmul := mul_contains hzlo hzhi htail.1 htail.2
      have hadd := add_contains (A := point c) (C := mul Z (evalPoly cs Z))
        (QComplex.le_refl c) (QComplex.le_refl c) hmul.1 hmul.2
      exact hadd

/-- If the output box misses zero, the input box contains no root.  This is
the finite discard step used by rational box subdivision. -/
theorem evalPoly_no_root_of_not_overlaps_zero
    {coeffs : CPoly.Coeffs} {Z : QBox} {z : QComplex}
    (hzlo : Z.lo <= z) (hzhi : z <= Z.hi)
    (hmiss : ¬ QBox.Overlaps (evalPoly coeffs Z) QBox.zero) :
    CPoly.eval coeffs z ≠ QComplex.zero := by
  intro hroot
  apply hmiss
  unfold QBox.Overlaps QBox.zero QBox.point
  change (evalPoly coeffs Z).lo <= QComplex.zero /\
    QComplex.zero <= (evalPoly coeffs Z).hi
  have hcontains := evalPoly_contains (coeffs := coeffs) (Z := Z) (z := z) hzlo hzhi
  simpa [hroot] using hcontains

def zeroAround (eps : QPos) : QBox :=
  { lo := { re := -eps.val, im := -eps.val },
    hi := { re := eps.val, im := eps.val } }

end QBox

def IsApproxRootAt (coeffs : CPoly.Coeffs) (z : ComplexCompute) (n : Nat) : Prop :=
  let eps : QPos :=
    if hn : n = 0 then
      { val := 1, property := by decide +kernel }
    else
      { val := (1 / (n : Rat)), property := by
          rw [Rat.div_def, Rat.one_mul]
          exact (Rat.inv_pos).2 ((Rat.natCast_pos).2 (Nat.pos_of_ne_zero hn)) }
  QBox.Overlaps (QBox.evalPoly coeffs (z.compute n)) (QBox.zeroAround eps)

def approxRootCheck (coeffs : CPoly.Coeffs) (z : ComplexCompute) (n : Nat) : Bool :=
  let eps : QPos :=
    if hn : n = 0 then
      { val := 1, property := by decide +kernel }
    else
      { val := (1 / (n : Rat)), property := by
          rw [Rat.div_def, Rat.one_mul]
          exact (Rat.inv_pos).2 ((Rat.natCast_pos).2 (Nat.pos_of_ne_zero hn)) }
  QBox.overlaps (QBox.evalPoly coeffs (z.compute n)) (QBox.zeroAround eps)

end ComputableAnalysis


