-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexAffine
-- name    : liuyao_ca_fd889115_k1_Analysis_ComplexAffine
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:50:26.765498+00:00
-- url     : https://prove2.me/theorems/c07ef229-c658-4ab8-bfda-2d9ffe6bf343
-- title:
--   Computable analysis · ComplexAffine · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ComplexAffine.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Basic

set_option autoImplicit true

/-!
# Certified affine complex operations

The general interval product of two represented complex values is certified
in `ComplexMultiplication`.  This file keeps the useful exact-scalar layer:
a rational complex constant acts on any certified complex raw by
coordinatewise affine interval operations.  In particular, multiplication by
the rational imaginary unit agrees with the existing endpoint-reversing
`mulI` operation.

No completed complex plane or imported complex-number library is used here.
-/

namespace ComputableAnalysis

namespace ComplexCompute

/-- Negation transports same-stage complex-box overlap. -/
theorem neg_equiv {z w : ComplexCompute} (hzw : z.Equiv w) :
    (neg z).Equiv (neg w) := by
  intro n
  have hover := (compareAt_overlap_iff z w n n).1 (hzw n)
  apply (compareAt_overlap_iff (neg z) (neg w) n n).2
  change QBox.Overlaps
    { lo := { re := -(z.compute n).hi.re, im := -(z.compute n).hi.im },
      hi := { re := -(z.compute n).lo.re, im := -(z.compute n).lo.im } }
    { lo := { re := -(w.compute n).hi.re, im := -(w.compute n).hi.im },
      hi := { re := -(w.compute n).lo.re, im := -(w.compute n).lo.im } }
  unfold QBox.Overlaps at hover ⊢
  exact ⟨
    ⟨Rat.neg_le_neg hover.2.1, Rat.neg_le_neg hover.2.2⟩,
    ⟨Rat.neg_le_neg hover.1.1, Rat.neg_le_neg hover.1.2⟩⟩

/-- A negative scalar action is the positive action of its negation after
box negation.  This finite identity lets the existing positive-scale proof
serve every rational scalar. -/
private theorem scaleRat_neg_compute_eq (r : Rat) (hr : ¬ 0 <= r)
    (z : ComplexCompute) :
    (fun n => QBox.scaleRat r (z.compute n)) =
      (fun n => QBox.scaleRat (-r) (QBox.neg (z.compute n))) := by
  funext n
  have hneg : r < 0 := (Rat.not_le).1 hr
  have hpos : 0 <= -r := by grind
  simp only [QBox.scaleRat, QBox.neg, if_neg hr, if_pos hpos]
  congr 1 <;> grind [Rat.neg_mul, Rat.mul_neg]

/-- Every rational scalar preserves validity of a complex raw.  The
nonnegative case is the existing direct endpoint calculation; the negative
case is reduced to it through `scaleRat_neg_compute_eq`. -/
theorem scaleRat_valid {r : Rat} {z : ComplexCompute}
    (hz : z.Valid) : (scaleRat r z).Valid := by
  by_cases hr : 0 <= r
  · exact scaleRat_valid_of_nonneg hr hz
  · have hpos : 0 <= -r := by
      have hneg : r < 0 := (Rat.not_le).1 hr
      grind
    have hvalid := scaleRat_valid_of_nonneg hpos (neg_valid hz)
    change ComplexCompute.ValidCompute (fun n => QBox.scaleRat r (z.compute n))
    change ComplexCompute.ValidCompute
      (fun n => QBox.scaleRat (-r) (QBox.neg (z.compute n))) at hvalid
    rw [scaleRat_neg_compute_eq r hr z]
    exact hvalid

/-- Rational scalar actions respect complex raw equivalence, including the
endpoint reversal required by negative scalars. -/
theorem scaleRat_equiv {r : Rat} {z w : ComplexCompute}
    (hzw : z.Equiv w) : (scaleRat r z).Equiv (scaleRat r w) := by
  by_cases hr : 0 <= r
  · exact scaleRat_equiv_of_nonneg hr hzw
  · intro n
    have hneg : r < 0 := (Rat.not_le).1 hr
    have hpos : 0 <= -r := by grind
    have hover := (compareAt_overlap_iff z w n n).1 (hzw n)
    apply (compareAt_overlap_iff (scaleRat r z) (scaleRat r w) n n).2
    simp only [scaleRat, QBox.scaleRat, if_neg hr]
    change QBox.Overlaps
      { lo := { re := r * (z.compute n).hi.re, im := r * (z.compute n).hi.im },
        hi := { re := r * (z.compute n).lo.re, im := r * (z.compute n).lo.im } }
      { lo := { re := r * (w.compute n).hi.re, im := r * (w.compute n).hi.im },
        hi := { re := r * (w.compute n).lo.re, im := r * (w.compute n).lo.im } }
    unfold QBox.Overlaps at hover ⊢
    constructor
    · constructor
      · have h := Rat.mul_le_mul_of_nonneg_left hover.2.1 hpos
        grind [Rat.neg_mul]
      · have h := Rat.mul_le_mul_of_nonneg_left hover.2.2 hpos
        grind [Rat.neg_mul]
    · constructor
      · have h := Rat.mul_le_mul_of_nonneg_left hover.1.1 hpos
        grind [Rat.neg_mul]
      · have h := Rat.mul_le_mul_of_nonneg_left hover.1.2 hpos
        grind [Rat.neg_mul]

/-- Addition transports equivalences of both complex raw operands. -/
theorem add_equiv {z z' w w' : ComplexCompute}
    (hzz' : z.Equiv z') (hww' : w.Equiv w') :
    (add z w).Equiv (add z' w') := by
  intro n
  have hz := (compareAt_overlap_iff z z' n n).1 (hzz' n)
  have hw := (compareAt_overlap_iff w w' n n).1 (hww' n)
  apply (compareAt_overlap_iff (add z w) (add z' w') n n).2
  change QBox.Overlaps
    { lo := QComplex.add (z.compute n).lo (w.compute n).lo,
      hi := QComplex.add (z.compute n).hi (w.compute n).hi }
    { lo := QComplex.add (z'.compute n).lo (w'.compute n).lo,
      hi := QComplex.add (z'.compute n).hi (w'.compute n).hi }
  unfold QBox.Overlaps QComplex.add
  exact ⟨
    ⟨rat_add_le_add hz.1.1 hw.1.1, rat_add_le_add hz.1.2 hw.1.2⟩,
    ⟨rat_add_le_add hz.2.1 hw.2.1, rat_add_le_add hz.2.2 hw.2.2⟩⟩

/-- The rational complex unit on the positive imaginary axis. -/
def imaginaryUnit : QComplex := { re := 0, im := 1 }

/-- Left multiplication by an exact rational complex scalar, expanded into
its two real coordinate actions.  Unlike the future represented-by-
represented product, this is already a certified affine operation. -/
def qcomplexLeftMul (c : QComplex) (z : ComplexCompute) : ComplexCompute :=
  scaleRat c.re z + scaleRat c.im (mulI z)

/-- Exact rational complex scalars preserve validity of a complex raw. -/
theorem qcomplexLeftMul_valid (c : QComplex) {z : ComplexCompute}
    (hz : z.Valid) : (qcomplexLeftMul c z).Valid := by
  unfold qcomplexLeftMul
  apply add_valid
  · exact scaleRat_valid hz
  · exact scaleRat_valid (mulI_valid hz)

/-- Exact rational complex scalars preserve equivalence of represented
complex values. -/
theorem qcomplexLeftMul_equiv (c : QComplex) {z w : ComplexCompute}
    (hzw : z.Equiv w) :
    (qcomplexLeftMul c z).Equiv (qcomplexLeftMul c w) := by
  unfold qcomplexLeftMul
  apply add_equiv
  · exact scaleRat_equiv hzw
  · exact scaleRat_equiv (mulI_equiv hzw)

/-- On exact rational complex inputs, the affine raw construction evaluates
to the ordinary finite rational complex product. -/
theorem qcomplexLeftMul_ofQComplex (c z : QComplex) :
    (qcomplexLeftMul c (ofQComplex z)).Equiv
      (ofQComplex (QComplex.mul c z)) := by
  intro n
  apply (compareAt_overlap_iff (qcomplexLeftMul c (ofQComplex z))
    (ofQComplex (QComplex.mul c z)) n n).2
  change QBox.Overlaps
    (QBox.add
      (QBox.scaleRat c.re (QBox.point z))
      (QBox.scaleRat c.im
        { lo := { re := -z.im, im := z.re },
          hi := { re := -z.im, im := z.re } }))
    (QBox.point (QComplex.mul c z))
  unfold QBox.add QBox.scaleRat QBox.point QComplex.mul QComplex.add
    QBox.Overlaps
  by_cases hcr : 0 <= c.re
  · by_cases hci : 0 <= c.im
    · simp [hcr, hci]
      constructor <;> grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
        Rat.mul_comm, Rat.sub_eq_add_neg]
    · simp [hcr, hci]
      constructor <;> grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
        Rat.mul_comm, Rat.sub_eq_add_neg]
  · by_cases hci : 0 <= c.im
    · simp [hcr, hci]
      constructor <;> grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
        Rat.mul_comm, Rat.sub_eq_add_neg]
    · simp [hcr, hci]
      constructor <;> grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
        Rat.mul_comm, Rat.sub_eq_add_neg]

/-- At every stage, exact affine multiplication by `i` is the direct
coordinate rotation `mulI`. -/
theorem qcomplexLeftMul_imaginaryUnit_compute (z : ComplexCompute) (n : Nat) :
    (qcomplexLeftMul imaginaryUnit z).compute n = (mulI z).compute n := by
  change QBox.add (QBox.scaleRat 0 (z.compute n))
    (QBox.scaleRat 1
      { lo := { re := -(z.compute n).hi.im, im := (z.compute n).lo.re },
        hi := { re := -(z.compute n).lo.im, im := (z.compute n).hi.re } }) =
    { lo := { re := -(z.compute n).hi.im, im := (z.compute n).lo.re },
      hi := { re := -(z.compute n).lo.im, im := (z.compute n).hi.re } }
  have h0 : (0 : Rat) <= 0 := by decide +kernel
  have h1 : (0 : Rat) <= 1 := by decide +kernel
  simp only [QBox.add, QBox.scaleRat, QComplex.add, if_pos h0, if_pos h1,
    Rat.zero_mul, Rat.one_mul]
  congr 1 <;> congr 1 <;> exact Rat.zero_add _

/-- The exact complex-algebra action of `i` is equivalent to `mulI` on every
certified complex raw. -/
theorem qcomplexLeftMul_imaginaryUnit_equiv {z : ComplexCompute}
    (hz : z.Valid) : (qcomplexLeftMul imaginaryUnit z).Equiv (mulI z) := by
  intro n
  apply (compareAt_overlap_iff (qcomplexLeftMul imaginaryUnit z) (mulI z) n n).2
  rw [qcomplexLeftMul_imaginaryUnit_compute]
  have hordered := valid_ordered (mulI_valid hz) n
  exact ⟨hordered, hordered⟩

end ComplexCompute

end ComputableAnalysis


