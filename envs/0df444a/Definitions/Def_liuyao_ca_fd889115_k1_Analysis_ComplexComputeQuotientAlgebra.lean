-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexComputeQuotientAlgebra
-- name    : liuyao_ca_fd889115_k1_Analysis_ComplexComputeQuotientAlgebra
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:52:34.715715+00:00
-- url     : https://prove2.me/theorems/8f0f506b-a556-453a-8fa0-ae2f1fcc4c35
-- title:
--   Computable analysis · ComplexComputeQuotientAlgebra · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ComplexComputeQuotientAlgebra.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexMultiplication

set_option autoImplicit true

/-!
# Finite quotient-algebra laws for represented complex values

The literal interval operations are intentionally not associative or
distributive as boxes: different evaluation trees lose different dependency
information.  They do, however, represent the same complex value.  Each law
below is proved at a finite stage by exhibiting one rational-complex point
contained in both result boxes.  Thus these are laws for `ComplexCompute.Equiv`,
not appeals to a pre-existing completed complex field.
-/

namespace ComputableAnalysis

namespace QBox

theorem overlaps_of_common_point {A B : QBox} {point : QComplex}
    (hA : A.lo <= point /\ point <= A.hi)
    (hB : B.lo <= point /\ point <= B.hi) : A.Overlaps B :=
  ⟨QComplex.le_trans hA.1 hB.2, QComplex.le_trans hB.1 hA.2⟩

theorem neg_contains {A : QBox} {point : QComplex}
    (hpoint : A.lo <= point /\ point <= A.hi) :
    (neg A).lo <= QComplex.neg point /\
      QComplex.neg point <= (neg A).hi := by
  change
    (-A.hi.re <= -point.re /\ -A.hi.im <= -point.im) /\
      (-point.re <= -A.lo.re /\ -point.im <= -A.lo.im)
  exact ⟨⟨Rat.neg_le_neg hpoint.2.1, Rat.neg_le_neg hpoint.2.2⟩,
    ⟨Rat.neg_le_neg hpoint.1.1, Rat.neg_le_neg hpoint.1.2⟩⟩

end QBox

namespace QComplex

theorem add_comm_cert (x y : QComplex) : add x y = add y x := by
  cases x; cases y; simp [add]
  constructor <;> exact Rat.add_comm _ _

theorem add_assoc_cert (x y z : QComplex) :
    add (add x y) z = add x (add y z) := by
  cases x; cases y; cases z; simp [add]
  constructor <;> exact Rat.add_assoc _ _ _

theorem zero_add_cert (x : QComplex) : add zero x = x := by
  cases x; simp [add, zero]
  constructor <;> grind

theorem add_zero_cert (x : QComplex) : add x zero = x := by
  cases x; simp [add, zero]
  constructor <;> grind

theorem add_neg_cert (x : QComplex) : add x (neg x) = zero := by
  cases x; simp [add, neg, zero]
  constructor <;> grind

theorem mul_comm_cert (x y : QComplex) : mul x y = mul y x := by
  cases x; cases y; simp [mul]
  constructor <;> grind [Rat.add_comm, Rat.mul_comm]

theorem one_mul_cert (x : QComplex) : mul one x = x := by
  rw [mul_comm_cert, mul_one_cert]

theorem zero_mul_cert (x : QComplex) : mul zero x = zero := by
  cases x; simp [mul, zero]
  constructor <;> grind

theorem mul_zero_cert (x : QComplex) : mul x zero = zero := by
  rw [mul_comm_cert, zero_mul_cert]

theorem scaleRat_add_cert (r : Rat) (x y : QComplex) :
    scaleRat r (add x y) = add (scaleRat r x) (scaleRat r y) := by
  cases x; cases y; simp [scaleRat, add]
  constructor <;> grind [Rat.mul_add]

theorem scaleRat_scaleRat_cert (r s : Rat) (x : QComplex) :
    scaleRat r (scaleRat s x) = scaleRat (r * s) x := by
  cases x; simp [scaleRat]
  constructor <;> grind [Rat.mul_assoc]

theorem scaleRat_mul_cert (r : Rat) (x y : QComplex) :
    scaleRat r (mul x y) = mul (scaleRat r x) y := by
  cases x; cases y; simp [scaleRat, mul]
  constructor <;> grind [Rat.mul_add, Rat.mul_assoc]

theorem add_scaleRat_cert (r s : Rat) (x : QComplex) :
    add (scaleRat r x) (scaleRat s x) = scaleRat (r + s) x := by
  cases x; simp [scaleRat, add]
  constructor <;> grind [Rat.add_mul]

theorem scaleRat_zero_cert (r : Rat) : scaleRat r zero = zero := by
  simp [scaleRat, zero]

theorem scaleRat_zeroScalar_cert (x : QComplex) : scaleRat 0 x = zero := by
  cases x; simp [scaleRat, zero]

theorem scaleRat_one_cert (x : QComplex) : scaleRat 1 x = x := by
  cases x; simp [scaleRat]

theorem scaleRat_neg_one_cert (x : QComplex) : scaleRat (-1) x = neg x := by
  cases x; simp [scaleRat, neg]
  constructor <;> grind

end QComplex

namespace ComplexCompute

private theorem equiv_of_common_points {left right : ComplexCompute}
    (points : Nat -> QComplex)
    (hleft : forall n,
      (left.compute n).lo <= points n /\ points n <= (left.compute n).hi)
    (hright : forall n,
      (right.compute n).lo <= points n /\ points n <= (right.compute n).hi) :
    left.Equiv right := by
  intro n
  apply (compareAt_overlap_iff left right n n).2
  exact QBox.overlaps_of_common_point (hleft n) (hright n)

theorem add_comm_equiv (z w : ComplexCompute) (hz : z.Valid) (hw : w.Valid) :
    (add z w).Equiv (add w z) := by
  let point := fun n => QComplex.add (z.compute n).center (w.compute n).center
  apply equiv_of_common_points point
  · intro n
    exact QBox.add_contains
      (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2
      (QBox.center_mem (valid_ordered hw n)).1
      (QBox.center_mem (valid_ordered hw n)).2
  · intro n
    dsimp [point]
    rw [QComplex.add_comm_cert]
    exact QBox.add_contains
      (QBox.center_mem (valid_ordered hw n)).1
      (QBox.center_mem (valid_ordered hw n)).2
      (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2

theorem add_assoc_equiv (x y z : ComplexCompute)
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid) :
    (add (add x y) z).Equiv (add x (add y z)) := by
  let point := fun n => QComplex.add
    (QComplex.add (x.compute n).center (y.compute n).center)
    (z.compute n).center
  apply equiv_of_common_points point
  · intro n
    have hxy := QBox.add_contains
      (QBox.center_mem (valid_ordered hx n)).1
      (QBox.center_mem (valid_ordered hx n)).2
      (QBox.center_mem (valid_ordered hy n)).1
      (QBox.center_mem (valid_ordered hy n)).2
    exact QBox.add_contains hxy.1 hxy.2
      (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2
  · intro n
    dsimp [point]
    rw [QComplex.add_assoc_cert]
    have hyz := QBox.add_contains
      (QBox.center_mem (valid_ordered hy n)).1
      (QBox.center_mem (valid_ordered hy n)).2
      (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2
    exact QBox.add_contains
      (QBox.center_mem (valid_ordered hx n)).1
      (QBox.center_mem (valid_ordered hx n)).2 hyz.1 hyz.2

theorem add_zero_equiv (z : ComplexCompute) (hz : z.Valid) :
    (add z zero).Equiv z := by
  let point := fun n => (z.compute n).center
  apply equiv_of_common_points point
  · intro n
    dsimp [point]
    rw [← QComplex.add_zero_cert (z.compute n).center]
    exact QBox.add_contains
      (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2
      (QComplex.le_refl _) (QComplex.le_refl _)
  · intro n
    exact QBox.center_mem (valid_ordered hz n)

theorem zero_add_equiv (z : ComplexCompute) (hz : z.Valid) :
    (add zero z).Equiv z :=
  equiv_trans (add_valid (ofQComplex_valid QComplex.zero) hz)
    (add_valid hz (ofQComplex_valid QComplex.zero)) hz
    (add_comm_equiv zero z (ofQComplex_valid QComplex.zero) hz)
    (add_zero_equiv z hz)

theorem add_neg_equiv (z : ComplexCompute) (hz : z.Valid) :
    (add z (neg z)).Equiv zero := by
  let point := fun _ : Nat => QComplex.zero
  apply equiv_of_common_points point
  · intro n
    dsimp [point]
    rw [← QComplex.add_neg_cert (z.compute n).center]
    have hcenter := QBox.center_mem (valid_ordered hz n)
    exact QBox.add_contains hcenter.1 hcenter.2
      (QBox.neg_contains hcenter).1 (QBox.neg_contains hcenter).2
  · intro _
    exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩

theorem mul_comm_equiv (z w : ComplexCompute) (hz : z.Valid) (hw : w.Valid) :
    (mul z w).Equiv (mul w z) := by
  let point := fun n => QComplex.mul (z.compute n).center (w.compute n).center
  apply equiv_of_common_points point
  · intro n
    exact QBox.mul_contains
      (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2
      (QBox.center_mem (valid_ordered hw n)).1
      (QBox.center_mem (valid_ordered hw n)).2
  · intro n
    dsimp [point]
    rw [QComplex.mul_comm_cert]
    exact QBox.mul_contains
      (QBox.center_mem (valid_ordered hw n)).1
      (QBox.center_mem (valid_ordered hw n)).2
      (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2

theorem mul_assoc_equiv (x y z : ComplexCompute)
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid) :
    (mul (mul x y) z).Equiv (mul x (mul y z)) := by
  let point := fun n => QComplex.mul
    (QComplex.mul (x.compute n).center (y.compute n).center)
    (z.compute n).center
  apply equiv_of_common_points point
  · intro n
    have hxy := QBox.mul_contains
      (QBox.center_mem (valid_ordered hx n)).1
      (QBox.center_mem (valid_ordered hx n)).2
      (QBox.center_mem (valid_ordered hy n)).1
      (QBox.center_mem (valid_ordered hy n)).2
    exact QBox.mul_contains hxy.1 hxy.2
      (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2
  · intro n
    dsimp [point]
    rw [QComplex.mul_assoc_cert]
    have hyz := QBox.mul_contains
      (QBox.center_mem (valid_ordered hy n)).1
      (QBox.center_mem (valid_ordered hy n)).2
      (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2
    exact QBox.mul_contains
      (QBox.center_mem (valid_ordered hx n)).1
      (QBox.center_mem (valid_ordered hx n)).2 hyz.1 hyz.2

theorem mul_one_equiv (z : ComplexCompute) (hz : z.Valid) :
    (mul z one).Equiv z := by
  let point := fun n => (z.compute n).center
  apply equiv_of_common_points point
  · intro n
    dsimp [point]
    rw [← QComplex.mul_one_cert (z.compute n).center]
    exact QBox.mul_contains
      (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2
      (QComplex.le_refl _) (QComplex.le_refl _)
  · intro n
    exact QBox.center_mem (valid_ordered hz n)

theorem one_mul_equiv (z : ComplexCompute) (hz : z.Valid) :
    (mul one z).Equiv z :=
  equiv_trans (mul_valid (ofQComplex_valid QComplex.one) hz)
    (mul_valid hz (ofQComplex_valid QComplex.one)) hz
    (mul_comm_equiv one z (ofQComplex_valid QComplex.one) hz)
    (mul_one_equiv z hz)

theorem mul_add_equiv (x y z : ComplexCompute)
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid) :
    (mul x (add y z)).Equiv (add (mul x y) (mul x z)) := by
  let point := fun n => QComplex.mul (x.compute n).center
    (QComplex.add (y.compute n).center (z.compute n).center)
  apply equiv_of_common_points point
  · intro n
    have hyz := QBox.add_contains
      (QBox.center_mem (valid_ordered hy n)).1
      (QBox.center_mem (valid_ordered hy n)).2
      (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2
    exact QBox.mul_contains
      (QBox.center_mem (valid_ordered hx n)).1
      (QBox.center_mem (valid_ordered hx n)).2 hyz.1 hyz.2
  · intro n
    dsimp [point]
    rw [QComplex.mul_add_cert]
    have hxy := QBox.mul_contains
      (QBox.center_mem (valid_ordered hx n)).1
      (QBox.center_mem (valid_ordered hx n)).2
      (QBox.center_mem (valid_ordered hy n)).1
      (QBox.center_mem (valid_ordered hy n)).2
    have hxz := QBox.mul_contains
      (QBox.center_mem (valid_ordered hx n)).1
      (QBox.center_mem (valid_ordered hx n)).2
      (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2
    exact QBox.add_contains hxy.1 hxy.2 hxz.1 hxz.2

theorem add_mul_equiv (x y z : ComplexCompute)
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid) :
    (mul (add x y) z).Equiv (add (mul x z) (mul y z)) := by
  exact equiv_trans
    (mul_valid (add_valid hx hy) hz)
    (mul_valid hz (add_valid hx hy))
    (add_valid (mul_valid hx hz) (mul_valid hy hz))
    (mul_comm_equiv (add x y) z (add_valid hx hy) hz)
    (equiv_trans
      (mul_valid hz (add_valid hx hy))
      (add_valid (mul_valid hz hx) (mul_valid hz hy))
      (add_valid (mul_valid hx hz) (mul_valid hy hz))
      (mul_add_equiv z x y hz hx hy)
      (add_equiv (mul_comm_equiv z x hz hx)
        (mul_comm_equiv z y hz hy)))

theorem scaleRat_add_equiv (r : Rat) (z w : ComplexCompute)
    (hz : z.Valid) (hw : w.Valid) :
    (scaleRat r (add z w)).Equiv
      (add (scaleRat r z) (scaleRat r w)) := by
  let point := fun n => QComplex.scaleRat r
    (QComplex.add (z.compute n).center (w.compute n).center)
  apply equiv_of_common_points point
  · intro n
    have hsum := QBox.add_contains
      (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2
      (QBox.center_mem (valid_ordered hw n)).1
      (QBox.center_mem (valid_ordered hw n)).2
    exact QBox.scaleRat_contains hsum.1 hsum.2
  · intro n
    dsimp [point]
    rw [QComplex.scaleRat_add_cert]
    have hzscale := QBox.scaleRat_contains
      (r := r) (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2
    have hwscale := QBox.scaleRat_contains
      (r := r) (QBox.center_mem (valid_ordered hw n)).1
      (QBox.center_mem (valid_ordered hw n)).2
    exact QBox.add_contains hzscale.1 hzscale.2 hwscale.1 hwscale.2

theorem scaleRat_scaleRat_equiv (r s : Rat) (z : ComplexCompute)
    (hz : z.Valid) :
    (scaleRat r (scaleRat s z)).Equiv (scaleRat (r * s) z) := by
  let point := fun n => QComplex.scaleRat r
    (QComplex.scaleRat s (z.compute n).center)
  apply equiv_of_common_points point
  · intro n
    have hs := QBox.scaleRat_contains
      (r := s) (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2
    exact QBox.scaleRat_contains hs.1 hs.2
  · intro n
    dsimp [point]
    rw [QComplex.scaleRat_scaleRat_cert]
    exact QBox.scaleRat_contains
      (r := r * s) (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2

theorem scaleRat_mul_equiv (r : Rat) (z w : ComplexCompute)
    (hz : z.Valid) (hw : w.Valid) :
    (scaleRat r (mul z w)).Equiv (mul (scaleRat r z) w) := by
  let point := fun n => QComplex.scaleRat r
    (QComplex.mul (z.compute n).center (w.compute n).center)
  apply equiv_of_common_points point
  · intro n
    have hmul := QBox.mul_contains
      (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2
      (QBox.center_mem (valid_ordered hw n)).1
      (QBox.center_mem (valid_ordered hw n)).2
    exact QBox.scaleRat_contains hmul.1 hmul.2
  · intro n
    dsimp [point]
    rw [QComplex.scaleRat_mul_cert]
    have hscale := QBox.scaleRat_contains
      (r := r) (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2
    exact QBox.mul_contains hscale.1 hscale.2
      (QBox.center_mem (valid_ordered hw n)).1
      (QBox.center_mem (valid_ordered hw n)).2

theorem add_scaleRat_equiv (r s : Rat) (z : ComplexCompute)
    (hz : z.Valid) :
    (add (scaleRat r z) (scaleRat s z)).Equiv
      (scaleRat (r + s) z) := by
  let point := fun n => QComplex.add
    (QComplex.scaleRat r (z.compute n).center)
    (QComplex.scaleRat s (z.compute n).center)
  apply equiv_of_common_points point
  · intro n
    have hr := QBox.scaleRat_contains
      (r := r) (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2
    have hs := QBox.scaleRat_contains
      (r := s) (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2
    exact QBox.add_contains hr.1 hr.2 hs.1 hs.2
  · intro n
    dsimp [point]
    rw [QComplex.add_scaleRat_cert]
    exact QBox.scaleRat_contains
      (r := r + s) (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2

theorem mul_zero_equiv (z : ComplexCompute) (hz : z.Valid) :
    (mul z zero).Equiv zero := by
  let point := fun _ : Nat => QComplex.zero
  apply equiv_of_common_points point
  · intro n
    dsimp [point]
    rw [← QComplex.mul_zero_cert (z.compute n).center]
    exact QBox.mul_contains
      (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2
      (QComplex.le_refl _) (QComplex.le_refl _)
  · intro _
    exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩

theorem zero_mul_equiv (z : ComplexCompute) (hz : z.Valid) :
    (mul zero z).Equiv zero :=
  equiv_trans (mul_valid (ofQComplex_valid QComplex.zero) hz)
    (mul_valid hz (ofQComplex_valid QComplex.zero))
    (ofQComplex_valid QComplex.zero)
    (mul_comm_equiv zero z (ofQComplex_valid QComplex.zero) hz)
    (mul_zero_equiv z hz)

theorem scaleRat_zero_equiv (r : Rat) :
    (scaleRat r zero).Equiv zero := by
  intro n
  apply (compareAt_overlap_iff (scaleRat r zero) zero n n).2
  have hpoint := QBox.scaleRat_contains (r := r)
    (A := QBox.point QComplex.zero)
    (QComplex.le_refl QComplex.zero) (QComplex.le_refl QComplex.zero)
  rw [QComplex.scaleRat_zero_cert] at hpoint
  exact QBox.overlaps_of_common_point hpoint
    ⟨QComplex.le_refl _, QComplex.le_refl _⟩

theorem scaleRat_zeroScalar_equiv (z : ComplexCompute) (hz : z.Valid) :
    (scaleRat 0 z).Equiv zero := by
  let point := fun _ : Nat => QComplex.zero
  apply equiv_of_common_points point
  · intro n
    dsimp [point]
    rw [← QComplex.scaleRat_zeroScalar_cert (z.compute n).center]
    exact QBox.scaleRat_contains
      (r := 0) (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2
  · intro _
    exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩

theorem scaleRat_one_equiv (z : ComplexCompute) (hz : z.Valid) :
    (scaleRat 1 z).Equiv z := by
  let point := fun n => (z.compute n).center
  apply equiv_of_common_points point
  · intro n
    dsimp [point]
    rw [← QComplex.scaleRat_one_cert (z.compute n).center]
    exact QBox.scaleRat_contains
      (r := 1) (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2
  · intro n
    exact QBox.center_mem (valid_ordered hz n)

theorem neg_equiv_scaleRat_neg_one (z : ComplexCompute) (hz : z.Valid) :
    (neg z).Equiv (scaleRat (-1) z) := by
  let point := fun n => QComplex.neg (z.compute n).center
  apply equiv_of_common_points point
  · intro n
    exact QBox.neg_contains (QBox.center_mem (valid_ordered hz n))
  · intro n
    dsimp [point]
    rw [← QComplex.scaleRat_neg_one_cert (z.compute n).center]
    exact QBox.scaleRat_contains
      (r := -1) (QBox.center_mem (valid_ordered hz n)).1
      (QBox.center_mem (valid_ordered hz n)).2

end ComplexCompute
end ComputableAnalysis


