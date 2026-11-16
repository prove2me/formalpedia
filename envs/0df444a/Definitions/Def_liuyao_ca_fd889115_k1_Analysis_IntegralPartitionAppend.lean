-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralPartitionAppend
-- name    : liuyao_ca_fd889115_k1_Analysis_IntegralPartitionAppend
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:55:10.2807+00:00
-- url     : https://prove2.me/theorems/704c6312-6988-4fd4-b797-c754288f62a2
-- title:
--   Computable analysis · IntegralPartitionAppend · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/IntegralPartitionAppend.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralBoundsComparison

set_option autoImplicit true

/-! Finite concatenation of adjacent rational partitions and rectangle
bounds. This supplies the finite arithmetic beneath integral additivity. -/
namespace ComputableAnalysis.Integral
set_option maxHeartbeats 1000000

def appendPartition {a b c : Rat} (P : RationalPartition a b) (Q : RationalPartition b c) : RationalPartition a c where
  pieces := P.pieces+Q.pieces
  positive := by have := P.positive; omega
  point := fun i => if i≤P.pieces then P.point i else Q.point (i-P.pieces)
  left_endpoint := by rw [if_pos (Nat.zero_le _),P.left_endpoint]
  right_endpoint := by
    rw [if_neg (by have := Q.positive; omega),Nat.add_sub_cancel_left,Q.right_endpoint]
  monotone := by
    intro i j hij hj
    by_cases hi : i≤P.pieces
    · by_cases hJ : j≤P.pieces
      · simp only [if_pos hi,if_pos hJ]; exact P.monotone i j hij hJ
      · simp only [if_pos hi,if_neg hJ]
        have hL := P.monotone i P.pieces hi (Nat.le_refl _)
        have hR := Q.monotone 0 (j-P.pieces) (Nat.zero_le _) (by omega)
        rw [P.right_endpoint] at hL
        rw [Q.left_endpoint] at hR
        exact Rat.le_trans hL hR
    · have hJ : ¬j≤P.pieces := by omega
      simp only [if_neg hi,if_neg hJ]
      exact Q.monotone (i-P.pieces) (j-P.pieces) (by omega) (by omega)

theorem appendPartition_left {a b c : Rat} (P : RationalPartition a b) (Q : RationalPartition b c)
    (i : Nat) (hi : i≤P.pieces) : (appendPartition P Q).point i=P.point i := by
  exact if_pos hi
theorem appendPartition_right {a b c : Rat} (P : RationalPartition a b) (Q : RationalPartition b c)
    (j : Nat) : (appendPartition P Q).point (P.pieces+j)=Q.point j := by
  by_cases hj : j=0
  · subst j
    simp only [Nat.add_zero,appendPartition,if_pos (Nat.le_refl _),P.right_endpoint,Q.left_endpoint]
  · change (if P.pieces+j≤P.pieces then _ else _)=_
    rw [if_neg (by omega),Nat.add_sub_cancel_left]

theorem rectangleSum_split (f : Nat → Rat) (m n : Nat) :
    rectangleSum f (m+n)=rectangleSum f m+rectangleSum (fun j => f (m+j)) n := by
  induction n with
  | zero => simp only [Nat.add_zero,rectangleSum,Rat.add_zero]
  | succ n ih =>
    rw [Nat.add_succ,rectangleSum,ih,rectangleSum]
    grind only

def appendBounds {F : FunctionOnInterval} (b : Rat) (hb0 : F.lower≤b) (hb1 : b≤F.upper)
    (A : Bounds (F.restrict F.lower b (Rat.le_refl) hb0 hb1))
    (B : Bounds (F.restrict b F.upper hb0 hb1 (Rat.le_refl))) : Bounds F where
  partition := appendPartition (a := F.lower) (b := b) (c := F.upper) A.partition B.partition
  lower := fun i => if i<A.partition.pieces then A.lower i else B.lower (i-A.partition.pieces)
  upper := fun i => if i<A.partition.pieces then A.upper i else B.upper (i-A.partition.pieces)
  lower_le := by
    intro i hi x hx n
    change i<A.partition.pieces+B.partition.pieces at hi
    by_cases hL : i<A.partition.pieces
    · change (if i<A.partition.pieces then _ else _)≤_
      rw [if_pos hL]
      change (appendPartition (a := F.lower) (b := b) (c := F.upper) A.partition B.partition).point i≤x ∧
        x≤(appendPartition (a := F.lower) (b := b) (c := F.upper) A.partition B.partition).point (i+1) at hx
      rw [appendPartition_left (a := F.lower) (b := b) (c := F.upper) A.partition B.partition i (by omega),appendPartition_left (a := F.lower) (b := b) (c := F.upper) A.partition B.partition (i+1) (by omega)] at hx
      exact A.lower_le i hL x hx n
    · let j := i-A.partition.pieces
      have hj : j<B.partition.pieces := by dsimp [j]; omega
      have he : i=A.partition.pieces+j := by dsimp [j]; omega
      have he1 : i+1=A.partition.pieces+(j+1) := by omega
      change (if i<A.partition.pieces then _ else _)≤_
      rw [if_neg hL]
      change (appendPartition (a := F.lower) (b := b) (c := F.upper) A.partition B.partition).point i≤x ∧
        x≤(appendPartition (a := F.lower) (b := b) (c := F.upper) A.partition B.partition).point (i+1) at hx
      rw [he1,he,appendPartition_right (a := F.lower) (b := b) (c := F.upper) A.partition B.partition,appendPartition_right (a := F.lower) (b := b) (c := F.upper) A.partition B.partition] at hx
      exact B.lower_le j hj x hx n
  upper_ge := by
    intro i hi x hx n
    change i<A.partition.pieces+B.partition.pieces at hi
    by_cases hL : i<A.partition.pieces
    · change _≤(if i<A.partition.pieces then _ else _)
      rw [if_pos hL]
      change (appendPartition (a := F.lower) (b := b) (c := F.upper) A.partition B.partition).point i≤x ∧
        x≤(appendPartition (a := F.lower) (b := b) (c := F.upper) A.partition B.partition).point (i+1) at hx
      rw [appendPartition_left (a := F.lower) (b := b) (c := F.upper) A.partition B.partition i (by omega),appendPartition_left (a := F.lower) (b := b) (c := F.upper) A.partition B.partition (i+1) (by omega)] at hx
      exact A.upper_ge i hL x hx n
    · let j := i-A.partition.pieces
      have hj : j<B.partition.pieces := by dsimp [j]; omega
      have he : i=A.partition.pieces+j := by dsimp [j]; omega
      have he1 : i+1=A.partition.pieces+(j+1) := by omega
      change _≤(if i<A.partition.pieces then _ else _)
      rw [if_neg hL]
      change (appendPartition (a := F.lower) (b := b) (c := F.upper) A.partition B.partition).point i≤x ∧
        x≤(appendPartition (a := F.lower) (b := b) (c := F.upper) A.partition B.partition).point (i+1) at hx
      rw [he1,he,appendPartition_right (a := F.lower) (b := b) (c := F.upper) A.partition B.partition,appendPartition_right (a := F.lower) (b := b) (c := F.upper) A.partition B.partition] at hx
      exact B.upper_ge j hj x hx n

theorem appendBounds_lowerSum {F : FunctionOnInterval} (b : Rat) (hb0 : F.lower≤b) (hb1 : b≤F.upper) (A B) :
    (appendBounds b hb0 hb1 A B).lowerSum=A.lowerSum+B.lowerSum := by
  change rectangleSum _ (A.partition.pieces+B.partition.pieces)=_
  rw [rectangleSum_split]
  congr 1
  · apply rectangleSum_congr
    intro i hi
    change ((appendPartition (a := F.lower) (b := b) (c := F.upper) A.partition B.partition).point (i+1)-(appendPartition (a := F.lower) (b := b) (c := F.upper) A.partition B.partition).point i)*
      (if i<A.partition.pieces then A.lower i else B.lower (i-A.partition.pieces))=_
    rw [appendPartition_left (a := F.lower) (b := b) (c := F.upper) A.partition B.partition (i+1) (by omega),appendPartition_left (a := F.lower) (b := b) (c := F.upper) A.partition B.partition i (by omega),if_pos hi]
  · apply rectangleSum_congr
    intro j hj
    change ((appendPartition (a := F.lower) (b := b) (c := F.upper) A.partition B.partition).point (A.partition.pieces+j+1)-
      (appendPartition (a := F.lower) (b := b) (c := F.upper) A.partition B.partition).point (A.partition.pieces+j))*
      (if A.partition.pieces+j<A.partition.pieces then _ else _)=_
    rw [show A.partition.pieces+j+1=A.partition.pieces+(j+1) by omega,
      appendPartition_right (a := F.lower) (b := b) (c := F.upper) A.partition B.partition,appendPartition_right (a := F.lower) (b := b) (c := F.upper) A.partition B.partition,if_neg (by omega),Nat.add_sub_cancel_left]

theorem appendBounds_upperSum {F : FunctionOnInterval} (b : Rat) (hb0 : F.lower≤b) (hb1 : b≤F.upper) (A B) :
    (appendBounds b hb0 hb1 A B).upperSum=A.upperSum+B.upperSum := by
  change rectangleSum _ (A.partition.pieces+B.partition.pieces)=_
  rw [rectangleSum_split]
  congr 1
  · apply rectangleSum_congr
    intro i hi
    change ((appendPartition (a := F.lower) (b := b) (c := F.upper) A.partition B.partition).point (i+1)-(appendPartition (a := F.lower) (b := b) (c := F.upper) A.partition B.partition).point i)*
      (if i<A.partition.pieces then A.upper i else B.upper (i-A.partition.pieces))=_
    rw [appendPartition_left (a := F.lower) (b := b) (c := F.upper) A.partition B.partition (i+1) (by omega),appendPartition_left (a := F.lower) (b := b) (c := F.upper) A.partition B.partition i (by omega),if_pos hi]
  · apply rectangleSum_congr
    intro j hj
    change ((appendPartition (a := F.lower) (b := b) (c := F.upper) A.partition B.partition).point (A.partition.pieces+j+1)-
      (appendPartition (a := F.lower) (b := b) (c := F.upper) A.partition B.partition).point (A.partition.pieces+j))*
      (if A.partition.pieces+j<A.partition.pieces then _ else _)=_
    rw [show A.partition.pieces+j+1=A.partition.pieces+(j+1) by omega,
      appendPartition_right (a := F.lower) (b := b) (c := F.upper) A.partition B.partition,appendPartition_right (a := F.lower) (b := b) (c := F.upper) A.partition B.partition,if_neg (by omega),Nat.add_sub_cancel_left]

end ComputableAnalysis.Integral


