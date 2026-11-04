-- Prove2me | Definitions.Def_Submission_ThreeSum_WeightEnumeration
-- name    : Submission_ThreeSum_WeightEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:45:47.372261+00:00
-- url     : https://prove2.me/theorems/159549e0-a2ae-431f-a6f2-bc26c7a14701
-- title:
--   Weight Enumeration
-- statement:
--   Definitions and structural lemmas for Weight Enumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightEnumeration.lean

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Mathlib.Data.List.Range
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices


set_option autoImplicit false
namespace ThreeSum.WeightEnumeration
open LocalHashMoments
variable {ι K : Type*} [DecidableEq ι] [NatCast K]
theorem range_blocks (m q : ℕ) :
    (List.range m).flatMap (fun b => (List.range q).map (fun r => b*q+r)) =
      List.range (m*q) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.range_succ,List.flatMap_append,List.flatMap_singleton,ih,Nat.succ_mul]
    exact List.range_add.symm
def decode (p : ℕ) : (l : List ι) → ℕ → (∀ i, i ∈ l → K)
  | [], _ => List.Pi.nil (fun _ => K)
  | i::l, k => List.Pi.cons i l ((k/p^l.length%p : ℕ) : K) (decode p l (k%p^l.length))
theorem pi_eq_range (p : ℕ) (l : List ι) :
    List.pi l (fun _ => (List.range p).map (fun n : ℕ => (n : K))) =
      (List.range (p^l.length)).map (decode (K := K) p l) := by
  induction l with
  | nil => simp [decode]
  | cons i l ih =>
    rw [List.pi_cons,ih]
    simp only [List.flatMap_map,List.map_map,List.length_cons,pow_succ',← range_blocks,
      List.map_flatMap]
    apply List.flatMap_congr
    intro b hb
    have hbp : b < p := List.mem_range.mp hb
    apply List.map_congr_left
    intro r hr
    have hrq : r < p^l.length := List.mem_range.mp hr
    have hq : 0 < p^l.length := by omega
    have hdiv : (b*p^l.length+r)/p^l.length = b := by
      rw [Nat.add_comm,Nat.add_mul_div_right _ _ hq,Nat.div_eq_of_lt hrq]
      simp
    simp only [Function.comp_apply,decode,hdiv,Nat.mod_eq_of_lt hbp,
      Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hrq]
theorem low_digit (p n e t : ℕ) (he : e < t) :
    (n%p^t)/p^e%p = n/p^e%p := by
  have hpow : p^t = p^e*p^(t-e) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow,Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (dvd_pow_self p (by omega : t-e ≠ 0))]
theorem decode_eq_digit (p : ℕ) (l : List ι) (k : ℕ) (i : ι) (hi : i ∈ l) :
    decode (K := K) p l k i hi = ((k/p^(l.length-1-l.idxOf i)%p : ℕ) : K) := by
  induction l generalizing k i with
  | nil => simp at hi
  | cons a l ih =>
    by_cases hia : i = a
    · subst i
      simp [decode,List.Pi.cons_def]
    · have hil : i ∈ l := (List.mem_cons.mp hi).resolve_left hia
      have hidx : l.idxOf i < l.length := List.idxOf_lt_length_of_mem hil
      simp only [decode,List.Pi.cons_def,dif_neg hia]
      rw [ih (k%p^l.length) i hil,List.idxOf_cons_ne _ (Ne.symm hia)]
      simp only [List.length_cons,Nat.succ_sub_one]
      rw [show l.length-(l.idxOf i+1) = l.length-1-l.idxOf i by omega]
      exact congrArg (fun n : ℕ => (n : K)) (low_digit p k _ _ (by omega))
def liftCoordinate {L : ℕ} (i : Fin L × Bool) : Fin (L+1) × Bool := (i.1.succ,i.2)
theorem liftCoordinate_injective (L : ℕ) :
    Function.Injective (@liftCoordinate L) := by
  intro i j hij
  apply Prod.ext
  · exact Fin.succ_injective L (congrArg Prod.fst hij)
  · exact congrArg (fun z : Fin (L+1) × Bool => z.2) hij
theorem coordinates_succ (L : ℕ) :
    coordinates (L+1) = (0,false)::(0,true)::(coordinates L).map liftCoordinate := by
  simp only [coordinates,List.finRange_succ,List.flatMap_cons,List.flatMap_map,
    List.map_flatMap,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    liftCoordinate]
theorem coordinates_length (L : ℕ) : (coordinates L).length = 2*L := by
  induction L with
  | zero => simp [coordinates]
  | succ L ih =>
    rw [coordinates_succ]
    simp only [List.length_cons,List.length_map,ih]
    omega
def coordinateIndex {L : ℕ} (i : Fin L × Bool) : ℕ :=
  2*i.1.val+(if i.2 then 1 else 0)
theorem coordinates_idxOf {L : ℕ} (i : Fin L × Bool) :
    (coordinates L).idxOf i = coordinateIndex i := by
  rcases i with ⟨i,b⟩
  induction L with
  | zero => exact Fin.elim0 i
  | succ L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · cases b <;> simp [coordinates_succ,coordinateIndex]
    · have hmap : ((coordinates L).map liftCoordinate).idxOf (j.succ,b) =
          (coordinates L).idxOf (j,b) := by
        change ((coordinates L).map liftCoordinate).idxOf (liftCoordinate (j,b)) = _
        simp only [List.idxOf,List.findIdx_map,Function.comp_def,
          (liftCoordinate_injective L).beq_eq]
      have hne : (0 : Fin (L+1)) ≠ j.succ := by
        intro he
        have hh := congrArg Fin.val he
        simp only [Fin.val_zero,Fin.val_succ] at hh
        omega
      rw [coordinates_succ]
      simp only [List.idxOf_cons,cond_eq_ite,beq_iff_eq,Prod.mk.injEq,hne,false_and,
        ite_false,hmap,ih j]
      unfold coordinateIndex
      simp only [Fin.val_succ]
      omega
def digit (p width k coordinate : ℕ) : ℕ := k/p^(width-1-coordinate)%p
def decodedWeight (L p k : ℕ) : Weight L K :=
  fun i => (digit p (2*L) k (coordinateIndex i) : K)
theorem allWeights_eq_range (L p : ℕ) :
    allWeights L ((List.range p).map (fun n : ℕ => (n : K))) =
      (List.range (p^(2*L))).map (decodedWeight (K := K) L p) := by
  unfold allWeights
  rw [pi_eq_range,List.map_map,coordinates_length]
  apply List.map_congr_left
  intro k hk
  funext i
  have hidx := coordinates_idxOf i
  simp only [List.idxOf,Bool.beq_eq_decide_eq] at hidx
  simp only [Function.comp_apply,decode_eq_digit,coordinates_length,
    decodedWeight,digit,List.idxOf,Bool.beq_eq_decide_eq,hidx]
theorem allWeights_length (L p : ℕ) :
    (allWeights L ((List.range p).map (fun n : ℕ => (n : K)))).length = p^(2*L) := by
  rw [allWeights_eq_range,List.length_map,List.length_range]
end ThreeSum.WeightEnumeration


