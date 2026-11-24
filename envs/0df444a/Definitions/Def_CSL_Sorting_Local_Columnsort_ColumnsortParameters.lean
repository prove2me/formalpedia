-- Prove2me | Definitions.Def_CSL_Sorting_Local_Columnsort_ColumnsortParameters
-- name    : CSL_Sorting_Local_Columnsort_ColumnsortParameters
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:20:51.087389+00:00
-- url     : https://prove2.me/theorems/b1bfadbf-f7fa-4035-b007-4f1406c3e7e8
-- title:
--   Coded sorting library: Sorting / Local / Columnsort / ColumnsortParameters
-- statement:
--   Module `CodedSorting.Sorting.Local.Columnsort.ColumnsortParameters` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Finite-layout and permutation accounting for grouped Columnsort
--
--   Companion to the actual zero-one sortedness proof. This file keeps data
--   conservation separate from sortedness, including the finite sentinel window.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Sorting.Local.Columnsort.ColumnsortParameters

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Sorting_Local_Columnsort_Columnsort
import Mathlib.Order.TypeTags
import Mathlib.Order.WithBot

section ColumnsortPermutation
/-!
# Finite-layout and permutation accounting for grouped Columnsort

Companion to the actual zero-one sortedness proof. This file keeps data
conservation separate from sortedness, including the finite sentinel window.
-/

set_option maxHeartbeats 800000

namespace CSL.Columnsort

open scoped BigOperators

/-- Swap the first two coordinates, retaining the record offset. -/
def exchangeOuter (α β γ : Type*) : α × (β × γ) ≃ β × (α × γ) where
  toFun p := (p.2.1, p.1, p.2.2)
  invFun p := (p.2.1, p.1, p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact source permutation for distributing whole groups cyclically. -/
def stripeEquiv (q s g : ℕ) : Fin s × Fin (q*g) ≃ Fin (q*s*g) :=
  ((Equiv.prodCongr (Equiv.refl (Fin s)) finProdFinEquiv.symm).trans
    (exchangeOuter (Fin s) (Fin q) (Fin g))).trans
    ((Equiv.prodCongr (Equiv.refl (Fin q)) finProdFinEquiv).trans
      (finProdFinEquiv.trans (finCongr (Nat.mul_assoc q s g).symm)))

theorem stripeEquiv_val (q s g : ℕ) (p : Fin s × Fin (q*g)) :
    (stripeEquiv q s g p).val = stripeIndex s g p.1.val p.2.val := by
  change (p.2.val % g + g*p.1.val) + (s*g)*(p.2.val/g) =
    (p.2.val/g*s+p.1.val)*g+p.2.val%g
  ring

/-- Recombining all residue streams retains every zero of an original column. -/
theorem stripe_zeroCount_sum (q s g : ℕ) (hg : 0 < g)
    (f : Fin (q*s*g) → Bool) :
    ∑ c : Fin s, zeroCount (stripe q s g hg c f) = zeroCount f := by
  have hf : (fun p : Fin s × Fin (q*g) => stripe q s g hg p.1 f p.2) =
      sortColumn f ∘ stripeEquiv q s g := by
    funext p
    apply congrArg (sortColumn f)
    apply Fin.ext
    exact (stripeEquiv_val q s g p).symm
  change (∑ c : Fin s, zeroCount (fun i : Fin (q*g) => stripe q s g hg c f i)) = _
  rw [← zeroCount_prod (fun p : Fin s × Fin (q*g) => stripe q s g hg p.1 f p.2),
    hf, zeroCount_equiv, zeroCount_sortColumn]

/-- Source order after undoing the group transpose is exactly group-row,
column, record-offset order. Its zero count equals the complete input's. -/
theorem afterStepFour_zeroCount (q s g : ℕ) (hg : 0 < g)
    (f : Fin s → Fin (q*s*g) → Bool) :
    zeroCount (fun p : Fin (s*q) × (Fin s × Fin g) =>
      afterStepFour q s g hg f p.1 p.2.1 p.2.2) = ∑ a, zeroCount (f a) := by
  let e := exchangeOuter (Fin s) (Fin (s*q)) (Fin g)
  have hperm := zeroCount_equiv e
    (fun p : Fin (s*q) × (Fin s × Fin g) =>
      afterStepFour q s g hg f p.1 p.2.1 p.2.2)
  rw [← hperm, zeroCount_prod]
  have hcol (c : Fin s) :
      zeroCount (fun p : Fin (s*q) × Fin g => afterStepFour q s g hg f p.1 c p.2) =
      zeroCount (newColumn q s g hg c f) := by
    let eqv : Fin (s*q) × Fin g ≃ Fin (s*(q*g)) :=
      finProdFinEquiv.trans (finCongr (Nat.mul_assoc s q g))
    have hf : (fun p : Fin (s*q) × Fin g => afterStepFour q s g hg f p.1 c p.2) =
        sortColumn (newColumn q s g hg c f) ∘ eqv := by
      funext p
      apply congrArg (sortColumn (newColumn q s g hg c f))
      apply Fin.ext
      change p.1.val*g+p.2.val = p.2.val+g*p.1.val
      ring
    rw [hf, zeroCount_equiv, zeroCount_sortColumn]
  change (∑ c : Fin s, zeroCount (fun p : Fin (s*q) × Fin g =>
    afterStepFour q s g hg f p.1 c p.2)) = _
  simp_rw [hcol, newColumn_zeroCount_eq]
  rw [Finset.sum_comm]
  simp_rw [stripe_zeroCount_sum]

/-- Exact flat-layout decoder, including the complete within-group offset. -/
def stepFourEquiv (q s g : ℕ) : Fin (s*q*(s*g)) ≃ Fin (s*q) × (Fin s × Fin g) :=
  finProdFinEquiv.symm.trans
    (Equiv.prodCongr (Equiv.refl (Fin (s*q))) finProdFinEquiv.symm)

theorem stepFourTape_at_fin (q s g : ℕ) (hg : 0 < g)
    (f : Fin s → Fin (q*s*g) → Bool) (i : Fin (s*q*(s*g))) :
    stepFourTape q s g hg f (i : ℤ) =
      afterStepFour q s g hg f (stepFourEquiv q s g i).1
        (stepFourEquiv q s g i).2.1 (stepFourEquiv q s g i).2.2 := by
  have h : (0 : ℤ) ≤ i ∧ (i : ℤ) < ((s*q*(s*g) : ℕ) : ℤ) := by
    constructor
    · exact_mod_cast (Nat.zero_le i.val)
    · exact_mod_cast i.isLt
  simp only [stepFourTape, dif_pos h, Int.toNat_natCast]
  rfl

theorem stepFourTape_zeroCount (q s g : ℕ) (hg : 0 < g)
    (f : Fin s → Fin (q*s*g) → Bool) :
    zeroCount (fun i : Fin (s*q*(s*g)) => stepFourTape q s g hg f (i : ℤ)) =
      ∑ a, zeroCount (f a) := by
  have hf : (fun i : Fin (s*q*(s*g)) => stepFourTape q s g hg f (i : ℤ)) =
      (fun p : Fin (s*q) × (Fin s × Fin g) =>
        afterStepFour q s g hg f p.1 p.2.1 p.2.2) ∘ stepFourEquiv q s g := by
    funext i
    exact stepFourTape_at_fin q s g hg f i
  rw [hf, zeroCount_equiv, afterStepFour_zeroCount]

/-- Sorting a finite consecutive collection of complete columns retains
exactly its zero count. The statement uses the actual blockSort execution. -/
theorem blockSort_window_zeroCount (B : ℕ) (hB : 0 < B) (n : ℕ) (offset : ℤ)
    (f : ℤ → Bool) :
    zeroCount (fun i : Fin (n*B) => blockSort B hB offset f (offset+(i : ℤ))) =
      zeroCount (fun i : Fin (n*B) => f (offset+(i : ℤ))) := by
  have hsplit (F : ℤ → Bool) :
      zeroCount (fun i : Fin (n*B) => F (offset+(i : ℤ))) =
        ∑ c : Fin n, zeroCount (fun j : Fin B => F (offset+(c : ℤ)*B+(j : ℤ))) := by
    have he := zeroCount_equiv (@finProdFinEquiv n B)
      (fun i : Fin (n*B) => F (offset+(i : ℤ)))
    rw [← he, zeroCount_prod]
    apply Finset.sum_congr rfl
    intro c _
    apply congrArg zeroCount
    funext j
    change F (offset + (finProdFinEquiv (c,j) : ℤ)) = F (offset+(c : ℤ)*B+(j : ℤ))
    apply congrArg F
    change offset+((j.val+B*c.val : ℕ) : ℤ) = offset+(c : ℤ)*B+(j : ℤ)
    push_cast
    ring
  rw [hsplit, hsplit]
  apply Finset.sum_congr rfl
  intro c _
  have hc : (fun j : Fin B => blockSort B hB offset f (offset+(c : ℤ)*B+(j : ℤ))) =
      sortColumn (fun j : Fin B => f (offset+(c : ℤ)*B+(j : ℤ))) := by
    funext j
    have hj0 : (0 : ℤ) ≤ j := by exact_mod_cast (Nat.zero_le j.val)
    have hjB : (j : ℤ) < (B : ℤ) := by exact_mod_cast j.isLt
    have ho := blockOrigin_eq B hB offset c (offset+(c : ℤ)*B+(j : ℤ))
      (by omega) (by nlinarith)
    have hs := blockSlot_address B hB offset (offset+(c : ℤ)*B+(j : ℤ))
    rw [ho] at hs
    have hslot : blockSlot B hB offset (offset+(c : ℤ)*B+(j : ℤ)) = j := by
      apply Fin.ext
      exact_mod_cast (show (blockSlot B hB offset (offset+(c : ℤ)*B+(j : ℤ)) : ℤ) =
        (j : ℤ) by omega)
    simp only [blockSort, ho, hslot]
  rw [hc, zeroCount_sortColumn]

theorem zeroCount_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι ⊕ κ → Bool) :
    zeroCount f = zeroCount (fun i => f (.inl i)) + zeroCount (fun i => f (.inr i)) := by
  let e : {p : ι ⊕ κ // f p = false} ≃
      ({i : ι // f (.inl i) = false} ⊕ {i : κ // f (.inr i) = false}) :=
    { toFun := fun p => match p with
        | ⟨.inl i, h⟩ => .inl ⟨i,h⟩
        | ⟨.inr i, h⟩ => .inr ⟨i,h⟩
      invFun := fun p => match p with
        | .inl i => ⟨.inl i.val,i.property⟩
        | .inr i => ⟨.inr i.val,i.property⟩
      left_inv := fun p => by rcases p with ⟨_ | _, _⟩ <;> rfl
      right_inv := fun p => by cases p <;> rfl }
  simpa only [zeroCount, Fintype.card_sum] using Fintype.card_congr e

/-- Number of zero records in a specified finite physical interval. -/
def windowZeros (f : ℤ → Bool) (offset : ℤ) (n : ℕ) : ℕ :=
  zeroCount (fun i : Fin n => f (offset+(i : ℤ)))

theorem windowZeros_add (f : ℤ → Bool) (offset : ℤ) (m n : ℕ) :
    windowZeros f offset (m+n) = windowZeros f offset m + windowZeros f (offset+m) n := by
  have he := zeroCount_equiv (@finSumFinEquiv m n)
    (fun i : Fin (m+n) => f (offset+(i : ℤ)))
  change zeroCount _ = _
  rw [← he, zeroCount_sum]
  congr 1
  apply congrArg zeroCount
  funext j
  change f (offset+((m+j.val : ℕ) : ℤ)) = f (offset+m+(j : ℤ))
  congr 1
  push_cast
  ring

theorem padded_windowZeros (f : ℤ → Bool) (N H : ℕ) (h : Band f 0 N) :
    windowZeros f (-H) (H+N+H) = H + windowZeros f 0 N := by
  have hleft : windowZeros f (-H) H = H := by
    have hf : (fun i : Fin H => f (-(H : ℤ)+(i : ℤ))) = fun _ => false := by
      funext i
      apply h.1
      have hi : (i : ℤ) < (H : ℤ) := by exact_mod_cast i.isLt
      omega
    unfold windowZeros
    rw [hf]
    simp [zeroCount]
  have hright : windowZeros f N H = 0 := by
    have hf : (fun i : Fin H => f ((N : ℤ)+(i : ℤ))) = fun _ => true := by
      funext i
      apply h.2
      have hi : (0 : ℤ) ≤ i := by exact_mod_cast Nat.zero_le i.val
      omega
    unfold windowZeros
    rw [hf]
    simp [zeroCount]
  rw [windowZeros_add, windowZeros_add, hleft]
  have he : -(H : ℤ)+(H : ℤ) = 0 := by omega
  have he' : -(H : ℤ)+((H+N : ℕ) : ℤ) = (N : ℤ) := by omega
  rw [he, he', hright, Nat.add_zero]

/-- Removing the H sentinels at each end after a half-shifted column sort
preserves every ordinary zero. The sentinel values remain in their own
prefix/suffix, established from the actual local sorting operation. -/
theorem shiftedSort_zeroCount (H : ℕ) (hH : 0 < H) (n : ℕ)
    (f : ℤ → Bool) (h : Band f 0 ((n*(2*H) : ℕ) : ℤ)) :
    windowZeros (blockSort (2*H) (by omega) (-H) f) 0 (n*(2*H)) =
      windowZeros f 0 (n*(2*H)) := by
  have hB : 0 < 2*H := by omega
  have hc := blockSort_window_zeroCount (2*H) hB (n+1) (-H) f
  change windowZeros _ _ _ = windowZeros _ _ _ at hc
  have hlen : (n+1)*(2*H) = H+n*(2*H)+H := by ring
  rw [hlen, padded_windowZeros _ _ _ (blockSort_band (2*H) hB (-H) f _ _ h),
    padded_windowZeros _ _ _ h] at hc
  exact Nat.add_left_cancel hc

/-- The integer sentinel extension agrees with the exact finite data interval. -/
theorem stepFourTape_outer_band (q s g : ℕ) (hg : 0 < g)
    (f : Fin s → Fin (q*s*g) → Bool) :
    Band (stepFourTape q s g hg f) 0 ((s*q*(s*g) : ℕ) : ℤ) := by
  constructor
  · intro i hi
    have hn : ¬(0 ≤ i ∧ i < (s*q*(s*g) : ℕ)) := by omega
    rw [stepFourTape, dif_neg hn, if_pos hi]
  · intro i hi
    have hn : ¬(0 ≤ i ∧ i < (s*q*(s*g) : ℕ)) := by exact fun h => not_lt_of_ge hi h.2
    have h0 : ¬i<0 := by
      have hz : (0 : ℤ) ≤ ((s*q*(s*g) : ℕ) : ℤ) := by exact_mod_cast Nat.zero_le (s*q*(s*g))
      omega
    rw [stepFourTape, dif_neg hn, if_neg h0]

/-- Conservation of all zero records by the complete concrete eight-step
algorithm, including both sentinel insertions/deletions. -/
theorem groupedColumnsort01_zeroCount (q s g H : ℕ) (hg : 0 < g) (hH : 0 < H)
    (hheight : q*s*g = 2*H) (f : Fin s → Fin (q*s*g) → Bool) :
    zeroCount (groupedColumnsort01 q s g H hg hH f) = ∑ a, zeroCount (f a) := by
  have hB : 0 < 2*H := by omega
  have hN : s*q*(s*g) = s*(2*H) := by rw [← hheight]; ring
  let F := stepFourTape q s g hg f
  have hb : Band F 0 ((s*(2*H) : ℕ) : ℤ) := by
    rw [← hN]
    exact stepFourTape_outer_band q s g hg f
  have hb' := blockSort_band (2*H) hB 0 F _ _ hb
  have hs := shiftedSort_zeroCount H hH s (blockSort (2*H) hB 0 F) hb'
  have hc := blockSort_window_zeroCount (2*H) hB s 0 F
  change windowZeros _ 0 _ = windowZeros _ 0 _ at hc
  have hresult := hs.trans hc
  rw [← hN] at hresult
  have hresult' : zeroCount (groupedColumnsort01 q s g H hg hH f) =
      zeroCount (fun i : Fin (s*q*(s*g)) => F (i : ℤ)) := by
    simp only [windowZeros, zero_add, F] at hresult
    exact hresult
  exact hresult'.trans (stepFourTape_zeroCount q s g hg f)

/-- For equal-length bit arrays, equality of zero counts is precisely enough
for data conservation; the conclusion is the standard List.Perm relation. -/
theorem perm_of_zeroCount_eq {n : ℕ} (f h : Fin n → Bool)
    (heq : zeroCount f = zeroCount h) : (List.ofFn f).Perm (List.ofFn h) := by
  have hs : sortColumn f = sortColumn h := by
    funext i
    have hiff : sortColumn f i = false ↔ sortColumn h i = false := by
      rw [sortColumn_false_iff, sortColumn_false_iff, heq]
    cases hf : sortColumn f i <;> cases hh : sortColumn h i <;> simp_all
  exact (sortColumn_perm f).symm.trans (hs ▸ sortColumn_perm h)

/-- The ordinary input column-major order, with no discarded coordinates. -/
def inputEquiv (q s g : ℕ) : Fin (s*q*(s*g)) ≃ Fin s × Fin (q*s*g) :=
  (finCongr (show s*q*(s*g) = s*(q*s*g) by ring)).trans finProdFinEquiv.symm

def flattenInput (q s g : ℕ) (f : Fin s → Fin (q*s*g) → Bool) :
    Fin (s*q*(s*g)) → Bool := fun i => f (inputEquiv q s g i).1 (inputEquiv q s g i).2

theorem flattenInput_zeroCount (q s g : ℕ) (f : Fin s → Fin (q*s*g) → Bool) :
    zeroCount (flattenInput q s g f) = ∑ a, zeroCount (f a) := by
  change zeroCount ((fun p : Fin s × Fin (q*s*g) => f p.1 p.2) ∘ inputEquiv q s g) = _
  rw [zeroCount_equiv, zeroCount_prod]

/-- Complete zero-one permutation correctness, including sentinel deletion.
Together with groupedColumnsort01_pairwise this proves both requirements
of a correct zero-one sort for the actual eight-step algorithm. -/
theorem groupedColumnsort01_perm (q s g H : ℕ) (hg : 0 < g) (hH : 0 < H)
    (hheight : q*s*g = 2*H) (f : Fin s → Fin (q*s*g) → Bool) :
    (List.ofFn (groupedColumnsort01 q s g H hg hH f)).Perm
      (List.ofFn (flattenInput q s g f)) := by
  apply perm_of_zeroCount_eq
  rw [groupedColumnsort01_zeroCount q s g H hg hH hheight, flattenInput_zeroCount]

/-- Both ordinary sorting obligations, for every zero-one input. -/
theorem groupedColumnsort01_correct (q s g H : ℕ)
    (hs : 0 < s) (hg : 0 < g) (hH : 0 < H)
    (hheight : q*s*g = 2*H) (hr : 2*s*(s+1) ≤ q*s)
    (f : Fin s → Fin (q*s*g) → Bool) :
    (List.ofFn (groupedColumnsort01 q s g H hg hH f)).Pairwise (· ≤ ·) ∧
    (List.ofFn (groupedColumnsort01 q s g H hg hH f)).Perm
      (List.ofFn (flattenInput q s g f)) :=
  ⟨groupedColumnsort01_pairwise q s g H hs hg hH hheight hr f,
    groupedColumnsort01_perm q s g H hg hH hheight f⟩

end CSL.Columnsort
end ColumnsortPermutation

section ColumnsortKeys
/-!
# Grouped Columnsort for arbitrary ordered keys

This module defines the same eight operations for keys in a bounded linear
order and proves that every threshold execution agrees with the verified
zero-one algorithm. Adjoining bottom and top gives the usual two sentinels
for any linearly ordered key type. No intermediate sortedness is assumed.
-/

namespace CSL.Columnsort

variable {α : Type*} [LinearOrder α]

/-- Actual residue-class stream after sorting an original key column. -/
def stripeKeys (q s g : ℕ) (hg : 0 < g) (c : Fin s)
    (f : Fin (q*s*g) → α) : Fin (q*g) → α := fun i =>
  sortColumn f ⟨stripeIndex s g c.val i.val,
    stripeIndex_lt q s g c.val i.val hg c.isLt i.isLt⟩

def newColumnKeys (q s g : ℕ) (hg : 0 < g) (c : Fin s)
    (f : Fin s → Fin (q*s*g) → α) : Fin (s*(q*g)) → α := fun i =>
  let p := finProdFinEquiv.symm i
  stripeKeys q s g hg c (f p.1) p.2

def afterStepFourKeys (q s g : ℕ) (hg : 0 < g)
    (f : Fin s → Fin (q*s*g) → α) (u : Fin (s*q)) (c : Fin s) (v : Fin g) : α :=
  sortColumn (newColumnKeys q s g hg c f)
    ⟨u.val*g+v.val, by have := u.isLt; have := v.isLt; nlinarith⟩

/-- Generic keys are sorted using exactly the same finite sorting permutation. -/
def blockSortKeys (B : ℕ) (hB : 0 < B) (offset : ℤ) (f : ℤ → α) : ℤ → α :=
  fun i => sortColumn (fun j : Fin B => f (blockOrigin B offset i+(j : ℤ)))
    (blockSlot B hB offset i)

variable [OrderBot α] [OrderTop α]

def stepFourTapeKeys (q s g : ℕ) (hg : 0 < g)
    (f : Fin s → Fin (q*s*g) → α) (i : ℤ) : α :=
  if hi : 0 ≤ i ∧ i < (s*q*(s*g) : ℕ) then
    let j : Fin (s*q*(s*g)) := ⟨i.toNat, (Int.toNat_lt hi.1).2 hi.2⟩
    let p : Fin (s*q) × Fin (s*g) := finProdFinEquiv.symm j
    let cv : Fin s × Fin g := finProdFinEquiv.symm p.2
    afterStepFourKeys q s g hg f p.1 cv.1 cv.2
  else if i < 0 then ⊥ else ⊤

/-- Concrete grouped Columnsort, with the sentinel positions deleted from
the returned finite tuple. -/
def groupedColumnsort (q s g H : ℕ) (hg : 0 < g) (hH : 0 < H)
    (f : Fin s → Fin (q*s*g) → α) : Fin (s*q*(s*g)) → α := fun i =>
  blockSortKeys (2*H) (by omega) (-H)
    (blockSortKeys (2*H) (by omega) 0 (stepFourTapeKeys q s g hg f)) (i : ℤ)

/-- Column-major input order, retaining each ordinary record exactly once. -/
def flattenKeys (q s g : ℕ) (f : Fin s → Fin (q*s*g) → α) :
    Fin (s*q*(s*g)) → α := fun i => f (inputEquiv q s g i).1 (inputEquiv q s g i).2

omit [OrderBot α] [OrderTop α] in
/-- Every monotone threshold commutes with the actual first redistribution. -/
theorem map_stripeKeys (q s g : ℕ) (hg : 0 < g) (c : Fin s)
    (f : Fin (q*s*g) → α) (θ : α → Bool) (hθ : Monotone θ) :
    θ ∘ stripeKeys q s g hg c f = stripe q s g hg c (θ ∘ f) := by
  have h := monotone_map_sortColumn f θ hθ
  funext i
  exact congrFun h _

omit [OrderBot α] [OrderTop α] in
theorem map_newColumnKeys (q s g : ℕ) (hg : 0 < g) (c : Fin s)
    (f : Fin s → Fin (q*s*g) → α) (θ : α → Bool) (hθ : Monotone θ) :
    θ ∘ newColumnKeys q s g hg c f = newColumn q s g hg c (fun a => θ ∘ f a) := by
  funext i
  exact congrFun (map_stripeKeys q s g hg c _ θ hθ) _

omit [OrderBot α] [OrderTop α] in
theorem map_afterStepFourKeys (q s g : ℕ) (hg : 0 < g)
    (f : Fin s → Fin (q*s*g) → α) (θ : α → Bool) (hθ : Monotone θ)
    (u : Fin (s*q)) (c : Fin s) (v : Fin g) :
    θ (afterStepFourKeys q s g hg f u c v) =
      afterStepFour q s g hg (fun a => θ ∘ f a) u c v := by
  have h := monotone_map_sortColumn (newColumnKeys q s g hg c f) θ hθ
  rw [map_newColumnKeys q s g hg c f θ hθ] at h
  exact congrFun h _

omit [OrderBot α] [OrderTop α] in
theorem map_blockSortKeys (B : ℕ) (hB : 0 < B) (offset : ℤ)
    (f : ℤ → α) (θ : α → Bool) (hθ : Monotone θ) :
    θ ∘ blockSortKeys B hB offset f = blockSort B hB offset (θ ∘ f) := by
  funext i
  exact congrFun (monotone_map_sortColumn
    (fun j : Fin B => f (blockOrigin B offset i+(j : ℤ))) θ hθ) _

/-- Sentinels map to the two distinct bits of the zero-one execution. -/
theorem map_stepFourTapeKeys (q s g : ℕ) (hg : 0 < g)
    (f : Fin s → Fin (q*s*g) → α) (θ : α → Bool) (hθ : Monotone θ)
    (hbot : θ ⊥ = false) (htop : θ ⊤ = true) :
    θ ∘ stepFourTapeKeys q s g hg f = stepFourTape q s g hg (fun a => θ ∘ f a) := by
  funext i
  try dsimp only [Function.comp_def, stepFourTapeKeys, stepFourTape]
  split_ifs with hi hn
  · exact map_afterStepFourKeys q s g hg f θ hθ _ _ _
  · exact hbot
  · exact htop

/-- The whole actual key execution, including all sentinel operations,
commutes with every admissible zero-one threshold. -/
theorem map_groupedColumnsort (q s g H : ℕ) (hg : 0 < g) (hH : 0 < H)
    (f : Fin s → Fin (q*s*g) → α) (θ : α → Bool) (hθ : Monotone θ)
    (hbot : θ ⊥ = false) (htop : θ ⊤ = true) :
    θ ∘ groupedColumnsort q s g H hg hH f =
      groupedColumnsort01 q s g H hg hH (fun a => θ ∘ f a) := by
  have houter := map_blockSortKeys (2*H) (by omega) (-H)
    (blockSortKeys (2*H) (by omega) 0 (stepFourTapeKeys q s g hg f)) θ hθ
  have hinner := map_blockSortKeys (2*H) (by omega) 0
    (stepFourTapeKeys q s g hg f) θ hθ
  rw [hinner, map_stepFourTapeKeys q s g hg f θ hθ hbot htop] at houter
  funext i
  exact congrFun houter (i : ℤ)

/-- The standard threshold at a key, with false at and below that key. -/
def threshold (a : α) : α → Bool := fun x => decide (a < x)

omit [OrderBot α] [OrderTop α] in
theorem threshold_monotone (a : α) : Monotone (threshold a) := by
  intro x y hxy
  cases hx : threshold a x <;> cases hy : threshold a y <;> try decide
  have hx' : a < x := by simpa [threshold] using hx
  have hy' : ¬a < y := by simpa [threshold] using hy
  exact False.elim (hy' (lt_of_lt_of_le hx' hxy))

omit [OrderTop α] in
@[simp] theorem threshold_bot (a : α) : threshold a ⊥ = false := by simp [threshold]

omit [OrderBot α] in
@[simp] theorem threshold_top (a : α) (ha : a < ⊤) : threshold a ⊤ = true := by
  simp [threshold, ha]

/-- The concrete eight-step algorithm sorts arbitrary keys. This is the
zero-one principle applied to actual executions, not a black-box premise. -/
theorem groupedColumnsort_monotone (q s g H : ℕ)
    (hs : 0 < s) (hg : 0 < g) (hH : 0 < H)
    (hheight : q*s*g = 2*H) (hr : 2*s*(s+1) ≤ q*s)
    (f : Fin s → Fin (q*s*g) → α) :
    Monotone (groupedColumnsort q s g H hg hH f) := by
  intro i j hij
  by_contra h
  have hij' : groupedColumnsort q s g H hg hH f j < groupedColumnsort q s g H hg hH f i :=
    lt_of_not_ge h
  let a := groupedColumnsort q s g H hg hH f j
  have hatop : a < ⊤ := lt_of_lt_of_le hij' le_top
  have hm := groupedColumnsort01_monotone q s g H hs hg hH hheight hr
    (fun c => threshold a ∘ f c)
  have he := map_groupedColumnsort q s g H hg hH f (threshold a)
    (threshold_monotone a) (threshold_bot a) (threshold_top a hatop)
  have hbits := hm hij
  rw [← congrFun he i, ← congrFun he j] at hbits
  have hi : threshold a (groupedColumnsort q s g H hg hH f i) = true := by
    simp only [threshold, decide_eq_true_eq]
    exact hij'
  have hj : threshold a (groupedColumnsort q s g H hg hH f j) = false := by
    simp [threshold, a]
  change threshold a _ ≤ threshold a _ at hbits
  rw [hi, hj] at hbits
  exact Bool.false_ne_true (hbits rfl)

/-- Sorted bit tuples with the same zero count agree pointwise. -/
theorem monotone_bits_eq_of_zeroCount_eq {n : ℕ} (f h : Fin n → Bool)
    (hf : Monotone f) (hh : Monotone h) (hc : zeroCount f = zeroCount h) : f = h := by
  apply List.ofFn_injective
  exact List.eq_of_perm_of_sorted (perm_of_zeroCount_eq f h hc) hf.ofFn_sorted hh.ofFn_sorted

/-- Threshold counts are conserved across the entire key execution,
including insertion and deletion of sentinel records. -/
theorem groupedColumnsort_threshold_eq (q s g H : ℕ)
    (hs : 0 < s) (hg : 0 < g) (hH : 0 < H)
    (hheight : q*s*g = 2*H) (hr : 2*s*(s+1) ≤ q*s)
    (f : Fin s → Fin (q*s*g) → α) (a : α) (ha : a < ⊤) :
    threshold a ∘ groupedColumnsort q s g H hg hH f =
      threshold a ∘ sortColumn (flattenKeys q s g f) := by
  have hθ := threshold_monotone a
  have hout := groupedColumnsort_monotone q s g H hs hg hH hheight hr f
  apply monotone_bits_eq_of_zeroCount_eq _ _ (hθ.comp hout)
    (hθ.comp (sortColumn_monotone _))
  have hzout : zeroCount (threshold a ∘ groupedColumnsort q s g H hg hH f) =
      ∑ c, zeroCount (threshold a ∘ f c) := by
    rw [map_groupedColumnsort q s g H hg hH f (threshold a) hθ
      (threshold_bot a) (threshold_top a ha)]
    exact groupedColumnsort01_zeroCount q s g H hg hH hheight _
  have hzin : zeroCount (threshold a ∘ sortColumn (flattenKeys q s g f)) =
      ∑ c, zeroCount (threshold a ∘ f c) := by
    rw [monotone_map_sortColumn _ (threshold a) hθ, zeroCount_sortColumn]
    change zeroCount (flattenInput q s g (fun c => threshold a ∘ f c)) = _
    exact flattenInput_zeroCount q s g _
  exact hzout.trans hzin.symm

/-- The complete execution agrees exactly with sorting the original values.
This also rules out loss of ordinary records when sentinel positions are
removed, including duplicate keys. -/
theorem groupedColumnsort_eq_sortColumn (q s g H : ℕ)
    (hs : 0 < s) (hg : 0 < g) (hH : 0 < H)
    (hheight : q*s*g = 2*H) (hr : 2*s*(s+1) ≤ q*s)
    (f : Fin s → Fin (q*s*g) → α) :
    groupedColumnsort q s g H hg hH f = sortColumn (flattenKeys q s g f) := by
  funext i
  by_contra h
  rcases lt_or_gt_of_ne h with hlt | hgt
  · let a := groupedColumnsort q s g H hg hH f i
    have ha : a < ⊤ := lt_of_lt_of_le hlt le_top
    have he := congrFun (groupedColumnsort_threshold_eq q s g H hs hg hH hheight hr f a ha) i
    change threshold a a = threshold a (sortColumn (flattenKeys q s g f) i) at he
    have hi : threshold a (sortColumn (flattenKeys q s g f) i) = true := by
      simp only [threshold, decide_eq_true_eq]
      exact hlt
    simp [threshold, hi] at he
    exact (not_le_of_gt hlt) he
  · let a := sortColumn (flattenKeys q s g f) i
    have ha : a < ⊤ := lt_of_lt_of_le hgt le_top
    have he := congrFun (groupedColumnsort_threshold_eq q s g H hs hg hH hheight hr f a ha) i
    change threshold a (groupedColumnsort q s g H hg hH f i) = threshold a a at he
    have hi : threshold a (groupedColumnsort q s g H hg hH f i) = true := by
      simp only [threshold, decide_eq_true_eq]
      exact hgt
    simp [threshold, hi] at he
    exact (not_le_of_gt hgt) he

/-- Full correctness of the concrete grouped Columnsort for ordered keys:
sorted output and the standard permutation relation to the entire input. -/
theorem groupedColumnsort_correct (q s g H : ℕ)
    (hs : 0 < s) (hg : 0 < g) (hH : 0 < H)
    (hheight : q*s*g = 2*H) (hr : 2*s*(s+1) ≤ q*s)
    (f : Fin s → Fin (q*s*g) → α) :
    (List.ofFn (groupedColumnsort q s g H hg hH f)).Pairwise (· ≤ ·) ∧
    (List.ofFn (groupedColumnsort q s g H hg hH f)).Perm
      (List.ofFn (flattenKeys q s g f)) := by
  rw [groupedColumnsort_eq_sortColumn q s g H hs hg hH hheight hr f]
  exact ⟨(sortColumn_monotone _).ofFn_sorted, sortColumn_perm _⟩

end CSL.Columnsort
end ColumnsortKeys

section ColumnsortParameters
/-!
# Grouped Columnsort in the paper's r,s,g parameters

The kernel uses r=q*s and the half-column record count H. This adapter
constructs q=r/s and H=r*g/2 from the paper's divisibility and parity
conditions. It also makes the column-major input list explicit.
-/

namespace CSL.Columnsort

open scoped BigOperators

variable {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α]

omit [LinearOrder α] [OrderBot α] [OrderTop α] in
theorem flattenKeys_ofFn (q s g : ℕ) (f : Fin s → Fin (q*s*g) → α) :
    List.ofFn (flattenKeys q s g f) = (List.ofFn (fun a => List.ofFn (f a))).flatten := by
  let hn : s*q*(s*g) = s*(q*s*g) := by ring
  rw [List.ofFn_congr hn, List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext a
  apply congrArg List.ofFn
  funext j
  have hidx : a.val*(q*s*g)+j.val < s*(q*s*g) := by
    have hi := j.isLt
    have ha := a.isLt
    nlinarith
  change f ((inputEquiv q s g (Fin.cast hn.symm ⟨a.val*(q*s*g)+j.val, hidx⟩)).1)
    ((inputEquiv q s g (Fin.cast hn.symm ⟨a.val*(q*s*g)+j.val, hidx⟩)).2) = f a j
  have he : inputEquiv q s g (Fin.cast hn.symm ⟨a.val*(q*s*g)+j.val, hidx⟩) = (a,j) := by
    have hval : (⟨a.val*(q*s*g)+j.val, by
        have hi := j.isLt
        have ha := a.isLt
        nlinarith⟩ : Fin (s*(q*s*g))) = finProdFinEquiv (a,j) := by
      apply Fin.ext
      change a.val*(q*s*g)+j.val = j.val+(q*s*g)*a.val
      ring
    change finProdFinEquiv.symm ⟨a.val*(q*s*g)+j.val, hidx⟩ = (a,j)
    rw [hval, Equiv.symm_apply_apply]
  rw [he]

/-- The concrete parameter choices required by the actual implementation. -/
structure Shape (r s g : ℕ) where
  q : ℕ
  H : ℕ
  width_eq : q*s = r
  half_eq : q*s*g = 2*H
  half_pos : 0 < H

def paperShape (r s g : ℕ) (hs : 0 < s) (hg : 0 < g)
    (heven : Even r) (hdiv : s ∣ r) (hr : 2*s*(s+1) ≤ r) : Shape r s g where
  q := r/s
  H := r*g/2
  width_eq := Nat.div_mul_cancel hdiv
  half_eq := by
    rw [Nat.div_mul_cancel hdiv]
    rcases heven with ⟨k, hk⟩
    have he : r*g = 2*(k*g) := by rw [hk]; ring
    omega
  half_pos := by
    have hrpos : 0 < r := by nlinarith
    have hprod : 0 < r*g := Nat.mul_pos hrpos hg
    rcases heven with ⟨k, hk⟩
    have he : r*g = 2*(k*g) := by rw [hk]; ring
    omega

/-- Only a proof cast in a fixed finite dimension, not a data movement. -/
def shapeInput {r s g : ℕ} (shape : Shape r s g)
    (f : Fin s → Fin (r*g) → α) : Fin s → Fin (shape.q*s*g) → α :=
  fun a i => f a (Fin.cast (congrArg (fun t => t*g) shape.width_eq) i)

/-- Eight-step grouped Columnsort, stated with the paper's exact parameters. -/
def columnsort (r s g : ℕ) (hs : 0 < s) (hg : 0 < g)
    (heven : Even r) (hdiv : s ∣ r) (hr : 2*s*(s+1) ≤ r)
    (f : Fin s → Fin (r*g) → α) : List α :=
  let shape := paperShape r s g hs hg heven hdiv hr
  List.ofFn (groupedColumnsort shape.q s g shape.H hg shape.half_pos (shapeInput shape f))

/-- The full Appendix D.1 correctness statement in r,s,g form: every input
is returned sorted, with exactly the same ordinary values and multiplicities.
The comparisons are actual Tuple.sort operations in the eight-step program. -/
theorem columnsort_correct (r s g : ℕ) (hs : 0 < s) (hg : 0 < g)
    (heven : Even r) (hdiv : s ∣ r) (hr : 2*s*(s+1) ≤ r)
    (f : Fin s → Fin (r*g) → α) :
    (columnsort r s g hs hg heven hdiv hr f).Pairwise (· ≤ ·) ∧
    (columnsort r s g hs hg heven hdiv hr f).Perm
      (List.ofFn (fun a => List.ofFn (f a))).flatten := by
  let shape := paperShape r s g hs hg heven hdiv hr
  have hr' : 2*s*(s+1) ≤ shape.q*s := by rw [shape.width_eq]; exact hr
  have h := groupedColumnsort_correct shape.q s g shape.H hs hg shape.half_pos
    shape.half_eq hr' (shapeInput shape f)
  rw [flattenKeys_ofFn] at h
  have hin : (List.ofFn (fun a => List.ofFn (shapeInput shape f a))).flatten =
      (List.ofFn (fun a => List.ofFn (f a))).flatten := by
    congr 1
    apply congrArg List.ofFn
    funext a
    exact (List.ofFn_congr (congrArg (fun t => t*g) shape.width_eq).symm (f a)).symm
  rw [hin] at h
  exact h

/-- Add the two formal sentinels; ordinary keys remain tagged and distinct
from both sentinels, even when the original key type is unbounded. -/
def sentinelKey (x : α) : WithBot (WithTop α) := (↑(x : WithTop α))

def columnsortSentinels (r s g : ℕ) (hs : 0 < s) (hg : 0 < g)
    (heven : Even r) (hdiv : s ∣ r) (hr : 2*s*(s+1) ≤ r)
    (f : Fin s → Fin (r*g) → α) : List (WithBot (WithTop α)) :=
  columnsort r s g hs hg heven hdiv hr (fun a i => sentinelKey (f a i))

omit [OrderBot α] [OrderTop α] in
/-- Appendix D.1 for any linear-order key type, using the two usual formal
sentinels during execution. The returned finite list is a permutation of
ordinary input keys only, so neither sentinel survives. -/
theorem columnsort_sentinels_correct (r s g : ℕ) (hs : 0 < s) (hg : 0 < g)
    (heven : Even r) (hdiv : s ∣ r) (hr : 2*s*(s+1) ≤ r)
    (f : Fin s → Fin (r*g) → α) :
    (columnsortSentinels r s g hs hg heven hdiv hr f).Pairwise (· ≤ ·) ∧
    (columnsortSentinels r s g hs hg heven hdiv hr f).Perm
      (List.ofFn (fun a => List.ofFn (fun i => sentinelKey (f a i)))).flatten :=
  columnsort_correct r s g hs hg heven hdiv hr (fun a i => sentinelKey (f a i))

omit [OrderBot α] [OrderTop α] in
/-- Every returned item is an ordinary input record; the tags rule out
confusing an input key with a newly inserted sentinel. -/
theorem columnsort_sentinels_ordinary (r s g : ℕ) (hs : 0 < s) (hg : 0 < g)
    (heven : Even r) (hdiv : s ∣ r) (hr : 2*s*(s+1) ≤ r)
    (f : Fin s → Fin (r*g) → α) (x : WithBot (WithTop α))
    (hx : x ∈ columnsortSentinels r s g hs hg heven hdiv hr f) :
    ∃ a : Fin s, ∃ i : Fin (r*g), x = sentinelKey (f a i) := by
  have hp := (columnsort_sentinels_correct r s g hs hg heven hdiv hr f).2
  rcases List.mem_flatten.mp (hp.mem_iff.mp hx) with ⟨l, hl, hxl⟩
  rcases List.mem_ofFn.mp hl with ⟨a, rfl⟩
  rcases List.mem_ofFn.mp hxl with ⟨i, hi⟩
  exact ⟨a, i, hi.symm⟩

/-- In flat group indices the implemented cyclic redistribution is exactly
π(j)=(j mod s)*r+floor(j/s), with r=q*s, as stated in the paper. -/
theorem groupTranspose_flat_index (q s a k c : ℕ) (hs : 0 < s) (hc : c < s) :
    (a*(q*s)+k*s+c) % s * (q*s) + (a*(q*s)+k*s+c) / s =
      c*(q*s)+a*q+k := by
  have he : a*(q*s)+k*s+c = (a*q+k)*s+c := by ring
  rw [he]
  rw [Nat.mul_comm (a*q+k) s, Nat.mul_add_mod, Nat.mul_add_div hs,
    Nat.mod_eq_of_lt hc, Nat.div_eq_of_lt hc]
  omega

omit [OrderBot α] [OrderTop α] in
/-- The concrete data read by a new column is precisely its residue class
of old group indices, with the complete within-group record offset kept. -/
theorem newColumnKeys_at_group (q s g : ℕ) (hg : 0 < g)
    (f : Fin s → Fin (q*s*g) → α) (a : Fin s) (k : Fin q) (c : Fin s) (v : Fin g) :
    newColumnKeys q s g hg c f (finProdFinEquiv (a,finProdFinEquiv (k,v))) =
      sortColumn (f a) (stripeEquiv q s g (c,finProdFinEquiv (k,v))) := by
  simp only [newColumnKeys, Equiv.symm_apply_apply]
  apply congrArg (sortColumn (f a))
  apply Fin.ext
  exact (stripeEquiv_val q s g (c,finProdFinEquiv (k,v))).symm

end CSL.Columnsort
end ColumnsortParameters


