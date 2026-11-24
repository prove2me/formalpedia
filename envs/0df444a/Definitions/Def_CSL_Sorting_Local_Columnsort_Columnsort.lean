-- Prove2me | Definitions.Def_CSL_Sorting_Local_Columnsort_Columnsort
-- name    : CSL_Sorting_Local_Columnsort_Columnsort
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:09:48.950913+00:00
-- url     : https://prove2.me/theorems/a6d5915b-5863-40ec-b644-efeb00342627
-- title:
--   Coded sorting library: Sorting / Local / Columnsort / Columnsort
-- statement:
--   Module `CodedSorting.Sorting.Local.Columnsort.Columnsort` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Grouped Columnsort: the actual first redistribution
--
--   Columns are sorted by Mathlib's finite sorting permutation, rather than by
--   postulating that some unknown local operation produces sorted columns.
--   The first redistribution reads the arithmetic-progression group indices of
--   those sorted columns.  Zero counts below are computed from these actual data.
--
--   This module proves sortedness of the complete eight-step zero-one execution.
--   The companion ColumnsortPermutation and ColumnsortKeys modules prove data
--   conservation and the lift to arbitrary ordered keys. No I/O cost is asserted.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Sorting.Local.Columnsort.Columnsort

import Definitions.Def_CSL_Compat
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Grouped Columnsort: the actual first redistribution

Columns are sorted by Mathlib's finite sorting permutation, rather than by
postulating that some unknown local operation produces sorted columns.
The first redistribution reads the arithmetic-progression group indices of
those sorted columns.  Zero counts below are computed from these actual data.

This module proves sortedness of the complete eight-step zero-one execution.
The companion ColumnsortPermutation and ColumnsortKeys modules prove data
conservation and the lift to arbitrary ordered keys. No I/O cost is asserted.
-/

namespace CSL.Columnsort

open scoped BigOperators

/-- A concrete sorting permutation, with original values retained exactly. -/
def sortColumn {n : ℕ} {α : Type*} [LinearOrder α] (f : Fin n → α) : Fin n → α :=
  f ∘ Tuple.sort f

theorem sortColumn_monotone {n : ℕ} {α : Type*} [LinearOrder α]
    (f : Fin n → α) : Monotone (sortColumn f) := Tuple.monotone_sort f

theorem sortColumn_perm {n : ℕ} {α : Type*} [LinearOrder α]
    (f : Fin n → α) : (List.ofFn (sortColumn f)).Perm (List.ofFn f) :=
  (Tuple.sort f).ofFn_comp_perm f

/-- The threshold step in the zero-one principle commutes with actual column
sorting. It is not assumed separately for each input. -/
theorem monotone_map_sortColumn {n : ℕ} {α β : Type*}
    [LinearOrder α] [LinearOrder β] (f : Fin n → α) (θ : α → β)
    (hθ : Monotone θ) :
    θ ∘ sortColumn f = sortColumn (θ ∘ f) := by
  change (θ ∘ f) ∘ Tuple.sort f = (θ ∘ f) ∘ Tuple.sort (θ ∘ f)
  apply Tuple.comp_sort_eq_comp_iff_monotone.mpr
  exact hθ.comp (sortColumn_monotone f)

/-- Count zero bits in a finite column. -/
def zeroCount {ι : Type*} [Fintype ι] (f : ι → Bool) : ℕ :=
  Fintype.card {i // f i = false}

theorem zeroCount_le {n : ℕ} (f : Fin n → Bool) : zeroCount f ≤ n := by
  simpa [zeroCount] using Fintype.card_subtype_le (fun i => f i = false)

theorem zeroCount_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (f : κ → Bool) : zeroCount (f ∘ e) = zeroCount f := by
  apply Fintype.card_congr
  exact e.subtypeEquiv (fun _ => Iff.rfl)

@[simp] theorem zeroCount_sortColumn {n : ℕ} (f : Fin n → Bool) :
    zeroCount (sortColumn f) = zeroCount f := zeroCount_equiv (Tuple.sort f) f

/-- The sorted column has exactly its original zero count at the beginning. -/
theorem sortColumn_false_iff {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    sortColumn f i = false ↔ i.val < zeroCount f := by
  have hle (b : Bool) : b ≤ false ↔ b = false := by cases b <;> decide
  have h := Tuple.lt_card_le_iff_apply_le_of_monotone (a := false) (sortColumn_monotone f) (j := i)
  simp only [hle] at h
  rw [← zeroCount_sortColumn f, zeroCount, Fintype.card_subtype]
  exact h.symm

/-- Zero counts of a concatenation of equal-size finite pieces. -/
theorem zeroCount_prod {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι × κ → Bool) :
    zeroCount f = ∑ a, zeroCount (fun b => f (a, b)) := by
  classical
  let e : {p : ι × κ // f p = false} ≃
      (a : ι) × {b : κ // f (a, b) = false} :=
    { toFun := fun p => ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
      invFun := fun p => ⟨(p.1, p.2.val), p.2.property⟩
      left_inv := fun p => by cases p; rfl
      right_inv := fun p => by cases p; rfl }
  simpa only [zeroCount, Fintype.card_sigma] using Fintype.card_congr e

/-- In a column of q*s groups of g records, this is the source position of
record i in the groups whose group number is congruent to c modulo s. -/
def stripeIndex (s g c i : ℕ) : ℕ := (i / g * s + c) * g + i % g

/-- The first Q*g records in a residue-class stream precede every source
position Q*s*g. This lower bound is an arithmetic fact about the actual map. -/
theorem stripeIndex_lower (s g c i Q : ℕ) (hg : 0 < g) (hc : c < s)
    (hi : i < Q * g) : stripeIndex s g c i < Q * s * g := by
  have hq : i / g < Q := (Nat.div_lt_iff_lt_mul hg).2 hi
  have hm := Nat.mod_lt i hg
  have hstep : i / g * s + c < Q * s := by nlinarith
  try dsimp [stripeIndex]
  nlinarith

/-- Conversely, a source position below (Q+1)*s*g must lie among the first
(Q+1)*g records of its residue-class stream. -/
theorem stripeIndex_upper (s g c i Q : ℕ) (hg : 0 < g)
    (hi : stripeIndex s g c i < (Q + 1) * s * g) : i < (Q + 1) * g := by
  by_contra h
  have hq : Q + 1 ≤ i / g := (Nat.le_div_iff_mul_le hg).2 (by omega)
  have hmul := Nat.mul_le_mul_right (s * g) hq
  have hsource : (Q + 1) * s * g ≤ stripeIndex s g c i := by
    calc
      (Q+1)*s*g ≤ (i/g)*s*g := by simpa only [Nat.mul_assoc] using hmul
      _ ≤ stripeIndex s g c i := by simp only [stripeIndex, Nat.add_mul]; omega
  omega

/-- All selected group records are valid indices of the original column. -/
theorem stripeIndex_lt (q s g c i : ℕ) (hg : 0 < g) (hc : c < s)
    (hi : i < q * g) : stripeIndex s g c i < q * s * g :=
  stripeIndex_lower s g c i q hg hc hi

/-- Actual stream selected from one sorted original column. -/
def stripe (q s g : ℕ) (hg : 0 < g) (c : Fin s)
    (f : Fin (q * s * g) → Bool) : Fin (q * g) → Bool := fun i =>
  sortColumn f ⟨stripeIndex s g c.val i.val,
    stripeIndex_lt q s g c.val i.val hg c.isLt i.isLt⟩

/-- Every complete s-group strip contributes exactly g zeros to each new
column; at most one additional g-record group can contribute more zeros.
This counts the actual data after the first sort and group redistribution. -/
theorem stripe_zeroCount_bounds (q s g : ℕ) (hs : 0 < s) (hg : 0 < g)
    (c : Fin s) (f : Fin (q * s * g) → Bool) :
    (zeroCount f / (s * g)) * g ≤ zeroCount (stripe q s g hg c f) ∧
    zeroCount (stripe q s g hg c f) ≤ (zeroCount f / (s * g) + 1) * g := by
  let z := zeroCount f
  let Q := z / (s * g)
  have hsg : 0 < s * g := Nat.mul_pos hs hg
  have hz : z ≤ q * (s * g) := by
    simpa only [z, Nat.mul_assoc] using zeroCount_le f
  have hQq : Q ≤ q := by
    simpa only [Q, Nat.mul_div_cancel _ hsg] using (Nat.div_le_div_right (c := s*g) hz)
  have hQg : Q * g ≤ q * g := Nat.mul_le_mul_right g hQq
  have hlow : Q * s * g ≤ z := by
    simpa only [Q, Nat.mul_assoc] using Nat.div_mul_le_self z (s * g)
  have hhigh : z < (Q + 1) * s * g := by
    simpa only [Q, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_add,
      Nat.add_mul] using Nat.lt_mul_div_succ z hsg
  constructor
  · let inject : Fin (Q * g) → {i : Fin (q * g) // stripe q s g hg c f i = false} :=
      fun i => ⟨⟨i.val, lt_of_lt_of_le i.isLt hQg⟩, by
        apply (sortColumn_false_iff f _).2
        exact lt_of_lt_of_le
          (stripeIndex_lower s g c.val i.val Q hg c.isLt i.isLt) hlow⟩
    have hinj : Function.Injective inject := by
      intro i j h
      apply Fin.ext
      exact congrArg (fun a => a.val.val) h
    simpa only [Fintype.card_fin, zeroCount, Q, z] using Fintype.card_le_of_injective inject hinj
  · let inject : {i : Fin (q * g) // stripe q s g hg c f i = false} → Fin ((Q+1)*g) :=
      fun i => ⟨i.val.val, by
        have hi := (sortColumn_false_iff f _).1 i.property
        exact stripeIndex_upper s g c.val i.val.val Q hg (lt_trans hi hhigh)⟩
    have hinj : Function.Injective inject := by
      intro i j h
      apply Subtype.ext
      apply Fin.ext
      exact congrArg (fun x : Fin ((Q+1)*g) => x.val) h
    simpa only [Fintype.card_fin, zeroCount, Q, z] using Fintype.card_le_of_injective inject hinj

/-- Concatenate the residue-c stream from every original column. This is the
actual second-step column before its second local sort. -/
def newColumn (q s g : ℕ) (hg : 0 < g) (c : Fin s)
    (f : Fin s → Fin (q * s * g) → Bool) : Fin (s * (q * g)) → Bool := fun i =>
  let p := finProdFinEquiv.symm i
  stripe q s g hg c (f p.1) p.2

/-- Common count of complete s-group strips in the original sorted columns. -/
def baseRows (s g : ℕ) {n : ℕ} (f : Fin s → Fin n → Bool) : ℕ :=
  ∑ a, zeroCount (f a) / (s * g)

theorem newColumn_zeroCount_eq (q s g : ℕ) (hg : 0 < g) (c : Fin s)
    (f : Fin s → Fin (q * s * g) → Bool) :
    zeroCount (newColumn q s g hg c f) =
      ∑ a, zeroCount (stripe q s g hg c (f a)) := by
  change zeroCount ((fun p : Fin s × Fin (q*g) => stripe q s g hg c (f p.1) p.2) ∘
    finProdFinEquiv.symm) = _
  rw [zeroCount_equiv, zeroCount_prod]

/-- Every new column has between t*g and (t+s)*g zeros, where t is the
same explicitly computed number for all new columns. -/
theorem newColumn_zeroCount_bounds (q s g : ℕ) (hs : 0 < s) (hg : 0 < g)
    (c : Fin s) (f : Fin s → Fin (q * s * g) → Bool) :
    baseRows s g f * g ≤ zeroCount (newColumn q s g hg c f) ∧
    zeroCount (newColumn q s g hg c f) ≤ (baseRows s g f + s) * g := by
  rw [newColumn_zeroCount_eq]
  constructor
  · simpa only [baseRows, Finset.sum_mul] using
      Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin s))) =>
        (stripe_zeroCount_bounds q s g hs hg c (f a)).1)
  · have h := Finset.sum_le_sum
      (fun a (_ : a ∈ (Finset.univ : Finset (Fin s))) =>
        (stripe_zeroCount_bounds q s g hs hg c (f a)).2)
    simpa [baseRows, Nat.add_mul, Finset.sum_add_distrib, Finset.sum_mul] using h

/-- Read the result after step 3 at the position prescribed by the inverse
of the group transpose in step 4. `u` is a group-row, `c` its column, and
`v` the unchanged record offset inside a group. In the flattened output
its exact physical position is `(u*s+c)*g+v`. -/
def afterStepFour (q s g : ℕ) (hg : 0 < g)
    (f : Fin s → Fin (q * s * g) → Bool)
    (u : Fin (s*q)) (c : Fin s) (v : Fin g) : Bool :=
  sortColumn (newColumn q s g hg c f)
    ⟨u.val*g + v.val, by have := u.isLt; have := v.isLt; nlinarith⟩

/-- Actual first four steps: every group-row before t is zero. -/
theorem stepFour_zero_prefix (q s g : ℕ) (hs : 0 < s) (hg : 0 < g)
    (f : Fin s → Fin (q*s*g) → Bool)
    (u : Fin (s*q)) (c : Fin s) (v : Fin g) (hu : u.val < baseRows s g f) :
    afterStepFour q s g hg f u c v = false := by
  apply (sortColumn_false_iff _ _).2
  have h := (newColumn_zeroCount_bounds q s g hs hg c f).1
  have hv := v.isLt
  change u.val*g + v.val < _
  nlinarith

/-- Actual first four steps: every group-row from t+s onwards is one. -/
theorem stepFour_one_suffix (q s g : ℕ) (hs : 0 < s) (hg : 0 < g)
    (f : Fin s → Fin (q*s*g) → Bool)
    (u : Fin (s*q)) (c : Fin s) (v : Fin g) (hu : baseRows s g f + s ≤ u.val) :
    afterStepFour q s g hg f u c v = true := by
  have h := (newColumn_zeroCount_bounds q s g hs hg c f).2
  have hn : ¬ afterStepFour q s g hg f u c v = false := by
    intro hfalse
    have hh := (sortColumn_false_iff (newColumn q s g hg c f) _).1 hfalse
    change u.val*g + v.val < _ at hh
    nlinarith
  cases he : afterStepFour q s g hg f u c v <;> simp_all

/-- The uncertain region is at most s whole group-rows, each with s groups
of g records. The paper's r≥2s(s+1) condition implies this is at most half
an original column; this proof obtains the slightly smaller s²g bound. -/
theorem dirtyRegion_halfColumn (q s g : ℕ)
    (hr : 2*s*(s+1) ≤ q*s) :
    2 * (s*s*g) ≤ q*s*g := by
  have h : 2*(s*s) ≤ q*s := by nlinarith
  nlinarith

/-- Sorting does not move ones into an already all-zero prefix. -/
theorem sortColumn_false_of_prefix {n : ℕ} (f : Fin n → Bool) (i : Fin n)
    (h : ∀ j : Fin n, j.val ≤ i.val → f j = false) : sortColumn f i = false := by
  apply (sortColumn_false_iff f i).2
  let inject : Fin (i.val+1) → {j : Fin n // f j = false} := fun j =>
    ⟨⟨j.val, by have := i.isLt; omega⟩, h _ (by change j.val ≤ i.val; have := j.isLt; omega)⟩
  have hinj : Function.Injective inject := by
    intro a b hab
    exact Fin.ext (congrArg (fun j => j.val.val) hab)
  have hc := Fintype.card_le_of_injective inject hinj
  have hc' : i.val+1 ≤ zeroCount f := by simpa only [zeroCount, Fintype.card_fin] using hc
  omega

/-- Sorting does not move zeros into an already all-one suffix. -/
theorem sortColumn_true_of_suffix {n : ℕ} (f : Fin n → Bool) (i : Fin n)
    (h : ∀ j : Fin n, i.val ≤ j.val → f j = true) : sortColumn f i = true := by
  let inject : {j : Fin n // f j = false} → Fin i.val := fun j =>
    ⟨j.val.val, by
      by_contra hj
      have hh := h j.val (by omega)
      rw [j.property] at hh
      cases hh⟩
  have hinj : Function.Injective inject := by
    intro a b hab
    apply Subtype.ext
    exact Fin.ext (congrArg (fun j : Fin i.val => j.val) hab)
  have hc : zeroCount f ≤ i.val := by
    simpa only [zeroCount, Fintype.card_fin] using Fintype.card_le_of_injective inject hinj
  have hn : sortColumn f i ≠ false := by
    intro hh
    have hh' := (sortColumn_false_iff f i).1 hh
    omega
  cases he : sortColumn f i <;> simp_all

theorem sortColumn_eq_of_monotone {n : ℕ} {α : Type*} [LinearOrder α]
    (f : Fin n → α) (h : Monotone f) : sortColumn f = f := by
  rw [sortColumn, (Tuple.sort_eq_refl_iff_monotone (f := f)).2 h]
  rfl

/-- All possible inversions are confined to a finite interval. On an integer
indexed array the outer constants represent the negative/positive sentinels. -/
def Band (f : ℤ → Bool) (a b : ℤ) : Prop :=
  (∀ i, i < a → f i = false) ∧ (∀ i, b ≤ i → f i = true)

def blockOrigin (B : ℕ) (offset i : ℤ) : ℤ :=
  offset + ((i-offset)/(B : ℤ))*(B : ℤ)

theorem blockOrigin_bounds (B : ℕ) (hB : 0 < B) (offset i : ℤ) :
    blockOrigin B offset i ≤ i ∧ i < blockOrigin B offset i + B := by
  have hb : 0 < (B : ℤ) := by exact_mod_cast hB
  have hl := Int.emod_nonneg (i-offset) (ne_of_gt hb)
  have hh := Int.emod_lt_of_pos (i-offset) hb
  have he := Int.ediv_mul_add_emod (i-offset) (B : ℤ)
  try dsimp [blockOrigin]
  constructor <;> nlinarith

def blockSlot (B : ℕ) (hB : 0 < B) (offset i : ℤ) : Fin B :=
  ⟨(i-blockOrigin B offset i).toNat, by
    have h := blockOrigin_bounds B hB offset i
    have hn : 0 ≤ i-blockOrigin B offset i := by omega
    exact (Int.toNat_lt hn).2 (by omega)⟩

theorem blockSlot_address (B : ℕ) (hB : 0 < B) (offset i : ℤ) :
    blockOrigin B offset i + (blockSlot B hB offset i : ℤ) = i := by
  have h := (blockOrigin_bounds B hB offset i).1
  have hn : 0 ≤ i-blockOrigin B offset i := by omega
  simp only [blockSlot, Int.toNat_of_nonneg hn]
  omega

/-- Simultaneous actual sorting of all length-B columns on a grid. Constants
outside the finite input remain constant, so the infinite notation allocates
no additional records and denotes the usual finite padded algorithm. -/
def blockSort (B : ℕ) (hB : 0 < B) (offset : ℤ) (f : ℤ → Bool) : ℤ → Bool :=
  fun i => sortColumn (fun j : Fin B => f (blockOrigin B offset i + (j : ℤ)))
    (blockSlot B hB offset i)

/-- Local sorting preserves the original all-zero prefix and all-one suffix;
the possible inversion interval does not expand. -/
theorem blockSort_band (B : ℕ) (hB : 0 < B) (offset : ℤ)
    (f : ℤ → Bool) (a b : ℤ) (h : Band f a b) :
    Band (blockSort B hB offset f) a b := by
  constructor
  · intro i hi
    apply sortColumn_false_of_prefix
    intro j hj
    have he := blockSlot_address B hB offset i
    have hj' : (j : ℤ) ≤ (blockSlot B hB offset i : ℤ) := by exact_mod_cast hj
    exact h.1 _ (by omega)
  · intro i hi
    apply sortColumn_true_of_suffix
    intro j hj
    have he := blockSlot_address B hB offset i
    have hj' : (blockSlot B hB offset i : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
    exact h.2 _ (by omega)

/-- Every globally sorted input is fixed by any grid of local sorts. -/
theorem blockSort_eq_of_monotone (B : ℕ) (hB : 0 < B) (offset : ℤ)
    (f : ℤ → Bool) (h : Monotone f) : blockSort B hB offset f = f := by
  funext i
  have hcol : Monotone (fun j : Fin B => f (blockOrigin B offset i + (j : ℤ))) := by
    intro j k hjk
    apply h
    have h' : (j : ℤ) ≤ (k : ℤ) := by exact_mod_cast hjk
    omega
  change sortColumn _ _ = _
  rw [sortColumn_eq_of_monotone _ hcol]
  change f (blockOrigin B offset i + (blockSlot B hB offset i : ℤ)) = f i
  rw [blockSlot_address]

/-- Every point in the same grid interval has exactly that block origin. -/
theorem blockOrigin_eq (B : ℕ) (hB : 0 < B) (offset k i : ℤ)
    (hl : offset+k*B ≤ i) (hu : i < offset+(k+1)*B) :
    blockOrigin B offset i = offset+k*B := by
  have hb : 0 < (B : ℤ) := by exact_mod_cast hB
  have he : (i-offset)/(B : ℤ) = k := by
    apply le_antisymm
    · have hlt : (i-offset)/(B : ℤ) < k+1 :=
        (Int.ediv_lt_iff_lt_mul hb).2 (by nlinarith)
      omega
    · apply (Int.le_ediv_iff_mul_le hb).2
      omega
  simp [blockOrigin, he]

/-- A single grid sort eliminates all inversions once their containing band
lies in one of its columns. -/
theorem blockSort_monotone_of_single_block (B : ℕ) (hB : 0 < B) (offset k : ℤ)
    (f : ℤ → Bool) (h : Band f (offset+k*B) (offset+(k+1)*B)) :
    Monotone (blockSort B hB offset f) := by
  have hp := blockSort_band B hB offset f _ _ h
  intro i j hij
  by_cases hi : i < offset+k*B
  · rw [hp.1 i hi]
    exact Bool.false_le _
  by_cases hj : offset+(k+1)*B ≤ j
  · rw [hp.2 j hj]
    exact Bool.le_true _
  have hbi := blockOrigin_eq B hB offset k i (by omega) (by omega)
  have hbj := blockOrigin_eq B hB offset k j (by omega) (by omega)
  have hsi := blockSlot_address B hB offset i
  have hsj := blockSlot_address B hB offset j
  have hslots : blockSlot B hB offset i ≤ blockSlot B hB offset j := by
    apply Fin.le_iff_val_le_val.mpr
    rw [hbi] at hsi
    rw [hbj] at hsj
    exact_mod_cast (show (blockSlot B hB offset i : ℤ) ≤
      (blockSlot B hB offset j : ℤ) by omega)
  try dsimp only [blockSort]
  rw [hbi, hbj]
  exact sortColumn_monotone _ hslots

/-- A band no longer than half a column fits either in an original column
or in a half-shifted column. This is the precise geometry of steps 5--7. -/
theorem half_column_cover (H : ℕ) (hH : 0 < H) (a b : ℤ)
    (hlen : b-a ≤ H) :
    (∃ k : ℤ, (k*(2*H) ≤ a ∧ b ≤ (k+1)*(2*H))) ∨
    (∃ k : ℤ, (-H+k*(2*H) ≤ a ∧ b ≤ -H+(k+1)*(2*H))) := by
  have hh : 0 < (H : ℤ) := by exact_mod_cast hH
  have hb : 0 < (2*(H : ℤ)) := by omega
  let k := a / (2*(H : ℤ))
  have ha := blockOrigin_bounds (2*H) (by omega) 0 a
  have hak : k*(2*(H : ℤ)) ≤ a ∧ a < (k+1)*(2*(H : ℤ)) := by
    simpa [blockOrigin, k, Nat.cast_mul, Nat.cast_ofNat, add_mul] using ha
  by_cases hb' : b ≤ (k+1)*(2*(H : ℤ))
  · exact Or.inl ⟨k, hak.1, hb'⟩
  · right
    refine ⟨k+1, ?_, ?_⟩ <;> nlinarith [hak.2]

/-- The actual two local-sort rounds finish every zero-one array whose
uncertain interval is no longer than half a column. No local correctness
assumption is supplied: both rounds invoke the concrete sorting permutation. -/
theorem two_grid_sorts_monotone (H : ℕ) (hH : 0 < H)
    (f : ℤ → Bool) (a b : ℤ) (hband : Band f a b) (hlen : b-a ≤ H) :
    Monotone (blockSort (2*H) (by omega) (-H)
      (blockSort (2*H) (by omega) 0 f)) := by
  have hB : 0 < 2*H := by omega
  rcases half_column_cover H hH a b hlen with ⟨k, hl, hu⟩ | ⟨k, hl, hu⟩
  · have hb : Band f (0+k*(2*H)) (0+(k+1)*(2*H)) := by
      constructor
      · intro i hi; exact hband.1 i (by simp only [zero_add] at hi; omega)
      · intro i hi; exact hband.2 i (by simp only [zero_add] at hi; omega)
    have hm := blockSort_monotone_of_single_block (2*H) hB 0 k f (by simpa using hb)
    rw [blockSort_eq_of_monotone (2*H) hB (-H) _ hm]
    exact hm
  · apply blockSort_monotone_of_single_block (2*H) hB (-H) k
    have hb := blockSort_band (2*H) hB 0 f a b hband
    constructor
    · intro i hi; exact hb.1 i (by exact lt_of_lt_of_le hi hl)
    · intro i hi; exact hb.2 i (by exact le_trans hu hi)

theorem baseRows_le (q s g : ℕ) (hs : 0 < s) (hg : 0 < g)
    (f : Fin s → Fin (q*s*g) → Bool) : baseRows s g f ≤ s*q := by
  have hsg : 0 < s*g := Nat.mul_pos hs hg
  have hb (a : Fin s) : zeroCount (f a) / (s*g) ≤ q := by
    have h := zeroCount_le (f a)
    have h' : zeroCount (f a) ≤ q*(s*g) := by simpa only [Nat.mul_assoc] using h
    simpa only [Nat.mul_div_cancel _ hsg] using (Nat.div_le_div_right (c := s*g) h')
  simpa [baseRows] using Finset.sum_le_sum
    (fun a (_ : a ∈ (Finset.univ : Finset (Fin s))) => hb a)

/-- Finite output of the actual first four steps, extended with negative and
positive sentinels. Decoding the flat index gives group-row, column, offset. -/
def stepFourTape (q s g : ℕ) (hg : 0 < g)
    (f : Fin s → Fin (q*s*g) → Bool) (i : ℤ) : Bool :=
  if hi : 0 ≤ i ∧ i < (s*q*(s*g) : ℕ) then
    let j : Fin (s*q*(s*g)) := ⟨i.toNat, (Int.toNat_lt hi.1).2 hi.2⟩
    let p : Fin (s*q) × Fin (s*g) := finProdFinEquiv.symm j
    let cv : Fin s × Fin g := finProdFinEquiv.symm p.2
    afterStepFour q s g hg f p.1 cv.1 cv.2
  else if i < 0 then false else true

/-- No hypothesis about intermediate columns is needed: this is the band
produced by running the first two sorts and the two group permutations on
an arbitrary input array. -/
theorem stepFourTape_band (q s g : ℕ) (hs : 0 < s) (hg : 0 < g)
    (f : Fin s → Fin (q*s*g) → Bool) :
    Band (stepFourTape q s g hg f)
      ((baseRows s g f * s * g : ℕ) : ℤ)
      (((baseRows s g f+s) * s * g : ℕ) : ℤ) := by
  have ht := baseRows_le q s g hs hg f
  have hsg : 0 < s*g := Nat.mul_pos hs hg
  have hstart : baseRows s g f*s*g ≤ s*q*(s*g) := by
    have h := Nat.mul_le_mul_right (s*g) ht
    simpa only [Nat.mul_assoc] using h
  constructor
  · intro i hi
    by_cases hin : 0 ≤ i ∧ i < (s*q*(s*g) : ℕ)
    · simp only [stepFourTape, dif_pos hin]
      apply stepFour_zero_prefix q s g hs hg
      change i.toNat / (s*g) < baseRows s g f
      apply (Nat.div_lt_iff_lt_mul hsg).2
      have h := (Int.toNat_lt hin.1).2 hi
      simpa only [Nat.mul_assoc] using h
    · have hstart' : ((baseRows s g f*s*g : ℕ) : ℤ) ≤
          ((s*q*(s*g) : ℕ) : ℤ) := by exact_mod_cast hstart
      have hn : i < 0 := by omega
      rw [stepFourTape, dif_neg hin, if_pos hn]
  · intro i hi
    by_cases hin : 0 ≤ i ∧ i < (s*q*(s*g) : ℕ)
    · simp only [stepFourTape, dif_pos hin]
      apply stepFour_one_suffix q s g hs hg
      change baseRows s g f+s ≤ i.toNat / (s*g)
      apply (Nat.le_div_iff_mul_le hsg).2
      have he : (i.toNat : ℤ) = i := Int.toNat_of_nonneg hin.1
      have h' : (((baseRows s g f+s)*(s*g) : ℕ) : ℤ) ≤ (i.toNat : ℤ) := by
        simpa only [he, Nat.mul_assoc] using hi
      exact_mod_cast h'
    · have hn : ¬ i < 0 := by
        have h0 : (0 : ℤ) ≤ (((baseRows s g f+s)*s*g : ℕ) : ℤ) := by exact_mod_cast (Nat.zero_le ((baseRows s g f+s)*s*g))
        omega
      rw [stepFourTape, dif_neg hin, if_neg hn]

/-- Execute steps 5--8 on the finite result of steps 1--4. The second grid
has origin -H, exactly representing H leading zero sentinels and H trailing
one sentinels before the last column-sort round, followed by their removal. -/
def groupedColumnsort01 (q s g H : ℕ) (hg : 0 < g) (hH : 0 < H)
    (f : Fin s → Fin (q*s*g) → Bool) : Fin (s*q*(s*g)) → Bool := fun i =>
  blockSort (2*H) (by omega) (-H)
    (blockSort (2*H) (by omega) 0 (stepFourTape q s g hg f)) (i : ℤ)

/-- Complete zero-one sortedness for the concrete eight-step grouped
Columnsort. `2H=q*s*g` is exactly the even column-height condition. The
input is arbitrary; no intermediate sortedness or band premise is assumed. -/
theorem groupedColumnsort01_monotone (q s g H : ℕ)
    (hs : 0 < s) (hg : 0 < g) (hH : 0 < H)
    (hheight : q*s*g = 2*H) (hr : 2*s*(s+1) ≤ q*s)
    (f : Fin s → Fin (q*s*g) → Bool) :
    Monotone (groupedColumnsort01 q s g H hg hH f) := by
  have hlen := dirtyRegion_halfColumn q s g hr
  have hsmall : s*s*g ≤ H := by omega
  have hlen' :
      (((baseRows s g f+s)*s*g : ℕ) : ℤ) -
        ((baseRows s g f*s*g : ℕ) : ℤ) ≤ (H : ℤ) := by
    have hh : ((s*s*g : ℕ) : ℤ) ≤ (H : ℤ) := by exact_mod_cast hsmall
    push_cast
    push_cast at hh
    nlinarith
  have hm := two_grid_sorts_monotone H hH (stepFourTape q s g hg f)
    _ _ (stepFourTape_band q s g hs hg f) hlen'
  intro i j hij
  apply hm
  exact_mod_cast hij

/-- The concrete output also has the standard List.Pairwise ordering
predicate, usable by the remainder of the sorting development. -/
theorem groupedColumnsort01_pairwise (q s g H : ℕ)
    (hs : 0 < s) (hg : 0 < g) (hH : 0 < H)
    (hheight : q*s*g = 2*H) (hr : 2*s*(s+1) ≤ q*s)
    (f : Fin s → Fin (q*s*g) → Bool) :
    (List.ofFn (groupedColumnsort01 q s g H hg hH f)).Pairwise (· ≤ ·) :=
  List.pairwise_ofFn.2 (fun _ _ hij =>
    groupedColumnsort01_monotone q s g H hs hg hH hheight hr f hij.le)

end CSL.Columnsort


