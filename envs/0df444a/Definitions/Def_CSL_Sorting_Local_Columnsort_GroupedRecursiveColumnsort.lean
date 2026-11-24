-- Prove2me | Definitions.Def_CSL_Sorting_Local_Columnsort_GroupedRecursiveColumnsort
-- name    : CSL_Sorting_Local_Columnsort_GroupedRecursiveColumnsort
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:08:28.375804+00:00
-- url     : https://prove2.me/theorems/0a439b48-55be-4f24-a465-227ad675f3ae
-- title:
--   Coded sorting library: Sorting / Local / Columnsort / GroupedRecursiveColumnsort
-- statement:
--   Module `CodedSorting.Sorting.Local.Columnsort.GroupedRecursiveColumnsort` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Four finite batches of actual recursive-sorter calls for Columnsort.
--   The returned trace is assembled from exactly these invocations.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Sorting.Local.Columnsort.GroupedRecursiveColumnsort

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Sorting_Local_Columnsort_FiniteColumnsort
import Definitions.Def_CSL_Shared_Programs_LocalTrace

section GroupedFiniteColumnsort
/-! Four finite batches of actual recursive-sorter calls for Columnsort.
The returned trace is assembled from exactly these invocations. -/

namespace CSL.GroupedRecursiveColumnsort

open CSL.Columnsort CSL.RecursiveColumnsort

variable {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α]

/-- Entire record groups from the first returned batch, in cyclic order.
The within-group coordinate is retained by the generic kernel. -/
def secondInput (q s g : ℕ) (hg : 0 < g) (one : Fin s → Fin (q*s*g) → α)
    (c : Fin s) (i : Fin (s*(q*g))) : α :=
  let p : Fin s × Fin (q*g) := finProdFinEquiv.symm i
  one p.1 ⟨stripeIndex s g c.val p.2.val,
    stripeIndex_lt q s g c.val p.2.val hg c.isLt p.2.isLt⟩

/-- The inverse whole-group transpose, with a finite sentinel extension.
It only reads returned values of the second batch, never sorts them again. -/
def afterTwoTape (q s g : ℕ) (two : Fin s → Fin (s*(q*g)) → α) (i : ℤ) : α :=
  if hi : 0 ≤ i ∧ i < (s*q*(s*g) : ℕ) then
    let j : Fin (s*q*(s*g)) := ⟨i.toNat, (Int.toNat_lt hi.1).2 hi.2⟩
    let p : Fin (s*q) × Fin (s*g) := finProdFinEquiv.symm j
    let cv : Fin s × Fin g := finProdFinEquiv.symm p.2
    two cv.1 ⟨p.1.val*g+cv.2.val, by have := p.1.isLt; have := cv.2.isLt; nlinarith⟩
  else if i < 0 then ⊥ else ⊤

/-- Four actual finite batches: s,s,s,s+1 child calls. Their returned values
feed the next batch; every trace item comes from those same invocations. -/
def fourRounds (sorter : Sorter α) (q s g H : ℕ) (hg : 0 < g)
    (f : Fin s → Fin (q*s*g) → α) : FourRun α (s*q*(s*g)) :=
  let first := fun c : Fin s => sorter (q*s*g) (f c)
  let second := fun c : Fin s => sorter (s*(q*g)) (secondInput q s g hg (fun c => (first c).output) c)
  let A := afterTwoTape q s g (fun c => (second c).output)
  let third := fun c : Fin s => sorter (q*s*g) (gridInput (q*s*g) 0 A c)
  let G := gridTape s (q*s*g) 0 (fun c => (third c).output)
  let fourth := fun c : Fin (s+1) => sorter (q*s*g) (gridInput (q*s*g) (-H) G c)
  { output := fun i => gridTape (s+1) (q*s*g) (-H) (fun c => (fourth c).output) (i : ℤ)
    first := List.ofFn (fun c => (first c).trace)
    second := List.ofFn (fun c => (second c).trace)
    third := List.ofFn (fun c => (third c).trace)
    fourth := List.ofFn (fun c => (fourth c).trace) }

theorem fourRounds_batch_lengths (sorter : Sorter α) (q s g H : ℕ) (hg : 0 < g)
    (f : Fin s → Fin (q*s*g) → α) :
    let result := fourRounds sorter q s g H hg f
    result.first.length = s ∧ result.second.length = s ∧
      result.third.length = s ∧ result.fourth.length = s+1 := by
  simp [fourRounds]

/-- Input to every stage-three batch has the claimed complete finite extent. -/
theorem afterTwoTape_bounds (q s g : ℕ) (two : Fin s → Fin (s*(q*g)) → α) :
    TapeBounds (afterTwoTape q s g two) 0 (s*q*(s*g)) := by
  constructor
  · intro i hi
    have hn : ¬(0 ≤ i ∧ i < (s*q*(s*g) : ℕ)) := by omega
    rw [afterTwoTape, dif_neg hn, if_pos hi]
  · intro i hi
    have hn : ¬(0 ≤ i ∧ i < (s*q*(s*g) : ℕ)) := by omega
    have hp : (0 : ℤ) ≤ ((s*q*(s*g) : ℕ) : ℤ) := by exact_mod_cast Nat.zero_le (s*q*(s*g))
    have h0 : ¬i<0 := by omega
    rw [afterTwoTape, dif_neg hn, if_neg h0]

/-- Enlarging the sentinel interval by half a column gives exactly s+1
finite columns in the final batch. -/
theorem gridTape_half_bounds (q s g H : ℕ) (hh : q*s*g = 2*H)
    (f : Fin s → Fin (q*s*g) → α) :
    TapeBounds (gridTape s (q*s*g) 0 f) (-H) ((s+1)*(q*s*g)) := by
  have hb := gridTape_bounds s (q*s*g) 0 f
  constructor
  · intro i hi
    apply hb.1
    have hH : (0 : ℤ) ≤ H := by exact_mod_cast Nat.zero_le H
    omega
  · intro i hi
    apply hb.2
    have he : ((q*s*g : ℕ) : ℤ) = 2*(H : ℤ) := by exact_mod_cast hh
    have hn : (0 : ℤ) ≤ H := by exact_mod_cast Nat.zero_le H
    push_cast at hi ⊢
    nlinarith

omit [OrderBot α] [OrderTop α] in
theorem blockSortKeys_height_congr {B C : ℕ} (h : B = C) (hB : 0 < B) (hC : 0 < C)
    (offset : ℤ) (f : ℤ → α) :
    blockSortKeys B hB offset f = blockSortKeys C hC offset f := by
  subst C
  rfl

/-- All finite returned values agree with the previously verified eight-step
algorithm once each recursive child returns its correct sorted permutation.
There is no extra hidden call to the specification sorter in fourRounds. -/
theorem fourRounds_output_eq (sorter : Sorter α)
    (hc : ∀ n (f : Fin n → α), Correct f (sorter n f).output)
    (q s g H : ℕ) (hg : 0 < g) (hH : 0 < H) (hh : q*s*g = 2*H)
    (f : Fin s → Fin (q*s*g) → α) :
    (fourRounds sorter q s g H hg f).output = groupedColumnsort q s g H hg hH f := by
  have hR : 0 < q*s*g := by omega
  have he (n : ℕ) (f : Fin n → α) := (hc n f).eq_sortColumn
  let A := afterTwoTape q s g (fun c => sortColumn (secondInput q s g hg (fun c => sortColumn (f c)) c))
  have hA : A = stepFourTapeKeys q s g hg f := by
    funext i
    try dsimp only [A, afterTwoTape, stepFourTapeKeys]
    split_ifs with h hi
    · rfl
    · rfl
    · rfl
  have hN : s*q*(s*g) = s*(q*s*g) := by ring
  have hAbounds : TapeBounds A 0 (s*(q*s*g)) := by
    rw [← hN]
    exact afterTwoTape_bounds q s g _
  let G := gridTape s (q*s*g) 0 (fun c => sortColumn (gridInput (q*s*g) 0 A c))
  have hG : G = blockSortKeys (2*H) (by omega) 0 (stepFourTapeKeys q s g hg f) := by
    change gridTape s (q*s*g) 0 _ = _
    rw [gridTape_sort_eq s (q*s*g) hR 0 A hAbounds,
      blockSortKeys_height_congr hh hR (by omega), hA]
  have hGb := gridTape_half_bounds q s g H hh (fun c => sortColumn (gridInput (q*s*g) 0 A c))
  have hlast : gridTape (s+1) (q*s*g) (-H)
      (fun c => sortColumn (gridInput (q*s*g) (-H) G c)) =
      blockSortKeys (2*H) (by omega) (-H) G := by
    rw [gridTape_sort_eq (s+1) (q*s*g) hR (-H) G hGb,
      blockSortKeys_height_congr hh hR (by omega)]
  funext i
  simp only [fourRounds, he]
  change gridTape (s+1) (q*s*g) (-H)
      (fun c => sortColumn (gridInput (q*s*g) (-H) G c)) (i : ℤ) = _
  rw [hlast, hG]
  rfl

/-- Actual finite batches preserve the full input and sort it. -/
theorem fourRounds_correct (sorter : Sorter α)
    (hc : ∀ n (f : Fin n → α), Correct f (sorter n f).output)
    (q s g H : ℕ) (hg : 0 < g) (hs : 0 < s) (hH : 0 < H)
    (hh : q*s*g = 2*H) (hr : 2*s*(s+1) ≤ q*s)
    (f : Fin s → Fin (q*s*g) → α) :
    Correct (flattenKeys q s g f) (fourRounds sorter q s g H hg f).output := by
  rw [fourRounds_output_eq sorter hc q s g H hg hH hh f]
  exact ⟨groupedColumnsort_monotone q s g H hs hg hH hh hr f,
    (groupedColumnsort_correct q s g H hs hg hH hh hr f).2⟩

end CSL.GroupedRecursiveColumnsort
end GroupedFiniteColumnsort

section RecursiveColumnsort
/-! Actual structurally recursive local Columnsort, with its execution trace.
The three-level memory and cost results are connected to this very trace in
LocalSortingCost; no numerical recurrence is substituted for the program. -/

namespace CSL.RecursiveColumnsort

open CSL.Columnsort CSL.LocalShape CSL.LocalTrace

variable {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α]

/-- Padding length of the exact finite core, written in its coordinate order. -/
def paddedLength (n : ℕ) : ℕ := sizeChoice n * (sizeChoice n)^2 * (sizeChoice n*1)

theorem paddedLength_eq (n : ℕ) : paddedLength n = sizeChoice n ^ 4 := by
  unfold paddedLength
  ring

theorem paddedLength_ge (n : ℕ) : n ≤ paddedLength n := by
  rw [paddedLength_eq]
  exact padding_ge n

/-- Column-major view of the actual padded parent input. -/
def paddedInput {n : ℕ} (f : Fin n → α) :
    Fin (sizeChoice n) → Fin ((sizeChoice n)^2*sizeChoice n*1) → α := fun a j =>
  pad (N := paddedLength n) f ((inputEquiv ((sizeChoice n)^2) (sizeChoice n) 1).symm (a,j))

omit [OrderBot α] in
theorem flatten_paddedInput {n : ℕ} (f : Fin n → α) :
    flattenKeys ((sizeChoice n)^2) (sizeChoice n) 1 (paddedInput f) =
      pad (N := paddedLength n) f := by
  funext i
  simp only [flattenKeys, paddedInput]
  change pad f ((inputEquiv ((sizeChoice n)^2) (sizeChoice n) 1).symm
    ((inputEquiv ((sizeChoice n)^2) (sizeChoice n) 1) i)) = pad f i
  rw [Equiv.symm_apply_apply]

/-- One actual non-leaf call, including padding, four child batches, and
removing only the parent's own padding. -/
def nodeRun (sorter : Sorter α) (n : ℕ) (f : Fin n → α) : Run α n :=
  let s := sizeChoice n
  let result := fourRounds sorter (s^2) s (columnLength n/2) (paddedInput f)
  { output := trim (paddedLength_ge n) result.output
    trace := .node n s result.first result.second result.third result.fourth }

/-- The cutoff is checked at each node. Fuel zero is a terminal memory call;
for the requested input range n≤H², three_levels_fit proves its size is legal. -/
def localRun (H : ℕ) (_hH : 0 < H) : (fuel n : ℕ) → (Fin n → α) → Run α n
  | 0, n, f => ⟨sortColumn f, .leaf n⟩
  | fuel+1, n, f =>
      if n ≤ 512*H then ⟨sortColumn f, .leaf n⟩
      else nodeRun (localRun H _hH fuel) n f

/-- Exact shape checks used when the recursive branch is taken. -/
theorem node_shape (n H : ℕ) (hH : 0 < H) (hn : 512*H < n) :
    0 < sizeChoice n ∧ 0 < columnLength n/2 ∧
      (sizeChoice n)^2*sizeChoice n*1 = 2*(columnLength n/2) ∧
      2*sizeChoice n*(sizeChoice n+1) ≤ (sizeChoice n)^2*sizeChoice n := by
  have hh := shape_bound n H hH hn
  have hs : 8 ≤ sizeChoice n := hh.2.1
  have hexp : sizeExponent n = (sizeExponent n-1)+1 := by omega
  have hsEven : sizeChoice n = 2*(2^(sizeExponent n-1)) := by
    conv_lhs => unfold sizeChoice; rw [hexp, pow_succ]
    ring
  have hrEven : columnLength n = 2*((sizeChoice n)^2*(2^(sizeExponent n-1))) := by
    unfold columnLength
    calc
      (sizeChoice n)^3 = (sizeChoice n)^2*sizeChoice n := by ring
      _ = _ := by conv_lhs => rhs; rw [hsEven]
                  ring
  have hrLow : 2 ≤ columnLength n := by
    have h := Nat.pow_le_pow_left hs 3
    norm_num at h
    exact le_trans (by norm_num : 2 ≤ 512) h
  have hrep : (sizeChoice n)^2*sizeChoice n*1 = columnLength n := by
    unfold columnLength
    ring
  have hsmall : 2*(sizeChoice n+1) ≤ (sizeChoice n)^2 := by nlinarith
  have hbig := Nat.mul_le_mul_left (sizeChoice n) hsmall
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [hrep]
    omega
  · nlinarith

/-- A non-leaf execution is correct whenever all its actual child executions
are correct. Padding is removed using the separately proved trim theorem. -/
theorem nodeRun_correct (sorter : Sorter α)
    (hc : ∀ n (f : Fin n → α), Correct f (sorter n f).output)
    (n H : ℕ) (hH : 0 < H) (hn : 512*H < n) (f : Fin n → α) :
    Correct f (nodeRun sorter n f).output := by
  obtain ⟨hs,hhalf,hheight,hr⟩ := node_shape n H hH hn
  have h := fourRounds_correct sorter hc ((sizeChoice n)^2) (sizeChoice n)
    (columnLength n/2) hs hhalf hheight hr (paddedInput f)
  rw [flatten_paddedInput] at h
  exact trim_correct (paddedLength_ge n) f _ h

/-- Correctness follows by structural recursion on the actual fuel; there
is no assumed termination or assumed correctness of a recursive oracle. -/
theorem localRun_correct (H : ℕ) (hH : 0 < H) (fuel n : ℕ) (f : Fin n → α) :
    Correct f (localRun H hH fuel n f).output := by
  induction fuel generalizing n with
  | zero => exact correct_sortColumn f
  | succ fuel ih =>
    by_cases hn : n ≤ 512*H
    · simpa only [localRun, if_pos hn] using correct_sortColumn f
    · simp only [localRun, if_neg hn]
      exact nodeRun_correct (localRun H hH fuel) (fun n f => ih n f) n H hH (by omega) f

/-- The real same-execution trace has precisely the four prescribed batches
and recursive column sizes. No cost inequality is included in this invariant. -/
theorem localRun_trace_fits (H : ℕ) (hH : 0 < H) (fuel n : ℕ) (f : Fin n → α) :
    Fits H fuel n (localRun H hH fuel n f).trace := by
  induction fuel generalizing n with
  | zero => exact Fits.leaf 0 n (Or.inl rfl)
  | succ fuel ih =>
    by_cases hn : n ≤ 512*H
    · simpa only [localRun, if_pos hn] using Fits.leaf (H := H) (fuel+1) n (Or.inr hn)
    · have liftIH (m : ℕ) (g : Fin m → α) (hm : m = columnLength n) :
          Fits H fuel (columnLength n) (localRun H hH fuel m g).trace := by
        rw [← hm]
        exact ih m g
      simp only [localRun, if_neg hn, nodeRun]
      apply Fits.node (by omega)
      · simp [fourRounds]
      · simp [fourRounds]
      · simp [fourRounds]
      · simp [fourRounds]
      all_goals
        intro child hchild
        simp only [fourRounds, List.mem_ofFn] at hchild
        obtain ⟨c,rfl⟩ := hchild
        apply liftIH
        unfold columnLength
        ring

end CSL.RecursiveColumnsort
end RecursiveColumnsort

section GroupedRecursiveColumnsort
/-! The near-memory variant sorts individual records while only permuting
whole groups. The group count, not record count, chooses each recursive shape.
The final input group may be partial; padding is removed by exact count. -/
namespace CSL.GroupedRecursiveColumnsort
open CSL.Columnsort CSL.RecursiveColumnsort
open CSL.LocalShape CSL.LocalTrace

variable {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α]

/-- Ceiling group count, including a possibly partial final group. -/
def groups (g n : ℕ) : ℕ := (n+g-1)/g

theorem groups_mul (g : ℕ) (hg : 0 < g) (n : ℕ) : groups g (n*g) = n := by
  unfold groups
  have he : n*g+g-1 = n*g+(g-1) := by omega
  rw [he, Nat.mul_comm n g, Nat.mul_add_div hg,
    Nat.div_eq_of_lt (by omega : g-1<g), Nat.add_zero]

theorem groups_capacity (g : ℕ) (hg : 0 < g) (n : ℕ) :
    n ≤ groups g n*g ∧ groups g n*g < n+g := by
  have hrem := Nat.mod_lt (n+g-1) hg
  have he := Nat.mod_add_div (n+g-1) g
  have hdiv := Nat.div_mul_le_self (n+g-1) g
  have hsub : n+g-1+1 = n+g := by omega
  unfold groups
  constructor
  · nlinarith
  · omega

/-- Number of record positions after the current group's shape padding. -/
def paddedRecords (g n : ℕ) : ℕ :=
  sizeChoice (groups g n) * (sizeChoice (groups g n))^2 * (sizeChoice (groups g n)*g)

theorem paddedRecords_eq (g n : ℕ) : paddedRecords g n = sizeChoice (groups g n)^4*g := by
  unfold paddedRecords
  ring

theorem paddedRecords_ge (g : ℕ) (hg : 0 < g) (n : ℕ) : n ≤ paddedRecords g n := by
  rw [paddedRecords_eq]
  exact le_trans (groups_capacity g hg n).1 (Nat.mul_le_mul_right g (padding_ge _))

/-- Padded input in column-major record order; grouping does not coalesce
records into an indivisible comparison key. -/
def paddedInput (g : ℕ) {n : ℕ} (f : Fin n → α) :
    Fin (sizeChoice (groups g n)) →
      Fin ((sizeChoice (groups g n))^2*sizeChoice (groups g n)*g) → α := fun a j =>
  pad (N := paddedRecords g n) f
    ((inputEquiv ((sizeChoice (groups g n))^2) (sizeChoice (groups g n)) g).symm (a,j))

omit [OrderBot α] in
theorem flatten_paddedInput (g : ℕ) {n : ℕ} (f : Fin n → α) :
    flattenKeys ((sizeChoice (groups g n))^2) (sizeChoice (groups g n)) g (paddedInput g f) =
      pad (N := paddedRecords g n) f := by
  funext i
  simp only [flattenKeys, paddedInput]
  change pad f ((inputEquiv ((sizeChoice (groups g n))^2) (sizeChoice (groups g n)) g).symm
    ((inputEquiv ((sizeChoice (groups g n))^2) (sizeChoice (groups g n)) g) i)) = pad f i
  rw [Equiv.symm_apply_apply]

/-- One grouped node. Child sorts still accept every individual record. -/
def nodeRun (g : ℕ) (hg : 0 < g) (sorter : Sorter α) (n : ℕ) (f : Fin n → α) : Run α n :=
  let m := groups g n
  let s := sizeChoice m
  let result := fourRounds sorter (s^2) s g ((columnLength m/2)*g) hg (paddedInput g f)
  { output := trim (paddedRecords_ge g hg n) result.output
    trace := .node m s result.first result.second result.third result.fourth }

/-- Same actual algorithm at every recursive depth, with a group-count cutoff. -/
def localRun (D g : ℕ) (_hD : 0 < D) (hg : 0 < g) :
    (fuel n : ℕ) → (Fin n → α) → Run α n
  | 0,n,f => ⟨sortColumn f,.leaf (groups g n)⟩
  | fuel+1,n,f =>
    if groups g n ≤ 512*D then ⟨sortColumn f,.leaf (groups g n)⟩
    else nodeRun g hg (localRun D g _hD hg fuel) n f

/-- The grouped node satisfies the full D.1 shape conditions in records. -/
theorem nodeRun_correct (g : ℕ) (hg : 0 < g) (sorter : Sorter α)
    (hc : ∀ n (f : Fin n → α), Correct f (sorter n f).output)
    (n D : ℕ) (hD : 0 < D) (hn : 512*D < groups g n) (f : Fin n → α) :
    Correct f (nodeRun g hg sorter n f).output := by
  obtain ⟨hs,hhalf,hheight,hr⟩ := RecursiveColumnsort.node_shape (groups g n) D hD hn
  have hheight' : (sizeChoice (groups g n))^2*sizeChoice (groups g n)*g =
      2*((columnLength (groups g n)/2)*g) := by nlinarith
  have h := fourRounds_correct sorter hc ((sizeChoice (groups g n))^2)
    (sizeChoice (groups g n)) g ((columnLength (groups g n)/2)*g) hg hs
    (Nat.mul_pos hhalf hg) hheight' hr (paddedInput g f)
  rw [flatten_paddedInput] at h
  exact trim_correct (paddedRecords_ge g hg n) f _ h

theorem localRun_correct (D g : ℕ) (hD : 0 < D) (hg : 0 < g)
    (fuel n : ℕ) (f : Fin n → α) : Correct f (localRun D g hD hg fuel n f).output := by
  induction fuel generalizing n with
  | zero => exact correct_sortColumn f
  | succ fuel ih =>
    by_cases hn : groups g n ≤ 512*D
    · simpa only [localRun, if_pos hn] using correct_sortColumn f
    · simp only [localRun, if_neg hn]
      exact nodeRun_correct g hg (localRun D g hD hg fuel) (fun n f => ih n f)
        n D hD (by omega) f

/-- The trace carries group counts but was emitted while sorting the full
record arrays; all four batches come from those actual recursive calls. -/
theorem localRun_trace_fits (D g : ℕ) (hD : 0 < D) (hg : 0 < g)
    (fuel n : ℕ) (f : Fin n → α) :
    Fits D fuel (groups g n) (localRun D g hD hg fuel n f).trace := by
  induction fuel generalizing n with
  | zero => exact Fits.leaf 0 (groups g n) (Or.inl rfl)
  | succ fuel ih =>
    by_cases hn : groups g n ≤ 512*D
    · simpa only [localRun, if_pos hn] using
        Fits.leaf (H := D) (fuel+1) (groups g n) (Or.inr hn)
    · have liftIH (m : ℕ) (f' : Fin m → α)
          (hm : m = columnLength (groups g n)*g) :
          Fits D fuel (columnLength (groups g n)) (localRun D g hD hg fuel m f').trace := by
        have he : groups g m = columnLength (groups g n) := by rw [hm, groups_mul g hg]
        rw [←he]
        exact ih m f'
      simp only [localRun, if_neg hn, nodeRun]
      apply Fits.node (by omega)
      · simp [fourRounds]
      · simp [fourRounds]
      · simp [fourRounds]
      · simp [fourRounds]
      all_goals
        intro child hchild
        simp only [fourRounds, List.mem_ofFn] at hchild
        obtain ⟨c,rfl⟩ := hchild
        apply liftIH
        unfold columnLength
        ring

end CSL.GroupedRecursiveColumnsort
end GroupedRecursiveColumnsort


