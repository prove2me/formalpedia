-- Prove2me | Definitions.Def_CSL_Sorting_Local_Framework_LocalSortingComplete
-- name    : CSL_Sorting_Local_Framework_LocalSortingComplete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:37:10.285541+00:00
-- url     : https://prove2.me/theorems/eef96244-1df1-4445-9737-4a2c97d12bc9
-- title:
--   Coded sorting library: Sorting / Local / Framework / LocalSortingComplete
-- statement:
--   Module `CodedSorting.Sorting.Local.Framework.LocalSortingComplete` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Costs are computed from the trace emitted by the recursive sorter itself.
--   Leaf batches share block buffers across all columns.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Sorting.Local.Framework.LocalSortingComplete

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Sorting_Local_Framework_LocalSortingCost
import Definitions.Def_CSL_Shared_Programs_GroupedShape
import Definitions.Def_CSL_Shared_Programs_NormalizationComplete
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_CSL_Sorting_Bounds_MergeRounds

section GroupedLocalSortingCost
/-! Costs are computed from the trace emitted by the recursive sorter itself.
Leaf batches share block buffers across all columns. -/
namespace CSL.GroupedLocalSortingCost
open RecursiveColumnsort LocalShape BucketMachine LocalSortingCost

/-- Padding, half-column shift, unshift, and removal of this call's padding.
Each pass reads its source stream and writes its destination stream. -/
def scanTransfers (B g n s : ℕ) :=
  2 * blockCount B (n*g) + 4 * blockCount B (s ^ 4*g) +
    2 * blockCount B ((s ^ 4 + s ^ 3)*g)

mutual
  def traceCost (B g : ℕ) (exchangeCost : InterchangeCost) : CallTree → ℕ
    | .leaf n => leafScan B (n*g)
    | .node n s first second third fourth =>
        6 * exchangeCost (sizeExponent n) (s ^ 4*g) + scanTransfers B g n s +
          batchCharge B (summarize B g exchangeCost first) +
          batchCharge B (summarize B g exchangeCost second) +
          batchCharge B (summarize B g exchangeCost third) +
          batchCharge B (summarize B g exchangeCost fourth)
  def summarize (B g : ℕ) (exchangeCost : InterchangeCost) : List CallTree → BatchSummary
    | [] => ⟨true, 0, 0⟩
    | head :: tail =>
        let rest := summarize B g exchangeCost tail
        ⟨CallTree.isLeaf head && rest.allLeaves, CallTree.inputSize head*g + rest.volume,
          traceCost B g exchangeCost head + rest.individualCost⟩
end

theorem summarize_spec (B g : ℕ) (exchangeCost : InterchangeCost) (trees : List CallTree) :
    summarize B g exchangeCost trees =
      ⟨trees.all CallTree.isLeaf, (trees.map (fun t => CallTree.inputSize t*g)).sum,
        (trees.map (traceCost B g exchangeCost)).sum⟩ := by
  induction trees with
  | nil => rfl
  | cons head tail ih => simp [summarize, ih]

private theorem sum_bound (trees : List CallTree) (f : CallTree → ℕ) (B A : ℕ)
    (h : ∀ tree ∈ trees, f tree * B ≤ A) : (trees.map f).sum * B ≤ trees.length * A := by
  induction trees with
  | nil => simp
  | cons tree rest ih =>
    have ht := h tree (by simp)
    have hr := ih (fun tree ht => h tree (by simp [ht]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-- A short-column batch uses the shared-buffer machine. A recursive batch
may pay per child because each such child is at least one block long. -/
theorem batch_bound (B g H fuel r D : ℕ) (hB : 0 < B) (hg : 0 < g) (hBH : B ≤ 2*H*g) (hD : 1 ≤ D)
    (exchangeCost : InterchangeCost) (trees : List CallTree)
    (hf : ∀ tree ∈ trees, LocalTrace.Fits H fuel r tree)
    (hc : ∀ tree ∈ trees, traceCost B g exchangeCost tree * B ≤ D * (r*g + B)) :
    batchCharge B (summarize B g exchangeCost trees) * B ≤ 2 * D * trees.length * (r*g) + 2 * B := by
  have hv : (trees.map (fun t => CallTree.inputSize t*g)).sum = trees.length * (r*g) := by
    have he : trees.map (fun t => CallTree.inputSize t*g) = trees.map (fun _ => r*g) := by
      apply List.map_congr_left
      intro tree ht
      rw [fits_inputSize (hf tree ht)]
    rw [he]
    simp
  rw [summarize_spec]
  unfold batchCharge
  try dsimp only
  split
  · have hs := leafScan_bound B hB (trees.length * (r*g))
    rw [hv]
    have hmul := Nat.mul_le_mul_right (trees.length * (r*g)) hD
    nlinarith
  · rename_i hnot
    have hr : B ≤ r*g := by
      by_contra h
      have hsmall : r ≤ 512 * H := by
        by_contra hbig
        have hm := Nat.mul_lt_mul_of_pos_right (show 2*H < r by omega) hg
        omega
      have hall : trees.all CallTree.isLeaf = true := by
        apply List.all_eq_true.mpr
        intro tree ht
        rw [(hf tree ht).leaf_of_small hsmall]
        rfl
      exact hnot hall
    have hsum := sum_bound trees (traceCost B g exchangeCost) B (D * (r*g + B)) hc
    have hm := Nat.mul_le_mul_left (trees.length * D) hr
    nlinarith

theorem scan_bound (B g : ℕ) (hB : 0 < B) (hg : 0 < g) (n : ℕ) (hn : 1 < n) (hBn : B ≤ n*g) :
    scanTransfers B g n (sizeChoice n) * B ≤ 138 * (n*g) := by
  have hnB := blockCount_capacity B hB (n*g)
  have hpB := blockCount_capacity B hB (sizeChoice n ^ 4*g)
  have heB := blockCount_capacity B hB ((sizeChoice n ^ 4 + sizeChoice n ^ 3)*g)
  have hp := padding_lt n hn
  have hs : 1 ≤ sizeChoice n := Nat.one_le_pow _ _ (by norm_num)
  have hr : sizeChoice n ^ 3 ≤ sizeChoice n ^ 4 := by
    calc
      sizeChoice n ^ 3 ≤ sizeChoice n * sizeChoice n ^ 3 := Nat.le_mul_of_pos_left _ (by omega)
      _ = sizeChoice n ^ 4 := by ring
  have hpg := Nat.mul_lt_mul_of_pos_right hp hg
  have hrg := Nat.mul_le_mul_right g hr
  unfold scanTransfers
  nlinarith only [hnB,hpB,heB,hpg,hrg,hBn]

/-- Exact finite-depth cost theorem over the actual execution trace.
The only algorithmic cost premise is a bound for the address-exchange
primitive at each nonterminal call. Four leaf batches share stream buffers. -/
theorem trace_cost_bound (B g H C : ℕ) (hB : 0 < B) (hg : 0 < g) (hH : 0 < H) (hBH : B ≤ 2*H*g)
    (exchangeCost : InterchangeCost)
    (hx : ∀ n, 512 * H < n → n ≤ H ^ 2 →
      exchangeCost (sizeExponent n) (sizeChoice n ^ 4*g) * B ≤ C * (sizeChoice n ^ 4*g + B))
    (fuel n : ℕ) (tree : CallTree) (hn : n ≤ H ^ 2) (hf : LocalTrace.Fits H fuel n tree) :
    traceCost B g exchangeCost tree * B ≤ 300 ^ fuel * (C + 2) * (n*g + B) := by
  induction fuel generalizing n tree with
  | zero =>
    rw [hf.leaf_of_zero]
    have hs := leafScan_bound B hB (n*g)
    simp only [traceCost, pow_zero, Nat.one_mul]
    exact le_trans hs (Nat.mul_le_mul_right (n*g+B) (by omega : 2 ≤ C+2))
  | succ fuel ih =>
    cases hf with
    | leaf _ _ hleaf =>
      have hs := leafScan_bound B hB (n*g)
      have hpow : 1 ≤ 300 ^ (fuel + 1) := Nat.one_le_pow _ _ (by omega)
      have hmul := Nat.mul_le_mul_right ((C + 2) * (n*g + B)) hpow
      simp only [traceCost]
      have h1 := le_trans hs (Nat.mul_le_mul_right (n*g+B) (by omega : 2 ≤ C+2))
      exact le_trans h1 (by simpa only [Nat.one_mul, Nat.mul_assoc] using hmul)
    | node hlarge hfirst hsecond hthird hfourth hf1 hf2 hf3 hf4 =>
      have h512 : 512 < n := by omega
      have hrn := column_lt n h512
      have hrH : columnLength n ≤ H ^ 2 := by omega
      let D := 300 ^ fuel * (C + 2)
      have hpow : 1 ≤ 300 ^ fuel := Nat.one_le_pow _ _ (by omega)
      have hCD : C + 2 ≤ D := Nat.le_mul_of_pos_left _ (by omega)
      have hD : 1 ≤ D := by omega
      have h1 := batch_bound B g H fuel (columnLength n) D hB hg hBH hD exchangeCost _ hf1
        (fun child hc => ih _ _ hrH (hf1 child hc))
      have h2 := batch_bound B g H fuel (columnLength n) D hB hg hBH hD exchangeCost _ hf2
        (fun child hc => ih _ _ hrH (hf2 child hc))
      have h3 := batch_bound B g H fuel (columnLength n) D hB hg hBH hD exchangeCost _ hf3
        (fun child hc => ih _ _ hrH (hf3 child hc))
      have h4 := batch_bound B g H fuel (columnLength n) D hB hg hBH hD exchangeCost _ hf4
        (fun child hc => ih _ _ hrH (hf4 child hc))
      rw [hfirst] at h1
      rw [hsecond] at h2
      rw [hthird] at h3
      rw [hfourth] at h4
      have hBn : B ≤ n*g := le_trans hBH (Nat.mul_le_mul_right g (by omega : 2*H ≤ n))
      have hscan := scan_bound B g hB hg n (by omega) hBn
      have hexchange := hx n hlarge hn
      have hpad := padding_lt n (by omega)
      have hvolume := child_volume n (by omega)
      have hxBound : 6 * exchangeCost (sizeExponent n) (sizeChoice n ^ 4*g) * B ≤ 102 * C * (n*g) := by
        have hm := Nat.mul_le_mul_left C (show sizeChoice n ^ 4*g + B ≤ 17 * (n*g) by
          have hpg := Nat.mul_lt_mul_of_pos_right hpad hg
          nlinarith only [hpg,hBn])
        nlinarith only [hexchange, hm]
      have hvolumeD := Nat.mul_le_mul_left (2 * D) (Nat.mul_le_mul_right g (Nat.le_of_lt hvolume))
      have hCDn := Nat.mul_le_mul_right (n*g) hCD
      have hpower : 300 ^ (fuel + 1) * (C + 2) = 300 * D := by
        try dsimp [D]
        rw [pow_succ]
        ring
      simp only [traceCost]
      rw [hpower]
      nlinarith only [h1, h2, h3, h4, hscan, hxBound, hvolumeD, hCDn, hBn,
        Nat.zero_le (D * B)]


/-- Three-level bound for the trace emitted by the actual grouped algorithm.
The size premise is stated in groups and the conclusion charges all records. -/
theorem actual_grouped_bound (B g H C : ℕ) (hB : 0 < B) (hg : 0 < g)
    (hH : 0 < H) (hBH : B ≤ 2*H*g) (exchangeCost : InterchangeCost)
    (hx : ∀ m, 512*H < m → m ≤ H^2 →
      exchangeCost (sizeExponent m) (sizeChoice m^4*g)*B ≤ C*(sizeChoice m^4*g+B))
    {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α]
    (n : ℕ) (f : Fin n → α) (hn : GroupedRecursiveColumnsort.groups g n ≤ H^2) :
    let result := GroupedRecursiveColumnsort.localRun H g hH hg 3 n f
    Correct f result.output ∧
      traceCost B g exchangeCost result.trace*B ≤
        27000000*(C+2)*(GroupedRecursiveColumnsort.groups g n*g+B) ∧
      leavesFit H result.trace := by
  have hf := GroupedRecursiveColumnsort.localRun_trace_fits H g hH hg 3 n f
  refine ⟨GroupedRecursiveColumnsort.localRun_correct H g hH hg 3 n f,?_,
    three_level_leaves_fit hH hn hf⟩
  simpa using trace_cost_bound B g H C hB hg hH hBH exchangeCost hx 3
    (GroupedRecursiveColumnsort.groups g n) _ hn hf

end CSL.GroupedLocalSortingCost
end GroupedLocalSortingCost

section GroupedNearMemory
/-! The actual grouped sorter gains the smaller near-memory field width.
Only the physical address-interchange cost is an external primitive contract. -/
namespace CSL.GroupedNearMemory
open LocalShape RecursiveColumnsort LocalSortingCost GroupedShape

/-- Full record correctness and same-trace cost, using the computed smaller
field width log₂(n/H)+3 rather than the scalar width log₂ H. -/
theorem grouped_near_memory (B H n : ℕ) (hB : 0 < B) (hH : 0 < H)
    (hBH : B ≤ H) (hHn : H ≤ n) (hg2 : 2 ≤ groupSize H n)
    (rate : ℕ → ℕ) (hrate : Monotone rate) (exchangeCost : InterchangeCost)
    (hx : ∀ t V, exchangeCost t V*B ≤ rate t*(V+B))
    {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α] (f : Fin n → α) :
    ∃ hg : 0 < groupSize H n, ∃ hD : 0 < memoryGroups H n,
      let result := GroupedRecursiveColumnsort.localRun
        (memoryGroups H n) (groupSize H n) hD hg 3 n f
      Correct f result.output ∧
        GroupedLocalSortingCost.traceCost B (groupSize H n) exchangeCost result.trace*B ≤
          54000000*(rate (Nat.log 2 (n/H)+3)+2)*(n+B) ∧
        leavesFit (memoryGroups H n) result.trace ∧ memoryGroups H n*groupSize H n ≤ H := by
  obtain ⟨hg,hD,hgH,hDg,hhalf,hlow,hhigh,hz,hvol⟩ := group_bounds H n hH hHn hg2
  have hBD : B ≤ 2*memoryGroups H n*groupSize H n := le_trans hBH hhalf
  have hcost (m : ℕ) (_hlarge : 512*memoryGroups H n < m)
      (hm : m ≤ memoryGroups H n^2) :
      exchangeCost (sizeExponent m) (sizeChoice m^4*groupSize H n)*B ≤
        rate (Nat.log 2 (n/H)+3)*(sizeChoice m^4*groupSize H n+B) := by
    have ht := field_width_bound H n hH hHn hg2 m hm
    exact le_trans (hx _ _) (Nat.mul_le_mul_right _ (hrate ht))
  have h := GroupedLocalSortingCost.actual_grouped_bound B (groupSize H n)
    (memoryGroups H n) (rate (Nat.log 2 (n/H)+3)) hB hg hD hBD exchangeCost hcost n f hz
  refine ⟨hg,hD,h.1,?_,h.2.2,hDg⟩
  have hm := Nat.mul_le_mul_left (27000000*(rate (Nat.log 2 (n/H)+3)+2))
    (show GroupedRecursiveColumnsort.groups (groupSize H n) n*groupSize H n+B ≤
      2*(n+B) by omega)
  exact le_trans h.2.1 (by nlinarith only [hm])

/-- Any leaf meeting the computed group cutoff fits in the original record
budget. This also covers the partially occupied final input group. -/
theorem leaf_records_fit (H n r : ℕ) (hH : 0 < H) (hHn : H ≤ n)
    (hg2 : 2 ≤ groupSize H n)
    (hr : GroupedRecursiveColumnsort.groups (groupSize H n) r ≤ 512*memoryGroups H n) :
    r ≤ 512*H := by
  have h := group_bounds H n hH hHn hg2
  have hc := (GroupedRecursiveColumnsort.groups_capacity (groupSize H n) h.1 r).1
  have hm := Nat.mul_le_mul_right (groupSize H n) hr
  have hb := Nat.mul_le_mul_left 512 h.2.2.2.1
  nlinarith only [hc,hm,hb]

/-- When grouping is not useful, the input is already within a constant
factor of H², justifying the scalar-width comparison in the other branch. -/
theorem small_group_large_input (H n : ℕ) (hn : 0 < n)
    (hg : groupSize H n < 2) : H^2 < 16*n := by
  have hr := Nat.mod_lt (H^2) (show 0 < 8*n by omega)
  have he := Nat.mod_add_div (H^2) (8*n)
  change H^2%(8*n)+(8*n)*groupSize H n=H^2 at he
  have hm := Nat.mul_le_mul_left (8*n) (show groupSize H n ≤ 1 by omega)
  nlinarith only [hr,he,hm]

/-- Bridge the exact integer-width estimate to the real logarithm of the
input-to-memory ratio, without identifying natural division with real division. -/
theorem log_width_le (H n : ℕ) (hH : 0 < H) (hHn : H ≤ n) :
    ((Nat.log 2 (n/H)+3 : ℕ) : ℝ) ≤
      Real.log ((n : ℝ)/(H : ℝ))/Real.log 2+3 := by
  let L := Nat.log 2 (n/H)
  have hq : 0 < n/H := Nat.div_pos hHn hH
  have hp := Nat.pow_log_le_self 2 (Nat.ne_of_gt hq)
  have hm := Nat.mul_le_mul_right H hp
  have hd := Nat.div_mul_le_self n H
  have hprod : 2^L*H ≤ n := le_trans hm hd
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hprodR : (2 : ℝ)^L*(H : ℝ) ≤ n := by exact_mod_cast hprod
  have hratio : (2 : ℝ)^L ≤ (n : ℝ)/(H : ℝ) := (le_div_iff₀ hHR).2 hprodR
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ)<2) L) hratio
  rw [Real.log_pow] at hlog
  have htwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h := (le_div_iff₀ htwo).2 hlog
  change ((L+3 : ℕ) : ℝ) ≤ _
  push_cast
  linarith

/-- Natural ceiling of the usual non-comparison interchange rate. -/
noncomputable def roundedRate (K a τ : ℝ) (t : ℕ) : ℕ :=
  ⌈K*(1+((t : ℝ)/a)^τ)⌉₊

theorem roundedRate_monotone (K a τ : ℝ) (hK : 0 ≤ K) (ha : 0 < a) (hτ : 0 ≤ τ) :
    Monotone (roundedRate K a τ) := by
  intro t u htu
  apply Nat.ceil_mono
  have ht : (0 : ℝ) ≤ (t : ℝ)/a := div_nonneg (Nat.cast_nonneg _) (le_of_lt ha)
  have htuR : (t : ℝ)/a ≤ (u : ℝ)/a :=
    div_le_div_of_nonneg_right (by exact_mod_cast htu) (le_of_lt ha)
  exact mul_le_mul_of_nonneg_left (add_le_add_right (Real.rpow_le_rpow ht htuR hτ) 1) hK

/-- A real-valued exchange-rate contract implies the integer contract used
by the actual trace proof; there is no assumed local-sort cost recurrence. -/
theorem rounded_exchange_contract (B : ℕ) (K a τ : ℝ)
    (exchangeCost : InterchangeCost)
    (hx : ∀ t V, ((exchangeCost t V*B : ℕ) : ℝ) ≤
      K*(1+((t : ℝ)/a)^τ)*((V+B : ℕ) : ℝ)) :
    ∀ t V, exchangeCost t V*B ≤ roundedRate K a τ t*(V+B) := by
  intro t V
  have hr := Nat.le_ceil (K*(1+((t : ℝ)/a)^τ))
  have hm := mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg (V+B))
  have h := le_trans (hx t V) hm
  exact_mod_cast h

/-- Absorb the additive three address bits and the ceiling into a fixed
constant. The remaining variable term is exactly (log(n/H)/a)^τ. -/
theorem rounded_rate_bound (K a τ x : ℝ) (t : ℕ) (hK : 0 ≤ K)
    (ha : 0 < a) (hτ : 0 ≤ τ) (hx : 0 ≤ x)
    (ht : (t : ℝ)/a ≤ x/Real.log 2+3) :
    (roundedRate K a τ t : ℝ)+2 ≤
      (K*(1+(1/Real.log 2+3)^τ)+3)*(1+x^τ) := by
  have htwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 ≤ 1/Real.log 2+3 := by positivity
  have hxpow : 0 ≤ x^τ := Real.rpow_nonneg hx τ
  have hcpow : 0 ≤ (1/Real.log 2+3)^τ := Real.rpow_nonneg hc τ
  have hbase : 0 ≤ (t : ℝ)/a := div_nonneg (Nat.cast_nonneg _) (le_of_lt ha)
  have hp : ((t : ℝ)/a)^τ ≤ (1/Real.log 2+3)^τ*(1+x^τ) := by
    by_cases hx1 : x ≤ 1
    · have hdiv := div_le_div_of_nonneg_right hx1 (le_of_lt htwo)
      have hp := Real.rpow_le_rpow hbase (show (t : ℝ)/a ≤ 1/Real.log 2+3 by linarith) hτ
      nlinarith only [hp,mul_nonneg hcpow hxpow]
    · have hdiv : (t : ℝ)/a ≤ (1/Real.log 2+3)*x := by
        have hx1' : 1 ≤ x := by linarith
        calc
          (t : ℝ)/a ≤ x/Real.log 2+3 := ht
          _ ≤ (1/Real.log 2+3)*x := by
            simp only [div_eq_mul_inv,one_mul]
            nlinarith only [hx1']
      have hp := Real.rpow_le_rpow hbase hdiv hτ
      rw [Real.mul_rpow hc hx] at hp
      nlinarith only [hp,hcpow]
  have hnonneg : 0 ≤ K*(1+((t : ℝ)/a)^τ) :=
    mul_nonneg hK (by linarith [Real.rpow_nonneg hbase τ])
  have hceil := Nat.ceil_lt_add_one hnonneg
  change (roundedRate K a τ t : ℝ) < K*(1+((t : ℝ)/a)^τ)+1 at hceil
  have hmul := mul_le_mul_of_nonneg_left hp hK
  have hextra := mul_nonneg (show 0 ≤ K+3 by linarith) hxpow
  nlinarith only [hceil,hmul,hextra]

/-- The exact near-memory logarithmic bound for the real rate in the paper,
for the genuinely grouped branch g≥2 and the actual emitted execution trace.
The physical exchange primitive's rate is the only cost contract here. -/
theorem grouped_power_cost (B H n : ℕ) (hB : 0 < B) (hH : 0 < H)
    (hBH : B ≤ H) (hHn : H ≤ n) (hg2 : 2 ≤ groupSize H n)
    (K a τ : ℝ) (hK : 0 ≤ K) (ha : 1 ≤ a) (hτ : 0 ≤ τ)
    (exchangeCost : InterchangeCost)
    (hx : ∀ t V, ((exchangeCost t V*B : ℕ) : ℝ) ≤
      K*(1+((t : ℝ)/a)^τ)*((V+B : ℕ) : ℝ))
    {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α] (f : Fin n → α) :
    ∃ hg : 0 < groupSize H n, ∃ hD : 0 < memoryGroups H n,
      let result := GroupedRecursiveColumnsort.localRun
        (memoryGroups H n) (groupSize H n) hD hg 3 n f
      Correct f result.output ∧
        ((GroupedLocalSortingCost.traceCost B (groupSize H n) exchangeCost result.trace*B : ℕ) : ℝ) ≤
          54000000*(K*(1+(1/Real.log 2+3)^τ)+3)*((n+B : ℕ) : ℝ)*
            (1+(Real.log ((n : ℝ)/(H : ℝ))/a)^τ) ∧
        leavesFit (memoryGroups H n) result.trace ∧ memoryGroups H n*groupSize H n ≤ H := by
  have ha0 : 0 < a := by linarith
  obtain ⟨hg,hD,hcorrect,hcost,hmem,hbudget⟩ := grouped_near_memory B H n hB hH hBH hHn hg2
    (roundedRate K a τ) (roundedRate_monotone K a τ hK ha0 hτ) exchangeCost
    (rounded_exchange_contract B K a τ exchangeCost hx) f
  refine ⟨hg,hD,hcorrect,?_,hmem,hbudget⟩
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hratio : (1 : ℝ) ≤ (n : ℝ)/(H : ℝ) :=
    (le_div_iff₀ hHR).2 (by simpa only [one_mul] using (show (H : ℝ) ≤ n by exact_mod_cast hHn))
  have hlog : 0 ≤ Real.log ((n : ℝ)/(H : ℝ)) := Real.log_nonneg hratio
  have hx0 : 0 ≤ Real.log ((n : ℝ)/(H : ℝ))/a := div_nonneg hlog (le_of_lt ha0)
  have ht := div_le_div_of_nonneg_right (log_width_le H n hH hHn) (le_of_lt ha0)
  have hthree : (3 : ℝ)/a ≤ 3 := (div_le_iff₀ ha0).2 (by linarith)
  have hdivision : (Real.log ((n : ℝ)/(H : ℝ))/Real.log 2+3)/a =
      (Real.log ((n : ℝ)/(H : ℝ))/a)/Real.log 2+3/a := by ring
  rw [hdivision] at ht
  have hrate := rounded_rate_bound K a τ (Real.log ((n : ℝ)/(H : ℝ))/a)
    (Nat.log 2 (n/H)+3) hK ha0 hτ hx0 (by linarith)
  have hm := mul_le_mul_of_nonneg_right hrate
    (show (0 : ℝ) ≤ 54000000*((n+B : ℕ) : ℝ) by positivity)
  have hcostR : ((GroupedLocalSortingCost.traceCost B (groupSize H n) exchangeCost
      (GroupedRecursiveColumnsort.localRun (memoryGroups H n) (groupSize H n) hD hg 3 n f).trace*B : ℕ) : ℝ) ≤
      54000000*((roundedRate K a τ (Nat.log 2 (n/H)+3) : ℝ)+2)*((n+B : ℕ) : ℝ) := by
    exact_mod_cast hcost
  nlinarith only [hcostR,hm]

end CSL.GroupedNearMemory
end GroupedNearMemory

section NearMemorySort
/-! Both branches of the actual near-memory local algorithm on n≤H².
For g<2, using unit groups remains sufficient because n>H²/16. -/
namespace CSL.NearMemorySort
open LocalShape RecursiveColumnsort LocalSortingCost GroupedShape GroupedNearMemory

/-- D≤32 floor(n/H) implies the same logarithmic field bound, independently
of whether D came from nontrivial grouping or the scalar fallback. -/
theorem width_of_memory_le_ratio (H n D m : ℕ)
    (hD : D ≤ 32*(n/H)) (hm : m ≤ D^2) :
    sizeExponent m ≤ Nat.log 2 (n/H)+3 := by
  let L := Nat.log 2 (n/H)
  have hq : n/H < 2^(L+1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hDpow : D ≤ 2^(L+6) := by
    have hm := Nat.mul_le_mul_left 32 (Nat.le_of_lt hq)
    have he : 32*2^(L+1) = 2^(L+6) := by
      rw [show L+6=(L+1)+5 by omega,pow_add]
      norm_num
      ring
    nlinarith only [hD,hm,he]
  have hnPow : m ≤ 2^(2*(L+6)) := by
    calc
      m ≤ D^2 := hm
      _ ≤ (2^(L+6))^2 := Nat.pow_le_pow_left hDpow _
      _ = _ := by rw [←pow_mul]; ring_nf
  have ht := exponent_of_power_le m (2*(L+6)) hnPow
  change sizeExponent m ≤ L+3
  omega

theorem scalar_memory_le_ratio (H n : ℕ) (hH : 0 < H) (hHn : H ≤ n)
    (hg : groupSize H n < 2) : H ≤ 32*(n/H) := by
  have hlarge := small_group_large_input H n (by omega) hg
  have hq : 0 < n/H := Nat.div_pos hHn hH
  have hrem := Nat.mod_lt n hH
  have he := Nat.mod_add_div n H
  have hn : n < 2*(n/H)*H := by nlinarith only [hrem,he,hq]
  nlinarith only [hlarge,hn,hH]

def chosenGroup (H n : ℕ) : ℕ := if 2 ≤ groupSize H n then groupSize H n else 1

def chosenMemory (H n : ℕ) : ℕ := H/chosenGroup H n

theorem chosenGroup_pos (H n : ℕ) : 0 < chosenGroup H n := by
  unfold chosenGroup
  split_ifs <;> omega

theorem chosenMemory_pos (H n : ℕ) (hH : 0 < H) (hHn : H ≤ n) :
    0 < chosenMemory H n := by
  unfold chosenMemory chosenGroup
  split_ifs with hg
  · exact (group_bounds H n hH hHn hg).2.1
  · simpa using hH

/-- The executable finite algorithm, with the useful-grouping test made
before the recursive calls. Both branches compare individual records. -/
def run (H : ℕ) (hH : 0 < H) (n : ℕ) (hHn : H ≤ n)
    {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α] (f : Fin n → α) : Run α n :=
  GroupedRecursiveColumnsort.localRun (chosenMemory H n) (chosenGroup H n)
    (chosenMemory_pos H n hH hHn) (chosenGroup_pos H n) 3 n f

theorem run_correct (H : ℕ) (hH : 0 < H) (n : ℕ) (hHn : H ≤ n)
    {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α] (f : Fin n → α) :
    Correct f (run H hH n hHn f).output :=
  GroupedRecursiveColumnsort.localRun_correct _ _ _ _ 3 n f

/-- Integer-rate bound for both branches of that same finite program. -/
theorem run_rate_bound (B H n : ℕ) (hB : 0 < B) (hH : 0 < H)
    (hBH : B ≤ H) (hHn : H ≤ n) (hnH : n ≤ H^2)
    (rate : ℕ → ℕ) (hrate : Monotone rate) (exchangeCost : InterchangeCost)
    (hx : ∀ t V, exchangeCost t V*B ≤ rate t*(V+B))
    {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α] (f : Fin n → α) :
    GroupedLocalSortingCost.traceCost B (chosenGroup H n) exchangeCost
      (run H hH n hHn f).trace*B ≤ 54000000*(rate (Nat.log 2 (n/H)+3)+2)*(n+B) ∧
    leavesFit (chosenMemory H n) (run H hH n hHn f).trace ∧
      chosenMemory H n*chosenGroup H n ≤ H := by
  by_cases hg : 2 ≤ groupSize H n
  · obtain ⟨hgpos,hDpos,hcorrect,hcost,hmem,hbudget⟩ :=
      grouped_near_memory B H n hB hH hBH hHn hg rate hrate exchangeCost hx f
    simpa only [run,chosenMemory,chosenGroup,if_pos hg,memoryGroups] using ⟨hcost,hmem,hbudget⟩
  · have hDR := scalar_memory_le_ratio H n hH hHn (by omega)
    have hcost (m : ℕ) (_hm : 512*H < m) (hmH : m ≤ H^2) :
        exchangeCost (sizeExponent m) (sizeChoice m^4*1)*B ≤
          rate (Nat.log 2 (n/H)+3)*(sizeChoice m^4*1+B) := by
      have ht := width_of_memory_le_ratio H n H m hDR hmH
      exact le_trans (hx _ _) (Nat.mul_le_mul_right _ (hrate ht))
    have h := GroupedLocalSortingCost.actual_grouped_bound B 1 H
      (rate (Nat.log 2 (n/H)+3)) hB (by decide) hH (by omega) exchangeCost hcost n f
      (by simpa [GroupedRecursiveColumnsort.groups] using hnH)
    have hcost' : GroupedLocalSortingCost.traceCost B 1 exchangeCost
        (GroupedRecursiveColumnsort.localRun H 1 hH (by decide) 3 n f).trace*B ≤
          54000000*(rate (Nat.log 2 (n/H)+3)+2)*(n+B) := by
      have hc := h.2.1
      simp only [GroupedRecursiveColumnsort.groups, Nat.add_sub_cancel, Nat.div_one, Nat.mul_one] at hc
      nlinarith only [hc, Nat.zero_le ((rate (Nat.log 2 (n/H)+3)+2)*(n+B))]
    simpa only [run,chosenMemory,chosenGroup,if_neg hg,Nat.div_one,Nat.mul_one] using
      And.intro hcost' (And.intro h.2.2 (le_refl H))

/-- The near-memory logarithmic rate holds for the actual branch-selecting
algorithm throughout H≤n≤H², including g=0 or g=1 before the fallback. -/
theorem run_power_cost (B H n : ℕ) (hB : 0 < B) (hH : 0 < H)
    (hBH : B ≤ H) (hHn : H ≤ n) (hnH : n ≤ H^2)
    (K a τ : ℝ) (hK : 0 ≤ K) (ha : 1 ≤ a) (hτ : 0 ≤ τ)
    (exchangeCost : InterchangeCost)
    (hx : ∀ t V, ((exchangeCost t V*B : ℕ) : ℝ) ≤
      K*(1+((t : ℝ)/a)^τ)*((V+B : ℕ) : ℝ))
    {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α] (f : Fin n → α) :
    ((GroupedLocalSortingCost.traceCost B (chosenGroup H n) exchangeCost
      (run H hH n hHn f).trace*B : ℕ) : ℝ) ≤
      54000000*(K*(1+(1/Real.log 2+3)^τ)+3)*((n+B : ℕ) : ℝ)*
        (1+(Real.log ((n : ℝ)/(H : ℝ))/a)^τ) ∧
    leavesFit (chosenMemory H n) (run H hH n hHn f).trace ∧
      chosenMemory H n*chosenGroup H n ≤ H := by
  have ha0 : 0 < a := by linarith
  obtain ⟨hcost,hmem,hbudget⟩ := run_rate_bound B H n hB hH hBH hHn hnH
    (roundedRate K a τ) (roundedRate_monotone K a τ hK ha0 hτ) exchangeCost
    (rounded_exchange_contract B K a τ exchangeCost hx) f
  refine ⟨?_,hmem,hbudget⟩
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hratio : (1 : ℝ) ≤ (n : ℝ)/(H : ℝ) :=
    (le_div_iff₀ hHR).2 (by simpa only [one_mul] using (show (H : ℝ) ≤ n by exact_mod_cast hHn))
  have hlog : 0 ≤ Real.log ((n : ℝ)/(H : ℝ)) := Real.log_nonneg hratio
  have hx0 : 0 ≤ Real.log ((n : ℝ)/(H : ℝ))/a := div_nonneg hlog (le_of_lt ha0)
  have ht := div_le_div_of_nonneg_right (log_width_le H n hH hHn) (le_of_lt ha0)
  have hthree : (3 : ℝ)/a ≤ 3 := (div_le_iff₀ ha0).2 (by linarith)
  have hdivision : (Real.log ((n : ℝ)/(H : ℝ))/Real.log 2+3)/a =
      (Real.log ((n : ℝ)/(H : ℝ))/a)/Real.log 2+3/a := by ring
  rw [hdivision] at ht
  have hrate := rounded_rate_bound K a τ (Real.log ((n : ℝ)/(H : ℝ))/a)
    (Nat.log 2 (n/H)+3) hK ha0 hτ hx0 (by linarith)
  have hm := mul_le_mul_of_nonneg_right hrate
    (show (0 : ℝ) ≤ 54000000*((n+B : ℕ) : ℝ) by positivity)
  have hcostR : ((GroupedLocalSortingCost.traceCost B (chosenGroup H n) exchangeCost
      (run H hH n hHn f).trace*B : ℕ) : ℝ) ≤
      54000000*((roundedRate K a τ (Nat.log 2 (n/H)+3) : ℝ)+2)*((n+B : ℕ) : ℝ) := by
    exact_mod_cast hcost
  nlinarith only [hcostR,hm]

end CSL.NearMemorySort
end NearMemorySort

section ChunkedNearMemory
/-! Sort H²-sized chunks by the proved near-memory program and merge their
actual block files in pairwise rounds. Small final chunks use RAM sorting. -/
namespace CSL.ChunkedNearMemory
open Columnsort RecursiveColumnsort LocalSortingCost BucketMachine BucketReader
open ExternalMergeFiles MergeRounds GroupedNearMemory
variable {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α]

def input (xs : List α) : Fin xs.length → α := fun i => xs[i.val]

omit [LinearOrder α] [OrderBot α] [OrderTop α] in
theorem input_list (xs : List α) : List.ofFn (input xs)=xs := by
  exact List.ofFn_getElem (xs := xs)

/-- Values and charges are read from the same localSort invocation. -/
def localSort (B H : ℕ) (hH : 0 < H) (exchangeCost : InterchangeCost) (xs : List α) : List α × ℕ :=
  if hn : H ≤ xs.length then
    let result := NearMemorySort.run H hH xs.length hn (input xs)
    (List.ofFn result.output,
      GroupedLocalSortingCost.traceCost B (NearMemorySort.chosenGroup H xs.length) exchangeCost result.trace)
  else (List.ofFn (sortColumn (input xs)),leafScan B xs.length)

theorem local_correct (B H : ℕ) (hH : 0 < H) (exchangeCost : InterchangeCost) (xs : List α) :
    (localSort B H hH exchangeCost xs).1.Pairwise (·≤·) ∧ (localSort B H hH exchangeCost xs).1.Perm xs := by
  unfold localSort
  split_ifs with hn
  · have h := NearMemorySort.run_correct H hH xs.length hn (input xs)
    exact ⟨h.1.ofFn_sorted,by simpa only [input_list] using h.2⟩
  · exact ⟨(sortColumn_monotone (input xs)).ofFn_sorted,
      by simpa only [input_list] using sortColumn_perm (input xs)⟩

theorem local_rate_bound (B H N : ℕ) (hB : 0 < B) (hH : 0 < H) (hBH : B ≤ H)
    (rate : ℕ → ℕ) (hrate : Monotone rate) (exchangeCost : InterchangeCost)
    (hx : ∀ t V,exchangeCost t V*B ≤ rate t*(V+B))
    (xs : List α) (hnH : xs.length ≤ H^2) (hnN : xs.length ≤ N) :
    (localSort B H hH exchangeCost xs).2*B ≤
      54000000*(rate (Nat.log 2 (N/H)+3)+2)*(xs.length+B) := by
  unfold localSort
  split_ifs with hn
  · have h := (NearMemorySort.run_rate_bound B H xs.length hB hH hBH hn hnH rate hrate
        exchangeCost hx (input xs)).1
    have ht : Nat.log 2 (xs.length/H) ≤ Nat.log 2 (N/H) := Nat.log_mono_right (Nat.div_le_div_right hnN)
    have hr := hrate (Nat.add_le_add_right ht 3)
    exact le_trans h (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 54000000 (Nat.add_le_add_right hr 2)))
  · exact le_trans (leafScan_bound B hB xs.length)
      (Nat.mul_le_mul_right _ (by omega : 2 ≤ 54000000*(rate (Nat.log 2 (N/H)+3)+2)))

def chunks (H : ℕ) (hH : 0 < H) (xs : List α) := pack (H^2) (Nat.pow_pos hH) xs

def localFiles (B : ℕ) (hB : 0 < B) (H : ℕ) (hH : 0 < H)
    (exchangeCost : InterchangeCost) (xs : List α) : List (File α) :=
  (chunks H hH xs).map (fun row => pack B hB (localSort B H hH exchangeCost row).1)

def localCost (B H : ℕ) (hH : 0 < H) (exchangeCost : InterchangeCost) (xs : List α) : ℕ :=
  ((chunks H hH xs).map (fun row => (localSort B H hH exchangeCost row).2)).sum

def mergeRun (B : ℕ) (hB : 0 < B) (H : ℕ) (hH : 0 < H)
    (exchangeCost : InterchangeCost) (fuel : ℕ) (xs : List α) : Result α :=
  rounds B (fun a b => decide (a≤b)) fuel (localFiles B hB H hH exchangeCost xs)

theorem localFiles_good (B : ℕ) (hB : 0 < B) (H : ℕ) (hH : 0 < H)
    (exchangeCost : InterchangeCost) (xs : List α) :
    ∀ file∈localFiles B hB H hH exchangeCost xs,GoodFile B file := by
  intro file hf
  obtain ⟨row,_,rfl⟩ := List.mem_map.mp hf
  exact pack_good B hB _

theorem localFiles_sorted (B : ℕ) (hB : 0 < B) (H : ℕ) (hH : 0 < H)
    (exchangeCost : InterchangeCost) (xs : List α) :
    ∀ file∈localFiles B hB H hH exchangeCost xs,file.flatten.Pairwise (·≤·) := by
  intro file hf
  obtain ⟨row,_,rfl⟩ := List.mem_map.mp hf
  rw [flatten_pack]
  exact (local_correct B H hH exchangeCost row).1

private theorem mapped_records_perm (B : ℕ) (hB : 0 < B) (H : ℕ) (hH : 0 < H)
    (exchangeCost : InterchangeCost) (rows : List (List α)) :
    (records (rows.map (fun row => pack B hB (localSort B H hH exchangeCost row).1))).Perm rows.flatten := by
  induction rows with
  | nil => simp
  | cons row rest ih =>
    simp only [List.map_cons,records_cons,flatten_pack,List.flatten_cons]
    exact ((local_correct B H hH exchangeCost row).2).append ih

theorem localFiles_perm (B : ℕ) (hB : 0 < B) (H : ℕ) (hH : 0 < H)
    (exchangeCost : InterchangeCost) (xs : List α) :
    (records (localFiles B hB H hH exchangeCost xs)).Perm xs := by
  have h := mapped_records_perm B hB H hH exchangeCost (chunks H hH xs)
  first
  | exact h
  | (have h_sx := h; simp only [chunks,flatten_pack] at h_sx ⊢; exact h_sx)
  | (have h_sx := h; simp only [chunks,flatten_pack] at h_sx; exact h_sx)
  | (simp only [chunks,flatten_pack]; exact h)

/- A constant c relating M to H implies at most c² initial chunks for
all n≤M². This count includes the final partial chunk. -/
omit [LinearOrder α] [OrderBot α] [OrderTop α] in
theorem chunks_count_bound (H M c : ℕ) (hH : 0 < H) (hM : M ≤ c*H)
    (xs : List α) (hn : xs.length ≤ M^2) : (chunks H hH xs).length ≤ c^2 := by
  have hcap := (pack_capacity (H^2) (Nat.pow_pos hH) xs).2
  have hm := Nat.pow_le_pow_left hM 2
  have hpos : 0 < H^2 := Nat.pow_pos hH
  change (chunks H hH xs).length*H^2 < xs.length+H^2 at hcap
  nlinarith only [hcap,hm,hn,hpos]

theorem mergeRun_correct (B : ℕ) (hB : 0 < B) (H M c : ℕ) (hH : 0 < H)
    (hM : M ≤ c*H) (exchangeCost : InterchangeCost) (xs : List α) (hn : xs.length ≤ M^2) :
    (records (mergeRun B hB H hH exchangeCost (Nat.clog 2 (c^2)) xs).files).Pairwise (·≤·) ∧
    (records (mergeRun B hB H hH exchangeCost (Nat.clog 2 (c^2)) xs).files).Perm xs := by
  have hc := chunks_count_bound H M c hH hM xs hn
  have hnfiles : (localFiles B hB H hH exchangeCost xs).length ≤ 2^(Nat.clog 2 (c^2)) := by
    simp only [localFiles,List.length_map]
    exact le_trans hc (Nat.le_pow_clog (by decide) (c^2))
  have h := rounds_final B hB (Nat.clog 2 (c^2)) (localFiles B hB H hH exchangeCost xs)
    hnfiles (localFiles_good B hB H hH exchangeCost xs) (localFiles_sorted B hB H hH exchangeCost xs)
  exact ⟨h.1,h.2.trans (localFiles_perm B hB H hH exchangeCost xs)⟩

omit [LinearOrder α] [OrderBot α] [OrderTop α] in
theorem member_length_le_flatten (rows : List (List α)) (row : List α) (hr : row∈rows) :
    row.length ≤ rows.flatten.length := by
  induction rows with
  | nil => simp at hr
  | cons front rest ih =>
    rcases List.mem_cons.mp hr with rfl|hr
    · simp
    · have h := ih hr
      simp only [List.flatten_cons,List.length_append]
      omega

/- Small final chunks contribute only a scan startup, and the whole
collection's startups are absorbed as soon as n≥H and B≤H. -/
omit [LinearOrder α] [OrderBot α] [OrderTop α] in
theorem chunks_startup (B H : ℕ) (hH : 0 < H) (hBH : B ≤ H)
    (xs : List α) (hn : H ≤ xs.length) : (chunks H hH xs).length*B ≤ 2*xs.length := by
  have hcap := (pack_capacity (H^2) (Nat.pow_pos hH) xs).2
  change (chunks H hH xs).length*H^2 < xs.length+H^2 at hcap
  have hHsq : H ≤ H^2 := by nlinarith only [hH]
  have hpos : 0 < H^2 := Nat.pow_pos hH
  by_cases hlarge : H^2 ≤ xs.length
  · have hm := Nat.mul_le_mul_left (chunks H hH xs).length (le_trans hBH hHsq)
    nlinarith only [hcap,hm,hlarge]
  · have hcount : (chunks H hH xs).length ≤ 1 := by nlinarith only [hcap,hlarge,hpos]
    have hm := Nat.mul_le_mul_right B hcount
    nlinarith only [hm,hBH,hn]

omit [LinearOrder α] [OrderBot α] [OrderTop α] in
private theorem sum_affine (rows : List (List α)) (cost : List α → ℕ) (B L : ℕ)
    (h : ∀ row∈rows,cost row*B ≤ L*(row.length+B)) :
    (rows.map cost).sum*B ≤ L*(rows.flatten.length+B*rows.length) := by
  induction rows with
  | nil => simp
  | cons row rest ih =>
    have hr := h row (by simp)
    have ht := ih (fun row hm => h row (by simp [hm]))
    simp only [List.map_cons,List.sum_cons,List.flatten_cons,List.length_append,List.length_cons]
    nlinarith only [hr,ht]

theorem localCost_bound (B H : ℕ) (hB : 0 < B) (hH : 0 < H) (hBH : B ≤ H)
    (rate : ℕ → ℕ) (hrate : Monotone rate) (exchangeCost : InterchangeCost)
    (hx : ∀ t V,exchangeCost t V*B ≤ rate t*(V+B))
    (xs : List α) (hn : H ≤ xs.length) :
    localCost B H hH exchangeCost xs*B ≤
      3*(54000000*(rate (Nat.log 2 (xs.length/H)+3)+2))*xs.length := by
  let L := 54000000*(rate (Nat.log 2 (xs.length/H)+3)+2)
  have h := sum_affine (chunks H hH xs) (fun row => (localSort B H hH exchangeCost row).2) B L (by
    intro row hr
    have hrow := block_size_bound (H^2) (Nat.pow_pos hH) xs row hr
    have hlen := member_length_le_flatten (chunks H hH xs) row hr
    simp only [chunks,flatten_pack] at hlen
    exact local_rate_bound B H xs.length hB hH hBH rate hrate exchangeCost hx row hrow hlen)
  simp only [chunks,flatten_pack] at h
  have hstartup := chunks_startup B H hH hBH xs hn
  have hm := Nat.mul_le_mul_left L hstartup
  change localCost B H hH exchangeCost xs*B ≤ 3*L*xs.length
  change localCost B H hH exchangeCost xs*B ≤ L*(xs.length+B*(chunks H hH xs).length) at h
  nlinarith only [h,hm]

theorem mergeRun_cost (B : ℕ) (hB : 0 < B) (H : ℕ) (hH : 0 < H) (hBH : B ≤ H)
    (exchangeCost : InterchangeCost) (fuel : ℕ) (xs : List α) (hn : H ≤ xs.length) :
    (mergeRun B hB H hH exchangeCost fuel xs).cost*B ≤ 8*fuel*xs.length := by
  have h := rounds_cost B hB (fun a b => decide (a≤b)) fuel (localFiles B hB H hH exchangeCost xs)
    (localFiles_good B hB H hH exchangeCost xs)
  rw [(localFiles_perm B hB H hH exchangeCost xs).length_eq] at h
  simp only [localFiles,List.length_map] at h
  have hstartup := chunks_startup B H hH hBH xs hn
  have hm := Nat.mul_le_mul_left (3*fuel) hstartup
  exact le_trans h (by nlinarith only [hm])

/-- Initial splitting is an actual shared-reader scan; individual chunk
files are flushed separately, including the final partial block. -/
def splitCost (B : ℕ) (hB : 0 < B) (H : ℕ) (hH : 0 < H) (xs : List α) :=
  (pack B hB xs).length+((chunks H hH xs).map (fun row => (pack B hB row).length)).sum

omit [LinearOrder α] [OrderBot α] [OrderTop α] in
theorem splitCost_realized (B : ℕ) (hB : 0 < B) (H : ℕ) (hH : 0 < H) (xs : List α) :
    ∃ files reader,
      StreamCopy.splitFiles B ((chunks H hH xs).map List.length)
        (Reader.fromDisk (pack B hB xs))=some (files,reader) ∧
      files.map List.flatten=chunks H hH xs ∧
      reader.reads+(files.map List.length).sum=splitCost B hB H hH xs := by
  obtain ⟨files,reader,he,hcontents,hcounts,_,_,_,hreads⟩ :=
    StreamCopy.splitFiles_correct B hB (chunks H hH xs) (Reader.fromDisk (pack B hB xs))
      (StreamCopy.pack_reader_valid B hB xs)
      (by simp [Reader.contents,Reader.fromDisk,chunks,flatten_pack])
  refine ⟨files,reader,he,hcontents,?_⟩
  rw [hcounts,hreads]
  simp [Reader.fromDisk,splitCost]

omit [LinearOrder α] [OrderBot α] [OrderTop α] in
theorem splitCost_bound (B : ℕ) (hB : 0 < B) (H : ℕ) (hH : 0 < H) (hBH : B ≤ H)
    (xs : List α) (hn : H ≤ xs.length) : splitCost B hB H hH xs*B ≤ 5*xs.length := by
  have h := sum_affine (chunks H hH xs) (fun row => (pack B hB row).length) B 1
    (fun row _ => by simpa using Nat.le_of_lt (pack_capacity B hB row).2)
  simp only [chunks,flatten_pack,Nat.one_mul] at h
  have hinput := Nat.le_of_lt (pack_capacity B hB xs).2
  have hstartup := chunks_startup B H hH hBH xs hn
  simp only [chunks] at hstartup
  unfold splitCost
  change ((pack B hB xs).length+((pack (H^2) (Nat.pow_pos hH) xs).map
    (fun row => (pack B hB row).length)).sum)*B ≤ _
  nlinarith only [h,hinput,hstartup,hBH,hn]

def totalCost (B : ℕ) (hB : 0 < B) (H : ℕ) (hH : 0 < H)
    (exchangeCost : InterchangeCost) (fuel : ℕ) (xs : List α) :=
  splitCost B hB H hH xs+localCost B H hH exchangeCost xs+
    (mergeRun B hB H hH exchangeCost fuel xs).cost

theorem total_rate_bound (B : ℕ) (hB : 0 < B) (H : ℕ) (hH : 0 < H) (hBH : B ≤ H)
    (rate : ℕ → ℕ) (hrate : Monotone rate) (exchangeCost : InterchangeCost)
    (hx : ∀ t V,exchangeCost t V*B ≤ rate t*(V+B))
    (fuel : ℕ) (xs : List α) (hn : H ≤ xs.length) :
    totalCost B hB H hH exchangeCost fuel xs*B ≤
      (162000000*(rate (Nat.log 2 (xs.length/H)+3)+2)+8*fuel+5)*xs.length := by
  have hs := splitCost_bound B hB H hH hBH xs hn
  have hl := localCost_bound B H hB hH hBH rate hrate exchangeCost hx xs hn
  have hm := mergeRun_cost B hB H hH hBH exchangeCost fuel xs hn
  unfold totalCost
  nlinarith only [hs,hl,hm]

end CSL.ChunkedNearMemory
end ChunkedNearMemory

section LocalSortingComplete
/-! Complete normalized local sorting reduction on M≤n≤M². The concrete
program includes chunk-local sorting, initial splitting, and disk merge rounds.
The address-interchange primitive retains its explicit implementation contract. -/
namespace CSL.LocalSortingComplete
open RecursiveColumnsort LocalSortingCost GroupedNearMemory ChunkedNearMemory MergeRounds

/-- Translate the same-execution integer trace bound to the real rate. -/
theorem total_power_bound (B : ℕ) (hB : 0 < B) (H : ℕ) (hH : 0 < H) (hBH : B ≤ H)
    (K a τ : ℝ) (hK : 0 ≤ K) (ha : 1 ≤ a) (hτ : 0 ≤ τ)
    (exchangeCost : InterchangeCost)
    (hx : ∀ t V,((exchangeCost t V*B : ℕ) : ℝ) ≤ K*(1+((t : ℝ)/a)^τ)*((V+B : ℕ) : ℝ))
    {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α]
    (fuel : ℕ) (xs : List α) (hn : H ≤ xs.length) :
    ((totalCost B hB H hH exchangeCost fuel xs*B : ℕ) : ℝ) ≤
      (162000000*(K*(1+(1/Real.log 2+3)^τ)+3)+8*(fuel : ℝ)+5)*(xs.length : ℝ)*
        (1+(Real.log ((xs.length : ℝ)/(H : ℝ))/a)^τ) := by
  have ha0 : 0 < a := by linarith
  have hcost := total_rate_bound B hB H hH hBH (roundedRate K a τ)
    (roundedRate_monotone K a τ hK ha0 hτ) exchangeCost
    (rounded_exchange_contract B K a τ exchangeCost hx) fuel xs hn
  have hHR : (0 : ℝ)<H := by exact_mod_cast hH
  have hratio : (1 : ℝ) ≤ (xs.length : ℝ)/(H : ℝ) :=
    (le_div_iff₀ hHR).2 (by simpa only [one_mul] using (show (H : ℝ) ≤ xs.length by exact_mod_cast hn))
  have hlog := Real.log_nonneg hratio
  have hx0 : 0 ≤ Real.log ((xs.length : ℝ)/(H : ℝ))/a := div_nonneg hlog (le_of_lt ha0)
  have ht := div_le_div_of_nonneg_right (log_width_le H xs.length hH hn) (le_of_lt ha0)
  have hthree : (3 : ℝ)/a ≤ 3 := (div_le_iff₀ ha0).2 (by linarith)
  have hdivision : (Real.log ((xs.length : ℝ)/(H : ℝ))/Real.log 2+3)/a =
      (Real.log ((xs.length : ℝ)/(H : ℝ))/a)/Real.log 2+3/a := by ring
  rw [hdivision] at ht
  have hrate := rounded_rate_bound K a τ (Real.log ((xs.length : ℝ)/(H : ℝ))/a)
    (Nat.log 2 (xs.length/H)+3) hK ha0 hτ hx0 (by linarith)
  have hm := mul_le_mul_of_nonneg_right hrate
    (show (0 : ℝ) ≤ 162000000*(xs.length : ℝ) by positivity)
  have hcostR : ((totalCost B hB H hH exchangeCost fuel xs*B : ℕ) : ℝ) ≤
      (162000000*((roundedRate K a τ (Nat.log 2 (xs.length/H)+3) : ℝ)+2)+8*(fuel : ℝ)+5)*
        (xs.length : ℝ) := by exact_mod_cast hcost
  have hextra := mul_nonneg
    (show (0 : ℝ) ≤ (8*(fuel : ℝ)+5)*(xs.length : ℝ) by positivity)
    (Real.rpow_nonneg hx0 τ)
  nlinarith only [hcostR,hm,hextra]

/-- An additive constant in the logarithm changes only a fixed multiplier. -/
theorem rpow_additive_shift (x y d τ : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hd : 0 ≤ d) (hτ : 0 ≤ τ) (hxy : y ≤ x+d) :
    1+y^τ ≤ (1+(1+d)^τ)*(1+x^τ) := by
  have hR : 0 ≤ (1+d)^τ := Real.rpow_nonneg (by linarith) τ
  have hxpow : 0 ≤ x^τ := Real.rpow_nonneg hx τ
  by_cases hx1 : x ≤ 1
  · have hp := Real.rpow_le_rpow hy (show y ≤ 1+d by linarith) hτ
    have hextra := mul_nonneg (show 0 ≤ 1+(1+d)^τ by linarith) hxpow
    nlinarith only [hp,hextra]
  · have hm := mul_le_mul_of_nonneg_left (show 1 ≤ x by linarith) hd
    have hp := Real.rpow_le_rpow hy (show y ≤ (1+d)*x by nlinarith only [hxy,hm]) hτ
    rw [Real.mul_rpow (by linarith) hx] at hp
    nlinarith only [hp,hR,hxpow]

/-- The physical-memory and reserved-memory logarithms differ by at most
log c, proved from M≤cH rather than assumed asymptotically equivalent. -/
theorem log_memory_transfer (H M c n : ℕ) (hH : 0 < H) (hHM : H ≤ M)
    (hMc : M ≤ c*H) (hMn : M ≤ n) (a : ℝ) (ha : 1 ≤ a) :
    0 ≤ Real.log ((n : ℝ)/(M : ℝ))/a ∧
    0 ≤ Real.log ((n : ℝ)/(H : ℝ))/a ∧
    0 ≤ Real.log (c : ℝ) ∧
    Real.log ((n : ℝ)/(H : ℝ))/a ≤ Real.log ((n : ℝ)/(M : ℝ))/a+Real.log (c : ℝ) := by
  have hM : 0 < M := by omega
  have hn : 0 < n := by omega
  have hc : 0 < c := by nlinarith only [hH,hHM,hMc]
  have hHR : (0 : ℝ)<H := by exact_mod_cast hH
  have hMR : (0 : ℝ)<M := by exact_mod_cast hM
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hcR : (0 : ℝ)<c := by exact_mod_cast hc
  have ha0 : 0 < a := by linarith
  have hratioM : (1 : ℝ) ≤ (n : ℝ)/(M : ℝ) :=
    (le_div_iff₀ hMR).2 (by simpa only [one_mul] using (show (M : ℝ) ≤ n by exact_mod_cast hMn))
  have hratioH : (1 : ℝ) ≤ (n : ℝ)/(H : ℝ) :=
    (le_div_iff₀ hHR).2 (by simpa only [one_mul] using (show (H : ℝ) ≤ n by exact_mod_cast (le_trans hHM hMn)))
  have hlogc : 0 ≤ Real.log (c : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ c by omega))
  refine ⟨div_nonneg (Real.log_nonneg hratioM) (le_of_lt ha0),
    div_nonneg (Real.log_nonneg hratioH) (le_of_lt ha0),hlogc,?_⟩
  have hlog := Real.log_le_log hMR (show (M : ℝ) ≤ (c : ℝ)*(H : ℝ) by exact_mod_cast hMc)
  rw [Real.log_mul (ne_of_gt hcR) (ne_of_gt hHR)] at hlog
  have hscale : Real.log (c : ℝ)/a ≤ Real.log (c : ℝ) :=
    (div_le_iff₀ ha0).2 (by nlinarith only [hlogc,ha])
  have hratio : Real.log ((n : ℝ)/(H : ℝ)) ≤
      Real.log ((n : ℝ)/(M : ℝ))+Real.log (c : ℝ) := by
    rw [Real.log_div (ne_of_gt hnR) (ne_of_gt hHR),Real.log_div (ne_of_gt hnR) (ne_of_gt hMR)]
    linarith
  have hdiv := div_le_div_of_nonneg_right hratio (le_of_lt ha0)
  rw [add_div] at hdiv
  linarith

/-- Explicit constant depending only on the fixed memory reservation factor
c and the exchange-rate constants, not n,M,B. -/
noncomputable def boundConstant (c : ℕ) (K τ : ℝ) : ℝ :=
  (162000000*(K*(1+(1/Real.log 2+3)^τ)+3)+8*(Nat.clog 2 (c^2) : ℝ)+5)*
    (1+(1+Real.log (c : ℝ))^τ)

/-- The normalized Section 6.3 sorting result on the entire M≤n≤M² range:
actual chunk-local runs followed by actual buffered pairwise merge rounds.
The conclusion includes conservation of duplicate records and the refined
log(n/M) factor. Address exchange remains a separately named primitive. -/
theorem refined_local_sort (B H M c : ℕ) (hB : 0 < B) (hH : 0 < H)
    (hBH : B ≤ H) (hHM : H ≤ M) (hMc : M ≤ c*H)
    (K a τ : ℝ) (hK : 0 ≤ K) (ha : 1 ≤ a) (hτ : 0 ≤ τ)
    (exchangeCost : InterchangeCost)
    (hx : ∀ t V,((exchangeCost t V*B : ℕ) : ℝ) ≤ K*(1+((t : ℝ)/a)^τ)*((V+B : ℕ) : ℝ))
    {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α]
    (xs : List α) (hMn : M ≤ xs.length) (hnM : xs.length ≤ M^2) :
    let fuel := Nat.clog 2 (c^2)
    let result := mergeRun B hB H hH exchangeCost fuel xs
    (records result.files).Pairwise (·≤·) ∧ (records result.files).Perm xs ∧
      ((totalCost B hB H hH exchangeCost fuel xs*B : ℕ) : ℝ) ≤
        boundConstant c K τ*(xs.length : ℝ)*(1+(Real.log ((xs.length : ℝ)/(M : ℝ))/a)^τ) := by
  have hcorrect := mergeRun_correct B hB H M c hH hMc exchangeCost xs hnM
  refine ⟨hcorrect.1,hcorrect.2,?_⟩
  have hcost := total_power_bound B hB H hH hBH K a τ hK ha hτ exchangeCost hx
    (Nat.clog 2 (c^2)) xs (le_trans hHM hMn)
  obtain ⟨hx0,hy0,hd0,hshift⟩ := log_memory_transfer H M c xs.length hH hHM hMc hMn a ha
  have hpower := rpow_additive_shift _ _ _ τ hx0 hy0 hd0 hτ hshift
  have htwo : (0 : ℝ)<Real.log 2 := Real.log_pos (by norm_num)
  have hR : 0 ≤ (1/Real.log 2+3)^τ := Real.rpow_nonneg (by positivity) τ
  have hC : 0 ≤ 162000000*(K*(1+(1/Real.log 2+3)^τ)+3)+8*(Nat.clog 2 (c^2) : ℝ)+5 := by positivity
  have hm := mul_le_mul_of_nonneg_left hpower (mul_nonneg hC (Nat.cast_nonneg xs.length))
  unfold boundConstant
  nlinarith only [hcost,hm]

end CSL.LocalSortingComplete
end LocalSortingComplete


