-- Prove2me | Definitions.Def_CSL_Shared_Memory_PolynomialWorkspace
-- name    : CSL_Shared_Memory_PolynomialWorkspace
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:01:28.649036+00:00
-- url     : https://prove2.me/theorems/6bd92b65-ddf6-435c-9d96-ff29c7478894
-- title:
--   Coded sorting library: Shared / Memory / PolynomialWorkspace
-- statement:
--   Module `CodedSorting.Shared.Memory.PolynomialWorkspace` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Coarse reservation bounds for the actual recursion trees. These bounds
--   reserve separate disk space for every invocation. They do not identify an
--   abstract function value with resident RAM and do not assume polynomial total
--   space as a premise. Physical allocation/refinement remains a separate layer.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Memory.PolynomialWorkspace

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Interchange_Framework_Recursion_RecursiveExchange
import Definitions.Def_CSL_Shared_Programs_LocalTrace
import Definitions.Def_CSL_Sorting_Local_Columnsort_GroupedRecursiveColumnsort
import Definitions.Def_CSL_Sorting_Radix_Model_ExternalMSD
import Mathlib.Data.Nat.Log

/-! Coarse reservation bounds for the actual recursion trees. These bounds
reserve separate disk space for every invocation. They do not identify an
abstract function value with resident RAM and do not assume polynomial total
space as a premise. Physical allocation/refinement remains a separate layer. -/
namespace CSL.PolynomialWorkspace
open scoped BigOperators
open RecursiveExchange

noncomputable section
namespace Exchange

def nodes : CallTree → ℕ
  | .stop _ _ _ => 1
  | .level _ _ _ children => 1+∑ c,nodes (children c)

/-- Reserve C full-volume files per actual invocation, including leaves.
Local reindexing and XOR operate on files of this size or smaller. -/
def reservation (C : ℕ) : CallTree → ℕ
  | .stop _ V _ => C*V
  | .level _ V _ children => C*V+∑ c,reservation C (children c)

theorem pruned_nodes_bound (base cutoff : ℕ) (leaf : ℕ → ℕ)
    (charge : ℕ → ℕ → ℕ) (k V : ℕ) :
    nodes (CallTree.prunedBuild base cutoff leaf charge k V) ≤ (Parameters.S+1)^(k+1) := by
  induction k generalizing V with
  | zero => simp [CallTree.prunedBuild,nodes]
  | succ k ih =>
    rw [CallTree.prunedBuild]
    split_ifs
    · simpa only [nodes] using (Nat.one_le_pow _ _ (by omega : 0 < Parameters.S+1))
    · simp only [nodes,Finset.sum_const,Finset.card_univ,child_count,smul_eq_mul]
      have hs := Finset.sum_le_sum (fun (c : Child) (_ : c∈Finset.univ) => ih (V/Parameters.W))
      simp only [Finset.sum_const,Finset.card_univ,child_count,smul_eq_mul] at hs
      have hp : 1 ≤ (Parameters.S+1)^(k+1) := Nat.one_le_pow _ _ (by omega)
      rw [pow_succ]
      nlinarith

theorem pruned_reservation_bound (C base cutoff : ℕ) (leaf : ℕ → ℕ)
    (charge : ℕ → ℕ → ℕ) (k V N : ℕ) (hVN : V ≤ N) :
    reservation C (CallTree.prunedBuild base cutoff leaf charge k V) ≤
      C*N*(Parameters.S+1)^(k+1) := by
  induction k generalizing V with
  | zero =>
    simp only [CallTree.prunedBuild,reservation,pow_one]
    have h := Nat.mul_le_mul_left C hVN
    have h' : C*N ≤ C*N*(Parameters.S+1) := Nat.le_mul_of_pos_right _ (by omega)
    exact h.trans h'
  | succ k ih =>
    rw [CallTree.prunedBuild]
    split_ifs
    · simp only [reservation]
      exact (Nat.mul_le_mul_left C hVN).trans
        (Nat.le_mul_of_pos_right _ (pow_pos (by omega) _))
    · simp only [reservation,Finset.sum_const,Finset.card_univ,child_count,smul_eq_mul]
      have hs := Finset.sum_le_sum (fun (c : Child) (_ : c∈Finset.univ) =>
        ih (V/Parameters.W) ((Nat.div_le_self _ _).trans hVN))
      simp only [Finset.sum_const,Finset.card_univ,child_count,smul_eq_mul] at hs
      have hv := Nat.mul_le_mul_left C hVN
      have hp : 1 ≤ (Parameters.S+1)^(k+1) := Nat.one_le_pow _ _ (by omega)
      have hh : C*N ≤ C*N*(Parameters.S+1)^(k+1) := Nat.le_mul_of_pos_right _ (by omega)
      rw [pow_succ]
      nlinarith

/-- Turning logarithmic depth into a fixed polynomial uses only integer
powers. The exponent depends on the fixed branching factor, not input size. -/
theorem branching_polynomial (q S k N : ℕ) (hq : 2 ≤ q)
    (hqN : q ≤ N) (hdepth : q^k ≤ N) :
    (S+1)^(k+1) ≤ N^(2*Nat.clog q (S+1)) := by
  let e := Nat.clog q (S+1)
  have hS : S+1 ≤ q^e := Nat.le_pow_clog (by omega) _
  calc
    (S+1)^(k+1) ≤ (q^e)^(k+1) := Nat.pow_le_pow_left hS _
    _ = (q^k)^e*q^e := by
      rw [← pow_mul,show e*(k+1)=k*e+e by ring,pow_add,pow_mul]
    _ ≤ N^e*N^e := Nat.mul_le_mul (Nat.pow_le_pow_left hdepth _)
      (Nat.pow_le_pow_left hqN _)
    _ = N^(2*e) := by rw [two_mul,pow_add]

/-- The complete address actually contains both long fields. In particular,
a nonempty invocation has at least one full field's worth of addresses. -/
theorem field_capacity {P G Z : Type} [Fintype P] [Fintype G] [Fintype Z]
    (t : ℕ) (hV : 0 < Fintype.card (Address.FullAddress P (Scalar t) G Z)) :
    radix^t ≤ Fintype.card (Address.FullAddress P (Scalar t) G Z) := by
  rw [fullAddress_card,short_field_card] at hV ⊢
  have hP : 0 < Fintype.card P := by
    by_contra h; have hz : Fintype.card P=0 := by omega
    simp [hz] at hV
  have hG : 0 < Fintype.card G := by
    by_contra h; have hz : Fintype.card G=0 := by omega
    simp [hz] at hV
  have hZ : 0 < Fintype.card Z := by
    by_contra h; have hz : Fintype.card Z=0 := by omega
    simp [hz] at hV
  have ht : 0 < radix^t := pow_pos radix_prime.pos _
  exact (Nat.le_mul_of_pos_left _ hP).trans
    ((Nat.le_mul_of_pos_right _ hG).trans
      ((Nat.le_mul_of_pos_right _ ht).trans (Nat.le_mul_of_pos_right _ hZ)))

/-- This discharges the depth bound from the real field type, rather than
postulating a logarithmic depth for an unrelated tree. -/
theorem actual_depth_bound {P G Z : Type} [Fintype P] [Fintype G] [Fintype Z]
    (base k : ℕ) (hb : 0 < base)
    (hV : 0 < Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z)) :
    radix ≤ Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z) ∧
    radix^k ≤ Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z) := by
  have hm : 1 < Parameters.m := by norm_num [Parameters.m_value]
  have ht := Nat.lt_pow_self hm (n := k)
  have hw : Parameters.m^k ≤ base*Parameters.m^k := Nat.le_mul_of_pos_left _ hb
  have hfield := field_capacity (base*Parameters.m^k) hV
  constructor
  · have hp : 1 ≤ base*Parameters.m^k := Nat.mul_pos hb (pow_pos (by omega) _) 
    simpa only [pow_one] using (Nat.pow_le_pow_right radix_prime.pos hp).trans hfield
  · exact (Nat.pow_le_pow_right radix_prime.pos (ht.le.trans hw)).trans hfield

/-- An actual pruned exchange's complete all-invocations reservation is a
fixed polynomial. Primitive charges do not appear in this proof. -/
theorem cutoff_reservation_polynomial (C base cutoff k rows : ℕ) (hb : 0 < base)
    (leaf : ℕ → ℕ) (charge : ℕ → ℕ → ℕ)
    {P G Z : Type} [Fintype P] [Fintype G] [Fintype Z]
    (layout : P ≃ Fin (rows*Parameters.W^k))
    (hV : 0 < Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z)) :
    let V := Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z)
    reservation C (cutoffExchange base cutoff leaf charge k rows (Gap := G) (Suffix := Z) layout).calls ≤
      C*V^(2*Nat.clog radix (Parameters.S+1)+1) := by
  try dsimp only
  rw [cutoffExchange_calls]
  obtain ⟨hqN,hdepth⟩ := actual_depth_bound base k hb hV
  have h := branching_polynomial radix Parameters.S k _ radix_prime.two_le hqN hdepth
  let V := Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z)
  have hfirst := pruned_reservation_bound C base cutoff leaf charge k V V le_rfl
  apply hfirst.trans
  have hp := Nat.mul_le_mul_left (C*V) h
  convert hp using 1 <;> (try simp only [V]) <;> first | rfl | ring


/-- Fixed coefficients can be encoded with a fixed additional exponent.
This is the integer polynomial bound needed by WordControl.encodeCounter. -/
theorem absorb_coefficient (C N exponent : ℕ) (hN : 2≤N) :
    C*N^exponent≤N^(Nat.clog 2 C+exponent) := by
  have hC : C≤N^(Nat.clog 2 C) := (Nat.le_pow_clog (by omega : 1<2) C).trans
    (Nat.pow_le_pow_left hN _)
  rw [pow_add]
  exact Nat.mul_le_mul_right _ hC

/-- Nonempty actual invocations have enough global address capacity to
absorb the fixed circuit coefficient. No depth premise is supplied. -/
theorem cutoff_integer_polynomial (C base cutoff k rows : ℕ) (hb : 0<base)
    (leaf : ℕ→ℕ) (charge : ℕ→ℕ→ℕ)
    {P G Z : Type} [Fintype P] [Fintype G] [Fintype Z]
    (layout : P ≃ Fin (rows*Parameters.W^k))
    (hV : 0<Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z)) :
    let V := Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z)
    reservation C (cutoffExchange base cutoff leaf charge k rows (Gap := G) (Suffix := Z) layout).calls≤
      V^(Nat.clog 2 C+2*Nat.clog radix (Parameters.S+1)+1) := by
  try dsimp only
  have h := cutoff_reservation_polynomial C base cutoff k rows hb leaf charge layout hV
  have hN := radix_prime.two_le.trans (actual_depth_bound base k hb hV).1
  have h' := absorb_coefficient C _ (2*Nat.clog radix (Parameters.S+1)+1) hN
  simpa only [Nat.add_assoc] using h.trans h'

end Exchange


namespace Local
open LocalShape
abbrev Tree := RecursiveColumnsort.CallTree

mutual
  def reservation (g : ℕ) : Tree → ℕ
    | .leaf n => 256*n*g
    | .node n _ a b c d => 256*n*g+batch g a+batch g b+batch g c+batch g d
  def batch (g : ℕ) : List Tree → ℕ
    | [] => 0
    | head::tail => reservation g head+batch g tail
end

theorem batch_sum (g : ℕ) (trees : List Tree) :
    batch g trees=(trees.map (reservation g)).sum := by
  induction trees with
  | nil => rfl
  | cons head tail ih => simp [batch,ih]

theorem batch_bound (g R : ℕ) (trees : List Tree)
    (h : ∀ t∈trees,reservation g t≤R) : batch g trees≤trees.length*R := by
  induction trees with
  | nil => simp [batch]
  | cons head tail ih =>
    have hh := h head (by simp)
    have ht := ih (fun t ht => h t (by simp [ht]))
    simp only [batch,List.length_cons]
    nlinarith

/-- All invocation files may be retained simultaneously. A factor 256 at
one node overprovisions input, output and all padded/shifted versions,
using s⁴<16n and s³≤s⁴. This coarse bound is independent of all primitive I/O charges. -/
theorem fits_reservation (H g : ℕ) (hH : 0 < H) (fuel n : ℕ) (tree : Tree)
    (hf : LocalTrace.Fits H fuel n tree) :
    reservation g tree ≤ 256*81^fuel*n*g := by
  induction fuel generalizing n tree with
  | zero => rw [hf.leaf_of_zero]; simp [reservation]
  | succ fuel ih =>
    cases hf with
    | leaf n hleaf =>
      simp only [reservation]
      have hpow : 1≤81^(fuel+1) := Nat.one_le_pow _ _ (by norm_num)
      simpa [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_left (256*n*g) hpow
    | node hlarge hfirst hsecond hthird hfourth f₁ f₂ f₃ f₄ =>
      have h₁ := batch_bound g (256*81^fuel*columnLength n*g) _
        (fun t ht => ih _ _ (f₁ t ht))
      have h₂ := batch_bound g (256*81^fuel*columnLength n*g) _
        (fun t ht => ih _ _ (f₂ t ht))
      have h₃ := batch_bound g (256*81^fuel*columnLength n*g) _
        (fun t ht => ih _ _ (f₃ t ht))
      have h₄ := batch_bound g (256*81^fuel*columnLength n*g) _
        (fun t ht => ih _ _ (f₄ t ht))
      rw [hfirst] at h₁; rw [hsecond] at h₂; rw [hthird] at h₃; rw [hfourth] at h₄
      have hv := child_volume n (by nlinarith)
      have hmul := Nat.mul_le_mul_left (256*81^fuel*g) hv.le
      have hpow : 1≤81^fuel := Nat.one_le_pow _ _ (by norm_num)
      have hroot := Nat.mul_le_mul_right (256*n*g) hpow
      simp only [reservation,pow_succ]
      try dsimp only [columnLength] at h₁ h₂ h₃ h₄ hmul
      nlinarith only [h₁,h₂,h₃,h₄,hmul,hroot]

/-- An explicit inventory of finite arrays: input, five padded versions,
and two extended shifted versions. The capacity is bounded before summing
it over the actual call tree. -/
theorem node_array_capacity (n g : ℕ) (hn : 1<n) :
    (n+5*sizeChoice n^4+2*(sizeChoice n^4+sizeChoice n^3))*g≤256*n*g := by
  have hp := padding_lt n hn
  have hs : 0<sizeChoice n := pow_pos (by norm_num) _
  have hr : sizeChoice n^3≤sizeChoice n^4 := by
    calc
      sizeChoice n^3≤sizeChoice n^3*sizeChoice n := Nat.le_mul_of_pos_right _ hs
      _=sizeChoice n^4 := by ring
  have h : n+5*sizeChoice n^4+2*(sizeChoice n^4+sizeChoice n^3)≤256*n := by omega
  exact Nat.mul_le_mul_right g h


theorem actual_grouped_reservation {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α]
    (H g : ℕ) (hH : 0 < H) (hg : 0 < g) (n : ℕ) (f : Fin n→α) :
    reservation g (GroupedRecursiveColumnsort.localRun H g hH hg 3 n f).trace ≤
      256*81^3*(GroupedRecursiveColumnsort.groups g n)*g :=
  fits_reservation H g hH 3 _ _
    (GroupedRecursiveColumnsort.localRun_trace_fits H g hH hg 3 n f)

end Local


namespace MSD
open ExternalMSD

structure Run where
  output : List ℕ
  nodes : ℕ
  reservation : ℕ

/-- Instrument the actual most-significant-digit recursion. Its output and
space counters use exactly the same prepared rows and recursive calls. -/
def run (C base : ℕ) (hb : 0 < base) (H : ℕ) (hH : 0 < H)
    (localSort : CSL.MSD.LocalSorter) : ℕ → List ℕ → Run
  | 0,xs => ⟨xs,1,C*xs.length⟩
  | fuel+1,xs =>
    if xs.length≤H^2 then
      ⟨localSort (fun x => x%base^(fuel+1)) xs,1,C*xs.length⟩
    else
      let rows := prepare base hb H hH localSort fuel xs
      let runs := (List.finRange base).map (fun k =>
        run C base hb H hH localSort fuel (child (CSL.MSD.digit base hb fuel) rows k))
      ⟨runs.flatMap Run.output,1+(runs.map Run.nodes).sum,
        C*xs.length+(runs.map Run.reservation).sum⟩

theorem output_eq (C base : ℕ) (hb : 0 < base) (H : ℕ) (hH : 0 < H)
    (localSort : CSL.MSD.LocalSorter) (fuel : ℕ) (xs : List ℕ) :
    (run C base hb H hH localSort fuel xs).output =
      ExternalMSD.sort base hb H hH localSort fuel xs := by
  induction fuel generalizing xs with
  | zero => rfl
  | succ fuel ih =>
    simp only [run,ExternalMSD.sort]
    split_ifs
    · rfl
    · simp only [List.flatMap_map,Function.comp_def,ih]

private theorem sum_map_le {β : Type*} (xs : List β) (f g : β→ℕ)
    (h : ∀ x∈xs,f x≤g x) : (xs.map f).sum≤(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    have hh := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons]
    omega

/-- Conservation of records at one actual MSD node controls the sum of
space reservations over all levels, even if every old file is retained. -/
theorem run_bounds (C base : ℕ) (hb : 0 < base) (H : ℕ) (hH : 0 < H)
    (localSort : CSL.MSD.LocalSorter) (hc : CSL.MSD.LocalCorrect localSort)
    (fuel : ℕ) (xs : List ℕ) :
    (run C base hb H hH localSort fuel xs).nodes≤1+base*fuel*xs.length ∧
    (run C base hb H hH localSort fuel xs).reservation≤C*(fuel+1)*xs.length := by
  induction fuel generalizing xs with
  | zero => simp [run]
  | succ fuel ih =>
    rw [run]
    split_ifs with hsmall
    · try dsimp only
      constructor
      · omega
      · have h := Nat.mul_le_mul_right (C*xs.length) (show 1≤fuel+1+1 by omega)
        simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h
    · try dsimp only
      let rows := prepare base hb H hH localSort fuel xs
      let f := fun k => child (CSL.MSD.digit base hb fuel) rows k
      have hv : ((List.finRange base).map (fun k => (f k).length)).sum=xs.length := by
        rw [children_volume]
        exact (prepare_perm base hb H hH localSort hc fuel xs).length_eq
      have hn := sum_map_le (List.finRange base)
        (fun k => (run C base hb H hH localSort fuel (f k)).nodes)
        (fun k => 1+base*fuel*(f k).length) (fun k _ => (ih (f k)).1)
      have hr := sum_map_le (List.finRange base)
        (fun k => (run C base hb H hH localSort fuel (f k)).reservation)
        (fun k => C*(fuel+1)*(f k).length) (fun k _ => (ih (f k)).2)
      simp only [List.sum_map_add,List.sum_map_mul_left,List.map_const',List.length_finRange,
        List.sum_replicate,smul_eq_mul,Nat.mul_one,hv] at hn hr
      simp only [List.map_map,Function.comp_def]
      have hpos : 1≤xs.length := by nlinarith
      constructor
      · change 1+((List.finRange base).map (fun k =>
          (run C base hb H hH localSort fuel (f k)).nodes)).sum≤_
        have hm := Nat.mul_le_mul_left base hpos
        nlinarith only [hn,hm]
      · change C*xs.length+((List.finRange base).map (fun k =>
          (run C base hb H hH localSort fuel (f k)).reservation)).sum≤_
        nlinarith only [hr]

/-- The manuscript's w=O(log N) hypothesis gives a polynomial depth. The
proof does not impose the stronger restriction w≤log N. -/
theorem fuel_bound (base w κ N : ℕ) (hb : 2≤base)
    (hw : w≤κ*Nat.clog 2 N) : Nat.clog base (2^w)≤κ*N := by
  have hf : Nat.clog base (2^w)≤w :=
    (Nat.le_pow_iff_clog_le (by omega)).1 (Nat.pow_le_pow_left hb _)
  have hlog : Nat.clog 2 N≤N := by
    apply (Nat.le_pow_iff_clog_le (by omega)).1
    exact (Nat.lt_pow_self (by omega) (n := N)).le
  exact hf.trans (hw.trans (Nat.mul_le_mul_left κ hlog))

/-- Raw payload reservation is quadratic in N even when every level's
files are retained. Empty child calls are included in the cubic node bound. -/
theorem polynomial_bounds (C base w κ H : ℕ) (hb : 2≤base) (hH : 0 < H)
    (localSort : CSL.MSD.LocalSorter) (hc : CSL.MSD.LocalCorrect localSort)
    (xs : List ℕ) (hbase : base≤xs.length) (hw : w≤κ*Nat.clog 2 xs.length) :
    let result := run C base (by omega) H hH localSort (Nat.clog base (2^w)) xs
    result.nodes≤1+κ*xs.length^3 ∧
    result.reservation≤C*(κ+1)*xs.length^2 := by
  try dsimp only
  obtain ⟨hn,hr⟩ := run_bounds C base (by omega) H hH localSort hc _ xs
  have hf := fuel_bound base w κ xs.length hb hw
  have hpos : 1≤xs.length := by omega
  constructor
  · apply hn.trans
    have hm := Nat.mul_le_mul hbase hf
    have hh := Nat.mul_le_mul_right xs.length hm
    nlinarith only [hh]
  · apply hr.trans
    have hdepth : Nat.clog base (2^w)+1≤(κ+1)*xs.length := by nlinarith
    have h := Nat.mul_le_mul_left (C*xs.length) hdepth
    nlinarith only [h]


private theorem pack_length_le {α : Type*} (B : ℕ) (hB : 0<B) (xs : List α) :
    (BucketMachine.pack B hB xs).length≤xs.length := by
  have h := (BucketMachine.pack_capacity B hB xs).2
  have hn : xs.length≤xs.length*B := Nat.le_mul_of_pos_right _ hB
  by_contra hbad
  have hm := Nat.mul_le_mul_right B (show xs.length+1≤(BucketMachine.pack B hB xs).length by omega)
  nlinarith

/-- Block-alignment slack of every actual interval scratch file is included.
It is not silently identified with its count of useful records. -/
theorem fragment_slots (base B : ℕ) (hb : 0<base) (hB : 0<B) (H : ℕ) (hH : 0<H)
    (localSort : CSL.MSD.LocalSorter) (hc : CSL.MSD.LocalCorrect localSort)
    (fuel : ℕ) (xs : List ℕ) :
    let rows := prepare base hb H hH localSort fuel xs
    let files := storedFragments (CSL.MSD.digit base hb fuel) B hB rows
    (files.map List.length).sum*B≤(1+base*B)*xs.length := by
  try dsimp only
  have h := fragment_transfer_capacity (CSL.MSD.digit base hb fuel) B hB
    (prepare base hb H hH localSort fuel xs)
  have hv := (prepare_perm base hb H hH localSort hc fuel xs).length_eq
  have hr : (prepare base hb H hH localSort fuel xs).length≤xs.length := by
    simpa only [prepare,sortedChunks,List.length_map] using
      pack_length_le (H^2) (Nat.pow_pos hH) xs
  rw [hv] at h
  have hm := Nat.mul_le_mul_right (base*B) hr
  have hh : transferSum B hB (fragments (CSL.MSD.digit base hb fuel)
      (prepare base hb H hH localSort fuel xs))*B≤(1+base*B)*xs.length := by
    nlinarith only [h,hm]
  simpa only [storedFragments,transferSum,List.map_map,Function.comp_def] using hh

/-- A coarse bound including per-node block-aligned interval files. The
coefficient 8+4baseB allows several current/old versions; both base and B
are at most N. Full files may be retained without violating polynomial space. -/
theorem aligned_polynomial_bound (base B w κ H : ℕ) (hb : 2≤base) (hH : 0<H)
    (localSort : CSL.MSD.LocalSorter) (hc : CSL.MSD.LocalCorrect localSort)
    (xs : List ℕ) (hbase : base≤xs.length) (hB : B≤xs.length)
    (hw : w≤κ*Nat.clog 2 xs.length) :
    (run (8+4*base*B) base (by omega) H hH localSort
      (Nat.clog base (2^w)) xs).reservation ≤12*(κ+1)*xs.length^4 := by
  have h := (polynomial_bounds (8+4*base*B) base w κ H hb hH localSort hc xs hbase hw).2
  have hm := Nat.mul_le_mul hbase hB
  have hn : 1≤xs.length^2 := Nat.one_le_pow _ _ (by omega)
  have hcoef : 8+4*base*B≤12*xs.length^2 := by nlinarith only [hm,hn]
  have hp := Nat.mul_le_mul_right ((κ+1)*xs.length^2) hcoef
  nlinarith only [h,hp]

end MSD
end
end CSL.PolynomialWorkspace


