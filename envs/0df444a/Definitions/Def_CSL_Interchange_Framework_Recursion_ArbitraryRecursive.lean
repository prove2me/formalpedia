-- Prove2me | Definitions.Def_CSL_Interchange_Framework_Recursion_ArbitraryRecursive
-- name    : CSL_Interchange_Framework_Recursion_ArbitraryRecursive
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:59:24.606595+00:00
-- url     : https://prove2.me/theorems/b95a3551-de91-4c5f-9ce1-72c6f3e0865b
-- title:
--   Coded sorting library: Interchange / Framework / Recursion / ArbitraryRecursive
-- statement:
--   Module `CodedSorting.Interchange.Framework.Recursion.ArbitraryRecursive` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   The arbitrary-width chunk list calls the actual recursive coded
--   exchange. No chunk-exchange correctness oracle is supplied to this module.
--   This file is the functional bridge; physical primitive costs are separate.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Interchange.Framework.Recursion.ArbitraryRecursive

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Indexing_DependentCoordinate
import Definitions.Def_CSL_Interchange_Framework_Recursion_RecursiveExchange

/-! The arbitrary-width chunk list calls the actual recursive coded
exchange. No chunk-exchange correctness oracle is supplied to this module.
This file is the functional bridge; physical primitive costs are separate. -/

namespace CSL.ArbitraryRecursive

open Address Circuit CodedSimulation ArbitrarySchedule DependentCoordinate
open RecursiveExchange

noncomputable section

structure Call where
  baseWidth : ℕ
  depth : ℕ
  deriving DecidableEq

def Call.width (c : Call) : ℕ := c.baseWidth * Parameters.m ^ c.depth

def calls (t₀ k e : ℕ) : List Call :=
  (scales Parameters.m k (e/t₀)).map (fun j => ⟨t₀,j⟩) ++ [⟨e%t₀,0⟩]

theorem calls_width (t₀ k e : ℕ) : ((calls t₀ k e).map Call.width).sum = e := by
  first
  | exact widths_sum Parameters.m t₀ k e
  | (have h_sx := widths_sum Parameters.m t₀ k e; simp only [calls,List.map_append,List.map_map,List.map_cons,List.map_nil,
    Call.width,pow_zero,Nat.mul_one,Function.comp_apply] at h_sx ⊢; exact h_sx)
  | (have h_sx := widths_sum Parameters.m t₀ k e; simp only [calls,List.map_append,List.map_map,List.map_cons,List.map_nil,
    Call.width,pow_zero,Nat.mul_one,Function.comp_apply] at h_sx; exact h_sx)
  | (simp only [calls,List.map_append,List.map_map,List.map_cons,List.map_nil,
    Call.width,pow_zero,Nat.mul_one,Function.comp_apply]; exact widths_sum Parameters.m t₀ k e)

theorem calls_depth (t₀ k e : ℕ) (i : Fin (calls t₀ k e).length) :
    ((calls t₀ k e).get i).depth ≤ k := by
  have hi := List.get_mem (calls t₀ k e) i
  rcases List.mem_append.mp hi with h | h
  · obtain ⟨j,hj,he⟩ := List.mem_map.mp h
    rw [← he]
    exact scales_depth _ _ _ _ hj
  · have he : (calls t₀ k e).get i = ⟨e%t₀,0⟩ := by simpa using h
    rw [he]
    exact Nat.zero_le k

abbrev Field (cs : List Call) (i : Fin cs.length) := Scalar (cs.get i).width
abbrev Fields (cs : List Call) := (i : Fin cs.length) → Field cs i

theorem fields_card (cs : List Call) :
    Fintype.card (Fields cs) = radix ^ (cs.map Call.width).sum := by
  simp only [Fields,Fintype.card_pi,Field,short_field_card]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_apply] using
    congrArg (fun xs : List Call => (xs.map Call.width).sum) (List.ofFn_get cs)

theorem calls_field_card (t₀ k e : ℕ) :
    Fintype.card (Fields (calls t₀ k e)) = radix^e := by
  rw [fields_card,calls_width]

abbrev LongAddress (cs : List Call) (Rows : ℕ) (Gap Suffix : Type*) :=
  FullAddress (Fin Rows) (Fields cs) Gap Suffix

def shortRows (cs : List Call) (Rows : ℕ) (i : Fin cs.length) : ℕ :=
  Fintype.card (ShortPrefix (Prefix:=Fin Rows) (α:=Field cs) i) /
    Parameters.W ^ (cs.get i).depth

theorem shortPrefix_divisible (cs : List Call) (Rows : ℕ) (i : Fin cs.length)
    (hfit : Parameters.W ^ (cs.get i).depth ∣ Rows) :
    Parameters.W ^ (cs.get i).depth ∣
      Fintype.card (ShortPrefix (Prefix:=Fin Rows) (α:=Field cs) i) := by
  simpa [ShortPrefix,Fintype.card_prod] using
    dvd_mul_of_dvd_left hfit (Fintype.card (BeforeField (α:=Field cs) i))

/-- The regrouped prefix contains the original padded rows and every high
chunk before i. Its divisibility is inherited from the padded row count. -/
def shortLayout (cs : List Call) (Rows : ℕ) (i : Fin cs.length)
    (hfit : Parameters.W ^ (cs.get i).depth ∣ Rows) :
    ShortPrefix (Prefix:=Fin Rows) (α:=Field cs) i ≃
      Fin (shortRows cs Rows i * Parameters.W ^ (cs.get i).depth) :=
  Fintype.equivFinOfCardEq (Nat.div_mul_cancel (shortPrefix_divisible cs Rows i hfit)).symm

/-- Expose one adjacent pair of corresponding chunks, invoke the actual
`recursiveExchange`, then restore the original coordinate grouping. -/
def executeOne (cs : List Call) (Rows : ℕ) {Gap Suffix : Type}
    (hfit : ∀ i : Fin cs.length, Parameters.W ^ (cs.get i).depth ∣ Rows)
    (i : Fin cs.length) (F : LongAddress cs Rows Gap Suffix → Bit) :=
  ArbitraryShapes.move (DependentCoordinate.repack i).symm
    (recursiveExchange (cs.get i).baseWidth (cs.get i).depth (shortRows cs Rows i)
      (shortLayout cs Rows i (hfit i))
      (ArbitraryShapes.move (DependentCoordinate.repack i) F))

theorem executeOne_correct (cs : List Call) (Rows : ℕ) {Gap Suffix : Type}
    (hfit : ∀ i : Fin cs.length, Parameters.W ^ (cs.get i).depth ∣ Rows)
    (i : Fin cs.length) (F : LongAddress cs Rows Gap Suffix → Bit) :
    executeOne cs Rows hfit i F = fun a => F (swapChunk i a) := by
  unfold executeOne
  rw [recursiveExchange_correct]
  have hdec : (fun x y : Fin cs.length => @LinearOrder.toDecidableEq _ inferInstance x y) =
      (inferInstance : DecidableEq (Fin cs.length)) := Subsingleton.elim _ _
  first
  | exact transported_chunk i F
  | (have h_sx := transported_chunk i F; simp only [hdec] at h_sx ⊢; exact h_sx)
  | (have h_sx := transported_chunk i F; simp only [hdec] at h_sx; exact h_sx)
  | (simp only [hdec]; exact transported_chunk i F)

def executeList (cs : List Call) (Rows : ℕ) {Gap Suffix : Type}
    (hfit : ∀ i : Fin cs.length, Parameters.W ^ (cs.get i).depth ∣ Rows) :
    List (Fin cs.length) → (LongAddress cs Rows Gap Suffix → Bit) →
      (LongAddress cs Rows Gap Suffix → Bit)
  | [],F => F
  | i::is,F => executeOne cs Rows hfit i (executeList cs Rows hfit is F)

theorem executeList_correct (cs : List Call) (Rows : ℕ) {Gap Suffix : Type}
    (hfit : ∀ i : Fin cs.length, Parameters.W ^ (cs.get i).depth ∣ Rows)
    (is : List (Fin cs.length)) (F : LongAddress cs Rows Gap Suffix → Bit) :
    executeList cs Rows hfit is F = fun a => F (runChunks is a) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [executeList,executeOne_correct,ih,runChunks]

def execute (cs : List Call) (Rows : ℕ) {Gap Suffix : Type}
    (hfit : ∀ i : Fin cs.length, Parameters.W ^ (cs.get i).depth ∣ Rows)
    (F : LongAddress cs Rows Gap Suffix → Bit) :=
  executeList cs Rows hfit Finset.univ.toList F

theorem execute_correct (cs : List Call) (Rows : ℕ) {Gap Suffix : Type}
    (hfit : ∀ i : Fin cs.length, Parameters.W ^ (cs.get i).depth ∣ Rows)
    (F : LongAddress cs Rows Gap Suffix → Bit) :
    execute cs Rows hfit F = transport exchangeEquiv F := by
  unfold execute
  rw [executeList_correct]
  funext a
  rw [runChunks_correct]
  rfl

/-- Every concrete emitted call has an admissible padded row layout. -/
theorem calls_fit_padded_rows (q t₀ k e : ℕ) (i : Fin (calls t₀ k e).length) :
    Parameters.W ^ ((calls t₀ k e).get i).depth ∣
      ArbitraryShapes.paddedCount (q^(2*borrowedWidth q Parameters.W k))
        (Parameters.W^(k+1)) :=
  all_depths_divide_padding q Parameters.W k _
    (by norm_num [Parameters.W_value]) (calls_depth t₀ k e i)

def padInput (cs : List Call) (Rows Rows' : ℕ) {Gap Suffix : Type}
    (F : LongAddress cs Rows Gap Suffix → Bit) : LongAddress cs Rows' Gap Suffix → Bit :=
  fun a => if h : a.prefixCoord.val < Rows then
    F ⟨⟨a.prefixCoord.val,h⟩,a.high,a.gap,a.low,a.suffix⟩ else 0

def restrictOutput (cs : List Call) (Rows Rows' : ℕ) {Gap Suffix : Type}
    (hrows : Rows ≤ Rows') (F : LongAddress cs Rows' Gap Suffix → Bit) :
    LongAddress cs Rows Gap Suffix → Bit :=
  fun a => F ⟨a.prefixCoord.castLE hrows,a.high,a.gap,a.low,a.suffix⟩

def paddedExecute (cs : List Call) (Rows Rows' : ℕ) {Gap Suffix : Type}
    (hrows : Rows ≤ Rows')
    (hfit : ∀ i : Fin cs.length, Parameters.W ^ (cs.get i).depth ∣ Rows')
    (F : LongAddress cs Rows Gap Suffix → Bit) :=
  restrictOutput cs Rows Rows' hrows (execute cs Rows' hfit (padInput cs Rows Rows' F))

theorem paddedExecute_correct (cs : List Call) (Rows Rows' : ℕ) {Gap Suffix : Type}
    (hrows : Rows ≤ Rows')
    (hfit : ∀ i : Fin cs.length, Parameters.W ^ (cs.get i).depth ∣ Rows')
    (F : LongAddress cs Rows Gap Suffix → Bit) :
    paddedExecute cs Rows Rows' hrows hfit F = transport exchangeEquiv F := by
  unfold paddedExecute
  rw [execute_correct]
  funext a
  simp only [restrictOutput,transport,exchangeEquiv,Equiv.coe_fn_symm_mk,
    exchange,padInput,Fin.coe_castLE]
  exact dif_pos a.prefixCoord.isLt

def prefixEquiv {P P' Field Gap Suffix : Type} (e : P ≃ P') :
    FullAddress P Field Gap Suffix ≃ FullAddress P' Field Gap Suffix where
  toFun a := ⟨e a.prefixCoord,a.high,a.gap,a.low,a.suffix⟩
  invFun a := ⟨e.symm a.prefixCoord,a.high,a.gap,a.low,a.suffix⟩
  left_inv a := by cases a; simp
  right_inv a := by cases a; simp

theorem prefix_exchange {P P' Field Gap Suffix : Type} (e : P ≃ P')
    (F : FullAddress P Field Gap Suffix → Bit) :
    ArbitraryShapes.move (prefixEquiv e).symm
      (transport exchangeEquiv (ArbitraryShapes.move (prefixEquiv e) F)) =
        transport exchangeEquiv F := by
  funext a
  cases a
  simp only [ArbitraryShapes.move,transport,prefixEquiv,exchangeEquiv,
    Equiv.coe_fn_mk,Equiv.coe_fn_symm_mk,Equiv.symm_symm,exchange,
    Equiv.symm_apply_apply]

/-- The full borrowed-field transformer contains the genuine coded
recursive calls inside its padded region, not a replacement swap oracle. -/
def borrowedExecute (cs : List Call) {Prefix High Gap Suffix : Type}
    (Rows Rows' : ℕ) (layout : (Prefix × High × High) ≃ Fin Rows)
    (hrows : Rows ≤ Rows')
    (hfit : ∀ i : Fin cs.length, Parameters.W ^ (cs.get i).depth ∣ Rows')
    (F : ArbitraryShapes.Original (Prefix:=Prefix) (High:=High) (Low:=Fields cs)
      (Gap:=Gap) (Suffix:=Suffix) → Bit) :=
  ArbitraryShapes.move ArbitraryShapes.finishEquiv
    (ArbitraryShapes.move (prefixEquiv layout).symm
      (paddedExecute cs Rows Rows' hrows hfit
        (ArbitraryShapes.move (prefixEquiv layout)
          (ArbitraryShapes.move ArbitraryShapes.borrowEquiv F))))

theorem borrowedExecute_correct (cs : List Call) {Prefix High Gap Suffix : Type}
    (Rows Rows' : ℕ) (layout : (Prefix × High × High) ≃ Fin Rows)
    (hrows : Rows ≤ Rows')
    (hfit : ∀ i : Fin cs.length, Parameters.W ^ (cs.get i).depth ∣ Rows')
    (F : ArbitraryShapes.Original (Prefix:=Prefix) (High:=High) (Low:=Fields cs)
      (Gap:=Gap) (Suffix:=Suffix) → Bit) :
    borrowedExecute cs Rows Rows' layout hrows hfit F = transport exchangeEquiv F := by
  unfold borrowedExecute
  rw [paddedExecute_correct,prefix_exchange]
  funext a
  cases a
  rfl

def paddedRows (Rows k : ℕ) := ArbitraryShapes.paddedCount Rows (Parameters.W^(k+1))

theorem original_rows_le_padded (Rows k : ℕ) : Rows ≤ paddedRows Rows k :=
  ArbitraryShapes.paddedCount_ge _ _ (pow_pos (by norm_num [Parameters.W_value]) _)

theorem automatic_calls_fit (Rows t₀ k e : ℕ) (i : Fin (calls t₀ k e).length) :
    Parameters.W ^ ((calls t₀ k e).get i).depth ∣ paddedRows Rows k :=
  dvd_trans (pow_dvd_pow Parameters.W (by have := calls_depth t₀ k e i; omega))
    (ArbitraryShapes.paddedCount_multiple _ _)

def automaticBorrowed (Rows t₀ k e : ℕ) {Prefix High Gap Suffix : Type}
    (layout : (Prefix × High × High) ≃ Fin Rows)
    (F : ArbitraryShapes.Original (Prefix:=Prefix) (High:=High)
      (Low:=Fields (calls t₀ k e)) (Gap:=Gap) (Suffix:=Suffix) → Bit) :=
  borrowedExecute (calls t₀ k e) Rows (paddedRows Rows k) layout
    (original_rows_le_padded Rows k) (automatic_calls_fit Rows t₀ k e) F

theorem automaticBorrowed_correct (Rows t₀ k e : ℕ) {Prefix High Gap Suffix : Type}
    (layout : (Prefix × High × High) ≃ Fin Rows)
    (F : ArbitraryShapes.Original (Prefix:=Prefix) (High:=High)
      (Low:=Fields (calls t₀ k e)) (Gap:=Gap) (Suffix:=Suffix) → Bit) :
    automaticBorrowed Rows t₀ k e layout F = transport exchangeEquiv F :=
  borrowedExecute_correct _ _ _ layout _ _ F

def highRows (Outer ρ : ℕ) := Outer*((radix^ρ)*(radix^ρ))

/-- Standard row-major packing, with the borrowed D-high before H-high. -/
def highPrefixLayout (Outer ρ : ℕ) :
    (Fin Outer × Scalar ρ × Scalar ρ) ≃ Fin (highRows Outer ρ) :=
  (Equiv.prodCongr (Equiv.refl (Fin Outer))
    ((Equiv.prodCongr (ZMod.finEquiv (radix^ρ)).symm.toEquiv
      (ZMod.finEquiv (radix^ρ)).symm.toEquiv).trans finProdFinEquiv)).trans finProdFinEquiv

theorem highRows_enough (Outer k : ℕ) (hOuter : 0<Outer) :
    Parameters.W^(k+1) ≤ highRows Outer (borrowedWidth radix Parameters.W k) := by
  have h := borrowed_rows_enough radix Parameters.W k radix_prime.one_lt
  have hpow : radix ^ (2 * borrowedWidth radix Parameters.W k) =
      radix ^ borrowedWidth radix Parameters.W k *
        radix ^ borrowedWidth radix Parameters.W k := by
    rw [two_mul,pow_add]
  rw [hpow] at h
  exact h.trans (Nat.le_mul_of_pos_left _ hOuter)

theorem generated_padding_bound (Outer k : ℕ) (hOuter : 0<Outer) :
    paddedRows (highRows Outer (borrowedWidth radix Parameters.W k)) k <
      2*highRows Outer (borrowedWidth radix Parameters.W k) :=
  ArbitraryShapes.paddedCount_lt_twice _ _
    (pow_pos (by norm_num [Parameters.W_value]) _) (highRows_enough Outer k hOuter)

/-- No layout or divisibility oracle remains: the borrowed row layout and
every recursive child prefix are constructed from the actual parameters. -/
def generatedBorrowed (Outer t₀ e : ℕ) {Gap Suffix : Type}
    (F : ArbitraryShapes.Original (Prefix:=Fin Outer)
      (High:=Scalar (borrowedWidth radix Parameters.W (depth Parameters.m t₀ e)))
      (Low:=Fields (calls t₀ (depth Parameters.m t₀ e)
        (e-borrowedWidth radix Parameters.W (depth Parameters.m t₀ e))))
      (Gap:=Gap) (Suffix:=Suffix) → Bit) :=
  automaticBorrowed
    (highRows Outer (borrowedWidth radix Parameters.W (depth Parameters.m t₀ e)))
    t₀ (depth Parameters.m t₀ e)
    (e-borrowedWidth radix Parameters.W (depth Parameters.m t₀ e))
    (highPrefixLayout Outer _) F

theorem generatedBorrowed_correct (Outer t₀ e : ℕ) {Gap Suffix : Type}
    (F : ArbitraryShapes.Original (Prefix:=Fin Outer)
      (High:=Scalar (borrowedWidth radix Parameters.W (depth Parameters.m t₀ e)))
      (Low:=Fields (calls t₀ (depth Parameters.m t₀ e)
        (e-borrowedWidth radix Parameters.W (depth Parameters.m t₀ e))))
      (Gap:=Gap) (Suffix:=Suffix) → Bit) :
    generatedBorrowed Outer t₀ e F = transport exchangeEquiv F :=
  automaticBorrowed_correct _ _ _ _ _ F

def baseCalls (t₀ e : ℕ) : List Call :=
  List.replicate (e/t₀) ⟨t₀,0⟩ ++ [⟨e%t₀,0⟩]

theorem baseCalls_width (t₀ e : ℕ) : ((baseCalls t₀ e).map Call.width).sum = e := by
  simp only [baseCalls,List.map_append,List.sum_append,List.map_replicate,
    List.sum_replicate,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Call.width,pow_zero,Nat.mul_one,smul_eq_mul,Nat.add_zero]
  simpa only [Nat.mul_comm] using Nat.div_add_mod e t₀

theorem baseCalls_depth (t₀ e : ℕ) (i : Fin (baseCalls t₀ e).length) :
    ((baseCalls t₀ e).get i).depth = 0 := by
  have hi := List.get_mem (baseCalls t₀ e) i
  rcases List.mem_append.mp hi with h | h
  · rw [(List.mem_replicate.mp h).2]
  · have he : (baseCalls t₀ e).get i = ⟨e%t₀,0⟩ := by simpa using h
    rw [he]

theorem baseCalls_fit (Rows t₀ e : ℕ) (i : Fin (baseCalls t₀ e).length) :
    Parameters.W ^ ((baseCalls t₀ e).get i).depth ∣ Rows := by
  rw [baseCalls_depth,pow_zero]
  exact one_dvd Rows

def generatedBase (Rows t₀ e : ℕ) {Gap Suffix : Type}
    (F : LongAddress (baseCalls t₀ e) Rows Gap Suffix → Bit) :=
  execute (baseCalls t₀ e) Rows (baseCalls_fit Rows t₀ e) F

theorem generatedBase_correct (Rows t₀ e : ℕ) {Gap Suffix : Type}
    (F : LongAddress (baseCalls t₀ e) Rows Gap Suffix → Bit) :
    generatedBase Rows t₀ e F = transport exchangeEquiv F :=
  execute_correct _ _ _ F

end
end CSL.ArbitraryRecursive


