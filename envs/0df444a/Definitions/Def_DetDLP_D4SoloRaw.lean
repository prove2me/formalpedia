-- Prove2me | Definitions.Def_DetDLP_D4SoloRaw
-- name    : DetDLP_D4SoloRaw
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T15:17:30.248326+00:00
-- url     : https://prove2.me/theorems/d591235c-7153-4b91-ada2-8a2eb6658f07
-- title:
--   Polynomial-time wire pre/post pipelines for partial core unrolling
-- statement:
--   This module specifies the polynomial-time raw bitstring pipelines `preWalkGen`, `postWalkGen`, and `permutePktQuery` used to compile partial core unrolling for high-arity lookup-separator bipartite Boolean tensor networks.
--
--   Given a rank query $q = [x, j]$, `preWalkGen` constructs a polynomial-size unary fuel list, generates the monic irreducible modulus bits $f$, builds the rank-walker context $\mathrm{ctx}$ for depth $D = \lceil \log_{32}(4m) \rceil$, and invokes the core-cut map to form the initial work item. Given the walker output, `postWalkGen` extracts either the global header (for $j = 0$) or, for $j > 0$, formats either a hit branch or a zero-weight overflow branch together with lookup and stopped-core source descriptors, while `permutePktQuery` routes packet query bits under accumulated port permutations.
--
--   These definitions and their accompanying `Groundwork.PolyT` proofs bridge the abstract partial-unrolling semantics to a single deterministic `PrimitiveMachine` enumerator without manual multi-tape state transitions.
-- source:
--   Deterministic Discrete Logarithms paper, Section 5.3 (Theorem 4.3 and Lemma 5.3)

import Definitions.Def_DetDLP_D4RankWalkerV2
import Definitions.Def_DetDLP_D4GuardWeight
import Definitions.Def_DetDLP_D4UnrollBudget
import Definitions.Def_DetDLP_D4Slice
import Theorems.Thm_DetDLP_m13a_irred_poly_machine
import Theorems.Thm_Groundwork_PolyT_div_pow
import Theorems.Thm_Groundwork_PolyT_pow_unary
import Theorems.Thm_Groundwork_PolyT_countP
import Theorems.Thm_Groundwork_PolyT_idxOf
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_foldl_add
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
import Theorems.Thm_P2M_Groundwork_PolyT_size__c8c8eb1b342f

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace DetDLP.D4SoloRaw

open Groundwork Groundwork.PolyT DetDLP DetDLP_W1_Queries Polynomial
open DetDLP.AppendixD4 DetDLP.D4RankWalker
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

section UnpackPack

private theorem scan_frame (x rev : Wd) (acc : List Wd) :
    (Encoding.frame x).foldl scan (false, true, rev, acc) = (false, false, [], (rev.reverse ++ x) :: acc) := by
  induction x generalizing rev with
  | nil => simp [Encoding.frame, scan]
  | cons b x ih =>
    change (Encoding.frame x).foldl scan (false, true, b :: rev, acc) = _
    simpa using ih (b :: rev)

private theorem scan_pack (xs acc : List Wd) :
    (pack xs).foldl scan (false, false, [], acc) = (true, true, [], xs.reverse ++ acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    change (Encoding.frame x ++ pack xs).foldl scan (false, true, [], acc) = _
    rw [List.foldl_append, scan_frame]
    simpa using ih (x :: acc)

@[simp] theorem unpack_pack (xs : List Wd) : unpack (pack xs) = xs := by
  simp [unpack, scan_pack]

@[simp] theorem unpack_encodeList_id (xs : List Wd) : unpack (Encoding.encodeList id xs) = xs :=
  unpack_pack xs

@[simp] theorem fld_pack (xs : List Wd) (i : ℕ) : fld (pack xs) i = xs.getD i [] := by
  simp [fld]

@[simp] theorem fld_encodeList_id (xs : List Wd) (i : ℕ) :
    fld (Encoding.encodeList id xs) i = xs.getD i [] := by
  simp [fld]

@[simp] theorem num_countWord (n : ℕ) : bval (countWord n) = n :=
  DetDLP_W1_Queries.decode_count n

@[simp] theorem ints_encodeNatListBin (ns : List ℕ) : ints (encodeNatListBin ns) = ns :=
  w5_M6Sort.decode_encode ns

theorem pack_eq_flat (xs : List Wd) : pack xs = xs.flatMap (fun u => true :: frame u) ++ [false] := by
  induction xs with
  | nil => rfl
  | cons u xs ih =>
    change true :: (Encoding.frame u ++ pack xs) = _
    simp [ih, List.flatMap, List.append_assoc]

theorem countWord_two_pow (B : ℕ) : countWord (2 ^ B) = List.replicate B false ++ [true] := by
  suffices hb : (2 ^ B).bits = List.replicate B false ++ [true] by
    have hne : 2 ^ B ≠ 0 := by positivity
    rw [countWord, if_neg hne, hb]
  induction B with
  | zero => decide
  | succ B ih =>
    have hpos : 2 ^ B ≠ 0 := by positivity
    have hbit : 2 ^ (B + 1) = Nat.bit false (2 ^ B) := by
      simp [Nat.bit, pow_succ']
    rw [hbit, Nat.bits_append_bit (2 ^ B) false (fun h => absurd h hpos), ih]
    rfl

end UnpackPack

section PolyTPrimitives

attribute [local fun_prop] PolyT.const PolyT.fst PolyT.snd PolyT.prodMk PolyT.comp PolyT.id'
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_cons__3a60f43a3b86
  P2M_Groundwork_PolyT_cond__4c673073da15 P2M_Groundwork_PolyT_ite__226169acf219
  P2M_Groundwork_PolyT_size__c8c8eb1b342f
  PolyT.div PolyT.mod PolyT.mul PolyT.div_pow PolyT.map PolyT.flatMap PolyT.filter
  PolyT.countP PolyT.sum PolyT.length PolyT.reverse PolyT.append PolyT.take PolyT.drop
  PolyT.getD PolyT.headD PolyT.tail PolyT.isEmpty PolyT.idxOf PolyT.any
  first_poly more_poly frame_poly w5_M6Sort.encode_poly w5_M6Sort.decode_poly w5_M6Sort.cw_poly

variable {α : Type} [Enc α]

@[local fun_prop] theorem poly_pack {g : α → List Wd} (hg : PolyT g) : PolyT (fun x => pack (g x)) := by
  simp only [pack_eq_flat]; fun_prop

@[local fun_prop] theorem poly_encodeList_id {g : α → List Wd} (hg : PolyT g) :
    PolyT (fun x => Encoding.encodeList id (g x)) :=
  poly_pack hg

@[local fun_prop] theorem poly_unpack {g : α → Wd} (hg : PolyT g) : PolyT (fun x => unpack (g x)) := by
  suffices h : PolyT unpack from h.comp hg
  have fold : PolyT (fun x : Wd => x.foldl scan (false, false, [], [])) := by
    refine PolyT.foldl_add (g := fun _ => scan) (by fun_prop) (by fun_prop) (by unfold scan; fun_prop) ?_
    refine ⟨fun _ => 6, PB.const 6, ?_⟩
    rintro x ⟨k, j, w, ws⟩ e _
    cases k <;> cases j <;> cases e <;> simp [scan, len_pair, len_bool, len_bools, len_cons, len_nil] <;> omega
  unfold unpack; fun_prop

@[local fun_prop] theorem poly_fld {g : α → Wd} {k : α → ℕ} (hg : PolyT g) (hk : PolyT k) :
    PolyT (fun x => fld (g x) (k x)) := by
  unfold fld; fun_prop

@[local fun_prop] theorem poly_num {g : α → Wd} {k : α → ℕ} (hg : PolyT g) (hk : PolyT k) :
    PolyT (fun x => num (g x) (k x)) := by
  unfold num; fun_prop

@[local fun_prop] theorem poly_ints {g : α → Wd} (hg : PolyT g) : PolyT (fun x => ints (g x)) :=
  w5_M6Sort.decode_poly.comp hg

@[local fun_prop] theorem poly_sliceField (n : ℕ) {g : α → Wd} (hg : PolyT g) :
    PolyT (fun x => D4Slice.field n (g x)) := by
  induction n generalizing g with
  | zero => exact first_poly hg
  | succ n ih => exact ih (more_poly hg)

private theorem clog2_eq_size (n : ℕ) : Nat.clog 2 n = Nat.size (n - 1) := by
  apply le_antisymm
  · apply (Nat.clog_le_iff_le_pow (by decide)).2
    have := Nat.lt_size_self (n - 1); omega
  · apply Nat.size_le.mpr
    have := Nat.le_pow_clog (by decide : 1 < 2) n
    have : 0 < 2 ^ Nat.clog 2 n := by positivity
    omega

@[local fun_prop] theorem poly_clog2 {s : α → ℕ} (hs : PolyT s) :
    PolyT (fun x => Nat.clog 2 (s x)) := by
  simp only [clog2_eq_size]
  exact P2M_Groundwork_PolyT_size__c8c8eb1b342f (PolyT.sub hs (const 1))

@[local fun_prop] theorem poly_clog32 {s : α → ℕ} (hs : PolyT s) :
    PolyT (fun x => Nat.clog 32 (s x)) := by
  have h (n : ℕ) : Nat.clog 32 n = (Nat.clog 2 n + 4) / 5 := Nat.clog_pow_left 2 5 n
  simp only [h]
  exact PolyT.div (PolyT.add (poly_clog2 hs) (const 4)) (const 5)

@[local fun_prop] theorem poly_level {s : α → ℕ} (hs : PolyT s) :
    PolyT (fun x => D3Stopped.level (s x)) :=
  poly_clog2 hs

theorem unary_of_le_level {g h : α → ℕ} (hg : PolyT g) (hh : PolyT h)
    (hb : ∀ x, g x ≤ D3Stopped.level (h x)) : Unary g := by
  have hp : PolyT (fun x => (((h x).bits.take (g x)).map fun _ => ())) :=
    PolyT.map (f := fun _ _ => ()) (const ()) (PolyT.take hg (PolyT.bits hh))
  apply hp.congr; intro x
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, List.length_replicate]
    apply min_eq_left
    rw [Nat.size_eq_bits_len]
    exact (hb x).trans (by rw [D3Stopped.level, clog2_eq_size]; exact Nat.size_le_size (Nat.sub_le ..))
  · intros; rfl

private theorem countP_lt_eq (n k : ℕ) : (List.range n).countP (fun t => decide (t < k)) = min n k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.countP_append, ih]; by_cases h : n < k <;> simp [h] <;> omega

theorem poly_sqrt_of_unary {u : α → ℕ} (hu : PolyT u) (hU : Unary u) :
    PolyT (fun x => (u x).sqrt) := by
  have hr := PolyT.range hU
  have hpred : PolyT (fun xt : α × ℕ => decide ((xt.2 + 1) * (xt.2 + 1) ≤ u xt.1)) := by
    have ht1 : PolyT (fun xt : α × ℕ => xt.2 + 1) := PolyT.add (PolyT.snd PolyT.id') (const 1)
    exact PolyT.decide_le (PolyT.mul ht1 ht1) (hu.comp (PolyT.fst PolyT.id'))
  apply (PolyT.countP (f := fun x t => decide ((t + 1) * (t + 1) ≤ u x)) hpred hr).congr
  intro x
  simp only [← Nat.le_sqrt, Nat.succ_le_iff, countP_lt_eq, min_eq_right (Nat.sqrt_le_self _)]

@[local fun_prop] theorem poly_threshold {s : α → ℕ} (hs : PolyT s) :
    PolyT (fun x => D3Stopped.threshold (s x)) := by
  unfold D3Stopped.threshold
  have hsqrt := poly_sqrt_of_unary (poly_level hs) (unary_of_le_level (poly_level hs) hs (fun _ => le_rfl))
  exact PolyT.div (PolyT.sub (PolyT.add hs hsqrt) (const 1)) (PolyT.max' (const 1) hsqrt)

@[local fun_prop] theorem poly_width {s j : α → ℕ} (hs : PolyT s) (hj : PolyT j) :
    PolyT (fun x => D3Stopped.width (s x) (j x)) := by
  unfold D3Stopped.width; fun_prop

private theorem rangeSum_eq (n : ℕ) (f : ℕ → ℕ) : ((List.range n).map f).sum = ∑ t ∈ Finset.range n, f t := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

private theorem shift_trunc_eq (S j : ℕ) :
    D3Stopped.shift S j = 2 * (((List.range (D3Stopped.level S)).map fun t => if t ≤ j then D3Stopped.width S t else 0).sum) := by
  rw [rangeSum_eq, D3Stopped.shift]; congr 1
  calc
    _ = ∑ t ∈ Finset.range (max (j + 1) (D3Stopped.level S)), (if t ≤ j then D3Stopped.width S t else 0) := by
      symm; rw [← Finset.sum_filter]; congr 1
      ext t; simp; omega
    _ = _ := by
      symm; apply Finset.sum_subset (Finset.range_mono (le_max_right ..))
      intro t _ ht
      have ht' : D3Stopped.level S ≤ t := by simpa using ht
      have hw : D3Stopped.width S t = 0 :=
        Nat.div_eq_of_lt ((Nat.div_le_self ..).trans_lt (ht'.trans_lt (Nat.lt_pow_self (by decide : 1 < 2))))
      simp [hw]

theorem shift_le_level (S j : ℕ) : D3Stopped.shift S j ≤ D3Stopped.level S := by
  have h : D3Stopped.shift S j + 2 * D3Stopped.width S j ≤ 4 * (D3Stopped.level S / 131072) := by
    induction j with
    | zero => simp [D3Stopped.shift, D3Stopped.width]; omega
    | succ j ih =>
      have hstep : D3Stopped.shift S (j + 1) = D3Stopped.shift S j + 2 * D3Stopped.width S (j + 1) := by
        simp [D3Stopped.shift, Finset.sum_range_succ, Nat.mul_add]
      have hw : D3Stopped.width S (j + 1) = D3Stopped.width S j / 2 := by
        simp only [D3Stopped.width, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_assoc]
      omega
  omega

@[local fun_prop] theorem poly_shift {s j : α → ℕ} (hs : PolyT s) (hj : PolyT j) :
    PolyT (fun x => D3Stopped.shift (s x) (j x)) := by
  have hr := PolyT.range (unary_of_le_level (poly_level hs) hs (fun _ => le_rfl))
  simp only [shift_trunc_eq]
  have hterm : PolyT (fun xt : α × ℕ => if xt.2 ≤ j xt.1 then D3Stopped.width (s xt.1) xt.2 else 0) :=
    P2M_Groundwork_PolyT_ite__226169acf219
      (PolyT.decide_le (PolyT.snd PolyT.id') (hj.comp (PolyT.fst PolyT.id')))
      (poly_width (hs.comp (PolyT.fst PolyT.id')) (PolyT.snd PolyT.id'))
      (const 0)
  exact PolyT.mul (const 2) (PolyT.sum (PolyT.map hterm hr))

@[local fun_prop] theorem poly_two_pow_shift {s j : α → ℕ} (hs : PolyT s) (hj : PolyT j) :
    PolyT (fun x => 2 ^ D3Stopped.shift (s x) (j x)) := by
  apply PolyT.pow_unary (const 2)
  exact unary_of_le_level (poly_shift hs hj) hs (fun _ => shift_le_level _ _)

@[local fun_prop] theorem poly_64_pow_shift {s j : α → ℕ} (hs : PolyT s) (hj : PolyT j) :
    PolyT (fun x => 64 ^ D3Stopped.shift (s x) (j x)) := by
  apply PolyT.pow_unary (const 64)
  exact unary_of_le_level (poly_shift hs hj) hs (fun _ => shift_le_level _ _)

@[local fun_prop] theorem poly_64_pow_clog32 {m : α → ℕ} (hm : PolyT m) :
    PolyT (fun x => 64 ^ Nat.clog 32 (m x)) := by
  apply PolyT.pow_unary (const 64)
  apply unary_of_le_level (poly_clog32 hm) hm
  intro _
  exact Nat.clog_anti_left (by decide) (by decide : 2 ≤ 32)

@[local fun_prop] theorem poly_2_pow_clog32 {m : α → ℕ} (hm : PolyT m) :
    PolyT (fun x => 2 ^ Nat.clog 32 (m x)) := by
  apply PolyT.pow_unary (const 2)
  apply unary_of_le_level (poly_clog32 hm) hm
  intro _
  exact Nat.clog_anti_left (by decide) (by decide : 2 ≤ 32)

@[local fun_prop] theorem poly_totalGuard {s m : α → ℕ} (hs : PolyT s) (hm : PolyT m) :
    PolyT (fun x => D4GuardTree.totalGuard (s x) (Nat.clog 32 (m x))) := by
  unfold D4GuardTree.totalGuard D4GuardTree.localAllowance
  have hD := poly_clog32 hm
  have hsh := poly_shift hs hD
  have hp2 := poly_two_pow_shift hs hD
  have hp64 := poly_64_pow_clog32 hm
  exact PolyT.mul
    (PolyT.mul (PolyT.mul (PolyT.mul (const 40) (PolyT.add hs (const 1))) (PolyT.add hsh (const 1))) hp2)
    hp64

@[local fun_prop] theorem poly_unrollBudget (K_mode : ℕ) {s m : α → ℕ} (hs : PolyT s) (hm : PolyT m) :
    PolyT (fun x => D4UnrollBudget.budget (s x) (Nat.clog 32 (m x)) K_mode) := by
  unfold D4UnrollBudget.budget
  have hD := poly_clog32 hm
  have hw_le : ∀ x, D3Stopped.width (s x) (Nat.clog 32 (m x)) ≤ D3Stopped.level (s x) :=
    fun _ => (Nat.div_le_self ..).trans (Nat.div_le_self ..)
  have hw_sqrt := poly_sqrt_of_unary (poly_width hs hD)
    (unary_of_le_level (poly_width hs hD) hs hw_le)
  have h1 : PolyT (fun x => 8 * (D3Stopped.level (s x) + 1) * 64 ^ Nat.clog 32 (m x)) :=
    PolyT.mul (PolyT.mul (const 8) (PolyT.add (poly_level hs) (const 1))) (poly_64_pow_clog32 hm)
  have h2 : PolyT (fun x => (2 * K_mode * (2 ^ Nat.clog 32 (m x) - 1) * s x) /
      max 1 (D3Stopped.width (s x) (Nat.clog 32 (m x))).sqrt) :=
    PolyT.div
      (PolyT.mul (PolyT.mul (const (2 * K_mode)) (PolyT.sub (poly_2_pow_clog32 hm) (const 1))) hs)
      (PolyT.max' (const 1) hw_sqrt)
  exact PolyT.add h1 h2

@[local fun_prop] theorem poly_range_list_len {β : Type} [Enc β] {w : α → List β} (hw : PolyT w) :
    PolyT (fun x => List.range (w x).length) :=
  PolyT.range (Unary.of_length hw)

def baseUnits (A : ℕ) (w : Wd) : List Unit :=
  (List.range (A + 1)).flatMap fun _ => () :: (w.map fun _ => ())

def sqUnits : ℕ → List Unit → List Unit
  | 0, xs => xs
  | k + 1, xs => (sqUnits k xs).flatMap fun _ => sqUnits k xs

def polyUnits (A : ℕ) (w : Wd) : List Unit :=
  sqUnits 4 (baseUnits A w)

theorem baseUnits_length (A : ℕ) (w : Wd) :
    (baseUnits A w).length = (A + 1) * (w.length + 1) := by
  simp [baseUnits, List.length_flatMap]

theorem sqUnits_length (k : ℕ) (xs : List Unit) :
    (sqUnits k xs).length = xs.length ^ (2 ^ k) := by
  induction k with
  | zero => simp [sqUnits]
  | succ k ih => simp [sqUnits, List.length_flatMap, ih, pow_succ, pow_mul]

theorem polyUnits_length (A : ℕ) (w : Wd) :
    (polyUnits A w).length = ((A + 1) * (w.length + 1)) ^ 16 := by
  rw [polyUnits, sqUnits_length, baseUnits_length]; rfl

@[local fun_prop] theorem poly_baseUnits (A : ℕ) {g : α → Wd} (hg : PolyT g) :
    PolyT (fun x => baseUnits A (g x)) := by
  unfold baseUnits; fun_prop

theorem poly_sqUnits (k : ℕ) {g : α → List Unit} (hg : PolyT g) :
    PolyT (fun x => sqUnits k (g x)) := by
  induction k with
  | zero => exact hg
  | succ k ih =>
    unfold sqUnits
    exact PolyT.flatMap (f := fun (x : α) (_ : Unit) => sqUnits k (g x))
      (ih.comp (PolyT.fst PolyT.id')) ih

@[local fun_prop] theorem poly_polyUnits (A : ℕ) {g : α → Wd} (hg : PolyT g) :
    PolyT (fun x => polyUnits A (g x)) :=
  poly_sqUnits 4 (poly_baseUnits A hg)

def unaryFuelRep (fuel : List Unit) (n : ℕ) (b : Bool) : Wd :=
  (fuel.take n).map fun _ => b

def rangeFuel (fuel : List Unit) (n : ℕ) : List ℕ :=
  List.range (fuel.take n).length

theorem unaryFuelRep_eq (fuel : List Unit) (n : ℕ) (b : Bool) (hle : n ≤ fuel.length) :
    unaryFuelRep fuel n b = List.replicate n b := by
  unfold unaryFuelRep
  apply List.ext_getElem
  · simp [min_eq_left hle]
  · simp

theorem rangeFuel_eq (fuel : List Unit) (n : ℕ) (hle : n ≤ fuel.length) :
    rangeFuel fuel n = List.range n := by
  unfold rangeFuel
  rw [List.length_take, min_eq_left hle]

@[local fun_prop] theorem poly_unaryFuelRep {f : α → List Unit} {n : α → ℕ} (b : Bool)
    (hf : PolyT f) (hn : PolyT n) : PolyT (fun x => unaryFuelRep (f x) (n x) b) := by
  unfold unaryFuelRep; fun_prop

@[local fun_prop] theorem poly_rangeFuel {f : α → List Unit} {n : α → ℕ}
    (hf : PolyT f) (hn : PolyT n) : PolyT (fun x => rangeFuel (f x) (n x)) := by
  unfold rangeFuel; fun_prop

end PolyTPrimitives

section RawPipelines

attribute [local fun_prop] PolyT.const PolyT.fst PolyT.snd PolyT.prodMk PolyT.comp PolyT.id'
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_cons__3a60f43a3b86
  P2M_Groundwork_PolyT_cond__4c673073da15 P2M_Groundwork_PolyT_ite__226169acf219
  P2M_Groundwork_PolyT_size__c8c8eb1b342f
  PolyT.div PolyT.mod PolyT.mul PolyT.add PolyT.sub
  PolyT.div_pow PolyT.map PolyT.flatMap PolyT.filter PolyT.countP PolyT.sum
  PolyT.length PolyT.reverse PolyT.append PolyT.take PolyT.drop PolyT.getD
  PolyT.headD PolyT.tail PolyT.isEmpty PolyT.idxOf PolyT.any
  PolyT.decide_eq PolyT.decide_le PolyT.decide_lt PolyT.and' PolyT.or' PolyT.not'
  first_poly more_poly frame_poly w5_M6Sort.encode_poly w5_M6Sort.decode_poly w5_M6Sort.cw_poly
  poly_pack poly_encodeList_id poly_unpack poly_fld poly_num poly_ints poly_sliceField
  poly_clog2 poly_clog32 poly_level poly_threshold poly_width poly_shift
  poly_two_pow_shift poly_64_pow_shift poly_64_pow_clog32 poly_2_pow_clog32
  poly_totalGuard poly_unrollBudget poly_range_list_len poly_polyUnits
  poly_unaryFuelRep poly_rangeFuel

def permutePktQuery (w : Wd) : Wd :=
  let pktDesc := fld w 0
  let betaBits := fld w 1
  let rawDesc := fld pktDesc 0
  let permBits := fld pktDesc 1
  let alphaBits := if permBits.isEmpty then betaBits
    else (ints permBits).map (fun j => betaBits.getD j false)
  pack [rawDesc, alphaBits]

theorem permutePktQuery_poly : PolyT permutePktQuery := by
  unfold permutePktQuery; fun_prop

def pow2Level4 (S : ℕ) : ℕ :=
  let t := 2 ^ D3Stopped.level S
  (t * t) * (t * t)

@[local fun_prop] theorem poly_pow2Level4 {α : Type} [Enc α] {s : α → ℕ} (hs : PolyT s) :
    PolyT (fun x => pow2Level4 (s x)) := by
  unfold pow2Level4
  have hp : PolyT (fun x => 2 ^ D3Stopped.level (s x)) :=
    PolyT.pow_unary (const 2) (unary_of_le_level (poly_level hs) hs (fun _ => le_rfl))
  exact PolyT.mul (PolyT.mul hp hp) (PolyT.mul hp hp)

def modInput (A : ℕ) (inp : Wd) : Wd :=
  let S := bval (D4Slice.field 5 inp)
  let fuel := polyUnits A inp
  unaryFuelRep fuel (4 * D3Stopped.level S) true ++ unaryFuelRep fuel (pow2Level4 S) false

@[local fun_prop] theorem poly_modInput (A : ℕ) {α : Type} [Enc α] {g : α → Wd} (hg : PolyT g) :
    PolyT (fun x => modInput A (g x)) := by
  unfold modInput; fun_prop

def fBitsRaw (A : ℕ) (inp : Wd) : Wd :=
  let m := modInput A inp
  ((DetDLP_M13A_IrredHermite.irredMachine m).reverse).take ((m.filter id).length)

@[local fun_prop] theorem poly_fBitsRaw (A : ℕ) {α : Type} [Enc α] {g : α → Wd} (hg : PolyT g) :
    PolyT (fun x => fBitsRaw A (g x)) := by
  unfold fBitsRaw
  have hm := poly_modInput A hg
  have hirr := m13a_irred_poly_machine.1.comp hm
  have hflt : PolyT (fun x => (modInput A (g x)).filter id) :=
    PolyT.filter (f := fun (_ : α) (b : Bool) => b) (PolyT.snd PolyT.id') hm
  exact PolyT.take (PolyT.length hflt) (PolyT.reverse hirr)

def rootOrigDeg (pinId : ℕ) (incl : List ℕ) : ℕ :=
  incl.length + if pinId = 0 then 0 else 1

@[local fun_prop] theorem poly_rootOrigDeg {α : Type} [Enc α] {p : α → ℕ} {i : α → List ℕ}
    (hp : PolyT p) (hi : PolyT i) : PolyT (fun x => rootOrigDeg (p x) (i x)) := by
  unfold rootOrigDeg; fun_prop

def rootRList (pinId : ℕ) (incl : List ℕ) : List ℕ :=
  (List.range ((() :: (incl.map fun _ => ())).length)).take (rootOrigDeg pinId incl)

@[local fun_prop] theorem poly_rootRList {α : Type} [Enc α] {p : α → ℕ} {i : α → List ℕ}
    (hp : PolyT p) (hi : PolyT i) : PolyT (fun x => rootRList (p x) (i x)) := by
  unfold rootRList; fun_prop

def rootPinPortPlus1 (pinId : ℕ) (incl : List ℕ) : ℕ :=
  let matches_ := (rootRList pinId incl).filter (fun r => !(incl.any (fun y => decide (y = r))))
  if matches_.isEmpty then 0 else matches_.headD 0 + 1

@[local fun_prop] theorem poly_rootPinPortPlus1 {α : Type} [Enc α] {p : α → ℕ} {i : α → List ℕ}
    (hp : PolyT p) (hi : PolyT i) : PolyT (fun x => rootPinPortPlus1 (p x) (i x)) := by
  unfold rootPinPortPlus1; fun_prop

def rootVSpecAt (origVs pinIds : List ℕ) (incls : List Wd) (vIdx : ℕ) : Wd :=
  let origV := origVs.getD vIdx 0
  let pinId := pinIds.getD vIdx 0
  let incl := ints (incls.getD vIdx [])
  let origDeg := rootOrigDeg pinId incl
  let pinPortPlus1 := rootPinPortPlus1 pinId incl
  let portMap := (rootRList pinId incl).map (fun r => incl.idxOf r)
  pack [[false], encodeNatListBin [origV, origDeg, pinPortPlus1], encodeNatListBin portMap]

@[local fun_prop] theorem poly_rootVSpecAt {α : Type} [Enc α]
    {ov pi : α → List ℕ} {inc : α → List Wd} {v : α → ℕ}
    (hov : PolyT ov) (hpi : PolyT pi) (hinc : PolyT inc) (hv : PolyT v) :
    PolyT (fun x => rootVSpecAt (ov x) (pi x) (inc x) (v x)) := by
  unfold rootVSpecAt; fun_prop

def rootRaw (cutW : Wd) (p : ℕ) : Wd :=
  let h0Enc := fld cutW 0
  let hosts := ints (fld cutW 1)
  let origVs := ints (fld cutW 2)
  let pinIds := ints (fld cutW 4)
  let incls := unpack (fld cutW 5)
  let pinsBits := pack ((List.range hosts.length).map fun bi => encodeNatListBin [bi, hosts.getD bi 0])
  let vSpecsBits := pack ((List.range origVs.length).map (rootVSpecAt origVs pinIds incls))
  pack [countWord 0, h0Enc, countWord p, pinsBits, vSpecsBits]

@[local fun_prop] theorem poly_rootRaw {α : Type} [Enc α] {c : α → Wd} {p : α → ℕ}
    (hc : PolyT c) (hp : PolyT p) : PolyT (fun x => rootRaw (c x) (p x)) := by
  unfold rootRaw; fun_prop

def rowRaw (fuel : List Unit) (S d : ℕ) : Wd :=
  let a := D3Stopped.shift S d
  let u := D3Stopped.width S d
  pack [countWord a, countWord u, unaryFuelRep fuel (64 ^ a) true]

@[local fun_prop] theorem poly_rowRaw {α : Type} [Enc α] {f : α → List Unit} {s d : α → ℕ}
    (hf : PolyT f) (hs : PolyT s) (hd : PolyT d) : PolyT (fun x => rowRaw (f x) (s x) (d x)) := by
  unfold rowRaw
  have ha := poly_shift hs hd
  have hu := poly_width hs hd
  have hp64 := poly_64_pow_shift hs hd
  exact poly_pack (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (w5_M6Sort.cw_poly ha)
    (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (w5_M6Sort.cw_poly hu)
      (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (poly_unaryFuelRep true hf hp64) (const []))))

def ctxRaw (fuel : List Unit) (S m p guard l : ℕ) (fBits : Wd) : Wd :=
  let D := Nat.clog 32 (4 * m)
  let rows := (rangeFuel fuel D).map (rowRaw fuel S)
  pack [countWord D, countWord (D3Stopped.threshold S), unaryFuelRep fuel (guard + p) true,
    unaryFuelRep fuel l true, fBits, pack rows, countWord guard]

@[local fun_prop] theorem poly_ctxRaw {α : Type} [Enc α]
    {fl : α → List Unit} {s m p g l : α → ℕ} {fb : α → Wd}
    (hfl : PolyT fl) (hs : PolyT s) (hm : PolyT m) (hp : PolyT p) (hg : PolyT g)
    (hl : PolyT l) (hfb : PolyT fb) :
    PolyT (fun x => ctxRaw (fl x) (s x) (m x) (p x) (g x) (l x) (fb x)) := by
  unfold ctxRaw
  have hD : PolyT (fun x => Nat.clog 32 (4 * m x)) := poly_clog32 (PolyT.mul (const 4) hm)
  have hrows : PolyT (fun x => (rangeFuel (fl x) (Nat.clog 32 (4 * m x))).map (rowRaw (fl x) (s x))) :=
    PolyT.map (poly_rowRaw (hfl.comp (PolyT.fst PolyT.id')) (hs.comp (PolyT.fst PolyT.id')) (PolyT.snd PolyT.id'))
      (poly_rangeFuel hfl hD)
  exact poly_pack (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (w5_M6Sort.cw_poly hD)
    (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (w5_M6Sort.cw_poly (poly_threshold hs))
      (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (poly_unaryFuelRep true hfl (PolyT.add hg hp))
        (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (poly_unaryFuelRep true hfl hl)
          (P2M_Groundwork_PolyT_cons__3a60f43a3b86 hfb
            (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (poly_pack hrows)
              (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (w5_M6Sort.cw_poly hg) (const []))))))))

def oneWordFuel (fuel : List Unit) (n : ℕ) : Wd :=
  encodeNatListBin ((rangeFuel fuel n).map fun idx => if idx = 0 then 1 else 0)

@[local fun_prop] theorem poly_oneWordFuel {α : Type} [Enc α] {fl : α → List Unit} {n : α → ℕ}
    (hfl : PolyT fl) (hn : PolyT n) : PolyT (fun x => oneWordFuel (fl x) (n x)) := by
  unfold oneWordFuel; fun_prop

def preWalkGen (cutFn : Wd → Wd) (A K_mode : ℕ) (q : Wd) : Wd :=
  let inp := fld q 0
  let j := num q 1
  let m := bval (D4Slice.field 3 inp)
  let S := bval (D4Slice.field 5 inp)
  let p := bval (D4Slice.field 6 inp)
  let l := bval (D4Slice.field 7 inp)
  let guard := D4GuardTree.totalGuard S (Nat.clog 32 (4 * m))
  let B := D4UnrollBudget.budget S (Nat.clog 32 (4 * m)) K_mode
  let fBits := fBitsRaw A inp
  let cutW := cutFn inp
  let fuel := polyUnits A q
  let ctx := ctxRaw fuel S m p guard l fBits
  let uRank := if j = 0 then 0 else j - 1
  pack [[], ctx, pack [rootRaw cutW p], pack [], countWord B, countWord uRank,
    oneWordFuel fuel (l * fBits.length), countWord 0]

theorem preWalkGen_poly {cutFn : Wd → Wd} (hcut : PolyT cutFn) (A K_mode : ℕ) :
    PolyT (preWalkGen cutFn A K_mode) := by
  unfold preWalkGen
  have hinp : PolyT (fun q : Wd => fld q 0) := poly_fld PolyT.id' (const 0)
  have hm : PolyT (fun q : Wd => bval (D4Slice.field 3 (fld q 0))) := by fun_prop
  have hS : PolyT (fun q : Wd => bval (D4Slice.field 5 (fld q 0))) := by fun_prop
  have hp : PolyT (fun q : Wd => bval (D4Slice.field 6 (fld q 0))) := by fun_prop
  have hl : PolyT (fun q : Wd => bval (D4Slice.field 7 (fld q 0))) := by fun_prop
  have hguard := poly_totalGuard hS (PolyT.mul (const 4) hm)
  have hB := poly_unrollBudget K_mode hS (PolyT.mul (const 4) hm)
  have hfBits := poly_fBitsRaw A hinp
  have hcut' := hcut.comp hinp
  have hfuel := poly_polyUnits A PolyT.id'
  have hctx := poly_ctxRaw hfuel hS hm hp hguard hl hfBits
  have huRank : PolyT (fun q : Wd => if num q 1 = 0 then 0 else num q 1 - 1) := by fun_prop
  exact poly_pack (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (const [])
    (P2M_Groundwork_PolyT_cons__3a60f43a3b86 hctx
      (P2M_Groundwork_PolyT_cons__3a60f43a3b86
        (poly_pack (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (poly_rootRaw hcut' hp) (const [])))
        (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (const (pack []))
          (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (w5_M6Sort.cw_poly hB)
            (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (w5_M6Sort.cw_poly huRank)
              (P2M_Groundwork_PolyT_cons__3a60f43a3b86
                (poly_oneWordFuel hfuel (PolyT.mul hl (PolyT.length hfBits)))
                (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (const (countWord 0)) (const [])))))))))

def findPinPos (pins : List Wd) (wIdx : ℕ) : ℕ :=
  ((List.range pins.length).filter (fun idx =>
    decide ((ints (pins.getD idx [])).getD 1 0 = wIdx))).headD pins.length

@[local fun_prop] theorem poly_findPinPos {α : Type} [Enc α] {ps : α → List Wd} {w : α → ℕ}
    (hps : PolyT ps) (hw : PolyT w) : PolyT (fun x => findPinPos (ps x) (w x)) := by
  unfold findPinPos; fun_prop

def convertVertexRaw (fuel : List Unit) (pins vSpecs : List Wd) (wIdx : ℕ) : Wd :=
  let sp := vSpecs.getD wIdx []
  if (fld sp 0).headD false then
    let rawDesc := fld sp 1
    let permBits := if (unpack sp).length < 3 then [] else fld sp 2
    true :: pack [rawDesc, permBits]
  else
    let meta_ := ints (fld sp 1)
    let origV := meta_.getD 0 0
    let origDeg := meta_.getD 1 0
    let pinPortPlus1 := meta_.getD 2 0
    let pinPos := findPinPos pins wIdx
    let portMap := ints (fld sp 2)
    let routed := (rangeFuel fuel origDeg).map fun r =>
      let tagB := decide (pinPortPlus1 = r + 1)
      let posN := if tagB then pinPos else portMap.getD r 0
      tagB :: countWord posN
    false :: pack [countWord origV, pack routed]

@[local fun_prop] theorem poly_convertVertexRaw {α : Type} [Enc α]
    {fl : α → List Unit} {ps vs : α → List Wd} {w : α → ℕ}
    (hfl : PolyT fl) (hps : PolyT ps) (hvs : PolyT vs) (hw : PolyT w) :
    PolyT (fun x => convertVertexRaw (fl x) (ps x) (vs x) (w x)) := by
  unfold convertVertexRaw; fun_prop

def stoppedItemDescRaw (fuel : List Unit) (origDesc fBits : Wd) (S l : ℕ) (item : Wd) : Wd :=
  let d₀ := num item 0
  let gEnc := fld item 1
  let pStop := num item 2
  let pins := unpack (fld item 3)
  let vSpecs := unpack (fld item 4)
  let converted := (List.range vSpecs.length).map (convertVertexRaw fuel pins vSpecs)
  true :: pack [countWord S, countWord l, countWord pStop, gEnc,
    pack [countWord d₀, fBits, pack [origDesc, pack converted]]]

@[local fun_prop] theorem poly_stoppedItemDescRaw {α : Type} [Enc α]
    {fl : α → List Unit} {od fb : α → Wd} {s l : α → ℕ} {it : α → Wd}
    (hfl : PolyT fl) (hod : PolyT od) (hfb : PolyT fb) (hs : PolyT s) (hl : PolyT l) (hit : PolyT it) :
    PolyT (fun x => stoppedItemDescRaw (fl x) (od x) (fb x) (s x) (l x) (it x)) := by
  unfold stoppedItemDescRaw; fun_prop

def findBoundaryLeaf (doneList : List Wd) (bi : ℕ) : ℕ :=
  ((List.range doneList.length).filter (fun idx =>
    (unpack (fld (doneList.getD idx []) 3)).any
      (fun pin => decide ((ints pin).getD 0 0 = bi)))).headD doneList.length

@[local fun_prop] theorem poly_findBoundaryLeaf {α : Type} [Enc α] {dl : α → List Wd} {b : α → ℕ}
    (hdl : PolyT dl) (hb : PolyT b) : PolyT (fun x => findBoundaryLeaf (dl x) (b x)) := by
  unfold findBoundaryLeaf; fun_prop

def lookupDescsRaw (origDesc mask : Wd) (degF l qPrec : ℕ) : List Wd :=
  ((List.range mask.length).filter (fun v => mask.getD v false)).map fun origV =>
    false :: pack [origDesc, countWord origV, countWord degF, countWord l, countWord qPrec]

@[local fun_prop] theorem poly_lookupDescsRaw {α : Type} [Enc α]
    {od mk : α → Wd} {df l qp : α → ℕ}
    (hod : PolyT od) (hmk : PolyT mk) (hdf : PolyT df) (hl : PolyT l) (hqp : PolyT qp) :
    PolyT (fun x => lookupDescsRaw (od x) (mk x) (df x) (l x) (qp x)) := by
  unfold lookupDescsRaw; fun_prop

def hitBranchRaw (reattachFn : Wd → Wd) (fuel : List Unit) (inp origDesc mask fBits walkerTail : Wd)
    (m k S l qPrec : ℕ) : Wd :=
  let finalWt := fld walkerTail 0
  let doneList := unpack (fld walkerTail 1)
  let leafOfBoundary := (rangeFuel fuel (4 * m * k)).map (findBoundaryLeaf doneList)
  let R_enc := reattachFn
    (pack [inp, doneList.map (fun _ => true), encodeNatListBin leafOfBoundary])
  let lDescs := lookupDescsRaw origDesc mask fBits.length l qPrec
  let sDescs := doneList.map (stoppedItemDescRaw fuel origDesc fBits S l)
  pack [R_enc, finalWt, pack (lDescs ++ sDescs)]

theorem poly_hitBranchRaw {reattachFn : Wd → Wd} (hre_fn : PolyT reattachFn)
    {α : Type} [Enc α]
    {fl : α → List Unit} {ip od mk fb wt : α → Wd} {m k s l qp : α → ℕ}
    (hfl : PolyT fl) (hip : PolyT ip) (hod : PolyT od) (hmk : PolyT mk)
    (hfb : PolyT fb) (hwt : PolyT wt) (hm : PolyT m) (hk : PolyT k)
    (hs : PolyT s) (hl : PolyT l) (hqp : PolyT qp) :
    PolyT (fun x => hitBranchRaw reattachFn (fl x) (ip x) (od x) (mk x) (fb x) (wt x)
      (m x) (k x) (s x) (l x) (qp x)) := by
  unfold hitBranchRaw
  have hre := hre_fn.comp (by fun_prop : PolyT (fun x =>
    pack [ip x, (unpack (fld (wt x) 1)).map (fun _ => true),
      encodeNatListBin ((rangeFuel (fl x) (4 * m x * k x)).map
        (findBoundaryLeaf (unpack (fld (wt x) 1))))]))
  exact poly_pack (P2M_Groundwork_PolyT_cons__3a60f43a3b86 hre
    (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (by fun_prop)
      (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (by fun_prop) (const []))))

def emptyGraphConst : AppendixD4.Graph :=
  ⟨0, 0, Fin.elim0, Fin.elim0, fun e => Fin.elim0 e⟩

def emptyStoppedDescRaw (origDesc fBits : Wd) (S p l : ℕ) : Wd :=
  true :: pack [countWord S, countWord l, countWord p, emptyGraphConst.encode,
    pack [countWord 0, fBits, pack [origDesc, pack []]]]

@[local fun_prop] theorem poly_emptyStoppedDescRaw {α : Type} [Enc α]
    {od fb : α → Wd} {s p l : α → ℕ}
    (hod : PolyT od) (hfb : PolyT fb) (hs : PolyT s) (hp : PolyT p) (hl : PolyT l) :
    PolyT (fun x => emptyStoppedDescRaw (od x) (fb x) (s x) (p x) (l x)) := by
  unfold emptyStoppedDescRaw; fun_prop

def missBranchRaw (reattachFn : Wd → Wd) (fuel : List Unit) (inp origDesc mask fBits : Wd)
    (m k S p l qPrec : ℕ) : Wd :=
  let m4Range := rangeFuel fuel (4 * m)
  let bRange := rangeFuel fuel (4 * m * k)
  let R_enc := reattachFn
    (pack [inp, m4Range.map (fun _ => true), encodeNatListBin (bRange.map (· / k))])
  let zeroWt := encodeNatListBin ((rangeFuel fuel (l * fBits.length)).map fun _ => 0)
  let lDescs := lookupDescsRaw origDesc mask fBits.length l qPrec
  let sDescs := m4Range.map (fun _ => emptyStoppedDescRaw origDesc fBits S p l)
  pack [R_enc, zeroWt, pack (lDescs ++ sDescs)]

theorem poly_missBranchRaw {reattachFn : Wd → Wd} (hre_fn : PolyT reattachFn)
    {α : Type} [Enc α]
    {fl : α → List Unit} {ip od mk fb : α → Wd} {m k s p l qp : α → ℕ}
    (hfl : PolyT fl) (hip : PolyT ip) (hod : PolyT od) (hmk : PolyT mk)
    (hfb : PolyT fb) (hm : PolyT m) (hk : PolyT k)
    (hs : PolyT s) (hp : PolyT p) (hl : PolyT l) (hqp : PolyT qp) :
    PolyT (fun x => missBranchRaw reattachFn (fl x) (ip x) (od x) (mk x) (fb x)
      (m x) (k x) (s x) (p x) (l x) (qp x)) := by
  unfold missBranchRaw
  have hre := hre_fn.comp (by fun_prop : PolyT (fun x =>
    pack [ip x, (rangeFuel (fl x) (4 * m x)).map (fun _ => true),
      encodeNatListBin ((rangeFuel (fl x) (4 * m x * k x)).map (· / k x))]))
  exact poly_pack (P2M_Groundwork_PolyT_cons__3a60f43a3b86 hre
    (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (by fun_prop)
      (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (by fun_prop) (const []))))

def postWalkGen (reattachFn : Wd → Wd) (A K_mode : ℕ) (pairQW : Wd) : Wd :=
  let q := fld pairQW 0
  let walkerOut := fld pairQW 1
  let inp := fld q 0
  let j := num q 1
  let origDesc := D4Slice.field 0 inp
  let m := bval (D4Slice.field 3 inp)
  let k := bval (D4Slice.field 4 inp)
  let S := bval (D4Slice.field 5 inp)
  let p := bval (D4Slice.field 6 inp)
  let l := bval (D4Slice.field 7 inp)
  let mask := D4Slice.field 8 inp
  let guard := D4GuardTree.totalGuard S (Nat.clog 32 (4 * m))
  let qPrec := guard + p
  let B := D4UnrollBudget.budget S (Nat.clog 32 (4 * m)) K_mode
  let fBits := fBitsRaw A inp
  let fuel := polyUnits A pairQW
  if j = 0 then
    pack [unaryFuelRep fuel B false ++ [true], countWord guard, fBits]
  else if walkerOut.headD false then
    hitBranchRaw reattachFn fuel inp origDesc mask fBits walkerOut.tail m k S l qPrec
  else
    missBranchRaw reattachFn fuel inp origDesc mask fBits m k S p l qPrec

theorem postWalkGen_poly {reattachFn : Wd → Wd} (hre_fn : PolyT reattachFn) (A K_mode : ℕ) :
    PolyT (postWalkGen reattachFn A K_mode) := by
  unfold postWalkGen
  have hq : PolyT (fun w : Wd => fld w 0) := poly_fld PolyT.id' (const 0)
  have hwo : PolyT (fun w : Wd => fld w 1) := poly_fld PolyT.id' (const 1)
  have hinp : PolyT (fun w : Wd => fld (fld w 0) 0) := poly_fld hq (const 0)
  have hj : PolyT (fun w : Wd => num (fld w 0) 1) := poly_num hq (const 1)
  have hod : PolyT (fun w : Wd => D4Slice.field 0 (fld (fld w 0) 0)) := poly_sliceField 0 hinp
  have hm : PolyT (fun w : Wd => bval (D4Slice.field 3 (fld (fld w 0) 0))) := by fun_prop
  have hk : PolyT (fun w : Wd => bval (D4Slice.field 4 (fld (fld w 0) 0))) := by fun_prop
  have hS : PolyT (fun w : Wd => bval (D4Slice.field 5 (fld (fld w 0) 0))) := by fun_prop
  have hp : PolyT (fun w : Wd => bval (D4Slice.field 6 (fld (fld w 0) 0))) := by fun_prop
  have hl : PolyT (fun w : Wd => bval (D4Slice.field 7 (fld (fld w 0) 0))) := by fun_prop
  have hmk : PolyT (fun w : Wd => D4Slice.field 8 (fld (fld w 0) 0)) := poly_sliceField 8 hinp
  have hguard := poly_totalGuard hS (PolyT.mul (const 4) hm)
  have hqp := PolyT.add hguard hp
  have hB := poly_unrollBudget K_mode hS (PolyT.mul (const 4) hm)
  have hfBits := poly_fBitsRaw A hinp
  have hfuel := poly_polyUnits A PolyT.id'
  apply P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_eq hj (const 0))
  · exact poly_pack (P2M_Groundwork_PolyT_cons__3a60f43a3b86
      (PolyT.append (poly_unaryFuelRep false hfuel hB) (const [true]))
      (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (w5_M6Sort.cw_poly hguard)
        (P2M_Groundwork_PolyT_cons__3a60f43a3b86 hfBits (const []))))
  · apply P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_eq (PolyT.headD hwo (const false)) (const true))
    · exact poly_hitBranchRaw hre_fn hfuel hinp hod hmk hfBits (PolyT.tail hwo) hm hk hS hl hqp
    · exact poly_missBranchRaw hre_fn hfuel hinp hod hmk hfBits hm hk hS hp hl hqp

end RawPipelines

end DetDLP.D4SoloRaw


