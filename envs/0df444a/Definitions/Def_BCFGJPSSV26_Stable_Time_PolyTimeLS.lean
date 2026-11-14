-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeLS
-- name    : BCFGJPSSV26_Stable_Time_PolyTimeLS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:19:09.714106+00:00
-- url     : https://prove2.me/theorems/9504cd9a-d554-4b32-aeea-536adcbafd53
-- title:
--   BCFGJPSSV26.Stable.Time.PolyTimeLS — The local search runs in polynomial time
-- statement:
--   This is module `BCFGJPSSV26.Stable.Time.PolyTimeLS` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   `BCFGJPSSV26.Stable.localSearch_polytime`: the local search is polynomial-time in
--   `(N, I, B)` with `N` and `B` in unary, one certificate for all `N`. It makes at most `B` steps,
--   each trying at most `B` tuples (`Tuples.tuples`, cut at `B`, `Tuples.tuples_polytime`) and
--   computing exact costs (`BCFGJPSSV26.Combine.costQ_polytime`); the lists keep length `k` with
--   entries below `k + B`.
--
--   The output has `k` entries, and `k` is written in binary, so the certificate is for the tuples
--   with `k` at most the number of rows of the table (`n + m` for an instance), and the empty list
--   otherwise.
--
--   **Part I** uses the local search with the fixed `N = 201` and the budget `(|x| + 2)^(2 p + 2)`:
--   compose `BCFGJPSSV26.Stable.localSearch_polytime` with `x ↦ (201, x, (|x| + 2)^(2 p + 2))`
--   (`Turing.MultiTapeTM.ComputableInPolyTime.encoding_length` and `unary_pow`), on the tuples with
--   `k` at most the number of rows (`BCFGJPSSV26.Stable.localSearch_polytime'`).
--
--   **Contents.** The module is published as a whole: 21 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeLS`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Time/PolyTimeLS.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_LocalSearch
public import Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeRaw
public import Definitions.Def_BuhaiPapers_Background_TuplesPolyTime
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryDiv
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Membership

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Time.PolyTimeLS` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The local search runs in polynomial time

`BCFGJPSSV26.Stable.localSearch_polytime`: the local search is polynomial-time in
`(N, I, B)` with `N` and `B` in unary, one certificate for all `N`. It makes at most `B` steps,
each trying at most `B` tuples (`Tuples.tuples`, cut at `B`, `Tuples.tuples_polytime`) and
computing exact costs (`BCFGJPSSV26.Combine.costQ_polytime`); the lists keep length `k` with
entries below `k + B`.

The output has `k` entries, and `k` is written in binary, so the certificate is for the tuples
with `k` at most the number of rows of the table (`n + m` for an instance), and the empty list
otherwise.

**Part I** uses the local search with the fixed `N = 201` and the budget `(|x| + 2)^(2 p + 2)`:
compose `BCFGJPSSV26.Stable.localSearch_polytime` with `x ↦ (201, x, (|x| + 2)^(2 p + 2))`
(`Turing.MultiTapeTM.ComputableInPolyTime.encoding_length` and `unary_pow`), on the tuples with
`k` at most the number of rows (`BCFGJPSSV26.Stable.localSearch_polytime'`).
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

namespace PolyTime

variable {α : Type} {input : α ↪ List Bool}

/-! ### Arithmetic and lists -/

theorem binMod' {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ f a % g a) input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_mod' hf.tidy hg.tidy)

theorem binDiv' {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ f a / g a) input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_div' hf.tidy hg.tidy)

theorem length_encNat_le (a : ℕ) : (encNat a).length ≤ a := by
  rw [encNat_apply, Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

theorem length_encNat_mono {a b : ℕ} (h : a ≤ b) : (encNat a).length ≤ (encNat b).length := by
  rw [encNat_apply, encNat_apply, Nat.size_eq_bits_len, Nat.size_eq_bits_len]
  exact Nat.size_le_size h

theorem set_eq_map_zipIdx (l : List ℕ) (i v : ℕ) :
    l.set i v = l.zipIdx.map fun p ↦ if p.2 = i then v else p.1 := by
  refine List.ext_getElem (by simp) fun j h₁ h₂ ↦ ?_
  simp only [List.getElem_set, List.getElem_map, List.getElem_zipIdx, zero_add]
  by_cases hj : j = i
  · subst hj
    simp
  · rw [if_neg (Ne.symm hj), if_neg hj]

/-- Setting an entry of a list of numbers. -/
theorem listSet' {l : α → List ℕ} {i v : α → ℕ} (hl : ComputableInPolyTime l input (encList encNat))
    (hi : ComputableInPolyTime i input encNat) (hv : ComputableInPolyTime v input encNat) :
    ComputableInPolyTime (fun a ↦ (l a).set (i a) (v a)) input (encList encNat) := by
  simp only [set_eq_map_zipIdx]
  have hz : ComputableInPolyTime (fun a ↦ (l a).zipIdx) input
      (encList (encPair encNat encUnary)) :=
    .of_tidy ((ComputableTidilyInPolyTime.zipIdx encNat).comp hl.tidy)
  exact mapWithInput (f := fun a (p : ℕ × ℕ) ↦ if p.2 = i a then v a else p.1) hz
    (ite_decide (decide_eq' (unary_to_binary.comp ((snd _ _).comp (snd _ _))) (hi.comp (fst _ _)))
      (hv.comp (fst _ _)) ((fst _ _).comp (snd _ _)))

theorem length_encList_set_le {β : Type} (e : β ↪ List Bool) (l : List β) (i : ℕ) (v : β) :
    (encList e (l.set i v)).length ≤ (encList e l).length + (2 * (e v).length + 1) := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, length_encList, List.map_cons, List.sum_cons]
      omega
    | succ i =>
      have := ih i
      simp only [List.set_cons_succ, length_encList, List.map_cons, List.sum_cons] at this ⊢
      omega

/-! ### The local search -/

/-- The encoding of `(m, w, S)`. -/
abbrev encApply : ℕ × List ℕ × List ℕ ↪ List Bool :=
  encPair encNat (encPair (encList encNat) (encList encNat))

theorem lsApply_polytime :
    ComputableInPolyTime (fun y : ℕ × List ℕ × List ℕ ↦ lsApply y.1 y.2.1 y.2.2) encApply
      (encList encNat) := by
  unfold lsApply
  have hstep : ComputableInPolyTime (fun p : (ℕ × List ℕ) × ℕ ↦
      if p.2 % p.1.1 ∈ p.1.2 then p.1.2 else p.1.2.set (p.2 / p.1.1) (p.2 % p.1.1))
      (encPair (encPair encNat (encList encNat)) encNat) (encList encNat) := by
    have hm : ComputableInPolyTime (fun p : (ℕ × List ℕ) × ℕ ↦ p.2 % p.1.1)
        (encPair (encPair encNat (encList encNat)) encNat) encNat :=
      binMod' (snd _ _) ((fst _ _).comp (fst _ _))
    exact ite_decide (decide_mem ((snd _ _).comp (fst _ _)) hm) ((snd _ _).comp (fst _ _))
      (listSet' ((snd _ _).comp (fst _ _)) (binDiv' (snd _ _) ((fst _ _).comp (fst _ _))) hm)
  refine foldlWith_of_bounded_growth (par := fun y : ℕ × List ℕ × List ℕ ↦ y.1)
    (list := fun y ↦ y.2.1) (init := fun y ↦ y.2.2)
    (step := fun m S x ↦ if x % m ∈ S then S else S.set (x / m) (x % m))
    (fst _ _) ((fst _ _).comp (snd _ _)) ((snd _ _).comp (snd _ _)) hstep
    (growth := fun y ↦ 2 * (encApply y).length + 1) ?_ ?_
  · exact ((PolyBounded.const 2).mul PolyBounded.self).add (.const 1)
  · intro y S x hx
    have h1 : (encNat x).length ≤ (encApply y).length := by
      refine (SizedListEncoding.length_elem_le (encA := encNat) (encL := encList encNat) _ _
        hx).trans ?_
      simp only [encApply, length_encPair]
      omega
    have h2 := length_encNat_mono (Nat.mod_le x y.1)
    split_ifs
    · omega
    · have := length_encList_set_le encNat S (x / y.1) (x % y.1)
      omega

@[fun_prop]
theorem lsApply' {m : α → ℕ} {w S : α → List ℕ} (hm : ComputableInPolyTime m input encNat)
    (hw : ComputableInPolyTime w input (encList encNat))
    (hS : ComputableInPolyTime S input (encList encNat)) :
    ComputableInPolyTime (fun a ↦ lsApply (m a) (w a) (S a)) input (encList encNat) :=
  lsApply_polytime.comp (g := fun a ↦ (m a, w a, S a)) (hm.prod (hw.prod hS))

@[fun_prop]
theorem lsImproves' {N : α → ℕ} {x : α → Raw} {S T : α → List ℕ}
    (hN : ComputableInPolyTime N input encUnary) (hx : ComputableInPolyTime x input encRaw)
    (hS : ComputableInPolyTime S input (encList encNat))
    (hT : ComputableInPolyTime T input (encList encNat)) :
    ComputableInPolyTime (fun a ↦ lsImproves (N a) (x a) (S a) (T a)) input encBool := by
  unfold lsImproves
  have hNq : ComputableInPolyTime (fun a ↦ ((N a : ℕ) : ℚ)) input encRat :=
    rat_natCast' (unary_to_binary.comp hN)
  have hkq : ComputableInPolyTime (fun a ↦ (((x a).k : ℕ) : ℚ)) input encRat :=
    rat_natCast' (raw_k' hx)
  exact rat_lt' (cost' hx hT) (rat_mul' (rat_sub' (const 1) (rat_div' (const 1)
    (rat_mul' hNq hkq))) (cost' hx hS))

theorem lsStep_eq (N : ℕ) (x : Raw) (B : ℕ) (S : List ℕ) :
    lsStep N x B S = lsApply x.m (((Tuples.tuples B (x.k * x.m) (Par.p N)).find?
      fun w ↦ lsImproves N x S (lsApply x.m w S)).getD []) S := by
  unfold lsStep
  cases (Tuples.tuples B (x.k * x.m) (Par.p N)).find? _ with
  | none => rfl
  | some w => rfl

/-- The encoding of `((N, x, B), S)`. -/
abbrev encStep : (ℕ × Raw × ℕ) × List ℕ ↪ List Bool :=
  encPair (encPair encUnary (encPair encRaw encUnary)) (encList encNat)

theorem lsStep_polytime : ComputableInPolyTime
    (fun p : (ℕ × Raw × ℕ) × List ℕ ↦ lsStep p.1.1 p.1.2.1 p.1.2.2 p.2) encStep
      (encList encNat) := by
  simp only [lsStep_eq]
  have hx : ComputableInPolyTime (fun p : (ℕ × Raw × ℕ) × List ℕ ↦ p.1.2.1) encStep encRaw :=
    (fst _ _).comp ((snd _ _).comp (fst _ _))
  have hN : ComputableInPolyTime (fun p : (ℕ × Raw × ℕ) × List ℕ ↦ p.1.1) encStep encUnary :=
    (fst _ _).comp (fst _ _)
  have hB : ComputableInPolyTime (fun p : (ℕ × Raw × ℕ) × List ℕ ↦ p.1.2.2) encStep encUnary :=
    (snd _ _).comp ((snd _ _).comp (fst _ _))
  have hS : ComputableInPolyTime (fun p : (ℕ × Raw × ℕ) × List ℕ ↦ p.2) encStep
      (encList encNat) := snd _ _
  have hp : ComputableInPolyTime (fun p : (ℕ × Raw × ℕ) × List ℕ ↦ Par.p p.1.1) encStep
      encUnary := by
    unfold Par.p
    exact unary_mul' (const 24) hN
  have htup : ComputableInPolyTime (fun p : (ℕ × Raw × ℕ) × List ℕ ↦
      Tuples.tuples p.1.2.2 (p.1.2.1.k * p.1.2.1.m) (Par.p p.1.1)) encStep
      (encList (encList encNat)) :=
    Tuples.tuples' hB (binMul' (raw_k' hx) (raw_m' hx)) hp
  have htest : ComputableInPolyTime (fun q : ((ℕ × Raw × ℕ) × List ℕ) × List ℕ ↦
      lsImproves q.1.1.1 q.1.1.2.1 q.1.2 (lsApply q.1.1.2.1.m q.2 q.1.2))
      (encPair encStep (encList encNat)) encBool :=
    lsImproves' (hN.comp (fst _ _)) (hx.comp (fst _ _)) (hS.comp (fst _ _))
      (lsApply' (raw_m' (hx.comp (fst _ _))) (snd _ _) (hS.comp (fst _ _)))
  have hfind := findWithInput (test := fun (p : (ℕ × Raw × ℕ) × List ℕ) w ↦
    lsImproves p.1.1 p.1.2.1 p.2 (lsApply p.1.2.1.m w p.2)) htup htest
  exact lsApply' (raw_m' hx) ((optionGetD (encList encNat)).comp (hfind.prod (const []))) hS

/-- The states of the local search: at most `k` entries, each below `k + B`. -/
theorem lsStep_small (N : ℕ) (x : Raw) (B : ℕ) {S : List ℕ} (hS : S.length ≤ x.k)
    (hS' : ∀ a ∈ S, a < x.k + B) :
    (lsStep N x B S).length ≤ x.k ∧ ∀ a ∈ lsStep N x B S, a < x.k + B := by
  rw [lsStep_eq]
  generalize hwdef : ((Tuples.tuples B (x.k * x.m) (Par.p N)).find?
    fun w ↦ lsImproves N x S (lsApply x.m w S)).getD [] = w
  have hw : ∀ y ∈ w, y < B := by
    rw [← hwdef]
    intro y hy
    cases h : (Tuples.tuples B (x.k * x.m) (Par.p N)).find?
        (fun w ↦ lsImproves N x S (lsApply x.m w S)) with
    | none => rw [h] at hy; simp at hy
    | some w' =>
      rw [h, Option.getD_some] at hy
      have hmem := List.mem_of_find?_eq_some h
      rw [Tuples.tuples_min] at hmem
      exact lt_of_lt_of_le ((Tuples.mem_tuples_le hmem).2 y hy) (min_le_left _ _)
  clear hwdef
  unfold lsApply
  induction w generalizing S with
  | nil => exact ⟨hS, hS'⟩
  | cons y w ih =>
    rw [List.foldl_cons]
    refine ih ?_ ?_ (fun z hz ↦ hw z (List.mem_cons_of_mem _ hz))
    · split_ifs
      · exact hS
      · rwa [List.length_set]
    · intro a ha
      split_ifs at ha
      · exact hS' a ha
      · rcases List.mem_or_eq_of_mem_set ha with ha | rfl
        · exact hS' a ha
        · have := hw y List.mem_cons_self
          have := Nat.mod_le y x.m
          omega

/-- **The local search**, on tuples with `k` at most the number of rows. -/
theorem localSearch' {N : α → ℕ} {x : α → Raw} {B : α → ℕ}
    (hN : ComputableInPolyTime N input encUnary) (hx : ComputableInPolyTime x input encRaw)
    (hB : ComputableInPolyTime B input encUnary) (hk : ∀ a, (x a).k ≤ (x a).table.length) :
    ComputableInPolyTime (fun a ↦ localSearch (N a) (x a) (B a)) input (encList encNat) := by
  unfold localSearch
  refine (iterateWith_spec (par := fun a ↦ (N a, x a, B a)) (count := B)
    (init := fun a ↦ List.range (x a).k) (step := fun p S ↦ lsStep p.1 p.2.1 p.2.2 S)
    (hN.prod (hx.prod hB)) hB (rangeN' hx (raw_k' hx) hk) lsStep_polytime
    (fun a _ S ↦ S.length ≤ (x a).k ∧ ∀ v ∈ S, v < (x a).k + B a)
    (fun a ↦ ⟨by simp, fun v hv ↦ by simp at hv; omega⟩)
    (fun a _ S _ h ↦ lsStep_small _ _ _ h.1 h.2)
    (size := fun a ↦ (x a).table.length * (2 * ((x a).table.length + B a) + 1)) ?_ ?_).1
  · have h1 := (raw_rows' hx).polyBounded
    have h2 := hB.polyBounded
    exact h1.mul (((PolyBounded.const 2).mul (h1.add h2)).add (.const 1))
  · intro a _ S _ h
    refine (length_encList_le encNat S (b := (x a).table.length + B a) fun v hv ↦ ?_).trans ?_
    · exact (length_encNat_le v).trans (by have := h.2 v hv; have := hk a; omega)
    · exact Nat.mul_le_mul_right _ (h.1.trans (hk a))

end PolyTime

open PolyTime

variable {α : Type} {input : α ↪ List Bool}

/-- The tuple with no centers when `k` exceeds the number of rows. -/
def fixK (x : Raw) : Raw := if x.k ≤ x.table.length then x else (x.n, x.m, 0, x.table)

theorem fixK_k_le (x : Raw) : (fixK x).k ≤ (fixK x).table.length := by
  unfold fixK
  split_ifs with h
  · exact h
  · exact Nat.zero_le _

theorem fixK_polytime : ComputableInPolyTime fixK encRaw encRaw := by
  unfold fixK
  refine ite_decide (binary_le' (raw_k' id') (unary_to_binary.comp (raw_rows' id'))) id' ?_
  exact (raw_n' id').prod ((raw_m' id').prod ((const 0).prod (raw_table' id')))

/-- **The local search is polynomial-time** in `(N, I, B)`, `N` and `B` in unary, on the tuples
with `k` at most the number of rows of the table (`n + m` for an instance): its output has `k`
entries, and `k` is written in binary. -/
theorem localSearch_polytime :
    Turing.MultiTapeTM.ComputableInPolyTime (fun y : ℕ × Raw × ℕ ↦
      if y.2.1.k ≤ y.2.1.table.length then localSearch y.1 y.2.1 y.2.2 else [])
      (Encoding.encPair Encoding.encUnary (Encoding.encPair encRaw Encoding.encUnary))
      (Encoding.encList Encoding.encNat) := by
  have hx : ComputableInPolyTime (fun y : ℕ × Raw × ℕ ↦ y.2.1)
      (encPair encUnary (encPair encRaw encUnary)) encRaw := (fst _ _).comp (snd _ _)
  have hc : ComputableInPolyTime (fun y : ℕ × Raw × ℕ ↦ decide (y.2.1.k ≤ y.2.1.table.length))
      (encPair encUnary (encPair encRaw encUnary)) encBool :=
    binary_le' (raw_k' hx) (unary_to_binary.comp (raw_rows' hx))
  have hLS := localSearch' (fst _ _) (fixK_polytime.comp hx) ((snd _ _).comp (snd _ _))
    fun y ↦ fixK_k_le y.2.1
  refine (ite_decide hc hLS (const [])).of_enc_eq fun y ↦ ?_
  by_cases h : y.2.1.k ≤ y.2.1.table.length
  · have hfix : fixK y.2.1 = y.2.1 := by
      unfold fixK
      exact if_pos h
    simp only [Function.comp_apply]
    rw [if_pos h, if_pos h, hfix]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

/-- **The local search for a computed input**, on inputs with `k` at most the number of rows. -/
theorem localSearch_polytime' {N : α → ℕ} {x : α → Raw} {B : α → ℕ}
    (hN : ComputableInPolyTime N input encUnary) (hx : ComputableInPolyTime x input encRaw)
    (hB : ComputableInPolyTime B input encUnary) (hk : ∀ a, (x a).k ≤ (x a).table.length) :
    ComputableInPolyTime (fun a ↦ localSearch (N a) (x a) (B a)) input (encList encNat) :=
  localSearch' hN hx hB hk

end BCFGJPSSV26.Stable


