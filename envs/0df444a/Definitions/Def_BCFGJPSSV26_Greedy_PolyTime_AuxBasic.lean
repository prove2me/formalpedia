-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxBasic
-- name    : BCFGJPSSV26_Greedy_PolyTime_AuxBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:04:07.848527+00:00
-- url     : https://prove2.me/theorems/89f4673d-ba52-4db2-bb98-3056aefe66d0
-- title:
--   BCFGJPSSV26.Greedy.PolyTime.AuxBasic — Polynomial time of the core: generic certificates and encodings
-- statement:
--   This is module `BCFGJPSSV26.Greedy.PolyTime.AuxBasic` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   Helpers for `BCFGJPSSV26/Greedy/PolyTime/Core.lean`: the encodings of core inputs (`n` and `m` in
--   unary), atoms, sequences and solutions; small generic certificates (powers, ceilings, binary
--   logarithms in unary, folds of `min` and `max`); and bounds on encoded lengths.
--
--   **Contents.** The module is published as a whole: 23 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxBasic`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/PolyTime/AuxBasic.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Defs
public import Definitions.Def_BuhaiPapers_Background_PolyTime_Rat
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryLog

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.PolyTime.AuxBasic` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial time of the core: generic certificates and encodings

Helpers for `BCFGJPSSV26/Greedy/PolyTime/Core.lean`: the encodings of core inputs (`n` and `m` in
unary), atoms, sequences and solutions; small generic certificates (powers, ceilings, binary
logarithms in unary, folds of `min` and `max`); and bounds on encoded lengths.
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy.PT

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

/-! ### Encodings -/

/-- Core inputs: `n` and `m` in unary, `k` in binary, then the table. -/
abbrev encCI : CoreIn ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encNat (encList (encList encRat))))

/-- Atoms, both components in binary. -/
abbrev encAt : AAtom ↪ List Bool := encPair encNat encNat

/-- Sequences of atoms. -/
abbrev encSq : List AAtom ↪ List Bool := encList encAt

/-- Solutions. -/
abbrev encSl : List (List AAtom) ↪ List Bool := encList encSq

variable {α : Type} {input : α ↪ List Bool}

/-! ### Generic certificates -/

theorem toBin {f : α → ℕ} (h : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime f input encNat :=
  unary_to_binary.comp h

theorem binAdd {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ f a + g a) input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_add' hf.tidy hg.tidy)

theorem binDiv {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ f a / g a) input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_div' hf.tidy hg.tidy)

theorem binMod {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ f a % g a) input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_mod' hf.tidy hg.tidy)

theorem unDiv2 {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime (fun a ↦ f a / 2) input encUnary :=
  .of_tidy ((ComputableTidilyInPolyTime.unary_div_const 2).comp hf.tidy)

/-- A case distinction on a decidable proposition. -/
theorem itep {β : Type} {encB : β ↪ List Bool} {p : α → Prop} [DecidablePred p]
    {f g : α → β} (hp : ComputableInPolyTime (fun a ↦ decide (p a)) input encBool)
    (hf : ComputableInPolyTime f input encB) (hg : ComputableInPolyTime g input encB) :
    ComputableInPolyTime (fun a ↦ if p a then f a else g a) input encB := by
  have := ite' hp hf hg
  simpa only [decide_eq_true_eq] using this

theorem ratPow {f : α → ℚ} {k : α → ℕ} (hf : ComputableInPolyTime f input encRat)
    (hk : ComputableInPolyTime k input encUnary) :
    ComputableInPolyTime (fun a ↦ f a ^ k a) input encRat := by
  have e : (fun a ↦ f a ^ k a) = fun a ↦ (List.replicate (k a) (f a)).prod :=
    funext fun a ↦ (List.prod_replicate _ _).symm
  rw [e]
  exact rat_prod' (replicate hk hf)

theorem natCeil {q : α → ℚ} (hq : ComputableInPolyTime q input encRat) :
    ComputableInPolyTime (fun a ↦ ⌈q a⌉₊) input encNat := by
  have h : ComputableInPolyTime (fun a ↦ (-⌊-q a⌋).toNat) input encNat :=
    intBin_toNat.comp (g := fun a ↦ -⌊-q a⌋)
      (.of_tidy (ComputableTidilyInPolyTime.intBin_neg.comp (rat_floor' (rat_neg' hq)).tidy))
  refine h.of_enc_eq fun a ↦ ?_
  rw [Int.floor_neg, neg_neg, Int.ceil_toNat]

theorem clog_le_size (Y : ℕ) : Nat.clog 2 Y ≤ Nat.size Y :=
  Nat.clog_le_of_le_pow (Nat.lt_size_self Y).le

/-- `⌈log₂ Y⌉`, in unary. -/
theorem clogU {Y : α → ℕ} (hY : ComputableInPolyTime Y input encNat) :
    ComputableInPolyTime (fun a ↦ Nat.clog 2 (Y a)) input encUnary :=
  binary_to_unary_bounded (binary_clog_two_nat' hY) (binary_size.comp hY)
    fun a ↦ clog_le_size (Y a)

theorem len_min_le (s v : ℚ) :
    (encRat (min s v)).length ≤ (encRat s).length + (encRat v).length := by
  rcases le_total s v with h | h
  · rw [min_eq_left h]; omega
  · rw [min_eq_right h]; omega

theorem len_max_le (s v : ℚ) :
    (encRat (max s v)).length ≤ (encRat s).length + (encRat v).length := by
  rcases le_total s v with h | h
  · rw [max_eq_right h]; omega
  · rw [max_eq_left h]; omega

/-- A fold of `min` over a computed list. -/
theorem foldlMin {l : α → List ℚ} {i : α → ℚ} (hl : ComputableInPolyTime l input (encList encRat))
    (hi : ComputableInPolyTime i input encRat) :
    ComputableInPolyTime (fun a ↦ (l a).foldl min (i a)) input encRat := by
  have hstep : ComputableInPolyTime (fun p : (α × ℚ) × ℚ ↦ min p.1.2 p.2)
      (encPair (encPair input encRat) encRat) encRat :=
    rat_min' ((snd _ _).comp (fst _ _)) (snd _ _)
  refine foldlWithInput_of_bounded_growth (step := fun _ s v ↦ min s v) hi
    ⟨hl, hstep, inferInstance, inferInstance⟩
    (growth := fun a ↦ (encList encRat (l a)).length) ⟨hl.polyBounded_length, ?_⟩
  intro a s v hv
  have h := SizedListEncoding.length_elem_le (encA := encRat) (encL := encList encRat) (l a) v hv
  have := len_min_le s v
  omega

/-- A fold of `max` over a computed list. -/
theorem foldlMax {l : α → List ℚ} {i : α → ℚ} (hl : ComputableInPolyTime l input (encList encRat))
    (hi : ComputableInPolyTime i input encRat) :
    ComputableInPolyTime (fun a ↦ (l a).foldl max (i a)) input encRat := by
  have hstep : ComputableInPolyTime (fun p : (α × ℚ) × ℚ ↦ max p.1.2 p.2)
      (encPair (encPair input encRat) encRat) encRat :=
    rat_max' ((snd _ _).comp (fst _ _)) (snd _ _)
  refine foldlWithInput_of_bounded_growth (step := fun _ s v ↦ max s v) hi
    ⟨hl, hstep, inferInstance, inferInstance⟩
    (growth := fun a ↦ (encList encRat (l a)).length) ⟨hl.polyBounded_length, ?_⟩
  intro a s v hv
  have h := SizedListEncoding.length_elem_le (encA := encRat) (encL := encList encRat) (l a) v hv
  have := len_max_le s v
  omega

theorem foldr_min_eq {β : Type} (g : β → ℚ) (S : List β) (K : ℚ) :
    S.foldr (fun a acc ↦ min (g a) acc) K = (S.map g).foldl min K := by
  induction S generalizing K with
  | nil => rfl
  | cons a S ih =>
    simp only [List.foldr_cons, List.map_cons, List.foldl_cons, ih]
    clear ih
    induction S generalizing K with
    | nil => simp [min_comm]
    | cons b S ih2 =>
      simp only [List.map_cons, List.foldl_cons]
      rw [ih2, min_right_comm]

/-! ### Encoded lengths -/

theorem len_encNat_mono {a b : ℕ} (h : a ≤ b) : (encNat a).length ≤ (encNat b).length := by
  rw [encNat_apply, encNat_apply, Nat.size_eq_bits_len, Nat.size_eq_bits_len]
  exact Nat.size_le_size h

theorem len_encNat_le_self (a : ℕ) : (encNat a).length ≤ a := by
  rw [encNat_apply, Nat.size_eq_bits_len]
  exact Nat.size_le.2 Nat.lt_two_pow_self

theorem len_encList_append {β : Type} (e : β ↪ List Bool) (l l' : List β) :
    (encList e (l ++ l')).length = (encList e l).length + (encList e l').length := by
  rw [length_encList, length_encList, length_encList, List.map_append, List.sum_append]

theorem len_encList_le_of {β : Type} (e : β ↪ List Bool) {l : List β} {N s : ℕ}
    (hN : l.length ≤ N) (hs : ∀ a ∈ l, (e a).length ≤ s) :
    (encList e l).length ≤ N * (2 * s + 1) :=
  (length_encList_le e l hs).trans (Nat.mul_le_mul_right _ hN)

end BCFGJPSSV26.Greedy.PT


