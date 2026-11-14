-- Prove2me | Definitions.Def_BuhaiPapers_Background_TuplesPolyTime
-- name    : BuhaiPapers_Background_TuplesPolyTime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:57:33.330706+00:00
-- url     : https://prove2.me/theorems/6db8b959-7fb5-400a-a8f5-9b0a2701a8ea
-- title:
--   Background.TuplesPolyTime — Tuples, cut at a budget, in polynomial time
-- statement:
--   This is module `Background.TuplesPolyTime`, shared background material of the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (Apache-2.0), published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) uses it.
--
--   The certificate of `Tuples.tuples` (`Tuples.tuples_polytime`), as in `BKS23/AlgorithmPolyTime.lean`:
--   the budget `L` and the length `T` in unary, the range `n` in binary, the entries in binary. Since
--   at most `L` tuples are kept, only the first `L` values of each coordinate matter, so `n` may be
--   replaced by `min L n` (`Tuples.tuples_min`), which is written in unary in time polynomial in `L`.
--
--   **Contents.** The module is published as a whole: 9 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BuhaiPapers_Background_TuplesPolyTime`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/Background/TuplesPolyTime.lean

module

public import Definitions.Def_BuhaiPapers_Background_Tuples
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Iteration
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `Background.TuplesPolyTime` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Tuples, cut at a budget, in polynomial time

The certificate of `Tuples.tuples` (`Tuples.tuples_polytime`), as in `BKS23/AlgorithmPolyTime.lean`:
the budget `L` and the length `T` in unary, the range `n` in binary, the entries in binary. Since
at most `L` tuples are kept, only the first `L` values of each coordinate matter, so `n` may be
replaced by `min L n` (`Tuples.tuples_min`), which is written in unary in time polynomial in `L`.
-/

@[expose] public section

namespace Tuples

open Turing.MultiTapeTM ComputableInPolyTime

/-- Only the first `L` values of a coordinate are kept. -/
theorem tupleStep_min (L n : ℕ) (l : List (List ℕ)) :
    tupleStep L n l = tupleStep L (min L n) l := by
  rcases le_total n L with h | h
  · rw [min_eq_right h]
  rw [min_eq_left h]
  unfold tupleStep
  cases l with
  | nil => rfl
  | cons q l =>
    rw [List.flatMap_cons, List.flatMap_cons,
      List.take_append_of_le_length (by simpa using h),
      List.take_append_of_le_length (by simp)]
    rw [← List.map_take, ← List.map_take, List.take_range, List.take_range, min_eq_left h,
      min_self]

/-- **Only `min L n` values matter.** -/
theorem tuples_min (L n T : ℕ) : tuples L n T = tuples L (min L n) T := by
  unfold tuples
  congr 1
  funext l
  exact tupleStep_min L n l

/-- Lists of numbers, in unary. -/
abbrev encVs : List ℕ ↪ List Bool := encList encUnary

theorem tupleStep_polytime : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × List (List ℕ) ↦ tupleStep p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary encUnary) (encList encVs)) (encList encVs) := by
  unfold tupleStep
  have h : ComputableInPolyTime (fun p : (ℕ × ℕ) × List (List ℕ) ↦
      p.2.flatMap fun q ↦ (List.range p.1.2).map (· :: q))
      (encPair (encPair encUnary encUnary) (encList encVs)) (encList encVs) :=
    flatMapWithInput (by fun_prop) (mapWithInput (by fun_prop) (by fun_prop))
  fun_prop

/-- The states of the tuple loop: at most `L + 1` tuples, of at most `i` entries below `n`. -/
theorem tuples_iter_small (L n i : ℕ) :
    (∀ q ∈ (tupleStep L n)^[i] [[]], q.length ≤ i ∧ ∀ a ∈ q, a < n) ∧
      ((tupleStep L n)^[i] [[]]).length ≤ L + 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨fun q hq ↦ ?_, ?_⟩
    · have hq' := List.mem_of_mem_take hq
      simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hq'
      obtain ⟨q', hq', a, ha, rfl⟩ := hq'
      obtain ⟨h1, h2⟩ := ih.1 q' hq'
      refine ⟨by simp; omega, fun b hb ↦ ?_⟩
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ha
      · exact h2 b hb
    · rw [tupleStep, List.length_take]
      omega

/-- The tuples with all three numbers in unary, the entries in unary. -/
theorem tuples_unary_polytime : ComputableInPolyTime (fun x : ℕ × ℕ × ℕ ↦ tuples x.1 x.2.1 x.2.2)
    (encPair encUnary (encPair encUnary encUnary)) (encList encVs) := by
  unfold tuples
  refine iterateWith (par := fun x : ℕ × ℕ × ℕ ↦ (x.1, x.2.1)) (count := fun x ↦ x.2.2)
    (init := fun _ ↦ [[]]) (step := fun p l ↦ tupleStep p.1 p.2 l) (by fun_prop) (by fun_prop)
    (by fun_prop) tupleStep_polytime
    (bound := fun x ↦ (x.1 + 1) * (2 * (x.2.2 * (2 * x.2.1 + 1)) + 1)) ?_ ?_
  · refine PolyBounded.of_forall_le 7 3 fun x ↦ ?_
    set s := (encPair encUnary (encPair encUnary encUnary) x).length
    have hs : x.1 + x.2.1 + x.2.2 ≤ s := by
      simp only [s, length_encPair, encUnary_apply, List.length_replicate]
      omega
    have h1 : x.1 + 1 ≤ s + 1 := by omega
    have h2 : x.2.2 ≤ s + 1 := by omega
    have h3 : 2 * x.2.1 + 1 ≤ 2 * (s + 1) := by omega
    calc (x.1 + 1) * (2 * (x.2.2 * (2 * x.2.1 + 1)) + 1)
        ≤ (s + 1) * (2 * ((s + 1) * (2 * (s + 1))) + 1 * (s + 1) * (s + 1)) := by
          gcongr
          nlinarith
      _ = 5 * (s + 1) ^ 3 := by ring
      _ ≤ 7 * (s + 1) ^ 3 := by gcongr; norm_num
  · intro x i hi
    obtain ⟨hsmall, hlen⟩ := tuples_iter_small x.1 x.2.1 i
    have helem : ∀ q ∈ (tupleStep x.1 x.2.1)^[i] [[]], (encVs q).length ≤
        x.2.2 * (2 * x.2.1 + 1) := by
      intro q hq
      obtain ⟨h1, h2⟩ := hsmall q hq
      refine (length_encList_le encUnary q (b := x.2.1) fun a ha ↦ ?_).trans
        (Nat.mul_le_mul_right _ (h1.trans hi))
      simpa [encUnary_apply] using (h2 a ha).le
    calc (encList encVs ((tupleStep x.1 x.2.1)^[i] [[]])).length
        ≤ ((tupleStep x.1 x.2.1)^[i] [[]]).length * (2 * (x.2.2 * (2 * x.2.1 + 1)) + 1) :=
          length_encList_le _ _ helem
      _ ≤ (x.1 + 1) * (2 * (x.2.2 * (2 * x.2.1 + 1)) + 1) := Nat.mul_le_mul_right _ hlen

/-- Lists of lists of unary numbers in binary. -/
theorem toBinaryLists : ComputableInPolyTime (fun l : List (List ℕ) ↦ l) (encList encVs)
    (encList (encList encNat)) := by
  have h : ComputableInPolyTime (fun l : List (List ℕ) ↦ l.map fun q ↦ q.map fun i ↦ i)
      (encList encVs) (encList (encList encNat)) :=
    mapWithInput (by fun_prop) (mapWithInput (by fun_prop) (unary_to_binary.comp (snd _ _)))
  simpa only [List.map_id'] using h

/-- **The tuples are polynomial-time**: the budget `L` and the length `T` in unary, the range `n`
in binary, the entries in binary. -/
theorem tuples_polytime : ComputableInPolyTime (fun x : ℕ × ℕ × ℕ ↦ tuples x.1 x.2.1 x.2.2)
    (encPair encUnary (encPair encNat encUnary)) (encList (encList encNat)) := by
  have hmin : ComputableInPolyTime (fun x : ℕ × ℕ × ℕ ↦ min x.1 x.2.1)
      (encPair encUnary (encPair encNat encUnary)) encUnary :=
    binary_min_unary' (fst _ _) ((fst _ _).comp (snd _ _))
  have h := toBinaryLists.comp (tuples_unary_polytime.comp
    (g := fun x : ℕ × ℕ × ℕ ↦ (x.1, min x.1 x.2.1, x.2.2))
    ((fst _ _).prod (hmin.prod (by fun_prop))))
  refine h.of_enc_eq fun x ↦ ?_
  simp only [Function.comp_apply]
  rw [← tuples_min]

@[fun_prop]
theorem tuples' {α : Type} {input : α ↪ List Bool} {f g h : α → ℕ}
    (hf : ComputableInPolyTime f input encUnary) (hg : ComputableInPolyTime g input encNat)
    (hh : ComputableInPolyTime h input encUnary) :
    ComputableInPolyTime (fun a ↦ tuples (f a) (g a) (h a)) input (encList (encList encNat)) :=
  tuples_polytime.comp (g := fun a ↦ (f a, g a, h a)) (hf.prod (hg.prod hh))

end Tuples


