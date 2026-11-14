-- Prove2me | Definitions.Def_BuhaiPapers_Background_Tuples
-- name    : BuhaiPapers_Background_Tuples
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:05.882298+00:00
-- url     : https://prove2.me/theorems/8ada7b1f-43ab-4a38-a4b4-c7580644531d
-- title:
--   Background.Tuples — Tuples, cut at a budget
-- statement:
--   This is module `Background.Tuples`, shared background material of the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (Apache-2.0), published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) uses it.
--
--   Algorithms that try all `T`-tuples over `{0, …, n - 1}` but must stay polynomial in a budget `L`
--   build the tuples one coordinate at a time and keep at most `L` of them at each step
--   (`Tuples.tuples`). When `n^T ≤ L` nothing is cut, and every tuple appears
--   (`Tuples.ofFn_mem_tuples`, `Tuples.mem_tuples`).
--
--   The same definitions are in `BKS23/Algorithm.lean`, with a polynomial-time certificate in
--   `BKS23/AlgorithmPolyTime.lean`; papers may not import each other, so they are repeated here for
--   the others.
--
--   **Contents.** The module is published as a whole: 10 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BuhaiPapers_Background_Tuples`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/Background/Tuples.lean

module

public import Mathlib.Data.List.OfFn
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `Background.Tuples` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Tuples, cut at a budget

Algorithms that try all `T`-tuples over `{0, …, n - 1}` but must stay polynomial in a budget `L`
build the tuples one coordinate at a time and keep at most `L` of them at each step
(`Tuples.tuples`). When `n^T ≤ L` nothing is cut, and every tuple appears
(`Tuples.ofFn_mem_tuples`, `Tuples.mem_tuples`).

The same definitions are in `BKS23/Algorithm.lean`, with a polynomial-time certificate in
`BKS23/AlgorithmPolyTime.lean`; papers may not import each other, so they are repeated here for
the others.
-/

@[expose] public section

namespace Tuples

/-- One more coordinate, for every tuple, cut at `L` tuples. -/
def tupleStep (L n : ℕ) (l : List (List ℕ)) : List (List ℕ) :=
  (l.flatMap fun q ↦ (List.range n).map (· :: q)).take L

/-- The `T`-tuples over `{0, …, n - 1}`, cut at `L` at every step: all of them if `n^T ≤ L`. -/
def tuples (L n T : ℕ) : List (List ℕ) := (tupleStep L n)^[T] [[]]

/-- One more coordinate, for every tuple. -/
def tupleStepFull (n : ℕ) (l : List (List ℕ)) : List (List ℕ) :=
  l.flatMap fun q ↦ (List.range n).map (· :: q)

theorem length_tupleStepFull (n : ℕ) (l : List (List ℕ)) :
    (tupleStepFull n l).length = n * l.length := by
  rw [tupleStepFull, List.length_flatMap]
  simp [mul_comm]

theorem length_iterate_tupleStepFull (n i : ℕ) :
    ((tupleStepFull n)^[i] [[]]).length = n ^ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', length_tupleStepFull, ih, pow_succ, mul_comm]

theorem mem_iterate_tupleStepFull {n : ℕ} : ∀ {i : ℕ} {q : List ℕ},
    q ∈ (tupleStepFull n)^[i] [[]] ↔ q.length = i ∧ ∀ x ∈ q, x < n
  | 0, q => by
    simp only [Function.iterate_zero, id, List.mem_singleton]
    constructor
    · rintro rfl
      simp
    · rintro ⟨h, -⟩
      exact List.length_eq_zero_iff.1 h
  | i + 1, q => by
    rw [Function.iterate_succ_apply', tupleStepFull, List.mem_flatMap]
    constructor
    · rintro ⟨q', hq', hq⟩
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq
      obtain ⟨h1, h2⟩ := mem_iterate_tupleStepFull.1 hq'
      refine ⟨by simp [h1], fun y hy ↦ ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact List.mem_range.1 hx
      · exact h2 y hy
    · rintro ⟨h1, h2⟩
      obtain _ | ⟨x, q'⟩ := q
      · simp at h1
      refine ⟨q', mem_iterate_tupleStepFull.2 ⟨by simpa using h1, fun y hy ↦ h2 y (by simp [hy])⟩,
        List.mem_map.2 ⟨x, List.mem_range.2 (h2 x (by simp)), rfl⟩⟩

theorem tuples_eq {L n T : ℕ} (h : n ^ T ≤ L) : tuples L n T = (tupleStepFull n)^[T] [[]] := by
  suffices ∀ i ≤ T, (tupleStep L n)^[i] [[]] = (tupleStepFull n)^[i] [[]] from this T le_rfl
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega), tupleStep]
    refine List.take_of_length_le ?_
    change (tupleStepFull n _).length ≤ L
    rw [length_tupleStepFull, length_iterate_tupleStepFull, ← pow_succ']
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact (Nat.pow_le_pow_right hn hi).trans h

/-- **Nothing is cut when `n^T ≤ L`**: the tuples are the lists of length `T` below `n`. -/
theorem mem_tuples {L n T : ℕ} (h : n ^ T ≤ L) {q : List ℕ} :
    q ∈ tuples L n T ↔ q.length = T ∧ ∀ x ∈ q, x < n := by
  rw [tuples_eq h, mem_iterate_tupleStepFull]

theorem ofFn_mem_tuples {L n T : ℕ} (h : n ^ T ≤ L) (Q : Fin T → Fin n) :
    List.ofFn (fun j ↦ (Q j : ℕ)) ∈ tuples L n T := by
  rw [mem_tuples h]
  refine ⟨by simp, fun x hx ↦ ?_⟩
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
  exact (Q j).2

/-- Every tuple, cut or not, has length `T` and entries below `n`. -/
theorem mem_tuples_le {L n T : ℕ} {q : List ℕ} (hq : q ∈ tuples L n T) :
    q.length = T ∧ ∀ x ∈ q, x < n := by
  suffices ∀ i, ∀ q ∈ (tupleStep L n)^[i] [[]], q.length = i ∧ ∀ x ∈ q, x < n from this T q hq
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    intro q hq
    rw [Function.iterate_succ_apply', tupleStep] at hq
    have hq' := List.mem_of_mem_take hq
    simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hq'
    obtain ⟨q', hq', a, ha, rfl⟩ := hq'
    obtain ⟨h1, h2⟩ := ih q' hq'
    refine ⟨by simp [h1], fun b hb ↦ ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ha
    · exact h2 b hb

end Tuples


