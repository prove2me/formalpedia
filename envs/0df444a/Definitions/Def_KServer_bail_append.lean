-- Prove2me | Definitions.Def_KServer_bail_append
-- name    : KServer_bail_append
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T11:01:11.705698+00:00
-- url     : https://prove2.me/theorems/d7947536-1bb8-4dcb-89a1-b933aff05cff
-- title:
--   Decomposition of online escape costs along chunk concatenation
-- statement:
--   Structural lemmas for the online escape semantics: the evader's movement cost is nonnegative and additive along concatenation of request blocks; the bail time of a concatenated chunk $A \mathbin{+\!\!+} B$ is the bail time in $A$ if the rule fires there and otherwise the shifted bail time in $B$ relative to the extended history; consequently the bail-aware cost satisfies $\mathrm{bailCost}(A \mathbin{+\!\!+} B) = \mathrm{bailCost}(A)$ when the rule fires in $A$, and $= \mathrm{cost}(A) + \mathrm{bailCost}(B)$ otherwise. Raising the escape price raises the cost by exactly the price difference on bailing histories and not at all on non-bailing ones. These identities let a chunk-combining argument split one coarse escape-priced service into its fine sub-chunk services.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Section 5 (Lemma 10 machinery), online escape form.

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace KServer

private theorem find?_congr' {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = q a) : l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.find?_cons]
    rw [h a (List.mem_cons_self ..)]
    cases q a
    · exact ih fun a ha => h a (List.mem_cons_of_mem _ ha)
    · rfl

/-- Movement cost over an appended request: one extra step. -/
theorem EvaderAlgorithm.cost_concat {X : Type*} [MetricSpace X]
    (E : EvaderAlgorithm X) (l : List (Set X)) (S : Set X) :
    E.cost (l ++ [S]) = E.cost l + dist (E.pos l) (E.pos (l ++ [S])) := by
  unfold EvaderAlgorithm.cost
  have hlen : (l ++ [S]).length = l.length + 1 := by simp
  rw [hlen, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]
  · rw [List.take_append_of_le_length (le_refl _), List.take_length,
      List.take_of_length_le (by simp)]

/-- The movement cost is monotone under extending the request sequence. -/
theorem EvaderAlgorithm.cost_le_cost_append {X : Type*} [MetricSpace X]
    (E : EvaderAlgorithm X) (h χ : List (Set X)) :
    E.cost h ≤ E.cost (h ++ χ) := by
  induction χ using List.reverseRecOn with
  | nil => simp
  | append_singleton χ S ih =>
    rw [← List.append_assoc, E.cost_concat]
    have := dist_nonneg (x := E.pos (h ++ χ)) (y := E.pos (h ++ χ ++ [S]))
    linarith

theorem EvaderAlgorithm.costOn_nonneg {X : Type*} [MetricSpace X]
    (E : EvaderAlgorithm X) (h χ : List (Set X)) : 0 ≤ E.costOn h χ := by
  unfold EvaderAlgorithm.costOn
  have := E.cost_le_cost_append h χ
  linarith

/-- Chunk costs add along concatenation. -/
theorem EvaderAlgorithm.costOn_append {X : Type*} [MetricSpace X]
    (E : EvaderAlgorithm X) (h A B : List (Set X)) :
    E.costOn h (A ++ B) = E.costOn h A + E.costOn (h ++ A) B := by
  unfold EvaderAlgorithm.costOn
  rw [← List.append_assoc]
  ring

/-- Splitting the bail time across a concatenation of two chunks: the bail
fires in `A` if it fires there, and otherwise fires in `B` relative to the
extended history. -/
theorem bailTime_append {X : Type*} (bail : List (Set X) → Bool)
    (h A B : List (Set X)) :
    bailTime bail h (A ++ B)
      = (bailTime bail h A).or ((bailTime bail (h ++ A) B).map (A.length + ·)) := by
  unfold bailTime
  have hlen : (A ++ B).length = A.length + B.length := by simp
  rw [hlen, List.range_add, List.find?_append]
  congr 1
  · -- the `A` part: predicates agree on `range A.length`
    refine find?_congr' _ _ _ fun q hq => ?_
    simp only [List.mem_range] at hq
    rw [List.take_append_of_le_length (by omega)]
  · -- the `B` part, shifted by `A.length`
    rw [List.find?_map]
    congr 1
    refine find?_congr' _ _ _ fun q hq => ?_
    simp only [List.mem_range] at hq
    show bail (h ++ (A ++ B).take (A.length + q)) = bail ((h ++ A) ++ B.take q)
    rw [List.take_append, List.take_of_length_le (by omega),
      Nat.add_sub_cancel_left, List.append_assoc]

/-- If the bail fires within `A`, serving `A ++ B` bails exactly as serving
`A` alone. -/
theorem EvaderAlgorithm.bailCost_append_of_bail {X : Type*} [MetricSpace X]
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    (h A B : List (Set X)) (p : ℝ) {q : ℕ}
    (hq : bailTime bail h A = some q) :
    E.bailCost bail h (A ++ B) p = E.bailCost bail h A p := by
  unfold EvaderAlgorithm.bailCost
  rw [bailTime_append, hq]
  show E.costOn h ((A ++ B).take q) + p = _
  have hqlt : q < A.length := List.mem_range.mp (List.mem_of_find?_eq_some hq)
  rw [List.take_append_of_le_length (by omega)]

/-- If the bail does not fire within `A`, serving `A ++ B` costs the full
service of `A` plus the bail-aware service of `B` after it. -/
theorem EvaderAlgorithm.bailCost_append_of_no_bail {X : Type*} [MetricSpace X]
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    (h A B : List (Set X)) (p : ℝ)
    (hq : bailTime bail h A = none) :
    E.bailCost bail h (A ++ B) p = E.costOn h A + E.bailCost bail (h ++ A) B p := by
  unfold EvaderAlgorithm.bailCost
  rw [bailTime_append, hq, Option.none_or]
  rcases hB : bailTime bail (h ++ A) B with - | q'
  · simp only [Option.map_none]
    exact E.costOn_append h A B
  · simp only [Option.map_some]
    show E.costOn h ((A ++ B).take (A.length + q')) + p = _
    rw [List.take_append, List.take_of_length_le (le_of_eq rfl |>.trans (by omega)),
      Nat.add_sub_cancel_left, E.costOn_append]
    ring

/-- Raising the escape price when the bail actually fires raises the cost by
exactly the price difference. -/
theorem EvaderAlgorithm.bailCost_price_of_bail {X : Type*} [MetricSpace X]
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    (h χ : List (Set X)) (p p' : ℝ) {q : ℕ}
    (hq : bailTime bail h χ = some q) :
    E.bailCost bail h χ p' = E.bailCost bail h χ p + (p' - p) := by
  unfold EvaderAlgorithm.bailCost
  rw [hq]
  ring

/-- With no bail, the price is irrelevant. -/
theorem EvaderAlgorithm.bailCost_of_no_bail {X : Type*} [MetricSpace X]
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    (h χ : List (Set X)) (p : ℝ)
    (hq : bailTime bail h χ = none) :
    E.bailCost bail h χ p = E.costOn h χ := by
  unfold EvaderAlgorithm.bailCost
  rw [hq]

theorem EvaderAlgorithm.bailCost_of_bail {X : Type*} [MetricSpace X]
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    (h χ : List (Set X)) (p : ℝ) {q : ℕ}
    (hq : bailTime bail h χ = some q) :
    E.bailCost bail h χ p = E.costOn h (χ.take q) + p := by
  unfold EvaderAlgorithm.bailCost
  rw [hq]

theorem EvaderAlgorithm.bailCost_nonneg {X : Type*} [MetricSpace X]
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    (h χ : List (Set X)) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ E.bailCost bail h χ p := by
  unfold EvaderAlgorithm.bailCost
  rcases hq : bailTime bail h χ with - | q
  · exact E.costOn_nonneg h χ
  · have := E.costOn_nonneg h (χ.take q)
    linarith

end KServer


