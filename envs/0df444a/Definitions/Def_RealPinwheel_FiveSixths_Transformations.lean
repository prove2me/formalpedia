-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_Transformations
-- name    : RealPinwheel_FiveSixths_Transformations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T06:35:07.854919+00:00
-- url     : https://prove2.me/theorems/ab38e9d4-b2be-4565-9e8d-e35b41778ea4
-- title:
--   Label-preserving replacement, unfolding and folding
-- statement:
--   For a labelled period vector $a$, replacing coordinate $j$ by $b$ changes that period alone. Unfolding removes task $j$, introduces $q$ distinct new tasks with period $qa_j$, and sorts all surviving and new tasks by period. With $n$ original tasks and $q\ge1$, the resulting vector has $n-1+q$ positions.
--
--   Folding an ordered tuple of dimension $r+2$ keeps its first $r$ tasks and replaces its final two tasks by one task with half the penultimate period, then sorts:
--
--   $$\operatorname{fold}(A)=\operatorname{sort}(a_1,\ldots,a_r,a_{r+1}/2).$$
--
--   These are concrete operations on labelled data. Sorted lists retain origin tags, so old tasks and new copies remain distinct even when periods coincide. Folding remembers the two final positions as the new task's children. No schedule-existence implication is part of these definitions.
--
--   **Formalization Note** The sorted labelled list supplies the finite carrier for the resulting vector. Unfolding is used only with positive $q$. Folding returns raw periods rather than asserting they are at least one: that property is proved in the source's reduction domain, rather than assumed inside the operation.
-- source:
--   Hiroshi Fujiwara, Grzegorz Gutowski, Katsuhisa Ouchi, Alexander Wolff, STOC 2027 submission #885 (October 2026), Lemma 8 and following paragraph, printed p. 3 (PDF p. 4); Lemma 9 and folding construction, printed pp. 4, 6–7 (PDF pp. 5, 7–8)

import Definitions.Def_RealPinwheel_FiveSixths_Instance

namespace RealPinwheel.FiveSixths

/-- Labelled replacement, without sorting: the same schedule retains its labels. -/
noncomputable def replacePeriod {n : ℕ} (a : Fin n → ℝ) (j : Fin n) (b : ℝ) : Fin n → ℝ :=
  Function.update a j b

/-- The surviving old task labels and the distinct new task labels. -/
def unfoldingLabels {n : ℕ} (j : Fin n) (q : ℕ) : List (Fin n ⊕ Fin q) :=
  ((List.finRange n).filter fun i => i ≠ j).map Sum.inl ++
    (List.finRange q).map Sum.inr

noncomputable def unfoldingPeriod {n : ℕ} (a : Fin n → ℝ) (j : Fin n) (q : ℕ) :
    Fin n ⊕ Fin q → ℝ :=
  Sum.elim a (fun _ => (q : ℝ) * a j)

/-- Sort labelled tasks, retaining their origins even when their periods coincide. -/
noncomputable def unfoldedLabels {n : ℕ} (a : Fin n → ℝ) (j : Fin n) (q : ℕ) :
    List (Fin n ⊕ Fin q) :=
  (unfoldingLabels j q).mergeSort
    (fun x y => decide (unfoldingPeriod a j q x ≤ unfoldingPeriod a j q y))

noncomputable def unfoldedPeriods {n : ℕ} (a : Fin n → ℝ) (j : Fin n) (q : ℕ) :
    Fin (unfoldedLabels a j q).length → ℝ :=
  fun i => unfoldingPeriod a j q ((unfoldedLabels a j q).get i)

/-- Folding the final two tasks of an (r+2)-instance: old labels 0,...,r-1 survive,
and the new label represents the two children r and r+1. -/
def foldingLabels (r : ℕ) : List (Fin (r + 2) ⊕ Unit) :=
  ((List.finRange (r + 2)).take r).map Sum.inl ++ [Sum.inr ()]

noncomputable def foldingPeriod {r : ℕ} (A : Instance (r + 2)) :
    Fin (r + 2) ⊕ Unit → ℝ :=
  Sum.elim A.period (fun _ => A.period ⟨r, by omega⟩ / 2)

noncomputable def foldedLabels {r : ℕ} (A : Instance (r + 2)) :
    List (Fin (r + 2) ⊕ Unit) :=
  (foldingLabels r).mergeSort (fun x y => decide (foldingPeriod A x ≤ foldingPeriod A y))

noncomputable def foldedPeriods {r : ℕ} (A : Instance (r + 2)) :
    Fin (foldedLabels A).length → ℝ :=
  fun i => foldingPeriod A ((foldedLabels A).get i)

end RealPinwheel.FiveSixths


