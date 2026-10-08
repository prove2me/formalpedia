-- Prove2me | Definitions.Def_SpeedScaling_AVR_TreeInduced
-- name    : SpeedScaling_AVR_TreeInduced
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:47.501053+00:00
-- url     : https://prove2.me/theorems/058d50d6-cd59-4037-8421-8891a5e9ba01
-- title:
--   Tree-induced interval matrices
-- statement:
--   A tree-induced matrix comes from a finite family of positive-length real intervals $I_j=[l_j,r_j]$. Intervals with overlapping interiors are properly nested in index order, and every interval has one unit of length outside the union of its predecessors. The matrix is
--   $$M_{ij}=\begin{cases}1/(r_j-l_j),&i\le j\text{ and }I_i\subseteq I_j,\\0,&\text{otherwise.}\end{cases}$$
--
--   This is the matrix used to reduce the canonical-instance energy bound to an eigenvalue estimate. Endpoint-only contact is allowed; the paper's printed four-interval example has two such intervals.
-- source:
--   Yao, Demers & Shenker, A scheduling model for reduced CPU energy, Proc. 36th IEEE FOCS (1995), DOI 10.1109/SFCS.1995.492493, p. 380, §5.2, tree-induced matrix definition.

import Mathlib

namespace SpeedScaling.AVR
noncomputable section
open MeasureTheory
open scoped Classical

/-- The interval representation of a tree-induced matrix on p. 380. -/
def IsTreeInduced {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ l r : Fin n → ℝ,
    (∀ j, l j < r j) ∧
    (∀ i j, i < j →
      (Set.Ioo (l i) (r i) ∩ Set.Ioo (l j) (r j)).Nonempty →
        Set.Icc (l i) (r i) ⊆ Set.Icc (l j) (r j)) ∧
    (∀ j,
      volume (Set.Icc (l j) (r j) \
        ⋃ i : Fin n, if i < j then Set.Icc (l i) (r i) else ∅) = 1) ∧
    (∀ i j,
      M i j = if i ≤ j ∧ Set.Icc (l i) (r i) ⊆ Set.Icc (l j) (r j)
        then 1 / (r j - l j) else 0)

end
end SpeedScaling.AVR


