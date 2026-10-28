-- Prove2me | Definitions.Def_WildeQIT_classicalTraceDist
-- name    : WildeQIT_classicalTraceDist
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T05:41:45.932379+00:00
-- url     : https://prove2.me/theorems/7cad84de-9ba4-402c-becb-17602c46da8b
-- title:
--   Classical trace distance $\|p-q\|_1$ (Definition 10.7.1)
-- statement:
--   **Definition 10.7.1 (Classical trace distance).** Let $p,q:\mathcal{X}\to\mathbb{R}$, where $\mathcal{X}$ is a finite alphabet. The classical trace distance between $p$ and $q$ is
--
--   $$
--   \|p-q\|_1 \;\equiv\; \sum_x |p(x)-q(x)| .
--   $$
--
--   For probability distributions, $\tfrac12\|p-q\|_1$ is the largest difference of the probabilities that $p$ and $q$ assign to an event (Lemma 10.7.1); it is the classical special case of the trace distance between density operators and the distance in which the continuity of entropy (Theorem 10.7.4) is measured.
--
--   **Formalization Note.** `WildeQIT.classicalTraceDist p q = ∑ x, |p x - q x|` for arbitrary real functions `p q : α → ℝ` on a `Fintype`; no normalisation or factor $\tfrac12$ is built in, exactly as in the book. (The quantum trace distance on matrices is a different declaration, `WildeQIT.traceDist`.)
-- source:
--   Wilde, Quantum Information Theory 2nd ed. (Cambridge 2017; arXiv:1106.1445v8), Definition 10.7.1, §Continuity of Entropy (roster-items.csv line 17271).

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
Wilde, *Quantum Information Theory* (2nd ed.), Definition 10.7.1 (Classical trace distance):
for `p, q : 𝒳 → ℝ` on a finite alphabet, `‖p − q‖₁ ≡ ∑_x |p(x) − q(x)|`.
-/

namespace WildeQIT

/-- Definition 10.7.1. The classical trace distance `‖p − q‖₁ = ∑_x |p(x) − q(x)|` between two
real-valued functions on a finite alphabet. -/
noncomputable def classicalTraceDist {α : Type} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ x, |p x - q x|

end WildeQIT


