-- Prove2me | Definitions.Def_ParetoIneff_IsDummyList
-- name    : ParetoIneff_IsDummyList
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:56.571037+00:00
-- url     : https://prove2.me/theorems/4e194403-9743-4bbd-bd53-a4e3e929415d
-- title:
--   Dummy processing times
-- statement:
--   The proof of Theorem 6 uses cost vectors whose entries other than $1$ and $\alpha$ are "arbitrarily high, pairwise distinct" finite processing times, written $\infty$. A **dummy list** fixes these values: $n-2$ pairwise distinct reals, each above
--   $$
--   \bigl((n-1)\alpha+1\bigr)\cdot\alpha .
--   $$
--   That size makes a task on a dummy machine cost more than the Price of Anarchy bound allows, even against an optimal makespan of $\alpha$.
--
--   **Formalization Note** The threshold is the mission's fixed meaning of "arbitrarily high". The subtraction $n-2$ is on natural numbers; canonical vectors exist only for $n\ge2$, where it is exact.
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, proof of Theorem 6, p.13

import Mathlib

open NNReal

namespace ParetoIneff

/-- An admissible **list of dummy processing times** for the canonical cost vectors of the proof
of Theorem 6, arXiv:1809.03454v7, p.13: `n − 2` values that are pairwise distinct and "arbitrarily
high", here all above `((n − 1)α + 1) · α`.

**Formalization Note** The paper writes `∞` for these entries and says they are "arbitrarily high,
pairwise distinct" finite processing times (p.13). The threshold `((n − 1)α + 1) · α` is the fixed
meaning given to "arbitrarily high" in this mission; it is the size the proof of Theorem 6 needs (a
dummy assignment must make the ratio exceed the PoA bound `(n − 1)α + 1` even against an optimal
makespan of `α`). `n − 2` is natural-number subtraction; canonical vectors exist only for `n ≥ 2`,
where it is exact. -/
def IsDummyList {n : ℕ} (α : ℝ) (d : Fin (n - 2) → ℝ≥0) : Prop :=
  Function.Injective d ∧ ∀ k : Fin (n - 2), (((n : ℝ) - 1) * α + 1) * α < (d k : ℝ)

end ParetoIneff


