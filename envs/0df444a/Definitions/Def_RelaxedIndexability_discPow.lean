-- Prove2me | Definitions.Def_RelaxedIndexability_discPow
-- name    : RelaxedIndexability_discPow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:19:27.36964+00:00
-- url     : https://prove2.me/theorems/a2a31715-adad-4243-8bbe-db47a32269f5
-- title:
--   $\beta^L$ for $L \in \mathbb N \cup \{+\infty\}$, with $\beta^{+\infty} = 0$
-- statement:
--   For a discount factor $\beta$ and $L \in \mathbb N \cup \{+\infty\}$,
--   $$
--   \beta^{L} = \begin{cases} \beta^{n}, & L = n \in \mathbb N,\\ 0, & L = +\infty. \end{cases}
--   $$
--   The value at $+\infty$ is the limit of $\beta^n$ for $0 < \beta < 1$. It is how the paper's formulas (35), (38) and the functions $f, g$ of Theorem 3 are read when a first-crossing time is infinite.
--
--   **Formalization Note** Defined by cases on `ℕ∞`, not through `ENat.toNat` (which would give $\beta^{+\infty} = \beta^0 = 1$).
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, (35), p.20; f and g in Theorem 3, p.23

import Mathlib

namespace RelaxedIndexability

/-- **`β^L` for `L ∈ ℕ ∪ {+∞}`** (Liu, arXiv:2107.11939v4, (35), p.20, and f, g, p.23):
`β^n` for a finite `n` and `β^{+∞} := 0`, the limit of `βⁿ` for `0 < β < 1`.

**Formalization Note.** Defined by cases on `ℕ∞`, not through `ENat.toNat` (which would give
`β^{+∞} = β^0 = 1`). -/
noncomputable def discPow (β : ℝ) : ℕ∞ → ℝ :=
  ENat.recTopCoe 0 fun n => β ^ n

end RelaxedIndexability


