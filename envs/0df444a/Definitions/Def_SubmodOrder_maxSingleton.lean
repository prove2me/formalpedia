-- Prove2me | Definitions.Def_SubmodOrder_maxSingleton
-- name    : SubmodOrder_maxSingleton
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:53.816984+00:00
-- url     : https://prove2.me/theorems/e52ac320-b48f-4360-aaf2-6c82a93fdce3
-- title:
--   The largest singleton value $\max_{e\in N} f(\{e\})$
-- statement:
--   For a set function $f$ on a finite ground set $N$, this is the largest value of a single element,
--
--   $$
--   \max\Bigl(0,\ \max_{e\in N} f(\{e\})\Bigr).
--   $$
--
--   Algorithm 1 starts from the threshold $\tau=\frac1k\max_{e\in N}f(\{e\})$, and the proof of Theorem 2 splits on whether $\mathrm{OPT}\le 2\max_{e\in N}f(\{e\})$.
--
--   **Formalization Note** The maximum is taken together with $0$. For a monotone $f$ with $f(\emptyset)=0$ every singleton value is nonnegative, so on a nonempty ground set this is exactly $\max_{e}f(\{e\})$; on the empty ground set it is $0$.
-- source:
--   Udwani, Submodular Order Functions and Assortment Optimization, arXiv:2107.02743v5, Algorithm 1, p.13, "Initialize τ = 1/k max_{e∈N} f({e})"; proof of Theorem 2, p.21

import Mathlib

namespace SubmodOrder

/-- The largest singleton value `max_{e ∈ N} f({e})` (Udwani, arXiv:2107.02743v5, Algorithm 1,
p.13: "Initialize τ = 1/k max_{e∈N} f({e})"; proof of Theorem 2, p.21: "OPT ≤ 2maxe∈N f({e})").

**Formalization Note.** The maximum is taken together with `0`, i.e. this is
`max(0, max_e f({e}))`. For a monotone `f` with `f ∅ = 0` every `f({e})` is nonnegative, so on a
nonempty ground set this is exactly the paper's maximum; on the empty ground set it is `0`
(where `OPT = 0` as well). -/
def maxSingleton {α : Type*} [Fintype α] (f : Finset α → ℝ) : ℝ :=
  Finset.univ.fold max 0 fun e => f {e}

end SubmodOrder


