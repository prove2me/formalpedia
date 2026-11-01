-- Prove2me | Definitions.Def_ProcessingNetworks_CTMCFoster_IsInvariantMeasure
-- name    : ProcessingNetworks_CTMCFoster_IsInvariantMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:40.315881+00:00
-- url     : https://prove2.me/theorems/d81dadb1-853f-4e76-ac4e-21bc627eca2a
-- title:
--   Invariant measures of a generator (Definition D.8)
-- statement:
--   Let $\Lambda$ be a generator matrix on $\mathscr S$ and $\eta=(\eta(i),i\in\mathscr S)$ a vector. The vector $\eta$ is **invariant** for $\Lambda$ if
--
--   $$
--   \eta\Lambda=0,\qquad\text{that is,}\qquad \sum_x\eta(x)\Lambda_{xy}=0\quad\text{for each }y\in\mathscr S,
--   $$
--
--   each series being convergent. A measure in the book is a non-negative vector, not necessarily a probability distribution. A stationary distribution of the continuous-time chain is a probability distribution invariant for $\Lambda$.
--
--   **Formalization Note** Non-negativity of $\eta$ is a hypothesis of the statements that use this predicate.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Definition D.8, eq. (D.17), p.291 (PDF 307)

import Mathlib

namespace ProcessingNetworks.CTMCFoster

/-- The non-negative vector `η` is invariant for `Λ` (Definition D.8): `η Λ = 0`, that is, for
each `y` the series `∑_x η(x) Λ x y` converges to `0`.

Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Definition D.8,
eq. (D.17), p.291 (PDF 307).

**Formalization Note** `HasSum` records the convergence the book takes for granted ("the product
on the left side of (D.17) is well defined"). Non-negativity of the measure is a hypothesis of each
statement using this predicate. -/
def IsInvariantMeasure {S : Type*} (Λ : S → S → ℝ) (η : S → ℝ) : Prop :=
  ∀ y, HasSum (fun x => η x * Λ x y) 0

end ProcessingNetworks.CTMCFoster


