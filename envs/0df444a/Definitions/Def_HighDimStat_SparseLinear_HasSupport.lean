-- Prove2me | Definitions.Def_HighDimStat_SparseLinear_HasSupport
-- name    : HighDimStat_SparseLinear_HasSupport
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:05:05.450162+00:00
-- url     : https://prove2.me/theorems/f219621c-63fd-4734-8d2f-cfc34d732b99
-- title:
--   A vector is supported on a given index subset
-- statement:
--   This predicate says that a vector's nonzero coordinates all lie inside a given subset $S$
--   of the coordinate index set — the standard notion of "support" used throughout Chapter 7,
--   starting on p. 200: "the vector $\theta^*$ has support $S \subset \{1,\dots,d\}$, meaning
--   that $\theta^*_j = 0$ for all $j \in S^c$."
--
--   For $\theta \in \mathbb R^d$ and $S \subseteq \{1,\dots,d\}$,
--
--   $$
--   \mathrm{HasSupport}(\theta, S) \;:\Longleftrightarrow\; \forall j \notin S,\ \theta_j = 0.
--   $$
--
--   **Formalization Note** This only asserts $\theta$ vanishes off $S$; it does not require
--   $\theta$ to be nonzero on every coordinate of $S$, exactly as the book's own usage (a
--   vector supported on $S$ may still have some zero entries within $S$).
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 200 (PDF p. 220)

import Mathlib

namespace HighDimStat.SparseLinear

/-- `θ` is supported on `S`: every coordinate outside `S` vanishes, `θⱼ = 0` for `j ∉ S`, as in
Wainwright, *High-Dimensional Statistics* (2019), p. 200 ("the vector θ* has support S ⊂
{1,...,d}, meaning that θ*ⱼ = 0 for all j ∈ Sᶜ"). -/
def HasSupport {d : ℕ} (θ : Fin d → ℝ) (S : Finset (Fin d)) : Prop :=
  ∀ j, j ∉ S → θ j = 0

end HighDimStat.SparseLinear


