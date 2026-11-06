-- Prove2me | Definitions.Def_GradSuffice_DetAlg
-- name    : GradSuffice_DetAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:18.994044+00:00
-- url     : https://prove2.me/theorems/7a912d98-1a5a-404e-972e-024c3c7e6ef4
-- title:
--   Deterministic first-order algorithm with $T$ queries
-- statement:
--   A **deterministic first-order algorithm with $T$ queries on $W$** chooses, at each round $t=1,\dots,T$, a query point $w_t\in W$ as a function of the oracle answers $(f(w_s),\xi_s)$ received at the earlier rounds $s<t$. No computational restriction is imposed; only queries are counted.
--
--   **Formalization Note** Rounds are 0-based: round $t$ maps the $t$ earlier answers, a function `Fin t → ℝ × StrongDual ℝ X`, to a point of $W$. Earlier query points are functions of earlier answers, so nothing is lost.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §2, p.4

import Mathlib

namespace GradSuffice

/-- **Deterministic first-order algorithm with `T` queries on `W`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §2, p.4: "A
first-order optimization algorithm interacts with the oracle for `T` rounds. At each round `t`, it
queries a point `w_t ∈ W` and receives `O(w_t)`. It chooses each point using the previous query
points and oracle responses […]. We impose no restrictions on the algorithm's computational power".

**Formalization Note.** Round `t` (0-based) maps the oracle answers of the earlier rounds,
`Fin t → ℝ × StrongDual ℝ X`, to the next query, which lies in `W`. The earlier query points are
functions of the earlier answers, so this loses nothing. Internal randomness is modelled by a
family of such algorithms indexed by a probability space (see `IsAccurate`). -/
structure DetAlg (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (W : Set X) (T : ℕ) where
  /-- The query rule of round `t`, given the answers of rounds `0, …, t − 1`. -/
  query : (t : Fin T) → (Fin t → ℝ × StrongDual ℝ X) → X
  query_mem : ∀ t h, query t h ∈ W

end GradSuffice


