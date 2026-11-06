-- Prove2me | Definitions.Def_GradSuffice_DetAlg_lastQuery
-- name    : GradSuffice_DetAlg_lastQuery
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:20:17.536898+00:00
-- url     : https://prove2.me/theorems/a66d9acf-deef-4a35-8f40-2b53f8047743
-- title:
--   Output of a run: the last query $w_T$
-- statement:
--   The **output** of a run of a first-order algorithm with $T\ge1$ queries is its last query point $w_T$. As the paper notes, this is no loss of generality: querying the intended output costs at most one more oracle call.
--
--   **Formalization Note** With 0-based rounds $w_T$ is the query of round $T-1$. Every statement using the output assumes $T\ge1$; the value $0$ returned at $T=0$ is never used.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §2, p.4

import Mathlib
import Definitions.Def_GradSuffice_DetAlg_hist

namespace GradSuffice

/-- **Output of a run: the last query `w_T`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §2, p.4: "Without loss of generality, the
algorithm outputs its last queried point `w_T`, since querying the output costs at most one
additional oracle call."

**Formalization Note.** The last query is the query of round `T − 1` (0-based). Every statement
using it assumes `0 < T`; the value `0` at `T = 0` is never used. -/
noncomputable def DetAlg.lastQuery {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {W : Set X} {T : ℕ} (A : DetAlg X W T)
    (f : X → ℝ) (g : X → StrongDual ℝ X) : X :=
  if hT : 0 < T then A.query ⟨T - 1, by omega⟩ (A.hist f g (T - 1)) else 0

end GradSuffice


