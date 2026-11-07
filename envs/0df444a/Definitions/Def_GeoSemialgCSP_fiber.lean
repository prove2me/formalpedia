-- Prove2me | Definitions.Def_GeoSemialgCSP_fiber
-- name    : GeoSemialgCSP_fiber
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:46:59.574454+00:00
-- url     : https://prove2.me/theorems/ce804b1e-38f0-44c5-8921-d3b87d0f6f68
-- title:
--   Fibers of a relation
-- statement:
--   For a relation $\Delta\subseteq[q]^k$, a position $j$ and a fixed tuple $b$, the **fiber** in position $j$ is
--   $$\{x\in[q]:\ (b_1,\dots,b_{j-1},x,b_{j+1},\dots,b_k)\in\Delta\},$$
--   obtained by fixing the other $k-1$ labels. The entry $b_j$ plays no role.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3, p.8 (PDF p.9)

import Mathlib

namespace GeoSemialgCSP

/-- **Fibers of a relation.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3, printed p.8 (PDF p.9): for `Δ ⊆ [q]^k`, its fiber in
position `j` obtained by fixing the other labels `b_{−j}` is `{a_j ∈ [q] : (b₁, …, a_j, …, b_k) ∈ Δ}`.

**Formalization Note.** The entry `b j` of the fixed tuple is ignored. -/
def fiber {k q : ℕ} (Δ : Set (Fin k → Fin q)) (j : Fin k) (b : Fin k → Fin q) : Set (Fin q) :=
  {x | Function.update b j x ∈ Δ}

end GeoSemialgCSP


