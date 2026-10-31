-- Prove2me | Definitions.Def_GhostPenalty_IsGenStationary
-- name    : GhostPenalty_IsGenStationary
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:09.837624+00:00
-- url     : https://prove2.me/theorems/a2bd2f5a-997b-4893-9039-3ee6d4c8ad34
-- title:
--   Generalized stationary solution of (P) (Definition 1)
-- statement:
--   A point $\hat x\in K$ is a **generalized stationary solution** of (P) if it is a KKT solution, a Fritz-John solution, or an External Stationary solution.
--
--   Without feasibility or regularity assumptions, convergence to generalized stationary points is the natural target of an algorithm for (P); it is the stopping test (S.1) of Algorithm 1.
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, Definition 1, p.5

import Mathlib
import Definitions.Def_GhostPenalty_IsKKT
import Definitions.Def_GhostPenalty_IsFJ
import Definitions.Def_GhostPenalty_IsES

namespace GhostPenalty

/-- **Generalized stationary solution of (P)** (Definition 1).
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, Definition 1, p.5:
"We call `x̂ ∈ K` a generalized stationary solution of (P) if any of these cases occurs", the
cases being KKT, Fritz-John (FJ) and External Stationary (ES) solution.

**Formalization Note.** Each of `IsKKT`, `IsFJ`, `IsES` contains `x̂ ∈ K`. -/
def IsGenStationary {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  IsKKT f g K x ∨ IsFJ g K x ∨ IsES g K x

end GhostPenalty


