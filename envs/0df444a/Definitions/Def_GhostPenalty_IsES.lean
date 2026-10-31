-- Prove2me | Definitions.Def_GhostPenalty_IsES
-- name    : GhostPenalty_IsES
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:35:50.920853+00:00
-- url     : https://prove2.me/theorems/1cdd4c5f-fed1-413a-9e1d-897a9b3d64fc
-- title:
--   External Stationary solution of (P) (Definition 1)
-- statement:
--   A point $\hat x\in K$ is an **External Stationary (ES) solution** of (P) if
--   $$g_i(\hat x)>0\ \text{for some } i\in\{1,\dots,m\}\quad\text{and}\quad M_0(\hat x)\ne\{0\}.$$
--   ES points are infeasible points that are stationary for the violation problem (4).
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, Definition 1, p.5

import Mathlib
import Definitions.Def_GhostPenalty_M0

namespace GhostPenalty

/-- **External Stationary (ES) solution of (P)** (Definition 1, third case).
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, Definition 1, p.5:
"A point `x̂ ∈ K` is, for problem (P), … • an External Stationary (ES) solution if `g_i(x̂) > 0`
for some `i ∈ {1,...,m}` and `M0(x̂) ≠ {0}`."

**Formalization Note.** Since `0 ∈ M0(x̂)` for `x̂ ∈ K`, `M0(x̂) ≠ {0}` means that `M0(x̂)`
contains a nonzero multiplier. -/
def IsES {n m : ℕ} (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ K ∧ (∃ i, 0 < g i x) ∧ M0 g K x ≠ {0}

end GhostPenalty


