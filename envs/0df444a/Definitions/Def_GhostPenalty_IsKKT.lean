-- Prove2me | Definitions.Def_GhostPenalty_IsKKT
-- name    : GhostPenalty_IsKKT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:06.73299+00:00
-- url     : https://prove2.me/theorems/2bc10d57-a5a7-4c04-a1bf-68e150f852bb
-- title:
--   KKT solution of (P) (Definition 1)
-- statement:
--   A point $\hat x\in K$ is a **KKT solution** of (P) if
--   $$g(\hat x)\le 0\quad\text{and}\quad M_1(\hat x)\ne\emptyset.$$
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, Definition 1, p.5

import Mathlib
import Definitions.Def_GhostPenalty_M1

namespace GhostPenalty

/-- **KKT solution of (P)** (Definition 1, first case).
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, Definition 1, p.5:
"A point `x̂ ∈ K` is, for problem (P), • a KKT solution if `g(x̂) ≤ 0` and `M1(x̂) ≠ ∅`".

**Formalization Note.** `g(x̂) ≤ 0` is componentwise. -/
def IsKKT {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ K ∧ (∀ i, g i x ≤ 0) ∧ (M1 f g K x).Nonempty

end GhostPenalty


