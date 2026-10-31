-- Prove2me | Definitions.Def_GhostPenalty_IsFJ
-- name    : GhostPenalty_IsFJ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:35:46.167635+00:00
-- url     : https://prove2.me/theorems/0525bf91-59a9-47a0-8a57-a93665408892
-- title:
--   Fritz-John solution of (P) (Definition 1)
-- statement:
--   A point $\hat x\in K$ is a **Fritz-John (FJ) solution** of (P) if
--   $$g(\hat x)\le 0\quad\text{and}\quad M_0(\hat x)\ne\{0\},$$
--   that is, $M_0(\hat x)$ contains a nonzero multiplier.
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, Definition 1, p.5

import Mathlib
import Definitions.Def_GhostPenalty_M0

namespace GhostPenalty

/-- **Fritz-John (FJ) solution of (P)** (Definition 1, second case).
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, Definition 1, p.5:
"A point `x̂ ∈ K` is, for problem (P), … • a Fritz-John (FJ) solution if `g(x̂) ≤ 0` and
`M0(x̂) ≠ {0}`".

**Formalization Note.** `g(x̂) ≤ 0` is componentwise. Since `0 ∈ M0(x̂)` for `x̂ ∈ K`,
`M0(x̂) ≠ {0}` means that `M0(x̂)` contains a nonzero multiplier. -/
def IsFJ {n m : ℕ} (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ K ∧ (∀ i, g i x ≤ 0) ∧ M0 g K x ≠ {0}

end GhostPenalty


