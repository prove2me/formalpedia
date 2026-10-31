-- Prove2me | Definitions.Def_GhostPenalty_AssumptionB
-- name    : GhostPenalty_AssumptionB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:33:59.379065+00:00
-- url     : https://prove2.me/theorems/2a60a62c-b450-4b63-af3b-835358b652c1
-- title:
--   Assumption B: Hölder continuity of $d(\cdot)$ on compact subsets of $K$
-- statement:
--   **Assumption B.** For every compact set $S\subseteq K$ there are constants $\theta>0$ and $\alpha>0$ such that
--   $$\|d(y)-d(z)\|\le\theta\|y-z\|^{\alpha}\qquad\text{for all } y,z\in S.$$
--   It is used in Theorem 1 (ii); Proposition 5 gives sufficient conditions ($\alpha=\tfrac12$).
--
--   **Formalization Note** The constants $\theta,\alpha$ are local to the assumption (unrelated to the function $\theta$ of (14)); $\|y-z\|^\alpha$ is the real power.
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, Assumption B, p.12

import Mathlib

namespace GhostPenalty

/-- **Assumption B**: Hölder continuity of the direction map on compact subsets of `K`.
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, §3, Assumption B, p.12: "For any compact set `S ⊆ K`, two positive constants `θ` and
`α` exist such that `‖d(y) − d(z)‖ ≤ θ‖y − z‖^α, ∀y,z ∈ S`."

**Formalization Note.** `‖·‖` is the Euclidean norm; `‖y − z‖^α` is the real power
(`Real.rpow`). The constants are named `θ`, `α` as on the page (unrelated to the function
`theta`). -/
def AssumptionB {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ S ⊆ K, IsCompact S → ∃ θ > (0 : ℝ), ∃ α > (0 : ℝ),
    ∀ y ∈ S, ∀ z ∈ S, ‖d y - d z‖ ≤ θ * ‖y - z‖ ^ α

end GhostPenalty


