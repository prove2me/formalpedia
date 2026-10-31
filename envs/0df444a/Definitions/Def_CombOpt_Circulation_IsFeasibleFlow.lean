-- Prove2me | Definitions.Def_CombOpt_Circulation_IsFeasibleFlow
-- name    : CombOpt_Circulation_IsFeasibleFlow
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:03:05.529693+00:00
-- url     : https://prove2.me/theorems/36ff5655-9cf2-4a3d-90b8-2e67e194f319
-- title:
--   Feasible $(r,s)$-flows
-- statement:
--   Let $u$ assign to each arc a capacity that is a nonnegative real number or $\infty$. An $(r,s)$-flow $x$ is **feasible** if $0\le x_e\le u_e$ for every arc $e$. The capacity $u_e=\infty$ means that there is no upper bound on $x_e$.
--
--   **Formalization Note** Capacities have type $\mathbb R_{\ge0}\cup\{\infty\}$ (`ℝ≥0∞`), so no separate nonnegativity hypothesis occurs. The inequality $x_e\le u_e$ is compared in the extended reals.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §3.2, (3.2), p. 38 and p. 39 (PDF pp. 47–48)

import Mathlib
import Definitions.Def_CombOpt_Circulation_MultiDigraph
import Definitions.Def_CombOpt_Circulation_IsFlow

open scoped ENNReal

namespace CombOpt.Circulation

variable {V E : Type*} [Fintype E] [DecidableEq V]

/-- A feasible `(r, s)`-flow, Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §3.2, (3.1)–(3.2), p. 38 (PDF p. 47): an `(r, s)`-flow with
`0 ≤ x_e ≤ u_e` for every arc. The capacities are "nonnegative real numbers or ∞" (p. 39, PDF
p. 48); `u_e = ∞` means that there is no upper bound on `x_e`.

**Formalization Note** Capacities have type `ℝ≥0∞`, which is exactly the book's range, so no
hypothesis `0 ≤ u` is needed. The comparison `x_e ≤ u_e` is made in `EReal`, not through
`ENNReal.ofReal`, so that no truncation of negative reals occurs. -/
def IsFeasibleFlow (G : MultiDigraph V E) (u : E → ℝ≥0∞) (r s : V) (x : E → ℝ) : Prop :=
  IsFlow G r s x ∧ ∀ e, 0 ≤ x e ∧ (x e : EReal) ≤ (u e : EReal)

end CombOpt.Circulation


