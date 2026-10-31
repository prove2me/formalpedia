-- Prove2me | Definitions.Def_GhostPenalty_EMFCQ
-- name    : GhostPenalty_EMFCQ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:35:44.041097+00:00
-- url     : https://prove2.me/theorems/95be0052-8380-4fb2-8c8d-c5caa1942186
-- title:
--   Extended Mangasarian-Fromovitz CQ (Definition 2)
-- statement:
--   The **extended Mangasarian-Fromovitz constraint qualification (eMFCQ)** holds at $\hat x\in K$ if
--   $$M_0(\hat x)=\{0\}.$$
--   At feasible points with $K=\mathbb R^n$ this is the classical MFCQ; at infeasible points it excludes ES points.
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, Definition 2, p.6

import Mathlib
import Definitions.Def_GhostPenalty_M0

namespace GhostPenalty

/-- **Extended Mangasarian-Fromovitz constraint qualification (eMFCQ)** (Definition 2).
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, Definition 2, p.6:
"We say that the extended Mangasarian-Fromovitz Constraint Qualification (eMFCQ) holds at
`x̂ ∈ K` if `M0(x̂) = {0}`."

**Formalization Note.** The point is required to lie in `K`, as in the definition. -/
def EMFCQ {n m : ℕ} (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ K ∧ M0 g K x = {0}

end GhostPenalty


