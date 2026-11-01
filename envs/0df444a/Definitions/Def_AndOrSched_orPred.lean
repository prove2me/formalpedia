-- Prove2me | Definitions.Def_AndOrSched_orPred
-- name    : AndOrSched_orPred
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:27:08.118325+00:00
-- url     : https://prove2.me/theorems/dc489fec-5193-4673-b3de-bd2ae999ae9b
-- title:
--   OR-predecessors $\mathcal P(b)$
-- statement:
--   For $b\in B$, the set of its OR-predecessors is
--   $$\mathcal P(b):=\{a\in A\mid (a,b)\in E_\vee\}.$$
--   It may be empty, in which case $b$ has no OR-constraint.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §1, p.2, "The set of OR-predecessors of job b ∈ B is denoted by P(b)"

import Mathlib
import Definitions.Def_AndOrSched_Instance
open scoped Classical NNReal

namespace AndOrSched

/-- The set of OR-predecessors of `b ∈ B`, `𝒫(b) := {a ∈ A | (a, b) ∈ E∨}`
(Happach, Schulz, arXiv:2001.07011v1, §1, p.2). It may be empty. -/
noncomputable def orPred (I : Instance) (b : I.B) : Finset I.A :=
  Finset.univ.filter fun a => I.orArc a b

end AndOrSched


