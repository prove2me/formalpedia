-- Prove2me | Definitions.Def_CostScaling_StrongPoly_fixedArcs
-- name    : CostScaling_StrongPoly_fixedArcs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:02:10.088301+00:00
-- url     : https://prove2.me/theorems/dec1c2de-f310-4b5f-b200-be93f040bfb1
-- title:
--   Section 4.2 — the set Fε of ε-fixed arcs
-- statement:
--   For a circulation network $G=(V,E)$ and an error parameter ε, an arc $(v,w)\in E$ is **ε-fixed** when all ε-optimal circulations have the same flow through it. The set of ε-fixed arcs is
--
--   $$
--   F_ε=\{(v,w)\in E:\text{for all ε-optimal circulations }g,g',\ g(v,w)=g'(v,w)\}.
--   $$
--
--   This set tracks the arcs whose flow can no longer change as the allowable optimality error shrinks. It is the object in Lemma 4.4 and Theorem 4.5.
--
--   **Formalization Note** The predicate for an ε-fixed arc is reused from Goldberg and Tarjan's 1989 work; it quantifies over ε-optimal circulations of the same network. The price convention differs by $p\mapsto-p$, which does not change this predicate.
-- source:
--   Goldberg & Tarjan, MIT/LCS/TM-333 (July 1987), Section 4.2, p. 16, paragraph before Corollary 4.3 and paragraph after it

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_EpsOptimal

namespace CostScaling.StrongPoly

open CycleCanceling.MinMean

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Section 4.2, p. 16: `F_ε` is the set of arcs of `E` whose flow is the same
in every `ε`-optimal circulation. -/
noncomputable def fixedArcs (N : CircNetwork V) (ε : ℝ) : Finset (V × V) := by
  classical
  exact N.E.filter (fun a => IsEpsFixed N ε a.1 a.2)

end CostScaling.StrongPoly


