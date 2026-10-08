-- Prove2me | Definitions.Def_CostScaling_StrongPoly_IsEpsTight
-- name    : CostScaling_StrongPoly_IsEpsTight
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:01:29.616073+00:00
-- url     : https://prove2.me/theorems/99accd0e-a32f-44a6-9850-e10fc2ea6559
-- title:
--   Section 2.2 — ε-tight circulations
-- statement:
--   Let $G=(V,E)$ be a finite symmetric circulation network with real capacities and antisymmetric real costs. A circulation $f$ is **ε-tight** if it is ε-optimal and is not ε′-optimal for any smaller error parameter ε′:
--
--   $$
--   f\text{ is ε-tight}\quad\Longleftrightarrow\quad f\text{ is ε-optimal and }\forall\,ε'<ε,\ f\text{ is not ε′-optimal}.
--   $$
--
--   Tightness records attainment at ε. Equality $ε=ε(f)$ alone would say only that ε is an infimum, so this predicate supplies the exact condition used in Lemma 4.4.
--
--   **Formalization Note** The reused 1989 definition writes reduced cost as $c(v,w)+p(v)-p(w)$, while this paper writes $c(v,w)-p(v)+p(w)$. Replacing $p$ by $-p$ makes the ε-optimality notions identical.
-- source:
--   Goldberg & Tarjan, MIT/LCS/TM-333 (July 1987), Section 2.2, p. 7, paragraph after (7)

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_EpsOptimal

namespace CostScaling.StrongPoly

open CycleCanceling.MinMean

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Section 2.2, p. 7: a circulation is `ε`-tight when it is `ε`-optimal but is
not `ε'`-optimal for any smaller error parameter `ε'`. This includes attainment
at `ε`, rather than just equality with the infimum `epsOpt`. -/
def IsEpsTight (N : CircNetwork V) (f : V → V → ℝ) (ε : ℝ) : Prop :=
  IsEpsOptimal N f ε ∧ ∀ ε' : ℝ, ε' < ε → ¬ IsEpsOptimal N f ε'

end CostScaling.StrongPoly


