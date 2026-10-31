-- Prove2me | Definitions.Def_PCLAssort_PipageRun
-- name    : PCLAssort_PipageRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:19:20.098993+00:00
-- url     : https://prove2.me/theorems/ec8f5c25-86ac-457a-be88-2b6f71441776
-- title:
--   A complete run of pipage rounding
-- statement:
--   A complete run of pipage rounding from $\bar x$ to $x^*$ is a finite sequence of pipage steps starting at $\bar x$ and ending at a point $x^*$ with at most one fractional coordinate. Since every step needs two fractional coordinates, the procedure stops exactly at such a point.
--
--   **Formalization Note** The reflexive-transitive closure of the step relation, together with the stopping condition.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), §4.3, pipage rounding, p.794 (PDF p.10)

import Mathlib
import Definitions.Def_PCLAssort_PipageStep
import Definitions.Def_PCLAssort_fracCoords

namespace PCLAssort

/-- A complete run of pipage rounding from `x` to `x'` (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, §4.3, p.794): "starting with
`x = x̄`, we repeat the following as long as there are at least two fractional variables in `x`".
It is a finite sequence of pipage steps ending at a point with at most one fractional coordinate.

**Formalization Note.** `Relation.ReflTransGen` of `PipageStep`; a step needs two fractional
coordinates, so a run stops exactly when at most one is left. -/
def PipageRun {V : Type} [Fintype V] [DecidableEq V] (s : V → ℝ) (F : (V → ℝ) → ℝ) (x x' : V → ℝ) :
    Prop :=
  Relation.ReflTransGen (PipageStep s F) x x' ∧ (fracCoords x').card ≤ 1

end PCLAssort


