-- Prove2me | Definitions.Def_PCLAssort_fracCoords
-- name    : PCLAssort_fracCoords
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:20.989663+00:00
-- url     : https://prove2.me/theorems/50853e1a-aae5-4a4a-84fb-c25870acdf0f
-- title:
--   Fractional coordinates of a vector
-- statement:
--   The set of fractional coordinates of $x\in\mathbb R^V$ is $\{i\in V: 0<x_i<1\}$. Pipage rounding runs while this set has at least two elements, and Algorithm 1 forms $I_2$ from the remaining fractional coordinate.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), pipage rounding and Algorithm 1, pp.794–795 (PDF pp.10–11)

import Mathlib

namespace PCLAssort

/-- The fractional coordinates `{i : 0 < x_i < 1}` of a vector `x` (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, pipage rounding and
Algorithm 1, pp.794–795). -/
noncomputable def fracCoords {V : Type} [Fintype V] (x : V → ℝ) : Finset V :=
  Finset.univ.filter (fun i => 0 < x i ∧ x i < 1)

end PCLAssort


