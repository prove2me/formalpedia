-- Prove2me | Definitions.Def_OAI_Probability_ThreeStateClauses_RadialAlgebra
-- name    : OAI_Probability_ThreeStateClauses_RadialAlgebra
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T19:40:06.667223+00:00
-- url     : https://prove2.me/theorems/bda22124-5241-477b-a1bb-ff4acb39ba1e
-- title:
--   Vectors on three coordinates and their average
-- statement:
--   Vectors on three spins are functions $w:\{0,1,2\}\to\mathbb{R}$, i.e. elements of $\mathbb{R}^3$. Their average is
--   $$
--   \operatorname{avg}(w)=\frac{w_0+w_1+w_2}{3}.
--   $$
--
--   These are the coordinates in which likelihood messages, posterior deviations and radial moment functionals of the three-state broadcast model are written.
--
--   **Formalization Note** The type is `Vec = Fin 3 → ℝ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/RadialAlgebra.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/RadialAlgebra.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThreeStateTreeClauses mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThreeStateTreeClauses

namespace OAI

/-! Radial Algebra. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
namespace ThreeState.TreeClauses.Radial

abbrev Vec := Fin 3 → ℝ

def avg (w : Vec) : ℝ := (w 0 + w 1 + w 2) / 3

end ThreeState.TreeClauses.Radial

end

end OAI


