-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleRows
-- name    : OAI_Combinatorics_EuclideanRamsey_CircleRows
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:31:55.295559+00:00
-- url     : https://prove2.me/theorems/9f5ee303-339f-410c-b3d0-b2d65af11c07
-- title:
--   Quadratic rows of five plane points
-- statement:
--   A finite configuration $a=(a_0,\dots,a_{s-1})$ of points of $\mathbb R^d$ is Ramsey when, for every number of colours $r$, some dimension $D$ has the property that every $r$-colouring of $\mathbb R^D$ contains a monochromatic copy of $a$ congruent to it.
--
--   For five points $a_0,\dots,a_4$ of $\mathbb R^2$, let $K$ be their coordinate field and $\tilde a_i=(1,a_{i0},a_{i1})$ their augmented points. This module defines the index set $\{0,1,2\}^2$ of quadratic monomials. It also defines the quadratic row of $a_i$,
--   $$
--   q_i(p,q)=\tilde a_i(p)\,\tilde a_i(q)\in K .
--   $$
--   A quadratic form with coefficient matrix $M$ takes the value $\sum_{p,q}M_{pq}\,q_i(p,q)$ at $a_i$. Independence of the five rows is the hypothesis of the quadratic sufficient condition for Ramsey configurations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/CircleRows.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/CircleRows.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseyCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleInterpolation

namespace OAI
noncomputable section
namespace EuclideanRamsey.CircleConsequence

abbrev QIndex := Option (Fin 2) × Option (Fin 2)
def quadraticRow (a : Fin 5 → Space 2) (i : Fin 5) (q : QIndex) : Coeff a :=
  augmented a i q.1 * augmented a i q.2

end EuclideanRamsey.CircleConsequence

end

end OAI


