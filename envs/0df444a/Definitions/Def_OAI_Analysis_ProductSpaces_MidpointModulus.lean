-- Prove2me | Definitions.Def_OAI_Analysis_ProductSpaces_MidpointModulus
-- name    : OAI_Analysis_ProductSpaces_MidpointModulus
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:04:32.039881+00:00
-- url     : https://prove2.me/theorems/87ea85b2-baac-4c9a-96be-85e34109693c
-- title:
--   The midpoint gain $\tfrac12(\|x+ty\|+\|x-ty\|)-\|x\|$
-- statement:
--   Let $X$ be a real normed space. For $t\in\mathbb R$ and $x,y\in X$ the *midpoint gain* is
--
--   $$
--   \operatorname{gain}_t(x,y)=\frac{\|x+ty\|+\|x-ty\|}{2}-\|x\|.
--   $$
--
--   It measures how much the average of the norms at the two symmetric points $x\pm ty$ exceeds the norm at their midpoint $x$; by the triangle inequality $0\le\operatorname{gain}_t(x,y)\le|t|\,\|y\|$.
--
--   When $\|x\|=1$ this is exactly the quantity whose infimum over directions $y$ of norm at least $1$ in a closed finite-codimensional subspace, supremum over such subspaces, and infimum over unit vectors $x$ defines the averaged asymptotic midpoint modulus $\bar\delta_X(t)$. Lower bounds of the form $\operatorname{gain}_t(u,y)\ge A\|y\|-B\|u\|$ for all $y$ in a suitable subspace are the form in which the modulus estimates for the $L^1$ product span are proved.
--
--   **Formalization Note** The Lean definition is `midpointGain t x y := (‖x + t • y‖ + ‖x - t • y‖) / 2 - ‖x‖`, for `X` a `NormedAddCommGroup` with `NormedSpace ℝ X`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/MidpointModulus.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/MidpointModulus.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the IndependentProducts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uX

namespace IndependentProducts
section MidpointGeometry
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

def midpointGain (t : ℝ) (x y : X) : ℝ := (‖x + t • y‖ + ‖x - t • y‖) / 2 - ‖x‖

end MidpointGeometry
end IndependentProducts

end

end OAI


