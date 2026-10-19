-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleExtension
-- name    : OAI_Combinatorics_EuclideanRamsey_CircleExtension
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:32:32.22928+00:00
-- url     : https://prove2.me/theorems/42506117-084e-4690-b93f-43f544dbdbd4
-- title:
--   Rational parametrization of a circle
-- statement:
--   A finite configuration $a=(a_0,\dots,a_{s-1})$ of points of $\mathbb R^d$ is Ramsey when, for every number of colours $r$, some dimension $D$ has the property that every $r$-colouring of $\mathbb R^D$ contains a monochromatic copy of $a$ congruent to it.
--
--   For a centre $c\in\mathbb R^2$, a radius $r$ and a parameter $t\in\mathbb R$, this module defines the point
--   $$
--   \sigma(t)=c+r\Bigl(\frac{1-t^2}{1+t^2},\ \frac{2t}{1+t^2}\Bigr)
--   $$
--   on the circle $|x-c|=|r|$. The map is the inverse stereographic projection. When $r\ne0$ it is injective and so produces infinitely many points of the circle. This is used to extend a few points on a circle to five distinct points on the same circle.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/CircleExtension.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/CircleExtension.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseyCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleInterpolation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleRows

namespace OAI
noncomputable section
namespace EuclideanRamsey.CircleConsequence

/-- Rational parametrization of a genuine radius-r circle. -/
def stereographic (c : Space 2) (r t : ℝ) : Space 2 :=
  c + r • WithLp.toLp 2 ![(1-t^2)/(1+t^2), (2*t)/(1+t^2)]

end EuclideanRamsey.CircleConsequence

end

end OAI


