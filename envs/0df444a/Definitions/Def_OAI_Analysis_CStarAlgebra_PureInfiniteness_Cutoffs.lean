-- Prove2me | Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Cutoffs
-- name    : OAI_Analysis_CStarAlgebra_PureInfiniteness_Cutoffs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:25:13.008252+00:00
-- url     : https://prove2.me/theorems/f89c6ea0-50f4-47c0-a598-aa3e8fcecb62
-- title:
--   Piecewise-linear ramp functions applied by continuous functional calculus
-- statement:
--   For real numbers $l<u$, the ramp function $\theta_{l,u}:\mathbb{R}\to\mathbb{R}$ is
--
--   $$
--   \theta_{l,u}(t)=\min\Bigl(1,\ \frac{\max(t-l,0)}{u-l}\Bigr)=
--   \begin{cases}0, & t\le l,\\ \dfrac{t-l}{u-l}, & l\le t\le u,\\ 1, & t\ge u,\end{cases}
--   $$
--
--   a continuous function with values in $[0,1]$ that rises linearly from $0$ to $1$ on $[l,u]$.
--
--   Let $A$ be a $C^*$-algebra, not necessarily unital, with its usual order. For a self-adjoint $a\in A$ and $0\le l<u$, the ramp of $a$ is the element $\theta_{l,u}(a)\in A$ obtained by the continuous functional calculus; no unit is needed because $\theta_{l,u}(0)=0$.
--
--   Ramps are continuous companions of the cut-downs $(a-l)_+$, obtained from $a$ by the functional calculus with $t\mapsto\max(t-l,0)$. In the surrounding development it is shown that for positive $a$ and $0\le l<u\le w$ the ramp $\theta_{l,u}(a)$ is a positive contraction, lies in the hereditary subalgebra $\overline{(a-l)_+A(a-l)_+}$, acts as a unit on a deeper cut-down, $\theta_{l,u}(a)\,(a-w)_+=(a-w)_+$, and has norm $1$ when $u\le\|a\|$.
--
--   **Formalization Note** The Lean names are `rampFn l u t` and `ramp a l u`, the latter being the non-unital functional calculus `cfcₙ (rampFn l u) a`. The formula is accepted for all real $l,u$: if $u=l$, division by zero gives $\theta_{l,u}=0$; and by Mathlib's conventions `ramp a l u` is $0$ when $a$ is not self-adjoint, or when $l<0$ and $u\neq l$ (then $\theta_{l,u}(0)\neq0$). The order on `A` is any order making it a star-ordered ring. The other sections of the file contain no declarations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Cutoffs.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Cutoffs.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the IndividualStrongInfiniteness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots

-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
section MoreHer
variable [PartialOrder A] [StarOrderedRing A]

end MoreHer
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
section Ramps
variable [PartialOrder A] [StarOrderedRing A]

def rampFn (l u t : ℝ) : ℝ := min 1 (max (t-l) 0 / (u-l))

def ramp (a : A) (l u : ℝ) : A := cfcₙ (rampFn l u) a

end Ramps
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]

section UnitalCutBounds
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

end UnitalCutBounds

end MainGap

end

end OAI


