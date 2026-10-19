-- Prove2me | Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Nonvanishing
-- name    : OAI_Analysis_CStarAlgebra_PureInfiniteness_Nonvanishing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:41:31.438123+00:00
-- url     : https://prove2.me/theorems/6c255a95-1c59-44e6-98cc-2b928b81ee5b
-- title:
--   Order conventions for quantitative non-vanishing under Hilbert-space representations
-- statement:
--   This file introduces no new mathematical objects. It fixes the orders used in its module: on a unital $C^*$-algebra $A$, and on the operator algebra $B(J)$ of every complex Hilbert space $J$, $a\le b$ means that $b-a$ is positive, i.e. self-adjoint with spectrum in $[0,\infty)$ (for operators, equivalently $\langle x,(b-a)x\rangle\ge0$ for all $x\in J$).
--
--   With these conventions the module proves quantitative non-vanishing statements, published separately. A Hilbert-space representation of $A$ is a unital $*$-homomorphism $\pi:A\to B(H)$ into the bounded operators on a complex Hilbert space $H$. The basic statement reads: let $d,y\in A$ with $y\ge0$, and suppose that every representation $\pi$ with $\pi(d)=0$ satisfies $\|\pi(y)\|\le\tfrac14$; then there is $\delta$ with $0<\delta<1$ such that every representation $\pi$ satisfies
--
--   $$
--   \|\pi(y)\|>\tfrac38\ \Longrightarrow\ \|\pi(d)\|>\delta .
--   $$
--
--   A general version replaces the thresholds $\tfrac14$ and $\tfrac38$ by any $s$ and $s'$ with $0\le s<s'$. Thus an exact statement about the representations that kill $d$ is upgraded to a uniform lower bound for $\|\pi(d)\|$.
--
--   **Formalization Note** The file consists only of the local instances `nonvanishingPartialOrder`, `nonvanishingStarOrderedRing`, `nonvanishingOperatorPartialOrder` and `nonvanishingOperatorStarOrderedRing`, which select Mathlib's `CStarAlgebra.spectralOrder` and `CStarAlgebra.spectralOrderedRing`. In the module's theorems the representations are bundled `HilbertRep` objects whose Hilbert spaces live in the same universe as `A`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Nonvanishing.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Nonvanishing.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Cutoffs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ChoicePairs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_FourChoices
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Defect
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Ultrafilter
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Avoidance
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Graph

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
universe u v
variable {A : Type u} [CStarAlgebra A]
local instance nonvanishingPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance nonvanishingStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance nonvanishingOperatorPartialOrder (J : Type*)
    [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J] :
    PartialOrder (J →L[ℂ] J) := CStarAlgebra.spectralOrder _
local instance nonvanishingOperatorStarOrderedRing (J : Type*)
    [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J] :
    StarOrderedRing (J →L[ℂ] J) := CStarAlgebra.spectralOrderedRing _
end MainGap

end

end OAI


