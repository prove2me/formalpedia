-- Prove2me | Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Defect
-- name    : OAI_Analysis_CStarAlgebra_PureInfiniteness_Defect
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:34:33.822094+00:00
-- url     : https://prove2.me/theorems/834ba190-acf7-4a48-b535-abb2dce81f25
-- title:
--   Order conventions for the defect estimates of the four-choice construction
-- statement:
--   This file introduces no new mathematical objects. It fixes, for each section of its module, the order used on unital $C^*$-algebras: on a unital $C^*$-algebra $A$, and, in the sections that consider a unital $*$-homomorphism $\pi:A\to D$ into a second unital $C^*$-algebra $D$, also on $D$, the relation $a\le b$ means that $b-a$ is positive, i.e. self-adjoint with spectrum in $[0,\infty)$. This is the order in which positivity and operator inequalities such as $BB^*\le\tfrac12\cdot1$ are read throughout the module.
--
--   With these conventions the module proves estimates on deficiencies, scaling defects and sandwiches, stated separately. A typical one reads as follows. Write $(U-\eta)_+$ for $U$ under the functional calculus with $t\mapsto\max(t-\eta,0)$. Let $\pi:A\to D$ be a unital $*$-homomorphism, $U,V\in A$ positive, $\eta>0$, $E\subseteq A$ finite and $w\in E$. If
--
--   $$
--   \Bigl\|\pi\Bigl((U-\eta)_+\Bigl(\sum_{x\in E}xVx^*\Bigr)(U-\eta)_+\Bigr)\Bigr\|\le2\eta ,
--   $$
--
--   then
--
--   $$
--   \|\pi(UwV)\|\le\sqrt{2\eta}\,\|V^{1/2}\|+\eta\,\|w\|\,\|V\| .
--   $$
--
--   Another result of the module shows that, for a positive $X$ with $(X-\tfrac18)_+\neq0$, no quadruple $B_0,\dots,B_3$ can satisfy exactly a certain list of relations (the bounds $B_0B_0^*\le\tfrac12$ and $B_2B_2^*\le\tfrac12$, orthogonality and equal-modulus relations within the pairs $(B_0,B_1)$ and $(B_2,B_3)$, support conditions, and the vanishing of two auxiliary elements built from $X$, $B_0$ and $B_2$); this is the exact algebraic core of the avoidance argument.
--
--   **Formalization Note** The file consists only of local instances (`deficiencyOrder`, `scalingDefectOrder`, `fourFixedOrder`, `defectSandwichOrder`, `representedDefectOrder` and their `StarOrderedRing` companions), each setting the partial order to Mathlib's `CStarAlgebra.spectralOrder` and the star-ordered-ring structure to `CStarAlgebra.spectralOrderedRing`. The theorems of the module, for instance `represented_mixed_estimate` and `four_fixed_impossible`, are published separately.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Defect.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Defect.lean by skeleton subtraction
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

-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
local instance deficiencyOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance deficiencyStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
local instance scalingDefectOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance scalingDefectStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
local instance fourFixedOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance fourFixedStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

end MainGap

namespace MainGap
variable {A D : Type*} [CStarAlgebra A] [CStarAlgebra D]
local instance defectSandwichOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance defectSandwichStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance representedDefectOrder : PartialOrder D := CStarAlgebra.spectralOrder D
local instance representedDefectStarOrder : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D

end MainGap

end

end OAI


