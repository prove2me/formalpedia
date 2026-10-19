-- Prove2me | Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Diagonalization
-- name    : OAI_Analysis_CStarAlgebra_PureInfiniteness_Diagonalization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:59:56.023616+00:00
-- url     : https://prove2.me/theorems/d24c4410-9743-4064-b933-c247acae9ba7
-- title:
--   The spectral order on a non-unital C*-algebra, fixed for the diagonalization theorems
-- statement:
--   Let $A$ be a possibly non-unital C$^*$-algebra over $\mathbb{C}$. The file equips $A$ (twice, once for each section of the module) with the spectral partial order
--   $$x\le y\iff y-x\ \text{is self-adjoint and its quasispectrum is contained in }[0,\infty),$$
--   where the quasispectrum is the spectrum computed in the unitization. With this order $A$ is a star-ordered ring, whose nonnegative elements are exactly the elements of the form $z^*z$.
--
--   No other objects are defined. The positivity hypotheses of the diagonalization theorems of the module are read in this order. Assume that every positive $h\in A$ is properly infinite, meaning that the diagonal matrix $\operatorname{diag}(h,h)\in M_2(A)$ is a norm limit of products $r_j^*\,h\,r_j$ with $1\times2$ matrices $r_j$ over $A$. The main theorem then states that for all positive $a,b\in A$, every $c\in A$ and every $\varepsilon>0$ there are $s,t\in A$ with
--   $$\|s^*as-a\|<\varepsilon,\qquad\|t^*bt-b\|<\varepsilon,\qquad\|s^*ct\|<\varepsilon .$$
--   Specializing to $a=x^2$, $b=y^2$, $c=xy$ with $x,y\ge0$ gives strong pure infiniteness in the form used in this development.
--
--   **Formalization Note** The members `boundedDiagonalizationPartialOrder`, `boundedDiagonalizationStarOrderedRing`, `diagonalizationPartialOrder` and `diagonalizationStarOrderedRing` are `local instance`s set to Mathlib's `CStarAlgebra.spectralOrder A` and `CStarAlgebra.spectralOrderedRing A`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Diagonalization.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Diagonalization.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Nonvanishing
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Compression
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Shrinking
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Products
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Separation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_IdealDetection
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_IdealComparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Signal

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance boundedDiagonalizationPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance boundedDiagonalizationStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance diagonalizationPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance diagonalizationStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

end MainGap

end

end OAI


