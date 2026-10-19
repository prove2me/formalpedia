-- Prove2me | Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Signal
-- name    : OAI_Analysis_CStarAlgebra_PureInfiniteness_Signal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:57:38.921376+00:00
-- url     : https://prove2.me/theorems/1d296c2f-37f8-47fb-9d8f-34d655944d32
-- title:
--   Spectral orders on a C*-algebra and on Hilbert-space operators, fixed for the signal estimates
-- statement:
--   Let $A$ be a possibly non-unital C$^*$-algebra over $\mathbb{C}$, and for a complex Hilbert space $H$ let $B(H)$ be the C$^*$-algebra of bounded linear operators on $H$. The file equips $A$, and each $B(H)$, with the spectral partial order
--   $$x\le y\iff y-x\ \text{is self-adjoint and its quasispectrum is contained in }[0,\infty).$$
--   For a non-unital algebra the quasispectrum is the spectrum computed in the unitization. In both cases the result is a star-ordered ring, whose nonnegative elements are the elements of the form $z^*z$. On $B(H)$ this means that $T\ge0$ iff $\langle\xi,T\xi\rangle\ge0$ for every $\xi\in H$.
--
--   No other objects are defined. The orders are declared separately for the sections of the module. They are the orders in which its operator inequalities are phrased, both in $A$ and in the representations of $A$ that appear in the norm-signal arguments. For example: if $a\ge0$, $\delta\ge0$ and $p\in\operatorname{Her}((a-\delta)_+)$, then $\delta\,p^*p\le p^*ap$. Here $(a-\delta)_+$ is $a$ cut down by $t\mapsto\max(t-\delta,0)$ through functional calculus, and $\operatorname{Her}(h)$ is the norm closure of $\{hxh^*:x\in A\}$.
--
--   **Formalization Note** The eight members (`signalCutPartialOrder`, `signalComparisonPartialOrder`, `signalOperatorPartialOrder`, `signalCoefficientPartialOrder`, `signalProductsPartialOrder` and the matching `StarOrderedRing` instances) are `local instance`s set to Mathlib's `CStarAlgebra.spectralOrder` and `CStarAlgebra.spectralOrderedRing`; the operator versions are parametrized by the Hilbert space $H$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Signal.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Signal.lean by skeleton subtraction
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

-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance signalCutPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance signalCutStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

end MainGap

namespace MainGap
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
local instance signalComparisonPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance signalComparisonStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance signalOperatorPartialOrder (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :
    PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance signalOperatorStarOrderedRing (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :
    StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance signalCoefficientPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance signalCoefficientStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance signalProductsPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance signalProductsStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

end MainGap

end

end OAI


