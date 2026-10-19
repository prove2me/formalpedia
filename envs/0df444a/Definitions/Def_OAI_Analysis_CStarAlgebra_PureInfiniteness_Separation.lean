-- Prove2me | Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Separation
-- name    : OAI_Analysis_CStarAlgebra_PureInfiniteness_Separation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:51:36.360002+00:00
-- url     : https://prove2.me/theorems/7097ea4e-8aba-452f-beca-994e4d384fab
-- title:
--   The spectral order on a C*-algebra, fixed for the iterated separation step
-- statement:
--   Let $A$ be a possibly non-unital C$^*$-algebra over $\mathbb{C}$. The file equips $A$ with its spectral partial order: for $x,y\in A$,
--   $$x\le y\iff y-x\ \text{is self-adjoint and its quasispectrum is contained in }[0,\infty).$$
--   For a non-unital algebra the quasispectrum is the spectrum computed in the unitization. With this order $A$ is a star-ordered ring: $x\le y$ holds if and only if $y-x$ is a finite sum of elements of the form $z^*z$, and in a C$^*$-algebra such sums are themselves of the form $z^*z$. So the nonnegative elements are exactly the usual positive elements.
--
--   No other objects are defined. This is the order in which the hypotheses $0\le a$, $0\le b$ and the conclusions $0\le p$, $0\le q$ of the separation results are read. The main such result takes positive contractions $a,b$, a contraction $c$ and a number $\zeta>0$ in an algebra where every positive element is properly infinite. It produces positive contractions $p\in\operatorname{Her}(a)$ and $q\in\operatorname{Her}(b)$ with $\|x\,c\,k\|\le\kappa\|x\|\|k\|$ for all $x\in\operatorname{Her}(p)$, $k\in\operatorname{Her}(q)$ and some $\kappa<\zeta$, together with norm-signal conditions linking $p$ to $a$ and $q$ to $b$. Here $\operatorname{Her}(h)$ is the norm closure of $\{hxh^*:x\in A\}$.
--
--   **Formalization Note** The two members `separationPartialOrder` and `separationStarOrderedRing` are `local instance`s set to Mathlib's `CStarAlgebra.spectralOrder A` and `CStarAlgebra.spectralOrderedRing A`; they are visible only inside this file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Separation.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Separation.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
local instance separationPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance separationStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

end MainGap

end

end OAI


