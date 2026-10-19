-- Prove2me | Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Avoidance
-- name    : OAI_Analysis_CStarAlgebra_PureInfiniteness_Avoidance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:38:00.673255+00:00
-- url     : https://prove2.me/theorems/083eabec-a6c1-4b55-ad58-7de2a03e35f9
-- title:
--   Hilbert-space representations of a unital $C^*$-algebra as bundled objects
-- statement:
--   Let $A$ be a unital $C^*$-algebra. A Hilbert-space representation of $A$ is a pair $R=(H_R,\pi_R)$ consisting of a complex Hilbert space $H_R$ and a unital $*$-homomorphism
--
--   $$
--   \pi_R:A\to B(H_R),
--   $$
--
--   where $B(H_R)$ is the $C^*$-algebra of bounded linear operators on $H_R$; thus $\pi_R$ is $\mathbb{C}$-linear and multiplicative, $\pi_R(a^*)=\pi_R(a)^*$ and $\pi_R(1)=1$. The Hilbert spaces are taken from a fixed universe of types, and the zero space is allowed.
--
--   The file also fixes the orders used in its module: on $A$, and on every operator algebra $B(J)$ of a complex Hilbert space $J$, $a\le b$ means that $b-a$ is positive (self-adjoint with spectrum in $[0,\infty)$; for operators, equivalently $\langle x,(b-a)x\rangle\ge0$ for all $x\in J$).
--
--   Bundling representations lets statements quantify over all of them. The module's main result, stated separately, is the four-choice avoidance theorem. Let $X\in A$ be positive, let $(X-\tfrac1{32})_+$ be $X$ under the functional calculus with $t\mapsto\max(t-\tfrac1{32},0)$, and let $\operatorname{Her}\bigl((X-\tfrac1{32})_+\bigr)$ be the norm closure of $(X-\tfrac1{32})_+A(X-\tfrac1{32})_+$. If every positive element $h$ of this hereditary subalgebra is properly infinite ($\operatorname{diag}(h,h)$ is a norm limit of $r_j^*hr_j$ with row vectors $r_j\in A^{1\times2}$), then for all $B_0,\dots,B_3\in A$ there are contractions $T_0,\dots,T_3$ in $\operatorname{Her}\bigl((X-\tfrac1{32})_+\bigr)$ such that no representation $R$ with $\|\pi_R(X)\|>\tfrac14$ satisfies $\pi_R(T_j)=\pi_R(B_j)$ for all $j$.
--
--   **Formalization Note** `HilbertRep A` is a structure with a carrier type `H` in a universe `v` (a parameter), instance fields making `H` a complete complex inner product space (registered as instances), and `hom`, a unital star-algebra homomorphism from `A` into the continuous linear operators on `H`. The local instances (`avoidancePartialOrder`, `avoidanceOperatorPartialOrder`, the `avoidanceLimit` variants for a section with indexed Hilbert spaces, and their star-ordered-ring companions) select Mathlib's spectral order.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Avoidance.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Avoidance.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
open Filter
open scoped Topology
universe u v
variable {ι : Type*} {A : Type u} [CStarAlgebra A]
local instance avoidanceLimitPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance avoidanceLimitStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance avoidanceLimitOperatorPartialOrder (J : Type*) [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] :
    PartialOrder (J →L[ℂ] J) := CStarAlgebra.spectralOrder _
local instance avoidanceLimitOperatorStarOrderedRing (J : Type*) [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] :
    StarOrderedRing (J →L[ℂ] J) := CStarAlgebra.spectralOrderedRing _
variable {H : ι → Type v} [∀ i, NormedAddCommGroup (H i)]
  [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]

end MainGap

namespace MainGap
universe u v
open Filter
open scoped Topology
variable (A : Type u) [CStarAlgebra A]

structure HilbertRep where
  H : Type v
  [normed : NormedAddCommGroup H]
  [inner : InnerProductSpace ℂ H]
  [complete : CompleteSpace H]
  hom : A →⋆ₐ[ℂ] (H →L[ℂ] H)

attribute [instance] HilbertRep.normed HilbertRep.inner HilbertRep.complete

variable {A}
local instance avoidancePartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance avoidanceStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance avoidanceOperatorPartialOrder (J : Type*) [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] :
    PartialOrder (J →L[ℂ] J) := CStarAlgebra.spectralOrder _
local instance avoidanceOperatorStarOrderedRing (J : Type*) [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] :
    StarOrderedRing (J →L[ℂ] J) := CStarAlgebra.spectralOrderedRing _

end MainGap

end

end OAI


