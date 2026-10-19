-- Prove2me | Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Shrinking
-- name    : OAI_Analysis_CStarAlgebra_PureInfiniteness_Shrinking
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:46:32.366281+00:00
-- url     : https://prove2.me/theorems/c6fa04e9-35ff-47f0-83f8-8b8092063129
-- title:
--   Entrywise amplification of $*$-homomorphisms to matrices, and the norm-signal condition
-- statement:
--   Let $A$ and $B$ be possibly non-unital C$^*$-algebras. Matrices over a C$^*$-algebra carry their C$^*$-norm. The minimal unitization of $A$ is $\tilde A=\mathbb{C}\oplus A$ with product $(\lambda,a)(\mu,b)=(\lambda\mu,\lambda b+\mu a+ab)$, and $A$ embeds in it as $a\mapsto(0,a)$. A *representation* of a unital C$^*$-algebra $D$ is a complex Hilbert space $H$ together with a unital $*$-homomorphism $R:D\to B(H)$ into the bounded operators on $H$. The file introduces two objects.
--
--   1. **Matrix amplification.** For a $*$-homomorphism $\pi:A\to B$ and an $m\times n$ matrix $x=(x_{ij})$ with entries in $A$,
--   $$\pi^{(m,n)}(x)=\bigl(\pi(x_{ij})\bigr)_{0\le i<m,\ 0\le j<n},$$
--   the $m\times n$ matrix over $B$ obtained by applying $\pi$ entrywise.
--
--   2. **Norm signal.** For $a,p\in A$, the condition $\operatorname{Sig}(a,p)$: for every representation $(H,R)$ of $\tilde A$,
--   $$\|R(a)\|>\tfrac12\ \Longrightarrow\ \|R(p)\|=1 .$$
--
--   The file also fixes, as local instances, the spectral order ($x\le y$ iff $y-x$ is self-adjoint with spectrum in $[0,\infty)$) on $A$, on $\tilde A$, and on $B(J)$ for complex Hilbert spaces $J$.
--
--   Matrix amplification is compatible with products and conjugate transposes, so it transports Cuntz comparison of matrices, and hence proper infiniteness, along $*$-homomorphisms, in particular from $A$ into its unitization. The norm signal records that an element $p$, typically a positive contraction in the hereditary subalgebra of $a$, still detects $a$ in every representation: wherever $a$ has norm above $1/2$, $p$ attains norm $1$. This is the information that the shrinking and separation steps preserve when they replace $a$ by a smaller hereditary piece.
--
--   **Formalization Note** `matrixMap π x` acts on `CStarMatrix (Fin m) (Fin n) A`. `NormSignal a p` quantifies over `HilbertRep.{u,u} (Unitization ℂ A)`, that is, over Hilbert spaces in the same universe `u` as $A$, and `R.hom` is a unital star-algebra homomorphism. The order instances (`shrinkingPartialOrder` and its variants) are declared `local`, so they are in force only inside this file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Shrinking.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Shrinking.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
universe u v
variable {A : Type u} [CStarAlgebra A]
local instance shrinkingPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance shrinkingStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance shrinkingOperatorPartialOrder (J : Type*) [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] :
    PartialOrder (J →L[ℂ] J) := CStarAlgebra.spectralOrder _
local instance shrinkingOperatorStarOrderedRing (J : Type*) [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] :
    StarOrderedRing (J →L[ℂ] J) := CStarAlgebra.spectralOrderedRing _

end MainGap

namespace MainGap
variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

def matrixMap (π : A →⋆ₙₐ[ℂ] B) {m n : ℕ} (x : CStarMatrix (Fin m) (Fin n) A) :
    CStarMatrix (Fin m) (Fin n) B := CStarMatrix.ofMatrix (fun i j => π (x i j))

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance shrinkingHerPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance shrinkingHerStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance shrinkingHerUnitizationPartialOrder : PartialOrder (Unitization ℂ A) :=
  CStarAlgebra.spectralOrder _
local instance shrinkingHerUnitizationStarOrderedRing : StarOrderedRing (Unitization ℂ A) :=
  CStarAlgebra.spectralOrderedRing _

end MainGap

namespace MainGap
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
local instance shrinkingNonunitalPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance shrinkingNonunitalStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance shrinkingNonunitalUnitizationPartialOrder : PartialOrder (Unitization ℂ A) :=
  CStarAlgebra.spectralOrder _
local instance shrinkingNonunitalUnitizationStarOrderedRing : StarOrderedRing (Unitization ℂ A) :=
  CStarAlgebra.spectralOrderedRing _

def NormSignal (a p : A) : Prop :=
  ∀ R : HilbertRep.{u,u} (Unitization ℂ A), (1/2:ℝ)<‖R.hom (a : Unitization ℂ A)‖ →
    ‖R.hom (p : Unitization ℂ A)‖=1

end MainGap

end

end OAI


