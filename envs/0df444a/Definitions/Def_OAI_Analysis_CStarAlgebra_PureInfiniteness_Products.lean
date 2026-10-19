-- Prove2me | Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Products
-- name    : OAI_Analysis_CStarAlgebra_PureInfiniteness_Products
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:50:11.944139+00:00
-- url     : https://prove2.me/theorems/2f3dc9ec-1fea-4164-9cf9-8b4b11f57476
-- title:
--   Coordinate evaluations and bounded families in $\ell^\infty$-products of C*-algebras
-- statement:
--   Let $I$ be an index set and $(E_i)_{i\in I}$ a family of possibly non-unital C$^*$-algebras. Their $\ell^\infty$-product
--   $$\prod_{i\in I}^{\infty}E_i=\Bigl\{\,f=(f_i)_{i\in I}\ :\ f_i\in E_i\text{ for all }i,\ \ \sup_{i\in I}\|f_i\|<\infty\Bigr\},$$
--   with coordinatewise algebraic operations and adjoint and with the supremum norm, is again a C$^*$-algebra. The file introduces two constructions.
--
--   1. **Coordinate evaluation.** For $i\in I$, the map
--   $$\mathrm{ev}_i:\prod_{j\in I}^{\infty}E_j\to E_i,\qquad f\mapsto f_i ,$$
--   which is additive, multiplicative, $\mathbb{C}$-linear and commutes with the adjoint, that is, a (non-unital) $*$-homomorphism.
--
--   2. **Assembling a bounded family.** Given elements $f_i\in E_i$ and a real number $M$ with $\|f_i\|\le M$ for every $i$, the element $[f]_M$ of the $\ell^\infty$-product whose coordinates are the $f_i$, so that $\mathrm{ev}_i([f]_M)=f_i$.
--
--   In addition, the file fixes as local instances the spectral order ($x\le y$ iff $y-x$ is self-adjoint with spectrum in $[0,\infty)$) on each factor $E_i$, on the product, and on the algebra $\ell^\infty(\mathbb{N},A)$ of bounded sequences in a single C$^*$-algebra $A$.
--
--   These constructions make it possible to pack a sequence of elements, one for each $n\in\mathbb{N}$ and all bounded by a common constant, into a single element of $\ell^\infty(\mathbb{N},A)$, to apply a qualitative statement there, and to read off information in every coordinate through the $*$-homomorphisms $\mathrm{ev}_n$. This is how uniform constants are extracted by contradiction in the shrinking step.
--
--   **Formalization Note** The product is Mathlib's `lp E ∞`. `lpEval i` is the bundled non-unital star-algebra homomorphism, `lpBuild f M h` takes the uniform bound `h : ∀ i, ‖f i‖ ≤ M` as an argument, and `lpEval_apply`, `lpBuild_apply` are the evaluation simp lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Products.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Products.lean by skeleton subtraction
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

-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance boundedSlotsOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance boundedSlotsStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

end MainGap

namespace MainGap
open scoped ENNReal
variable {I : Type*} {E : I → Type*} [∀ i, NonUnitalCStarAlgebra (E i)]
local instance productFactorOrder (i : I) : PartialOrder (E i) := CStarAlgebra.spectralOrder _
local instance productFactorStarOrder (i : I) : StarOrderedRing (E i) := CStarAlgebra.spectralOrderedRing _
local instance boundedProductOrder : PartialOrder (lp E ∞) := CStarAlgebra.spectralOrder _
local instance boundedProductStarOrder : StarOrderedRing (lp E ∞) := CStarAlgebra.spectralOrderedRing _

def lpEval (i : I) : lp E ∞ →⋆ₙₐ[ℂ] E i where
  toFun f := f i
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

@[simp] lemma lpEval_apply (i : I) (f : lp E ∞) : lpEval i f=f i := rfl

def lpBuild (f : ∀ i, E i) (M : ℝ) (h : ∀ i, ‖f i‖ ≤ M) : lp E ∞ :=
  ⟨f, memℓp_infty ⟨M, by rintro t ⟨i,rfl⟩; exact h i⟩⟩

@[simp] lemma lpBuild_apply (f : ∀ i, E i) (M : ℝ) (h : ∀ i, ‖f i‖ ≤ M) (i : I) :
    lpBuild f M h i = f i := rfl

end MainGap

namespace MainGap
open scoped ENNReal
variable {I : Type*} {E : I → Type*} [∀ i, NonUnitalCStarAlgebra (E i)] [DecidableEq I]

end MainGap

namespace MainGap
open scoped ENNReal
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
local instance sequenceFactorOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance sequenceFactorStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance boundedSequenceOrder : PartialOrder (lp (fun _ : ℕ => A) ∞) := CStarAlgebra.spectralOrder _
local instance boundedSequenceStarOrder : StarOrderedRing (lp (fun _ : ℕ => A) ∞) := CStarAlgebra.spectralOrderedRing _

end MainGap

end

end OAI


