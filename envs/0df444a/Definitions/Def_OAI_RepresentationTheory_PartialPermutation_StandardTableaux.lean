-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_StandardTableaux
-- name    : OAI_RepresentationTheory_PartialPermutation_StandardTableaux
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:24:25.71065+00:00
-- url     : https://prove2.me/theorems/c93b5f49-35ab-4518-9ae0-bd1cd1747288
-- title:
--   Standard fillings of finite posets and counts of standard Young tableaux
-- statement:
--   Let $\alpha$ be a finite partially ordered set with $n=|\alpha|$ elements. A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}\times\mathbb{N}$ ($i$ the row, $j$ the column, both starting at $0$) that is closed downwards in the componentwise order; $|\mu|$ is its number of cells, $\mu_1$ the length of its first row and $\mu_1'$ the length of its first column.
--
--   1. **Standard fillings.** A standard filling of $\alpha$ is a bijection $e\colon\alpha\to\{0,1,\dots,n-1\}$ that is strictly increasing: $a<b$ implies $e(a)<e(b)$. There are finitely many standard fillings.
--   2. **Standard tableau count.** For a Young diagram $\mu$, the number $f^\mu$ is the number of standard fillings of the cells of $\mu$ with the componentwise order. Strict monotonicity for this order means that the entries increase along every row and down every column, so $f^\mu$ is the number of standard Young tableaux of shape $\mu$ (filled with $0,\dots,|\mu|-1$).
--   3. **Longest first line.** $\ell(\mu)=\max(\mu_1,\mu_1')$.
--   4. **Deficit.** $\delta(\mu)=|\mu|-\ell(\mu)$, the number of cells not in the longer of the first row and the first column.
--   5. **Chosen filling.** Every finite poset has a specific standard filling, obtained by numbering its elements along a fixed linear extension of the order; in particular standard fillings always exist.
--
--   In formulas,
--
--   $$
--   f^\mu=\#\big\{e\colon\mu\to\{0,\dots,|\mu|-1\}\ \text{bijective}\ :\ e(i,j)<e(i',j')\ \text{whenever } i\le i',\ j\le j',\ (i,j)\neq(i',j')\big\},\qquad \delta(\mu)=|\mu|-\max(\mu_1,\mu_1').
--   $$
--
--   The number $f^\mu$ is the dimension of the irreducible representation of the symmetric group on $|\mu|$ letters labelled by $\mu$, and the deficit measures how far $\mu$ is from a single row or a single column; lower bounds for $f^\mu$ in terms of the deficit are what control reciprocal degree sums $\sum_\mu (f^\mu)^{-u}$.
--
--   **Formalization Note** `StandardFilling α` is the subtype of equivalences from $\alpha$ to `Fin` of the cardinality of $\alpha$ that are `StrictMono`, with an unnamed `Fintype` instance; `standardCount μ` counts standard fillings of `μ.cells` with the order induced from the product order on pairs of naturals; `maxLine μ` is the maximum of `μ.rowLen 0` and `μ.colLen 0`; `deficit μ` uses natural-number subtraction, which never truncates here because the first row and first column lie inside $\mu$; and `chosenFilling α` is built from Mathlib's `LinearExtension α` through the order isomorphism with `Fin`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/StandardTableaux.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/StandardTableaux.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the PartialPermutation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Plancherel
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TrivialRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ConvolutionKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ComponentGeometry
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SmallKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ProjectionCovers
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Restriction
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicMatrices
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Equivalences
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SymmetricTransfer

namespace OAI

section
namespace PartialPermutation
namespace Tableau

noncomputable section
open Finset

def StandardFilling (α : Type*) [Fintype α] [PartialOrder α] :=
  {e : α ≃ Fin (Fintype.card α) // StrictMono e}

instance (α : Type*) [Fintype α] [PartialOrder α] : Fintype (StandardFilling α) :=
  by
    classical
    unfold StandardFilling
    infer_instance

def standardCount (μ : YoungDiagram) : ℕ :=
  Fintype.card (StandardFilling μ.cells)

def maxLine (μ : YoungDiagram) : ℕ := max (μ.rowLen 0) (μ.colLen 0)
def deficit (μ : YoungDiagram) : ℕ := μ.cells.card - maxLine μ

def chosenFilling (α : Type*) [Fintype α] [PartialOrder α] : StandardFilling α := by
  letI : Fintype (LinearExtension α) := inferInstanceAs (Fintype α)
  let e : LinearExtension α ≃o Fin (Fintype.card α) :=
    (Fintype.orderIsoFinOfCardEq (LinearExtension α) (by rfl)).symm
  refine ⟨{toFun := fun a => e (toLinearExtension a)
           invFun := fun i => (e.symm i : α)
           left_inv := ?_
           right_inv := ?_}, ?_⟩
  · intro a
    exact e.symm_apply_apply a
  · intro i
    exact e.apply_symm_apply i
  · intro a b hab
    apply e.strictMono
    apply lt_of_le_of_ne (toLinearExtension.monotone hab.le)
    intro h
    exact (ne_of_lt hab) h

end
end Tableau
end PartialPermutation
end

end OAI


