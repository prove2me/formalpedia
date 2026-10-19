-- Prove2me | Definitions.Def_OAI_Analysis_BackwardIntertwiners_AlgebraCorollary
-- name    : OAI_Analysis_BackwardIntertwiners_AlgebraCorollary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T02:13:10.892982+00:00
-- url     : https://prove2.me/theorems/a68dd68d-2a96-4dc8-a03a-accfb74b51ff
-- title:
--   Separability of $\ell^2(\mathbb{Z})$ and of $L^2(\mathbb{Z}_2;\ell^2(\mathbb{Z}))$, and nontriviality of the latter
-- statement:
--   Let $\ell^2(\mathbb{Z})$ be the Hilbert space of square-summable complex sequences indexed by $\mathbb{Z}$, with standard basis vectors $e_j$. Let $\Omega=\mathbb{Z}_2$ be the ring of $2$-adic integers with the completion $\mu$ of its normalized Haar probability measure, and let
--   $$\mathcal H=L^2\bigl(\Omega,\mu;\ell^2(\mathbb{Z})\bigr)$$
--   be the Hilbert space of (equivalence classes of) square-integrable $\ell^2(\mathbb{Z})$-valued functions on $\Omega$. The file records three structural facts.
--
--   1. $\ell^2(\mathbb{Z})$ is separable: the countable set $\{e_j:j\in\mathbb{Z}\}$ has dense linear span.
--   2. $\mathcal H$ is nontrivial: $\mathcal H\neq\{0\}$.
--   3. $\mathcal H$ is separable.
--
--   The space $\mathcal H$ is the model space on which the project's operator is built. Together with the infinite-dimensionality of $\mathcal H$, these facts place $\mathcal H$ in the class of infinite-dimensional separable complex Hilbert spaces, all of which are isometrically isomorphic; this is what allows an operator constructed on $\mathcal H$ to be transported to an arbitrary infinite-dimensional separable complex Hilbert space.
--
--   **Formalization Note** The three facts are the typeclass instances `fiber_separable`, `global_nontrivial` and `global_separable`, for `Fiber = lp (fun _ : ℤ => ℂ) 2` and `GlobalHilbert = Lp Fiber 2 baseMeasure`. Separability of `Fiber` is proved from the density of the span of the vectors `lp.single 2 j 1`; nontriviality is derived from the project's lemma that $\mathcal H$ is not finite-dimensional; separability of $\mathcal H$ is obtained from Mathlib's general instances once separability of the fibre is available.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/AlgebraCorollary.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/AlgebraCorollary.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BackwardIntertwiners mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberTails
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ExplicitWeights
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_HaarBase
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberMaps
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_BackwardWeights
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_GlobalOperators
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ErgodicTransitivity
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_OrdinaryStructure
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_DiagonalSymbols
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_PolarDiagonals
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_HilbertClassification

namespace OAI

namespace BackwardIntertwiners
open Filter Topology MeasureTheory Set
noncomputable section
open scoped ENNReal
instance fiber_separable : TopologicalSpace.SeparableSpace Fiber := by
  let s : Set Fiber := Set.range (fun j : ℤ => lp.single 2 j (1:ℂ))
  have hs : TopologicalSpace.IsSeparable s := (Set.countable_range _).isSeparable
  have hc : closure (Submodule.span ℂ s : Set Fiber) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    let P := (Submodule.span ℂ s).topologicalClosure
    change v ∈ P
    apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
      (lp.hasSum_single (by norm_num : (2:ENNReal) ≠ ∞) v)
    apply Filter.Eventually.of_forall
    intro t
    apply P.sum_mem
    intro j _
    apply Submodule.le_topologicalClosure
    have hj : (lp.single 2 j (1:ℂ) : Fiber) ∈ Submodule.span ℂ s :=
      Submodule.subset_span ⟨j,rfl⟩
    simpa only [←lp.single_smul,smul_eq_mul,mul_one] using
      (Submodule.span ℂ s).smul_mem (v j) hj
  exact TopologicalSpace.isSeparable_univ_iff.mp (hc ▸ hs.span.closure)
instance global_nontrivial : Nontrivial GlobalHilbert :=
  not_subsingleton_iff_nontrivial.mp (by
    intro hs
    let := hs
    exact globalHilbert_infinite inferInstance)
instance global_separable : TopologicalSpace.SeparableSpace GlobalHilbert := by
  change TopologicalSpace.SeparableSpace (Lp Fiber 2 baseMeasure)
  let : Fact ((2:ENNReal) ≠ ∞) := ⟨by norm_num⟩
  infer_instance

end
end BackwardIntertwiners

end OAI


