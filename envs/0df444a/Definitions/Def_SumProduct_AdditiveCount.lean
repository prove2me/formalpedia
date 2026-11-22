-- Prove2me | Definitions.Def_SumProduct_AdditiveCount
-- name    : SumProduct_AdditiveCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T23:47:11.182827+00:00
-- url     : https://prove2.me/theorems/0bee4dca-00ec-4f56-8996-cee5034fc1d6
-- title:
--   Additive Count
-- statement:
--   Definitions and structural lemmas for Additive Count, from Mathlib Initiative and contributors's pinned A real sum-product counterexample conditional on Martinet’s tower theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean

import Definitions.Def_SumProduct_Boxes
set_option autoImplicit true
open scoped NumberField
open Pointwise
namespace SumProduct
open NumberField NumberField.InfinitePlace in
/-- The Minkowski (real) embedding of a totally real field, `α ↦ (σ_w α)_w`, into the coordinate
space `InfinitePlace K → ℝ`. -/
noncomputable def realEmbed (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (α : 𝓞 K) : NumberField.InfinitePlace K → ℝ :=
  fun w => embedding_of_isReal (NumberField.IsTotallyReal.isReal w) (α : K)
open NumberField NumberField.mixedEmbedding in
/-- The additive embedding `𝒪_K ↪ mixedSpace K` (the mixed embedding restricted to the integers).
Its range is `mixedEmbedding.integerLattice K`. -/
noncomputable def latticeEmbed (K : Type*) [Field K] [NumberField K] : 𝓞 K →+ mixedSpace K :=
  ((mixedEmbedding K).comp (algebraMap (𝓞 K) K)).toAddMonoidHom
theorem latticeEmbed_injective {K : Type*} [Field K] [NumberField K] :
    Function.Injective (latticeEmbed K) :=
  (NumberField.mixedEmbedding_injective K).comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)
open NumberField NumberField.mixedEmbedding in
/-- The range of `latticeEmbed` is exactly the integer lattice. -/
theorem range_latticeEmbed (K : Type*) [Field K] [NumberField K] :
    Set.range (latticeEmbed K) = ↑(mixedEmbedding.integerLattice K) := by
  rw [mixedEmbedding.integerLattice, LinearMap.coe_range]
  rfl
open NumberField NumberField.mixedEmbedding in
/-- The bijection `𝒪_K ≃ integerLattice K` induced by the (injective) lattice embedding. -/
noncomputable def latticeEquiv (K : Type*) [Field K] [NumberField K] :
    𝓞 K ≃ ↥(mixedEmbedding.integerLattice K) :=
  (Equiv.ofInjective (latticeEmbed K) latticeEmbed_injective).trans
    (Equiv.setCongr (range_latticeEmbed K))
end SumProduct


