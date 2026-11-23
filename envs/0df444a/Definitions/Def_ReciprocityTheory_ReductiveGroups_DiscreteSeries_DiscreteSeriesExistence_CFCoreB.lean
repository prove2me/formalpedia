-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreB
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:41:31.88817+00:00
-- url     : https://prove2.me/theorems/cdaadd50-ad30-4dfe-8bed-c9e50dc8f760
-- title:
--   CFCore B
-- statement:
--   Definitions and structural lemmas for CFCore B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section Intertwine
variable {M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {E' : Fin n → Fin n → Module.End ℂ M'}
end Intertwine
section Prod
variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
def prodE (E₁ : Fin n → Fin n → Module.End ℂ M₁) (E₂ : Fin n → Fin n → Module.End ℂ M₂) :
    Fin n → Fin n → Module.End ℂ (WithLp 2 (M₁ × M₂)) := fun a b =>
  (WithLp.linearEquiv 2 ℂ (M₁ × M₂)).symm.toLinearMap ∘ₗ (LinearMap.prodMap (E₁ a b) (E₂ a b)) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (M₁ × M₂)).toLinearMap
def prFst : WithLp 2 (M₁ × M₂) →ₗ[ℂ] M₁ := LinearMap.fst ℂ M₁ M₂ ∘ₗ (WithLp.linearEquiv 2 ℂ (M₁ × M₂)).toLinearMap
def prSnd : WithLp 2 (M₁ × M₂) →ₗ[ℂ] M₂ := LinearMap.snd ℂ M₁ M₂ ∘ₗ (WithLp.linearEquiv 2 ℂ (M₁ × M₂)).toLinearMap
variable {E₁ : Fin n → Fin n → Module.End ℂ M₁} {E₂ : Fin n → Fin n → Module.End ℂ M₂}
end Prod
section ProdUnitary
variable {M₁ M₂ : Type*} [NormedAddCommGroup M₁] [InnerProductSpace ℂ M₁] [NormedAddCommGroup M₂]
  [InnerProductSpace ℂ M₂] {ε : Fin n → Bool}
  {E₁ : Fin n → Fin n → Module.End ℂ M₁} {E₂ : Fin n → Fin n → Module.End ℂ M₂}
end ProdUnitary
end ReciprocityTheory.ChartRestriction.DS


