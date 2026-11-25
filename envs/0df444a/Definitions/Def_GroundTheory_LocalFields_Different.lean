-- Prove2me | Definitions.Def_GroundTheory_LocalFields_Different
-- name    : GroundTheory_LocalFields_Different
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T05:53:37.536922+00:00
-- url     : https://prove2.me/theorems/f4294447-af10-4d92-a745-524b3cd96573
-- title:
--   Different
-- statement:
--   Definitions and structural lemmas for Different, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Different.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel Polynomial
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
attribute [local instance high] FaithfulSMul.to_isTorsionFree
section DVR
open IsDiscreteValuationRing
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
end DVR
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]
instance isSeparable_fractionRing_integer [Algebra.IsSeparable K L] :
    Algebra.IsSeparable (FractionRing 𝒪[K]) (FractionRing 𝒪[L]) := by
  have H : RingHom.comp (algebraMap (FractionRing 𝒪[K]) (FractionRing 𝒪[L]))
      ↑(FractionRing.algEquiv 𝒪[K] K).symm.toRingEquiv =
        RingHom.comp ↑(FractionRing.algEquiv 𝒪[L] L).symm.toRingEquiv (algebraMap K L) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors 𝒪[K])
    ext
    simp only [RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply 𝒪[K] 𝒪[L] L, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
  exact Algebra.IsSeparable.of_equiv_equiv _ _ H
def differentExponent : ℕ := multiplicity (𝓂[L]) (differentIdeal 𝒪[K] 𝒪[L])
variable [FiniteDimensional K L]
section Separable
variable [Algebra.IsSeparable K L]
end Separable
variable {K L}
section Separable
variable [Algebra.IsSeparable K L]
variable (K L)
instance finite_quotient_maximalIdeal : Finite (𝒪[K] ⧸ 𝓂[K]) :=
  inferInstanceAs (Finite 𝓀[K])
end Separable
section Tower
variable (K L M : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension K L] [ValuativeExtension L M] [ValuativeExtension K M]
  [FiniteDimensional K L] [FiniteDimensional L M] [Algebra.IsSeparable K M]
end Tower
section Discriminant
variable [Algebra.IsSeparable K L]
variable (K L)
end Discriminant
end GroundTheory.LocalField


