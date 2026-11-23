-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulEqOfNormOne
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulEqOfNormOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:33:18.755902+00:00
-- url     : https://prove2.me/theorems/ebf0e1ce-0f5b-46e7-94a5-79839e974fdf
-- title:
--   Map Mul Eq Of Norm One
-- statement:
--   Definitions and structural lemmas for Map Mul Eq Of Norm One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MapMulEqOfNormOne.lean

import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
namespace GlobalTheory.CompanionTheory.SW.NormOneHaar
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
def mulEquiv (u v : K) (h : u * v = 1) : K ≃ₜ+ K where
  toFun y := u * y
  invFun y := v * y
  left_inv y := by
    show v * (u * y) = y
    rw [← mul_assoc, mul_comm v u, h, one_mul]
  right_inv y := by
    show u * (v * y) = y
    rw [← mul_assoc, h, one_mul]
  map_add' x y := mul_add u x y
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id
def invEquiv (σ : K →+* K) (hc : Continuous σ) (hi : ∀ y, σ (σ y) = y) : K ≃ₜ+ K where
  toFun := σ
  invFun := σ
  left_inv := hi
  right_inv := hi
  map_add' := map_add σ
  continuous_toFun := hc
  continuous_invFun := hc
variable [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
end GlobalTheory.CompanionTheory.SW.NormOneHaar


