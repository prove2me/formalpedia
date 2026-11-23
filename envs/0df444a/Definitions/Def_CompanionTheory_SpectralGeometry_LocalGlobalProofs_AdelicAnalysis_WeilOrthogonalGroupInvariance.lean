-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WeilOrthogonalGroupInvariance
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WeilOrthogonalGroupInvariance
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:50:48.970806+00:00
-- url     : https://prove2.me/theorems/a8f0fef1-418a-4cba-a728-45e15c0bf0f7
-- title:
--   Weil Orthogonal Group Invariance
-- statement:
--   Definitions and structural lemmas for Weil Orthogonal Group Invariance, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WeilOrthogonalGroupInvariance.lean

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Core.OrthMeas
def mulVecEquiv {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (g : Matrix ι ι R) (hdet : IsUnit g.det) : (ι → R) ≃+ (ι → R) where
  toFun x := g *ᵥ x
  invFun x := g⁻¹ *ᵥ x
  left_inv x := by simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hdet]
  right_inv x := by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g hdet]
  map_add' := Matrix.mulVec_add g
end GlobalTheory.CompanionTheory.SW.Core.OrthMeas


