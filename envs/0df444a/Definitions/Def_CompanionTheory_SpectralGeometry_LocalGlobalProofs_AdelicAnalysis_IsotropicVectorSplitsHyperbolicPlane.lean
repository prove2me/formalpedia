-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IsotropicVectorSplitsHyperbolicPlane
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IsotropicVectorSplitsHyperbolicPlane
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:30.457797+00:00
-- url     : https://prove2.me/theorems/157503f5-fdfb-4391-b0ea-2d81c12b323d
-- title:
--   Isotropic Vector Splits Hyperbolic Plane
-- statement:
--   Definitions and structural lemmas for Isotropic Vector Splits Hyperbolic Plane, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IsotropicVectorSplitsHyperbolicPlane.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.HypSplit
section Alg
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)
theorem hE_eq_dot (u v : Fin M → E) :
    hE σ J u v = Matrix.vecMul (fun i => σ (u i)) J ⬝ᵥ v := by
  simp only [hE, hform, Matrix.vecMul, dotProduct, Finset.sum_mul, RingHom.coe_coe]
  exact Finset.sum_comm
def hLin (u : Fin M → E) : (Fin M → E) →ₗ[E] E where
  toFun := hE σ J u
  map_add' v w := by simp only [hE_eq_dot, dotProduct_add]
  map_smul' a v := by simp only [hE_eq_dot, dotProduct_smul, RingHom.id_apply]
variable {σ J}
end Alg
end GlobalTheory.CompanionTheory.SW.HypSplit


