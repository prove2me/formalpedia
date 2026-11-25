-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartanDecompositionGeneralLinear
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartanDecompositionGeneralLinear
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T09:46:50.729207+00:00
-- url     : https://prove2.me/theorems/02654ae6-a2f0-5d62-b761-50754758738b
-- title:
--   Cartan Decomposition General Linear
-- statement:
--   Definitions and structural lemmas for Cartan Decomposition General Linear, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/CartanDecompositionGeneralLinear.lean

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk


set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
namespace GlobalTheory.CompanionTheory.QL.KAK
variable {F : Type} [Field F]
def dg {n : ℕ} (a : Fin n → Fˣ) : GL (Fin n) F where
  val := Matrix.diagonal fun i => (a i : F)
  inv := Matrix.diagonal fun i => (((a i)⁻¹ : Fˣ) : F)
  val_inv := by simp [Matrix.diagonal_mul_diagonal]
  inv_val := by simp [Matrix.diagonal_mul_diagonal]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
end GlobalTheory.CompanionTheory.QL.KAK


