-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TracePowGrassmannBlockCurvatureSupertraceZero
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TracePowGrassmannBlockCurvatureSupertraceZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:49.586624+00:00
-- url     : https://prove2.me/theorems/d34bbd92-660f-45c0-a8e6-b8b7775b47e3
-- title:
--   Trace Pow Grassmann Block Curvature Supertrace Zero
-- statement:
--   Definitions and structural lemmas for Trace Pow Grassmann Block Curvature Supertrace Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TracePowGrassmannBlockCurvatureSupertraceZero.lean

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_VecMulVecComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial TensorProduct
namespace GlobalTheory.GrassModel.SuperTrace
variable {n : ℕ}
def Sg (m : ℕ) (z : Big n) : Prop :=
  ∀ a : Fin n, ((1 : Ext n) ⊗ₜ vec n a) * z = (-1) ^ m * (z * ((1 : Ext n) ⊗ₜ vec n a))
def MSg {r s : Type*} (m : ℕ) (M : Matrix r s (Big n)) : Prop := ∀ i j, Sg m (M i j)
end GlobalTheory.GrassModel.SuperTrace


