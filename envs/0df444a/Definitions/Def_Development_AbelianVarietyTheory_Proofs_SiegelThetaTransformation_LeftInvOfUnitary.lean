-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LeftInvOfUnitary
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LeftInvOfUnitary
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:40:40.257476+00:00
-- url     : https://prove2.me/theorems/9ba7827a-63b7-4c75-9993-76107fa02ba2
-- title:
--   Left Inv Of Unitary
-- statement:
--   Definitions and structural lemmas for Left Inv Of Unitary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LeftInvOfUnitary.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HaarUpqIsMulRightInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Matrix Formalism.BasicNotions
open scoped ENNReal
namespace GlobalTheory.VolPairExists
variable {P Q : ℕ}
theorem jpq_mul_self : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  unfold Formalism.UG.Jpq
  simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
theorem left_inv_of_unitary {u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ}
    (h : uᴴ * Formalism.UG.Jpq P Q * u = Formalism.UG.Jpq P Q) : Formalism.UG.Jpq P Q * uᴴ * Formalism.UG.Jpq P Q * u = 1 := by
  calc Formalism.UG.Jpq P Q * uᴴ * Formalism.UG.Jpq P Q * u = Formalism.UG.Jpq P Q * (uᴴ * Formalism.UG.Jpq P Q * u) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, jpq_mul_self]
def mkU (u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (h : uᴴ * Formalism.UG.Jpq P Q * u = Formalism.UG.Jpq P Q) :
    UpqT P Q :=
  (⟨⟨u, Formalism.UG.Jpq P Q * uᴴ * Formalism.UG.Jpq P Q, mul_eq_one_comm.1 (left_inv_of_unitary h),
    left_inv_of_unitary h⟩, h⟩ : Formalism.UG.Upq P Q)
variable {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ}
variable {A A' : Matrix (Fin P ⊕ Fin Q) (Fin n) ℂ} {L : Matrix (Fin n) (Fin P ⊕ Fin Q) ℂ}
end GlobalTheory.VolPairExists


