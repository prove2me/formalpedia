-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SteinitzPiIdealsLinearEquivOfClassGroupProd
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SteinitzPiIdealsLinearEquivOfClassGroupProd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:08.182796+00:00
-- url     : https://prove2.me/theorems/38e1c85a-7178-41cb-a139-fdbb8edf11a4
-- title:
--   Steinitz Pi Ideals Linear Equiv Of Class Group Prod
-- statement:
--   Definitions and structural lemmas for Steinitz Pi Ideals Linear Equiv Of Class Group Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SteinitzPiIdealsLinearEquivOfClassGroupProd.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FinitelyManyIsoClassesProjectiveNumberField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
namespace GlobalTheory.SteinitzProd
variable {R : Type} [CommRing R] [IsDedekindDomain R]
def coprimeEquiv (I J : Ideal R) (u v : R) (hu : u ∈ I) (hv : v ∈ J) (h : u + v = 1) :
    (I × J) ≃ₗ[R] ((⊤ : Ideal R) × (I * J : Ideal R)) where
  toFun p := (⟨p.1 + p.2, Submodule.mem_top⟩,
    ⟨v * p.1 - u * p.2, Ideal.sub_mem _ (mul_comm (p.1 : R) v ▸ Ideal.mul_mem_mul p.1.2 hv)
      (Ideal.mul_mem_mul hu p.2.2)⟩)
  invFun q := (⟨u * q.1 + q.2, add_mem (Ideal.mul_mem_right _ I hu)
      ((Ideal.mul_le_left (I := I) (J := J)) q.2.2)⟩,
    ⟨v * q.1 - q.2, Ideal.sub_mem _ (Ideal.mul_mem_right _ J hv)
      ((Ideal.mul_le_right (I := I) (J := J)) q.2.2)⟩)
  map_add' p q := by
    ext <;> simp <;> ring
  map_smul' c p := by
    ext <;> simp <;> ring
  left_inv p := by
    ext
    · simp only; linear_combination (p.1 : R) * h
    · simp only; linear_combination (p.2 : R) * h
  right_inv q := by
    ext
    · simp only; linear_combination (q.1 : R) * h
    · simp only; linear_combination (q.2 : R) * h
end GlobalTheory.SteinitzProd


