-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAuxiliaryPlacesSquarePatternsSUnits
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAuxiliaryPlacesSquarePatternsSUnits
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T17:12:19.291225+00:00
-- url     : https://prove2.me/theorems/d764a61d-38f6-4846-b7f4-4b85ac4e0d0e
-- title:
--   Exists Auxiliary Places Square Patterns SUnits
-- statement:
--   Definitions and structural lemmas for Exists Auxiliary Places Square Patterns SUnits, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsAuxiliaryPlacesSquarePatternsSUnits.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPlaceIsSquareAndNotIsSquare
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexSquaresSUnitsNumberFieldStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
namespace GlobalTheory.QNorm
def adjoinRoot {G : Type} [CommGroup G] (Q : Subgroup G) (d : G) (hd : d * d ∈ Q) :
    Subgroup G where
  carrier := {x | x ∈ Q ∨ x * d ∈ Q}
  one_mem' := Or.inl Q.one_mem
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (Q.mul_mem ha hb)
    · exact Or.inr (by rw [mul_assoc]; exact Q.mul_mem ha hb)
    · exact Or.inr (by rw [mul_right_comm]; exact Q.mul_mem ha hb)
    · refine Or.inl ?_
      have h := Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem hd)
      have e : a * d * (b * d) * (d * d)⁻¹ = a * b := by
        rw [mul_mul_mul_comm, mul_inv_cancel_right]
      rwa [e] at h
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (Q.inv_mem ha)
    · refine Or.inr ?_
      have h := Q.mul_mem (Q.inv_mem ha) hd
      have e : (a * d)⁻¹ * (d * d) = a⁻¹ * d := by
        rw [mul_inv, mul_assoc, inv_mul_cancel_left]
      rwa [e] at h
end GlobalTheory.QNorm


