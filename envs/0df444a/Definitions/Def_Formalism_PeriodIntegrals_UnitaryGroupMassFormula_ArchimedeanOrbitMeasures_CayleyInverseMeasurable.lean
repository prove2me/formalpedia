-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayleyInverseMeasurable
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayleyInverseMeasurable
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T09:57:08.318217+00:00
-- url     : https://prove2.me/theorems/0c3f55b1-205a-50e2-9b80-6e8837411926
-- title:
--   Cayley Inverse Measurable
-- statement:
--   Definitions and structural lemmas for Cayley Inverse Measurable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayleyInverseMeasurable.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayK
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExOm
import Theorems.Thm_HcInf_Jpq_conjTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace HcInf
open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
section Chart
variable (P Q : ℕ)
local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ
theorem cayCand_mem (g : UpqT P Q) : cayCand P Q g ∈ lieU P Q := by
  set G := UpqT.mat g with hG
  set J := HcS.UG.Jpq P Q
  have hU : Gᴴ * J * G = J := by
    have := (mem_Upq_iff P Q _).1 (toS P Q g).2
    rwa [← mat_eq] at this
  by_cases hu : IsUnit (G + 1).det
  · set K := (G + 1)⁻¹
    set X := cayCand P Q g with hX
    have hXdef : X = (1 + 1) * K * (G - 1) := rfl
    have hKG : K * (G + 1) = 1 := Matrix.nonsing_inv_mul _ hu
    have hGK : (G + 1) * K = 1 := Matrix.mul_nonsing_inv _ hu
    have hXG : X * (G + 1) = (1 + 1) * (G - 1) := by
      have e : (G - 1) * (G + 1) = (G + 1) * (G - 1) := by noncomm_ring
      rw [hXdef, Matrix.mul_assoc, Matrix.mul_assoc, e, ← Matrix.mul_assoc K, hKG, Matrix.one_mul]
    have hu' : IsUnit (G + 1)ᴴ.det := by
      rw [Matrix.det_conjTranspose]
      exact hu.star
    show Xᴴ * J + J * X = 0
    have key : (G + 1)ᴴ * (Xᴴ * J + J * X) * (G + 1) = 0 := by
      have e1 : (G + 1)ᴴ * (Xᴴ * J + J * X) * (G + 1) =
          (X * (G + 1))ᴴ * J * (G + 1) + (G + 1)ᴴ * J * (X * (G + 1)) := by
        rw [Matrix.conjTranspose_mul]
        noncomm_ring
      have hJ : Jᴴ = J := Jpq_conjTranspose P Q
      have h2 : ((1 : Mat) + 1)ᴴ = 1 + 1 := by simp
      rw [e1, hXG, Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
        Matrix.conjTranspose_one]
      have e2 : (Gᴴ - 1) * (1 + 1) * J * (G + 1) + (Gᴴ + 1) * J * ((1 + 1) * (G - 1)) =
          (1 + 1) * ((1 + 1) * (Gᴴ * J * G - J)) := by noncomm_ring
      rw [e2, hU, sub_self, Matrix.mul_zero, Matrix.mul_zero]
    have e3 : Xᴴ * J + J * X =
        ((G + 1)ᴴ)⁻¹ * ((G + 1)ᴴ * (Xᴴ * J + J * X) * (G + 1)) * K := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu', Matrix.one_mul,
        Matrix.mul_assoc, hGK, Matrix.mul_one]
    rw [e3, key, Matrix.mul_zero, Matrix.zero_mul]
  · have : cayCand P Q g = 0 := by
      show (1 + 1) * (G + 1)⁻¹ * (G - 1) = 0
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hu, Matrix.mul_zero, Matrix.zero_mul]
    rw [this]
    exact (lieU P Q).zero_mem
end Chart
end HcInf


