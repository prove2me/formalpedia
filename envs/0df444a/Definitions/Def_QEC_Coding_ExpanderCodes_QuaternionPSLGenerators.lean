-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionPSLGenerators
-- name    : QEC_Coding_ExpanderCodes_QuaternionPSLGenerators
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T11:39:53.227483+00:00
-- url     : https://prove2.me/theorems/eeabc0b1-23e5-4ae1-b744-b3a3397e1d64
-- title:
--   Quaternion PSLGenerators
-- statement:
--   Definitions and structural lemmas for Quaternion PSLGenerators, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionPSLGenerators.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
import Theorems.Thm_QEC_Coding_ExpanderCodes_ProjectiveDeterminant_conjugate_mem_specialProjectiveSubgroup
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_base_prime_matrix_mem_psl_of_root

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]
variable (f : F →+* K) (epsilon : F) (r y s i : K)
  (hEpsilon : epsilon ≠ 0) (hRoot : r ^ 2 = f epsilon)
  (hR : r ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
  (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
  (hRatio : s ^ 2 = y / (1 + y)) (hI : i ^ 2 = -1)
local notation "E" => projectiveMatrixEquivOfRoot (f epsilon) r y hRoot hR hOne hTwo
local notation "L" => indexedLeft f epsilon y hTwoF hY hOne hTwo
local notation "R" => indexedRight f epsilon y hEpsilon hTwoF hY hOne hTwo
include hEpsilon hRatio hI
theorem indexedLeft_matrix_mem_psl (t : TorusIndex epsilon) :
    E (L t) ∈ ProjectiveDeterminant.specialProjectiveSubgroup := by
  unfold indexedLeft
  rw [map_mul, map_mul, map_inv]
  apply ProjectiveDeterminant.conjugate_mem_specialProjectiveSubgroup
  exact (base_prime_matrix_mem_psl_of_root (f epsilon) r y s i
    ((map_ne_zero f).mpr hEpsilon) hRoot hR hY hOne hTwo hRatio hI).1
theorem indexedRight_matrix_mem_psl (t : TorusIndex epsilon) :
    E (R t) ∈ ProjectiveDeterminant.specialProjectiveSubgroup := by
  unfold indexedRight
  rw [map_mul, map_mul, map_inv]
  apply ProjectiveDeterminant.conjugate_mem_specialProjectiveSubgroup
  exact (base_prime_matrix_mem_psl_of_root (f epsilon) r y s i
    ((map_ne_zero f).mpr hEpsilon) hRoot hR hY hOne hTwo hRatio hI).2
def pslLeft (t : TorusIndex epsilon) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
  ProjectiveDeterminant.liftToPSL (E (L t))
    (indexedLeft_matrix_mem_psl f epsilon r y s i hEpsilon hRoot hR hTwoF
      hY hOne hTwo hRatio hI t)
def pslRight (t : TorusIndex epsilon) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
  ProjectiveDeterminant.liftToPSL (E (R t))
    (indexedRight_matrix_mem_psl f epsilon r y s i hEpsilon hRoot hR hTwoF
      hY hOne hTwo hRatio hI t)
local notation "PL" => pslLeft f epsilon r y s i hEpsilon hRoot hR hTwoF
  hY hOne hTwo hRatio hI
local notation "PR" => pslRight f epsilon r y s i hEpsilon hRoot hR hTwoF
  hY hOne hTwo hRatio hI
end QEC.Coding.ExpanderCodes.QuaternionGenerators


