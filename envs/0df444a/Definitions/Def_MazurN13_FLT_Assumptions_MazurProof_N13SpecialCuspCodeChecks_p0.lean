-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialCuspCodeChecks_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialCuspCodeChecks_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:36:31.570985+00:00
-- url     : https://prove2.me/theorems/3bd69c5d-fa75-4216-8c5e-c6819907b1a9
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialCuspCodeChecks source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialCuspCodeChecks

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialCuspCodeChecks
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialAbelCodeQuotient_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialCuspReduction_p0

set_option autoImplicit false




/-!
Source pin: a6290bc36c3549d89239da82b13b1f59ebd0388e.
Uncompiled candidate. Every Lean check: NOT RUN.
These finite cusp checks test normalization and the known inverse-infinity
relation. They do not prove general specialization additivity.
-/

namespace MazurProof.N13.SpecialCuspCodeChecks

noncomputable section

open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction

/-- The sheet at x = 1 is reversed by the good-model coordinate change. -/
theorem pointCode_cusp (c : N13Mumford.Cusp13) :
    pointCode (specialCuspEquiv c) =
      match c with
      | .infinityPlus => 8
      | .infinityMinus => -8
      | .zeroPlus => 1
      | .zeroMinus => -1
      | .negOnePlus => -7
      | .negOneMinus => 7 := by
  rw [pointCode_eq_codeBP, curvePointEquiv_specialCuspEquiv]
  cases c <;> norm_num [codeBP, cuspCoordinate, baseAmplitude]

/-- The raw code of the doubled positive anchor is 16. -/
theorem divisorCode_double_anchor :
    divisorCode s(specialCuspEquiv .infinityPlus,
      specialCuspEquiv .infinityPlus) = 16 := by
  rw [divisorCode_mk, pointCode_cusp]
  norm_num

/-- The anchored negative-infinity divisor has raw code zero. -/
theorem divisorCode_negative_anchor :
    divisorCode s(specialCuspEquiv .infinityMinus,
      specialCuspEquiv .infinityPlus) = 0 := by
  rw [divisorCode_mk, pointCode_cusp, pointCode_cusp]
  norm_num

/-- The inverse-infinity witness C+A has code 13, not 8: A is sheet one. -/
theorem divisorCode_inverse_pair :
    divisorCode s(specialCuspEquiv .zeroPlus,
      specialCuspEquiv .negOnePlus) = 13 := by
  rw [divisorCode_mk, pointCode_cusp, pointCode_cusp]
  decide

/-- After recentering by 16, the two inverse-infinity witnesses have
opposite codes, 16 and 3, as required by their generic inverse relation. -/
theorem inverse_pair_recentered :
    divisorCode s(specialCuspEquiv .zeroPlus,
        specialCuspEquiv .negOnePlus) -
        divisorCode s(specialCuspEquiv .infinityPlus,
          specialCuspEquiv .infinityPlus) =
      -(divisorCode s(specialCuspEquiv .infinityMinus,
          specialCuspEquiv .infinityPlus) -
        divisorCode s(specialCuspEquiv .infinityPlus,
          specialCuspEquiv .infinityPlus)) := by
  rw [divisorCode_inverse_pair, divisorCode_double_anchor,
    divisorCode_negative_anchor]
  decide

end

end MazurProof.N13.SpecialCuspCodeChecks


