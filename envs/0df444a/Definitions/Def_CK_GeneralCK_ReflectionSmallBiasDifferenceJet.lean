-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasDifferenceJet
-- name    : CK_GeneralCK_ReflectionSmallBiasDifferenceJet
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T21:09:37.716034+00:00
-- url     : https://prove2.me/theorems/1c7bc306-e59f-43b4-aba8-ecc9e558f86d
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasDifferenceJet` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasDifferenceJet` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasDifferenceJet` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasDifferenceJet (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasDifferenceJet.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasDifferenceJetChecks1
import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasDifferenceJetChecks2

-- ===== source module GeneralCK.ReflectionSmallBiasDifferenceJet =====
section

namespace GeneralCK.Reflection.SmallBiasDifferenceJet

open Filter Asymptotics SmallBiasPolynomial SmallBiasJet SmallBiasDifferenceTable
open SmallBiasHalfSumPowers SmallBiasBivariateBase SmallBiasContactSum
open scoped Topology

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem atanhA_checked : equalityCheck (compactAtanh coordinateA) atanhA = true := by
  decide +kernel

theorem atanhB_checked : equalityCheck (compactAtanh coordinateB) atanhB = true := by
  decide +kernel

theorem crossA_checked : equalityCheck (mulTrunc 24 coordinateA atanhB) crossA = true := by
  decide +kernel

theorem crossB_checked : equalityCheck (mulTrunc 24 coordinateB atanhA) crossB = true := by
  decide +kernel

theorem preDifference_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d preDifference_raw) (finePart d preDifference) = true := by
  interval_cases d
  · exact preDifference_degree0
  · exact preDifference_degree1
  · exact preDifference_degree2
  · exact preDifference_degree3
  · exact preDifference_degree4
  · exact preDifference_degree5
  · exact preDifference_degree6
  · exact preDifference_degree7
  · exact preDifference_degree8
  · exact preDifference_degree9
  · exact preDifference_degree10
  · exact preDifference_degree11
  · exact preDifference_degree12
  · exact preDifference_degree13
  · exact preDifference_degree14
  · exact preDifference_degree15
  · exact preDifference_degree16
  · exact preDifference_degree17
  · exact preDifference_degree18
  · exact preDifference_degree19
  · exact preDifference_degree20
  · exact preDifference_degree21
  · exact preDifference_degree22
  · exact preDifference_degree23
  · exact preDifference_degree24
  · exact preDifference_degree25
  · exact preDifference_degree26
  · exact preDifference_degree27
  · exact preDifference_degree28
  · exact preDifference_degree29
  · exact preDifference_degree30
  · exact preDifference_degree31
  · exact preDifference_degree32
  · exact preDifference_degree33
  · exact preDifference_degree34
  · exact preDifference_degree35
  · exact preDifference_degree36
  · exact preDifference_degree37
  · exact preDifference_degree38
  · exact preDifference_degree39
  · exact preDifference_degree40
  · exact preDifference_degree41
  · exact preDifference_degree42
  · exact preDifference_degree43
  · exact preDifference_degree44
  · exact preDifference_degree45
  · exact preDifference_degree46
  · exact preDifference_degree47

theorem preDifference_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k ((crossA ++ crossB) ++ (scale (-1) contactSum22)) z = eval k preDifference z := by
  have he := eval_eq_of_fineParts 48 k preDifference_raw preDifference z
    (fineBound_sound preDifference_raw_bound) (fineBound_sound preDifference_result_bound)
    preDifference_degrees
  exact he

theorem difference_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d difference_raw) (finePart d candidateTable) = true := by
  interval_cases d
  · exact difference_degree0
  · exact difference_degree1
  · exact difference_degree2
  · exact difference_degree3
  · exact difference_degree4
  · exact difference_degree5
  · exact difference_degree6
  · exact difference_degree7
  · exact difference_degree8
  · exact difference_degree9
  · exact difference_degree10
  · exact difference_degree11
  · exact difference_degree12
  · exact difference_degree13
  · exact difference_degree14
  · exact difference_degree15
  · exact difference_degree16
  · exact difference_degree17
  · exact difference_degree18
  · exact difference_degree19
  · exact difference_degree20
  · exact difference_degree21
  · exact difference_degree22
  · exact difference_degree23
  · exact difference_degree24
  · exact difference_degree25
  · exact difference_degree26
  · exact difference_degree27
  · exact difference_degree28
  · exact difference_degree29
  · exact difference_degree30
  · exact difference_degree31
  · exact difference_degree32
  · exact difference_degree33
  · exact difference_degree34
  · exact difference_degree35
  · exact difference_degree36
  · exact difference_degree37
  · exact difference_degree38
  · exact difference_degree39
  · exact difference_degree40
  · exact difference_degree41
  · exact difference_degree42
  · exact difference_degree43
  · exact difference_degree44
  · exact difference_degree45
  · exact difference_degree46
  · exact difference_degree47

theorem difference_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (preDifference ++ (reflectB contactSum22)) z = eval k candidateTable z := by
  have he := eval_eq_of_fineParts 48 k difference_raw candidateTable z
    (fineBound_sound difference_raw_bound) (fineBound_sound difference_result_bound)
    difference_degrees
  exact he

theorem difference_approximates_table {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k SmallBiasCurvatureAssembly.complexDifference candidateTable := by
  have ha := ((Approximates.coordinateA 24 k).compactAtanh hk (by rfl)).replacePolynomial
    (equalityCheck_sound atanhA_checked k)
  have hb := ((Approximates.coordinateB 24 k).compactAtanh hk (by rfl)).replacePolynomial
    (equalityCheck_sound atanhB_checked k)
  have hca := ((Approximates.coordinateA 24 k).mul hk hb).replacePolynomial
    (equalityCheck_sound crossA_checked k)
  have hcb := ((Approximates.coordinateB 24 k).mul hk ha).replacePolynomial
    (equalityCheck_sound crossB_checked k)
  have hc := contact_approximates_table hk hklog
  have hm : Approximates 24 k
      (fun z => SmallBiasComplexDomain.contactValue ((z.1-z.2)/2) (meanFunction z))
      (reflectB contactSum22) := by
    simpa only [halfSum,meanFunction,SmallBiasComplexDomain.meanEntropy,
      SmallBiasComplexDomain.entropyExt_neg,sub_eq_add_neg] using hc.reflectB
  have hpre := ((hca.addAppend hcb).addAppend (hc.scale (-1))).replacePolynomial
    (preDifference_eval k)
  have hh := (hpre.addAppend hm).replacePolynomial (difference_eval k)
  convert hh using 1
  funext z
  simp only [SmallBiasCurvatureAssembly.complexDifference,SmallBiasComplexDomain.difference,
    halfSum,meanFunction,Rat.cast_neg,Rat.cast_one]
  ring

theorem remainder_order24 : SmallBiasCurvatureAssembly.remainder =O[𝓝 0]
    (fun z : ℂ × ℂ => ‖z‖^24) := by
  have hk : (Real.log 2:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
  have hh := difference_approximates_table hk rfl
  apply hh.error.congr_left
  intro z
  rw [eval_candidateTable]
  rfl

end GeneralCK.Reflection.SmallBiasDifferenceJet

end


