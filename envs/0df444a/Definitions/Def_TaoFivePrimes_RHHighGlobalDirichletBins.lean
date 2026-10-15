-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighGlobalDirichletBins
-- name    : TaoFivePrimes_RHHighGlobalDirichletBins
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T04:19:31.292967+00:00
-- url     : https://prove2.me/theorems/1e34b5d9-bf45-4761-ba76-34c58770dbf9
-- title:
--   TaoFivePrimes_RHHighGlobalDirichletBins
-- statement:
--   Proposed global binned coefficient table with a proved balanced lookup and ordinary kernel-checked140-bit magnitude bounds. Exact accumulation from Dirichlet terms requires a separate finite certificate. No analytic, sign, count or RH assertion is made.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighGlobalDirichletBins00
import Definitions.Def_TaoFivePrimes_RHHighGlobalDirichletBins01
import Definitions.Def_TaoFivePrimes_RHHighGlobalDirichletBins02
import Definitions.Def_TaoFivePrimes_RHHighGlobalDirichletBins03
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RHHighGlobalDirichletBins
open RHHighGlobalBinTree
noncomputable def values : List Nat := RHHighGlobalDirichletBins00.rows.flatten++RHHighGlobalDirichletBins01.rows.flatten++RHHighGlobalDirichletBins02.rows.flatten++RHHighGlobalDirichletBins03.rows.flatten
noncomputable def tree : Tree := (.node 464 (.node 224 (.node 112 (.node 48 (.node 16 (.leaf RHHighGlobalDirichletBins00.row00) (.node 16 (.leaf RHHighGlobalDirichletBins00.row01) (.leaf RHHighGlobalDirichletBins00.row02))) (.node 32 (.node 16 (.leaf RHHighGlobalDirichletBins00.row03) (.leaf RHHighGlobalDirichletBins00.row04)) (.node 16 (.leaf RHHighGlobalDirichletBins00.row05) (.leaf RHHighGlobalDirichletBins00.row06)))) (.node 48 (.node 16 (.leaf RHHighGlobalDirichletBins00.row07) (.node 16 (.leaf RHHighGlobalDirichletBins00.row08) (.leaf RHHighGlobalDirichletBins00.row09))) (.node 32 (.node 16 (.leaf RHHighGlobalDirichletBins00.row10) (.leaf RHHighGlobalDirichletBins00.row11)) (.node 16 (.leaf RHHighGlobalDirichletBins00.row12) (.leaf RHHighGlobalDirichletBins00.row13))))) (.node 112 (.node 48 (.node 16 (.leaf RHHighGlobalDirichletBins00.row14) (.node 16 (.leaf RHHighGlobalDirichletBins00.row15) (.leaf RHHighGlobalDirichletBins01.row00))) (.node 32 (.node 16 (.leaf RHHighGlobalDirichletBins01.row01) (.leaf RHHighGlobalDirichletBins01.row02)) (.node 16 (.leaf RHHighGlobalDirichletBins01.row03) (.leaf RHHighGlobalDirichletBins01.row04)))) (.node 64 (.node 32 (.node 16 (.leaf RHHighGlobalDirichletBins01.row05) (.leaf RHHighGlobalDirichletBins01.row06)) (.node 16 (.leaf RHHighGlobalDirichletBins01.row07) (.leaf RHHighGlobalDirichletBins01.row08))) (.node 32 (.node 16 (.leaf RHHighGlobalDirichletBins01.row09) (.leaf RHHighGlobalDirichletBins01.row10)) (.node 16 (.leaf RHHighGlobalDirichletBins01.row11) (.leaf RHHighGlobalDirichletBins01.row12)))))) (.node 240 (.node 112 (.node 48 (.node 16 (.leaf RHHighGlobalDirichletBins01.row13) (.node 16 (.leaf RHHighGlobalDirichletBins01.row14) (.leaf RHHighGlobalDirichletBins01.row15))) (.node 32 (.node 16 (.leaf RHHighGlobalDirichletBins02.row00) (.leaf RHHighGlobalDirichletBins02.row01)) (.node 16 (.leaf RHHighGlobalDirichletBins02.row02) (.leaf RHHighGlobalDirichletBins02.row03)))) (.node 64 (.node 32 (.node 16 (.leaf RHHighGlobalDirichletBins02.row04) (.leaf RHHighGlobalDirichletBins02.row05)) (.node 16 (.leaf RHHighGlobalDirichletBins02.row06) (.leaf RHHighGlobalDirichletBins02.row07))) (.node 32 (.node 16 (.leaf RHHighGlobalDirichletBins02.row08) (.leaf RHHighGlobalDirichletBins02.row09)) (.node 16 (.leaf RHHighGlobalDirichletBins02.row10) (.leaf RHHighGlobalDirichletBins02.row11))))) (.node 112 (.node 48 (.node 16 (.leaf RHHighGlobalDirichletBins02.row12) (.node 16 (.leaf RHHighGlobalDirichletBins02.row13) (.leaf RHHighGlobalDirichletBins02.row14))) (.node 32 (.node 16 (.leaf RHHighGlobalDirichletBins02.row15) (.leaf RHHighGlobalDirichletBins03.row00)) (.node 16 (.leaf RHHighGlobalDirichletBins03.row01) (.leaf RHHighGlobalDirichletBins03.row02)))) (.node 64 (.node 32 (.node 16 (.leaf RHHighGlobalDirichletBins03.row03) (.leaf RHHighGlobalDirichletBins03.row04)) (.node 16 (.leaf RHHighGlobalDirichletBins03.row05) (.leaf RHHighGlobalDirichletBins03.row06))) (.node 32 (.node 16 (.leaf RHHighGlobalDirichletBins03.row07) (.leaf RHHighGlobalDirichletBins03.row08)) (.node 16 (.leaf RHHighGlobalDirichletBins03.row09) (.leaf RHHighGlobalDirichletBins03.row10)))))))
theorem valid_checked : valid tree=true := by decide +kernel
theorem flatten_checked : flatten tree=values := by decide +kernel
noncomputable def word (j : Nat) : Nat := get zeroWord tree j
lemma word_eq (j : Nat) : word j=(values[j]?).getD zeroWord := by
  rw [word,get_sound zeroWord tree valid_checked,flatten_checked]
noncomputable def coefficient (j k : Nat) : Int×Int :=
  (RHHighDirichletBinning.field (word j) (2*k),RHHighDirichletBinning.field (word j) (2*k+1))
noncomputable def groups : List (Nat×List (Int×Int)) :=
  (List.range 929).filterMap (fun j=>if word j=zeroWord then none
    else some (j,RHHighDirichletBinning.decodeCoefficients 24 (word j)))
theorem coefficients_checked : (List.range 929).all (fun j=>(List.range 24).all (fun k=>
    decide (|(coefficient j k).1|≤(2:Int)^140 ∧ |(coefficient j k).2|≤(2:Int)^140)))=true := by decide +kernel
lemma coefficient_bound (j k : Nat) (hj:j<929) (hk:k<24) :
    |(coefficient j k).1|≤(2:Int)^140 ∧ |(coefficient j k).2|≤(2:Int)^140 := by
  have h:=(List.all_eq_true.mp coefficients_checked) j (List.mem_range.mpr hj)
  have hh:=(List.all_eq_true.mp h) k (List.mem_range.mpr hk)
  exact of_decide_eq_true hh
end RHHighGlobalDirichletBins
noncomputable def TaoFivePrimes_RHHighGlobalDirichletBins : Nat := 929


