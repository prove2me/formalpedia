-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactSum
-- name    : CK_GeneralCK_ReflectionSmallBiasContactSum
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T13:41:08.683665+00:00
-- url     : https://prove2.me/theorems/773fe7a7-7d09-490d-bec7-c76599547a72
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasContactSum` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasContactSum` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasContactSum` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasContactSum (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasContactSum.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactSumChecks1
import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactSumChecks2
import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactSumChecks3
import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactSumChecks4
import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactSumChecks5
import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactSumChecks6
import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactSumChecks7
import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactSumChecks8
import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactSumChecks9
import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactSumChecks10

-- ===== source module GeneralCK.ReflectionSmallBiasContactSum =====
section

namespace GeneralCK.Reflection.SmallBiasContactSum

open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasContactDegrees SmallBiasHalfSumPowers SmallBiasBivariateBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem contactSum4_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d contactSum4_raw) (finePart d contactSum4) = true := by
  interval_cases d
  · exact contactSum4_degree0
  · exact contactSum4_degree1
  · exact contactSum4_degree2
  · exact contactSum4_degree3
  · exact contactSum4_degree4
  · exact contactSum4_degree5
  · exact contactSum4_degree6
  · exact contactSum4_degree7
  · exact contactSum4_degree8
  · exact contactSum4_degree9
  · exact contactSum4_degree10
  · exact contactSum4_degree11
  · exact contactSum4_degree12
  · exact contactSum4_degree13
  · exact contactSum4_degree14
  · exact contactSum4_degree15
  · exact contactSum4_degree16
  · exact contactSum4_degree17
  · exact contactSum4_degree18
  · exact contactSum4_degree19
  · exact contactSum4_degree20
  · exact contactSum4_degree21
  · exact contactSum4_degree22
  · exact contactSum4_degree23
  · exact contactSum4_degree24
  · exact contactSum4_degree25
  · exact contactSum4_degree26
  · exact contactSum4_degree27
  · exact contactSum4_degree28
  · exact contactSum4_degree29
  · exact contactSum4_degree30
  · exact contactSum4_degree31
  · exact contactSum4_degree32
  · exact contactSum4_degree33
  · exact contactSum4_degree34
  · exact contactSum4_degree35
  · exact contactSum4_degree36
  · exact contactSum4_degree37
  · exact contactSum4_degree38
  · exact contactSum4_degree39
  · exact contactSum4_degree40
  · exact contactSum4_degree41
  · exact contactSum4_degree42
  · exact contactSum4_degree43
  · exact contactSum4_degree44
  · exact contactSum4_degree45
  · exact contactSum4_degree46
  · exact contactSum4_degree47

theorem contactSum4_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (group2 ++ group4) z = eval k contactSum4 z := by
  have he := eval_eq_of_fineParts 48 k contactSum4_raw contactSum4 z
    (fineBound_sound contactSum4_raw_bound) (fineBound_sound contactSum4_result_bound)
    contactSum4_degrees
  exact he

theorem contactSum6_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d contactSum6_raw) (finePart d contactSum6) = true := by
  interval_cases d
  · exact contactSum6_degree0
  · exact contactSum6_degree1
  · exact contactSum6_degree2
  · exact contactSum6_degree3
  · exact contactSum6_degree4
  · exact contactSum6_degree5
  · exact contactSum6_degree6
  · exact contactSum6_degree7
  · exact contactSum6_degree8
  · exact contactSum6_degree9
  · exact contactSum6_degree10
  · exact contactSum6_degree11
  · exact contactSum6_degree12
  · exact contactSum6_degree13
  · exact contactSum6_degree14
  · exact contactSum6_degree15
  · exact contactSum6_degree16
  · exact contactSum6_degree17
  · exact contactSum6_degree18
  · exact contactSum6_degree19
  · exact contactSum6_degree20
  · exact contactSum6_degree21
  · exact contactSum6_degree22
  · exact contactSum6_degree23
  · exact contactSum6_degree24
  · exact contactSum6_degree25
  · exact contactSum6_degree26
  · exact contactSum6_degree27
  · exact contactSum6_degree28
  · exact contactSum6_degree29
  · exact contactSum6_degree30
  · exact contactSum6_degree31
  · exact contactSum6_degree32
  · exact contactSum6_degree33
  · exact contactSum6_degree34
  · exact contactSum6_degree35
  · exact contactSum6_degree36
  · exact contactSum6_degree37
  · exact contactSum6_degree38
  · exact contactSum6_degree39
  · exact contactSum6_degree40
  · exact contactSum6_degree41
  · exact contactSum6_degree42
  · exact contactSum6_degree43
  · exact contactSum6_degree44
  · exact contactSum6_degree45
  · exact contactSum6_degree46
  · exact contactSum6_degree47

theorem contactSum6_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (contactSum4 ++ group6) z = eval k contactSum6 z := by
  have he := eval_eq_of_fineParts 48 k contactSum6_raw contactSum6 z
    (fineBound_sound contactSum6_raw_bound) (fineBound_sound contactSum6_result_bound)
    contactSum6_degrees
  exact he

theorem contactSum8_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d contactSum8_raw) (finePart d contactSum8) = true := by
  interval_cases d
  · exact contactSum8_degree0
  · exact contactSum8_degree1
  · exact contactSum8_degree2
  · exact contactSum8_degree3
  · exact contactSum8_degree4
  · exact contactSum8_degree5
  · exact contactSum8_degree6
  · exact contactSum8_degree7
  · exact contactSum8_degree8
  · exact contactSum8_degree9
  · exact contactSum8_degree10
  · exact contactSum8_degree11
  · exact contactSum8_degree12
  · exact contactSum8_degree13
  · exact contactSum8_degree14
  · exact contactSum8_degree15
  · exact contactSum8_degree16
  · exact contactSum8_degree17
  · exact contactSum8_degree18
  · exact contactSum8_degree19
  · exact contactSum8_degree20
  · exact contactSum8_degree21
  · exact contactSum8_degree22
  · exact contactSum8_degree23
  · exact contactSum8_degree24
  · exact contactSum8_degree25
  · exact contactSum8_degree26
  · exact contactSum8_degree27
  · exact contactSum8_degree28
  · exact contactSum8_degree29
  · exact contactSum8_degree30
  · exact contactSum8_degree31
  · exact contactSum8_degree32
  · exact contactSum8_degree33
  · exact contactSum8_degree34
  · exact contactSum8_degree35
  · exact contactSum8_degree36
  · exact contactSum8_degree37
  · exact contactSum8_degree38
  · exact contactSum8_degree39
  · exact contactSum8_degree40
  · exact contactSum8_degree41
  · exact contactSum8_degree42
  · exact contactSum8_degree43
  · exact contactSum8_degree44
  · exact contactSum8_degree45
  · exact contactSum8_degree46
  · exact contactSum8_degree47

theorem contactSum8_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (contactSum6 ++ group8) z = eval k contactSum8 z := by
  have he := eval_eq_of_fineParts 48 k contactSum8_raw contactSum8 z
    (fineBound_sound contactSum8_raw_bound) (fineBound_sound contactSum8_result_bound)
    contactSum8_degrees
  exact he

theorem contactSum10_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d contactSum10_raw) (finePart d contactSum10) = true := by
  interval_cases d
  · exact contactSum10_degree0
  · exact contactSum10_degree1
  · exact contactSum10_degree2
  · exact contactSum10_degree3
  · exact contactSum10_degree4
  · exact contactSum10_degree5
  · exact contactSum10_degree6
  · exact contactSum10_degree7
  · exact contactSum10_degree8
  · exact contactSum10_degree9
  · exact contactSum10_degree10
  · exact contactSum10_degree11
  · exact contactSum10_degree12
  · exact contactSum10_degree13
  · exact contactSum10_degree14
  · exact contactSum10_degree15
  · exact contactSum10_degree16
  · exact contactSum10_degree17
  · exact contactSum10_degree18
  · exact contactSum10_degree19
  · exact contactSum10_degree20
  · exact contactSum10_degree21
  · exact contactSum10_degree22
  · exact contactSum10_degree23
  · exact contactSum10_degree24
  · exact contactSum10_degree25
  · exact contactSum10_degree26
  · exact contactSum10_degree27
  · exact contactSum10_degree28
  · exact contactSum10_degree29
  · exact contactSum10_degree30
  · exact contactSum10_degree31
  · exact contactSum10_degree32
  · exact contactSum10_degree33
  · exact contactSum10_degree34
  · exact contactSum10_degree35
  · exact contactSum10_degree36
  · exact contactSum10_degree37
  · exact contactSum10_degree38
  · exact contactSum10_degree39
  · exact contactSum10_degree40
  · exact contactSum10_degree41
  · exact contactSum10_degree42
  · exact contactSum10_degree43
  · exact contactSum10_degree44
  · exact contactSum10_degree45
  · exact contactSum10_degree46
  · exact contactSum10_degree47

theorem contactSum10_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (contactSum8 ++ group10) z = eval k contactSum10 z := by
  have he := eval_eq_of_fineParts 48 k contactSum10_raw contactSum10 z
    (fineBound_sound contactSum10_raw_bound) (fineBound_sound contactSum10_result_bound)
    contactSum10_degrees
  exact he

theorem contactSum12_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d contactSum12_raw) (finePart d contactSum12) = true := by
  interval_cases d
  · exact contactSum12_degree0
  · exact contactSum12_degree1
  · exact contactSum12_degree2
  · exact contactSum12_degree3
  · exact contactSum12_degree4
  · exact contactSum12_degree5
  · exact contactSum12_degree6
  · exact contactSum12_degree7
  · exact contactSum12_degree8
  · exact contactSum12_degree9
  · exact contactSum12_degree10
  · exact contactSum12_degree11
  · exact contactSum12_degree12
  · exact contactSum12_degree13
  · exact contactSum12_degree14
  · exact contactSum12_degree15
  · exact contactSum12_degree16
  · exact contactSum12_degree17
  · exact contactSum12_degree18
  · exact contactSum12_degree19
  · exact contactSum12_degree20
  · exact contactSum12_degree21
  · exact contactSum12_degree22
  · exact contactSum12_degree23
  · exact contactSum12_degree24
  · exact contactSum12_degree25
  · exact contactSum12_degree26
  · exact contactSum12_degree27
  · exact contactSum12_degree28
  · exact contactSum12_degree29
  · exact contactSum12_degree30
  · exact contactSum12_degree31
  · exact contactSum12_degree32
  · exact contactSum12_degree33
  · exact contactSum12_degree34
  · exact contactSum12_degree35
  · exact contactSum12_degree36
  · exact contactSum12_degree37
  · exact contactSum12_degree38
  · exact contactSum12_degree39
  · exact contactSum12_degree40
  · exact contactSum12_degree41
  · exact contactSum12_degree42
  · exact contactSum12_degree43
  · exact contactSum12_degree44
  · exact contactSum12_degree45
  · exact contactSum12_degree46
  · exact contactSum12_degree47

theorem contactSum12_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (contactSum10 ++ group12) z = eval k contactSum12 z := by
  have he := eval_eq_of_fineParts 48 k contactSum12_raw contactSum12 z
    (fineBound_sound contactSum12_raw_bound) (fineBound_sound contactSum12_result_bound)
    contactSum12_degrees
  exact he

theorem contactSum14_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d contactSum14_raw) (finePart d contactSum14) = true := by
  interval_cases d
  · exact contactSum14_degree0
  · exact contactSum14_degree1
  · exact contactSum14_degree2
  · exact contactSum14_degree3
  · exact contactSum14_degree4
  · exact contactSum14_degree5
  · exact contactSum14_degree6
  · exact contactSum14_degree7
  · exact contactSum14_degree8
  · exact contactSum14_degree9
  · exact contactSum14_degree10
  · exact contactSum14_degree11
  · exact contactSum14_degree12
  · exact contactSum14_degree13
  · exact contactSum14_degree14
  · exact contactSum14_degree15
  · exact contactSum14_degree16
  · exact contactSum14_degree17
  · exact contactSum14_degree18
  · exact contactSum14_degree19
  · exact contactSum14_degree20
  · exact contactSum14_degree21
  · exact contactSum14_degree22
  · exact contactSum14_degree23
  · exact contactSum14_degree24
  · exact contactSum14_degree25
  · exact contactSum14_degree26
  · exact contactSum14_degree27
  · exact contactSum14_degree28
  · exact contactSum14_degree29
  · exact contactSum14_degree30
  · exact contactSum14_degree31
  · exact contactSum14_degree32
  · exact contactSum14_degree33
  · exact contactSum14_degree34
  · exact contactSum14_degree35
  · exact contactSum14_degree36
  · exact contactSum14_degree37
  · exact contactSum14_degree38
  · exact contactSum14_degree39
  · exact contactSum14_degree40
  · exact contactSum14_degree41
  · exact contactSum14_degree42
  · exact contactSum14_degree43
  · exact contactSum14_degree44
  · exact contactSum14_degree45
  · exact contactSum14_degree46
  · exact contactSum14_degree47

theorem contactSum14_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (contactSum12 ++ group14) z = eval k contactSum14 z := by
  have he := eval_eq_of_fineParts 48 k contactSum14_raw contactSum14 z
    (fineBound_sound contactSum14_raw_bound) (fineBound_sound contactSum14_result_bound)
    contactSum14_degrees
  exact he

theorem contactSum16_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d contactSum16_raw) (finePart d contactSum16) = true := by
  interval_cases d
  · exact contactSum16_degree0
  · exact contactSum16_degree1
  · exact contactSum16_degree2
  · exact contactSum16_degree3
  · exact contactSum16_degree4
  · exact contactSum16_degree5
  · exact contactSum16_degree6
  · exact contactSum16_degree7
  · exact contactSum16_degree8
  · exact contactSum16_degree9
  · exact contactSum16_degree10
  · exact contactSum16_degree11
  · exact contactSum16_degree12
  · exact contactSum16_degree13
  · exact contactSum16_degree14
  · exact contactSum16_degree15
  · exact contactSum16_degree16
  · exact contactSum16_degree17
  · exact contactSum16_degree18
  · exact contactSum16_degree19
  · exact contactSum16_degree20
  · exact contactSum16_degree21
  · exact contactSum16_degree22
  · exact contactSum16_degree23
  · exact contactSum16_degree24
  · exact contactSum16_degree25
  · exact contactSum16_degree26
  · exact contactSum16_degree27
  · exact contactSum16_degree28
  · exact contactSum16_degree29
  · exact contactSum16_degree30
  · exact contactSum16_degree31
  · exact contactSum16_degree32
  · exact contactSum16_degree33
  · exact contactSum16_degree34
  · exact contactSum16_degree35
  · exact contactSum16_degree36
  · exact contactSum16_degree37
  · exact contactSum16_degree38
  · exact contactSum16_degree39
  · exact contactSum16_degree40
  · exact contactSum16_degree41
  · exact contactSum16_degree42
  · exact contactSum16_degree43
  · exact contactSum16_degree44
  · exact contactSum16_degree45
  · exact contactSum16_degree46
  · exact contactSum16_degree47

theorem contactSum16_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (contactSum14 ++ group16) z = eval k contactSum16 z := by
  have he := eval_eq_of_fineParts 48 k contactSum16_raw contactSum16 z
    (fineBound_sound contactSum16_raw_bound) (fineBound_sound contactSum16_result_bound)
    contactSum16_degrees
  exact he

theorem contactSum18_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d contactSum18_raw) (finePart d contactSum18) = true := by
  interval_cases d
  · exact contactSum18_degree0
  · exact contactSum18_degree1
  · exact contactSum18_degree2
  · exact contactSum18_degree3
  · exact contactSum18_degree4
  · exact contactSum18_degree5
  · exact contactSum18_degree6
  · exact contactSum18_degree7
  · exact contactSum18_degree8
  · exact contactSum18_degree9
  · exact contactSum18_degree10
  · exact contactSum18_degree11
  · exact contactSum18_degree12
  · exact contactSum18_degree13
  · exact contactSum18_degree14
  · exact contactSum18_degree15
  · exact contactSum18_degree16
  · exact contactSum18_degree17
  · exact contactSum18_degree18
  · exact contactSum18_degree19
  · exact contactSum18_degree20
  · exact contactSum18_degree21
  · exact contactSum18_degree22
  · exact contactSum18_degree23
  · exact contactSum18_degree24
  · exact contactSum18_degree25
  · exact contactSum18_degree26
  · exact contactSum18_degree27
  · exact contactSum18_degree28
  · exact contactSum18_degree29
  · exact contactSum18_degree30
  · exact contactSum18_degree31
  · exact contactSum18_degree32
  · exact contactSum18_degree33
  · exact contactSum18_degree34
  · exact contactSum18_degree35
  · exact contactSum18_degree36
  · exact contactSum18_degree37
  · exact contactSum18_degree38
  · exact contactSum18_degree39
  · exact contactSum18_degree40
  · exact contactSum18_degree41
  · exact contactSum18_degree42
  · exact contactSum18_degree43
  · exact contactSum18_degree44
  · exact contactSum18_degree45
  · exact contactSum18_degree46
  · exact contactSum18_degree47

theorem contactSum18_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (contactSum16 ++ group18) z = eval k contactSum18 z := by
  have he := eval_eq_of_fineParts 48 k contactSum18_raw contactSum18 z
    (fineBound_sound contactSum18_raw_bound) (fineBound_sound contactSum18_result_bound)
    contactSum18_degrees
  exact he

theorem contactSum20_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d contactSum20_raw) (finePart d contactSum20) = true := by
  interval_cases d
  · exact contactSum20_degree0
  · exact contactSum20_degree1
  · exact contactSum20_degree2
  · exact contactSum20_degree3
  · exact contactSum20_degree4
  · exact contactSum20_degree5
  · exact contactSum20_degree6
  · exact contactSum20_degree7
  · exact contactSum20_degree8
  · exact contactSum20_degree9
  · exact contactSum20_degree10
  · exact contactSum20_degree11
  · exact contactSum20_degree12
  · exact contactSum20_degree13
  · exact contactSum20_degree14
  · exact contactSum20_degree15
  · exact contactSum20_degree16
  · exact contactSum20_degree17
  · exact contactSum20_degree18
  · exact contactSum20_degree19
  · exact contactSum20_degree20
  · exact contactSum20_degree21
  · exact contactSum20_degree22
  · exact contactSum20_degree23
  · exact contactSum20_degree24
  · exact contactSum20_degree25
  · exact contactSum20_degree26
  · exact contactSum20_degree27
  · exact contactSum20_degree28
  · exact contactSum20_degree29
  · exact contactSum20_degree30
  · exact contactSum20_degree31
  · exact contactSum20_degree32
  · exact contactSum20_degree33
  · exact contactSum20_degree34
  · exact contactSum20_degree35
  · exact contactSum20_degree36
  · exact contactSum20_degree37
  · exact contactSum20_degree38
  · exact contactSum20_degree39
  · exact contactSum20_degree40
  · exact contactSum20_degree41
  · exact contactSum20_degree42
  · exact contactSum20_degree43
  · exact contactSum20_degree44
  · exact contactSum20_degree45
  · exact contactSum20_degree46
  · exact contactSum20_degree47

theorem contactSum20_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (contactSum18 ++ group20) z = eval k contactSum20 z := by
  have he := eval_eq_of_fineParts 48 k contactSum20_raw contactSum20 z
    (fineBound_sound contactSum20_raw_bound) (fineBound_sound contactSum20_result_bound)
    contactSum20_degrees
  exact he

theorem contactSum22_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d contactSum22_raw) (finePart d contactSum22) = true := by
  interval_cases d
  · exact contactSum22_degree0
  · exact contactSum22_degree1
  · exact contactSum22_degree2
  · exact contactSum22_degree3
  · exact contactSum22_degree4
  · exact contactSum22_degree5
  · exact contactSum22_degree6
  · exact contactSum22_degree7
  · exact contactSum22_degree8
  · exact contactSum22_degree9
  · exact contactSum22_degree10
  · exact contactSum22_degree11
  · exact contactSum22_degree12
  · exact contactSum22_degree13
  · exact contactSum22_degree14
  · exact contactSum22_degree15
  · exact contactSum22_degree16
  · exact contactSum22_degree17
  · exact contactSum22_degree18
  · exact contactSum22_degree19
  · exact contactSum22_degree20
  · exact contactSum22_degree21
  · exact contactSum22_degree22
  · exact contactSum22_degree23
  · exact contactSum22_degree24
  · exact contactSum22_degree25
  · exact contactSum22_degree26
  · exact contactSum22_degree27
  · exact contactSum22_degree28
  · exact contactSum22_degree29
  · exact contactSum22_degree30
  · exact contactSum22_degree31
  · exact contactSum22_degree32
  · exact contactSum22_degree33
  · exact contactSum22_degree34
  · exact contactSum22_degree35
  · exact contactSum22_degree36
  · exact contactSum22_degree37
  · exact contactSum22_degree38
  · exact contactSum22_degree39
  · exact contactSum22_degree40
  · exact contactSum22_degree41
  · exact contactSum22_degree42
  · exact contactSum22_degree43
  · exact contactSum22_degree44
  · exact contactSum22_degree45
  · exact contactSum22_degree46
  · exact contactSum22_degree47

theorem contactSum22_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (contactSum20 ++ group22) z = eval k contactSum22 z := by
  have he := eval_eq_of_fineParts 48 k contactSum22_raw contactSum22 z
    (fineBound_sound contactSum22_raw_bound) (fineBound_sound contactSum22_result_bound)
    contactSum22_degrees
  exact he

theorem phi_decomposition : SmallBiasPicardData.phi = phiGroup2 ++ phiGroup4 ++ phiGroup6 ++ phiGroup8 ++ phiGroup10 ++ phiGroup12 ++ phiGroup14 ++ phiGroup16 ++ phiGroup18 ++ phiGroup20 ++ phiGroup22 := by
  decide +kernel

theorem phi_valid : ∀ t ∈ SmallBiasPicardData.phi, 2≤t.a ∧ t.b=0 := by
  have h : SmallBiasPicardData.phi.all (fun t => decide (2≤t.a ∧ t.b=0)) = true := by
    decide +kernel
  intro t ht
  exact of_decide_eq_true (List.all_eq_true.mp h t ht)

theorem contact_approximates_table {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => SmallBiasComplexDomain.contactValue (halfSum z) (meanFunction z)) contactSum22 := by
  have h2 := group2_approximates hk hklog
  have h4 := (h2.addAppend (group4_approximates hk hklog)).replacePolynomial
    (contactSum4_eval k)
  have h6 := (h4.addAppend (group6_approximates hk hklog)).replacePolynomial
    (contactSum6_eval k)
  have h8 := (h6.addAppend (group8_approximates hk hklog)).replacePolynomial
    (contactSum8_eval k)
  have h10 := (h8.addAppend (group10_approximates hk hklog)).replacePolynomial
    (contactSum10_eval k)
  have h12 := (h10.addAppend (group12_approximates hk hklog)).replacePolynomial
    (contactSum12_eval k)
  have h14 := (h12.addAppend (group14_approximates hk hklog)).replacePolynomial
    (contactSum14_eval k)
  have h16 := (h14.addAppend (group16_approximates hk hklog)).replacePolynomial
    (contactSum16_eval k)
  have h18 := (h16.addAppend (group18_approximates hk hklog)).replacePolynomial
    (contactSum18_eval k)
  have h20 := (h18.addAppend (group20_approximates hk hklog)).replacePolynomial
    (contactSum20_eval k)
  have h22 := (h20.addAppend (group22_approximates hk hklog)).replacePolynomial
    (contactSum22_eval k)
  have ht : Approximates 24 k
      (fun z => evalContact k SmallBiasPicardData.phi (halfSum z) (meanFunction z)) contactSum22 := by
    convert h22 using 1
    funext z
    rw [phi_decomposition]
    simp only [evalContact_append]
    <;> ring
  have hs : AnalyticAt ℂ halfSum 0 := by
    simpa only [pow_one] using (halfPower1_approximates hk).analytic
  have he := (mean_approximates hk hklog).analytic
  have he0 : meanFunction 0 = (Real.log 2:ℂ) := by
    simp [meanFunction,SmallBiasComplexDomain.meanEntropy,ComplexEntropy.entropyExt]
  exact contactValue_of_finite hs he (by simp [halfSum])
    (by rw [he0,← hklog]; exact hk)
    (SmallBiasPicardData.phi_approximates_table hk hklog) phi_valid ht

end GeneralCK.Reflection.SmallBiasContactSum

end


