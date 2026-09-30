-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree14
-- name    : CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree14
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:30:39.255419+00:00
-- url     : https://prove2.me/theorems/e9e5e192-4d64-4c94-8605-3187271aeb78
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree14` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree14` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree14` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionSmallBiasContactDegree14 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionSmallBiasContactDegree14.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree14Checks1
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree14Checks2

-- ===== source module GeneralCK.Certificates.ReflectionSmallBiasContactDegree14 =====
section

namespace GeneralCK.Reflection.SmallBiasContactDegrees

open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasHalfSumPowers SmallBiasBivariateBase SmallBiasBivariateInverse

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem body14_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d body14_raw) (finePart d body14) = true := by
  interval_cases d
  · exact body14_degree0
  · exact body14_degree1
  · exact body14_degree2
  · exact body14_degree3
  · exact body14_degree4
  · exact body14_degree5
  · exact body14_degree6
  · exact body14_degree7
  · exact body14_degree8
  · exact body14_degree9
  · exact body14_degree10
  · exact body14_degree11
  · exact body14_degree12
  · exact body14_degree13
  · exact body14_degree14
  · exact body14_degree15
  · exact body14_degree16
  · exact body14_degree17
  · exact body14_degree18
  · exact body14_degree19
  · exact body14_degree20
  · exact body14_degree21
  · exact body14_degree22
  · exact body14_degree23
  · exact body14_degree24
  · exact body14_degree25
  · exact body14_degree26
  · exact body14_degree27
  · exact body14_degree28
  · exact body14_degree29
  · exact body14_degree30
  · exact body14_degree31
  · exact body14_degree32
  · exact body14_degree33
  · exact body14_degree34
  · exact body14_degree35
  · exact body14_degree36
  · exact body14_degree37
  · exact body14_degree38
  · exact body14_degree39
  · exact body14_degree40
  · exact body14_degree41
  · exact body14_degree42
  · exact body14_degree43
  · exact body14_degree44
  · exact body14_degree45
  · exact body14_degree46
  · exact body14_degree47

theorem body14_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (mulTrunc 24 halfPower14 inversePower13) z = eval k body14 z := by
  have he := eval_eq_of_fineParts 48 k body14_raw body14 z
    (fineBound_sound body14_raw_bound) (fineBound_sound body14_result_bound)
    body14_degrees
  change eval k (normalize body14_raw) z = eval k body14 z
  rw [eval_normalize]
  exact he

theorem group14_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d group14_raw) (finePart d group14) = true := by
  interval_cases d
  · exact group14_degree0
  · exact group14_degree1
  · exact group14_degree2
  · exact group14_degree3
  · exact group14_degree4
  · exact group14_degree5
  · exact group14_degree6
  · exact group14_degree7
  · exact group14_degree8
  · exact group14_degree9
  · exact group14_degree10
  · exact group14_degree11
  · exact group14_degree12
  · exact group14_degree13
  · exact group14_degree14
  · exact group14_degree15
  · exact group14_degree16
  · exact group14_degree17
  · exact group14_degree18
  · exact group14_degree19
  · exact group14_degree20
  · exact group14_degree21
  · exact group14_degree22
  · exact group14_degree23
  · exact group14_degree24
  · exact group14_degree25
  · exact group14_degree26
  · exact group14_degree27
  · exact group14_degree28
  · exact group14_degree29
  · exact group14_degree30
  · exact group14_degree31
  · exact group14_degree32
  · exact group14_degree33
  · exact group14_degree34
  · exact group14_degree35
  · exact group14_degree36
  · exact group14_degree37
  · exact group14_degree38
  · exact group14_degree39
  · exact group14_degree40
  · exact group14_degree41
  · exact group14_degree42
  · exact group14_degree43
  · exact group14_degree44
  · exact group14_degree45
  · exact group14_degree46
  · exact group14_degree47

theorem group14_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (mulTrunc 24 coefficient14 body14) z = eval k group14 z := by
  have he := eval_eq_of_fineParts 48 k group14_raw group14 z
    (fineBound_sound group14_raw_bound) (fineBound_sound group14_result_bound)
    group14_degrees
  change eval k (normalize group14_raw) z = eval k group14 z
  rw [eval_normalize]
  exact he

theorem coefficient14_approximates (k : ℂ) :
    Approximates 24 k (fun _ => eval k coefficient14 (0:ℂ × ℂ)) coefficient14 := by
  convert Approximates.exactPolynomial 24 k coefficient14 using 1
  funext z
  simp [coefficient14,eval,evalTerm]

theorem evalContact_group14 (k s e : ℂ) :
    evalContact k phiGroup14 s e = eval k coefficient14 (0:ℂ × ℂ)*(s^14*(e⁻¹)^13) := by
  norm_num [phiGroup14,coefficient14,evalContact,evalContactTerm,eval,evalTerm]
  <;> ring

theorem group14_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => evalContact k phiGroup14 (halfSum z) (meanFunction z)) group14 := by
  have hb := ((halfPower14_approximates hk).mul hk (inversePower13_approximates hk hklog)).replacePolynomial
    (body14_eval k)
  have hh := ((coefficient14_approximates k).mul hk hb).replacePolynomial
    (group14_eval k)
  simpa only [evalContact_group14] using hh

end GeneralCK.Reflection.SmallBiasContactDegrees

end


