-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree6
-- name    : CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:57:28.133278+00:00
-- url     : https://prove2.me/theorems/6fafa291-6614-48aa-b44b-371a3810f4e3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree6` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree6` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree6` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionSmallBiasContactDegree6 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionSmallBiasContactDegree6.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree6Checks1
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree6Checks2
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree6Checks3
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree6Checks4
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree6Checks5

-- ===== source module GeneralCK.Certificates.ReflectionSmallBiasContactDegree6 =====
section

namespace GeneralCK.Reflection.SmallBiasContactDegrees

open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasHalfSumPowers SmallBiasBivariateBase SmallBiasBivariateInverse

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem body6_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d body6_raw) (finePart d body6) = true := by
  interval_cases d
  · exact body6_degree0
  · exact body6_degree1
  · exact body6_degree2
  · exact body6_degree3
  · exact body6_degree4
  · exact body6_degree5
  · exact body6_degree6
  · exact body6_degree7
  · exact body6_degree8
  · exact body6_degree9
  · exact body6_degree10
  · exact body6_degree11
  · exact body6_degree12
  · exact body6_degree13
  · exact body6_degree14
  · exact body6_degree15
  · exact body6_degree16
  · exact body6_degree17
  · exact body6_degree18
  · exact body6_degree19
  · exact body6_degree20
  · exact body6_degree21
  · exact body6_degree22
  · exact body6_degree23
  · exact body6_degree24
  · exact body6_degree25
  · exact body6_degree26
  · exact body6_degree27
  · exact body6_degree28
  · exact body6_degree29
  · exact body6_degree30
  · exact body6_degree31
  · exact body6_degree32
  · exact body6_degree33
  · exact body6_degree34
  · exact body6_degree35
  · exact body6_degree36
  · exact body6_degree37
  · exact body6_degree38
  · exact body6_degree39
  · exact body6_degree40
  · exact body6_degree41
  · exact body6_degree42
  · exact body6_degree43
  · exact body6_degree44
  · exact body6_degree45
  · exact body6_degree46
  · exact body6_degree47

theorem body6_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (mulTrunc 24 halfPower6 inversePower5) z = eval k body6 z := by
  have he := eval_eq_of_fineParts 48 k body6_raw body6 z
    (fineBound_sound body6_raw_bound) (fineBound_sound body6_result_bound)
    body6_degrees
  change eval k (normalize body6_raw) z = eval k body6 z
  rw [eval_normalize]
  exact he

theorem group6_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d group6_raw) (finePart d group6) = true := by
  interval_cases d
  · exact group6_degree0
  · exact group6_degree1
  · exact group6_degree2
  · exact group6_degree3
  · exact group6_degree4
  · exact group6_degree5
  · exact group6_degree6
  · exact group6_degree7
  · exact group6_degree8
  · exact group6_degree9
  · exact group6_degree10
  · exact group6_degree11
  · exact group6_degree12
  · exact group6_degree13
  · exact group6_degree14
  · exact group6_degree15
  · exact group6_degree16
  · exact group6_degree17
  · exact group6_degree18
  · exact group6_degree19
  · exact group6_degree20
  · exact group6_degree21
  · exact group6_degree22
  · exact group6_degree23
  · exact group6_degree24
  · exact group6_degree25
  · exact group6_degree26
  · exact group6_degree27
  · exact group6_degree28
  · exact group6_degree29
  · exact group6_degree30
  · exact group6_degree31
  · exact group6_degree32
  · exact group6_degree33
  · exact group6_degree34
  · exact group6_degree35
  · exact group6_degree36
  · exact group6_degree37
  · exact group6_degree38
  · exact group6_degree39
  · exact group6_degree40
  · exact group6_degree41
  · exact group6_degree42
  · exact group6_degree43
  · exact group6_degree44
  · exact group6_degree45
  · exact group6_degree46
  · exact group6_degree47

theorem group6_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (mulTrunc 24 coefficient6 body6) z = eval k group6 z := by
  have he := eval_eq_of_fineParts 48 k group6_raw group6 z
    (fineBound_sound group6_raw_bound) (fineBound_sound group6_result_bound)
    group6_degrees
  change eval k (normalize group6_raw) z = eval k group6 z
  rw [eval_normalize]
  exact he

theorem coefficient6_approximates (k : ℂ) :
    Approximates 24 k (fun _ => eval k coefficient6 (0:ℂ × ℂ)) coefficient6 := by
  convert Approximates.exactPolynomial 24 k coefficient6 using 1
  funext z
  simp [coefficient6,eval,evalTerm]

theorem evalContact_group6 (k s e : ℂ) :
    evalContact k phiGroup6 s e = eval k coefficient6 (0:ℂ × ℂ)*(s^6*(e⁻¹)^5) := by
  norm_num [phiGroup6,coefficient6,evalContact,evalContactTerm,eval,evalTerm]
  <;> ring

theorem group6_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => evalContact k phiGroup6 (halfSum z) (meanFunction z)) group6 := by
  have hb := ((halfPower6_approximates hk).mul hk (inversePower5_approximates hk hklog)).replacePolynomial
    (body6_eval k)
  have hh := ((coefficient6_approximates k).mul hk hb).replacePolynomial
    (group6_eval k)
  simpa only [evalContact_group6] using hh

end GeneralCK.Reflection.SmallBiasContactDegrees

end


