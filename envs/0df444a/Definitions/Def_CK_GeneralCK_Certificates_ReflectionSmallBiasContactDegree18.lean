-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree18
-- name    : CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree18
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T08:17:05.750959+00:00
-- url     : https://prove2.me/theorems/7861c317-3958-4ee5-ae3c-4d201e3ef84d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree18` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree18` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree18` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionSmallBiasContactDegree18 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionSmallBiasContactDegree18.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree18Checks1
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree18Checks2

-- ===== source module GeneralCK.Certificates.ReflectionSmallBiasContactDegree18 =====
section

namespace GeneralCK.Reflection.SmallBiasContactDegrees

open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasHalfSumPowers SmallBiasBivariateBase SmallBiasBivariateInverse

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem body18_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d body18_raw) (finePart d body18) = true := by
  interval_cases d
  · exact body18_degree0
  · exact body18_degree1
  · exact body18_degree2
  · exact body18_degree3
  · exact body18_degree4
  · exact body18_degree5
  · exact body18_degree6
  · exact body18_degree7
  · exact body18_degree8
  · exact body18_degree9
  · exact body18_degree10
  · exact body18_degree11
  · exact body18_degree12
  · exact body18_degree13
  · exact body18_degree14
  · exact body18_degree15
  · exact body18_degree16
  · exact body18_degree17
  · exact body18_degree18
  · exact body18_degree19
  · exact body18_degree20
  · exact body18_degree21
  · exact body18_degree22
  · exact body18_degree23
  · exact body18_degree24
  · exact body18_degree25
  · exact body18_degree26
  · exact body18_degree27
  · exact body18_degree28
  · exact body18_degree29
  · exact body18_degree30
  · exact body18_degree31
  · exact body18_degree32
  · exact body18_degree33
  · exact body18_degree34
  · exact body18_degree35
  · exact body18_degree36
  · exact body18_degree37
  · exact body18_degree38
  · exact body18_degree39
  · exact body18_degree40
  · exact body18_degree41
  · exact body18_degree42
  · exact body18_degree43
  · exact body18_degree44
  · exact body18_degree45
  · exact body18_degree46
  · exact body18_degree47

theorem body18_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (mulTrunc 24 halfPower18 inversePower17) z = eval k body18 z := by
  have he := eval_eq_of_fineParts 48 k body18_raw body18 z
    (fineBound_sound body18_raw_bound) (fineBound_sound body18_result_bound)
    body18_degrees
  change eval k (normalize body18_raw) z = eval k body18 z
  rw [eval_normalize]
  exact he

theorem group18_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d group18_raw) (finePart d group18) = true := by
  interval_cases d
  · exact group18_degree0
  · exact group18_degree1
  · exact group18_degree2
  · exact group18_degree3
  · exact group18_degree4
  · exact group18_degree5
  · exact group18_degree6
  · exact group18_degree7
  · exact group18_degree8
  · exact group18_degree9
  · exact group18_degree10
  · exact group18_degree11
  · exact group18_degree12
  · exact group18_degree13
  · exact group18_degree14
  · exact group18_degree15
  · exact group18_degree16
  · exact group18_degree17
  · exact group18_degree18
  · exact group18_degree19
  · exact group18_degree20
  · exact group18_degree21
  · exact group18_degree22
  · exact group18_degree23
  · exact group18_degree24
  · exact group18_degree25
  · exact group18_degree26
  · exact group18_degree27
  · exact group18_degree28
  · exact group18_degree29
  · exact group18_degree30
  · exact group18_degree31
  · exact group18_degree32
  · exact group18_degree33
  · exact group18_degree34
  · exact group18_degree35
  · exact group18_degree36
  · exact group18_degree37
  · exact group18_degree38
  · exact group18_degree39
  · exact group18_degree40
  · exact group18_degree41
  · exact group18_degree42
  · exact group18_degree43
  · exact group18_degree44
  · exact group18_degree45
  · exact group18_degree46
  · exact group18_degree47

theorem group18_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (mulTrunc 24 coefficient18 body18) z = eval k group18 z := by
  have he := eval_eq_of_fineParts 48 k group18_raw group18 z
    (fineBound_sound group18_raw_bound) (fineBound_sound group18_result_bound)
    group18_degrees
  change eval k (normalize group18_raw) z = eval k group18 z
  rw [eval_normalize]
  exact he

theorem coefficient18_approximates (k : ℂ) :
    Approximates 24 k (fun _ => eval k coefficient18 (0:ℂ × ℂ)) coefficient18 := by
  convert Approximates.exactPolynomial 24 k coefficient18 using 1
  funext z
  simp [coefficient18,eval,evalTerm]

theorem evalContact_group18 (k s e : ℂ) :
    evalContact k phiGroup18 s e = eval k coefficient18 (0:ℂ × ℂ)*(s^18*(e⁻¹)^17) := by
  norm_num [phiGroup18,coefficient18,evalContact,evalContactTerm,eval,evalTerm]
  <;> ring

theorem group18_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => evalContact k phiGroup18 (halfSum z) (meanFunction z)) group18 := by
  have hb := ((halfPower18_approximates hk).mul hk (inversePower17_approximates hk hklog)).replacePolynomial
    (body18_eval k)
  have hh := ((coefficient18_approximates k).mul hk hb).replacePolynomial
    (group18_eval k)
  simpa only [evalContact_group18] using hh

end GeneralCK.Reflection.SmallBiasContactDegrees

end


