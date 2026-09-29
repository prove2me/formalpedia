-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree20
-- name    : CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree20
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T07:49:18.49348+00:00
-- url     : https://prove2.me/theorems/2711150e-b2d4-4895-84a1-a7a7b176e2c2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree20` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree20` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree20` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionSmallBiasContactDegree20 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionSmallBiasContactDegree20.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree20Checks1
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree20Checks2

-- ===== source module GeneralCK.Certificates.ReflectionSmallBiasContactDegree20 =====
section

namespace GeneralCK.Reflection.SmallBiasContactDegrees

open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasHalfSumPowers SmallBiasBivariateBase SmallBiasBivariateInverse

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem body20_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d body20_raw) (finePart d body20) = true := by
  interval_cases d
  · exact body20_degree0
  · exact body20_degree1
  · exact body20_degree2
  · exact body20_degree3
  · exact body20_degree4
  · exact body20_degree5
  · exact body20_degree6
  · exact body20_degree7
  · exact body20_degree8
  · exact body20_degree9
  · exact body20_degree10
  · exact body20_degree11
  · exact body20_degree12
  · exact body20_degree13
  · exact body20_degree14
  · exact body20_degree15
  · exact body20_degree16
  · exact body20_degree17
  · exact body20_degree18
  · exact body20_degree19
  · exact body20_degree20
  · exact body20_degree21
  · exact body20_degree22
  · exact body20_degree23
  · exact body20_degree24
  · exact body20_degree25
  · exact body20_degree26
  · exact body20_degree27
  · exact body20_degree28
  · exact body20_degree29
  · exact body20_degree30
  · exact body20_degree31
  · exact body20_degree32
  · exact body20_degree33
  · exact body20_degree34
  · exact body20_degree35
  · exact body20_degree36
  · exact body20_degree37
  · exact body20_degree38
  · exact body20_degree39
  · exact body20_degree40
  · exact body20_degree41
  · exact body20_degree42
  · exact body20_degree43
  · exact body20_degree44
  · exact body20_degree45
  · exact body20_degree46
  · exact body20_degree47

theorem body20_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (mulTrunc 24 halfPower20 inversePower19) z = eval k body20 z := by
  have he := eval_eq_of_fineParts 48 k body20_raw body20 z
    (fineBound_sound body20_raw_bound) (fineBound_sound body20_result_bound)
    body20_degrees
  change eval k (normalize body20_raw) z = eval k body20 z
  rw [eval_normalize]
  exact he

theorem group20_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d group20_raw) (finePart d group20) = true := by
  interval_cases d
  · exact group20_degree0
  · exact group20_degree1
  · exact group20_degree2
  · exact group20_degree3
  · exact group20_degree4
  · exact group20_degree5
  · exact group20_degree6
  · exact group20_degree7
  · exact group20_degree8
  · exact group20_degree9
  · exact group20_degree10
  · exact group20_degree11
  · exact group20_degree12
  · exact group20_degree13
  · exact group20_degree14
  · exact group20_degree15
  · exact group20_degree16
  · exact group20_degree17
  · exact group20_degree18
  · exact group20_degree19
  · exact group20_degree20
  · exact group20_degree21
  · exact group20_degree22
  · exact group20_degree23
  · exact group20_degree24
  · exact group20_degree25
  · exact group20_degree26
  · exact group20_degree27
  · exact group20_degree28
  · exact group20_degree29
  · exact group20_degree30
  · exact group20_degree31
  · exact group20_degree32
  · exact group20_degree33
  · exact group20_degree34
  · exact group20_degree35
  · exact group20_degree36
  · exact group20_degree37
  · exact group20_degree38
  · exact group20_degree39
  · exact group20_degree40
  · exact group20_degree41
  · exact group20_degree42
  · exact group20_degree43
  · exact group20_degree44
  · exact group20_degree45
  · exact group20_degree46
  · exact group20_degree47

theorem group20_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (mulTrunc 24 coefficient20 body20) z = eval k group20 z := by
  have he := eval_eq_of_fineParts 48 k group20_raw group20 z
    (fineBound_sound group20_raw_bound) (fineBound_sound group20_result_bound)
    group20_degrees
  change eval k (normalize group20_raw) z = eval k group20 z
  rw [eval_normalize]
  exact he

theorem coefficient20_approximates (k : ℂ) :
    Approximates 24 k (fun _ => eval k coefficient20 (0:ℂ × ℂ)) coefficient20 := by
  convert Approximates.exactPolynomial 24 k coefficient20 using 1
  funext z
  simp [coefficient20,eval,evalTerm]

theorem evalContact_group20 (k s e : ℂ) :
    evalContact k phiGroup20 s e = eval k coefficient20 (0:ℂ × ℂ)*(s^20*(e⁻¹)^19) := by
  norm_num [phiGroup20,coefficient20,evalContact,evalContactTerm,eval,evalTerm]
  <;> ring

theorem group20_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => evalContact k phiGroup20 (halfSum z) (meanFunction z)) group20 := by
  have hb := ((halfPower20_approximates hk).mul hk (inversePower19_approximates hk hklog)).replacePolynomial
    (body20_eval k)
  have hh := ((coefficient20_approximates k).mul hk hb).replacePolynomial
    (group20_eval k)
  simpa only [evalContact_group20] using hh

end GeneralCK.Reflection.SmallBiasContactDegrees

end


