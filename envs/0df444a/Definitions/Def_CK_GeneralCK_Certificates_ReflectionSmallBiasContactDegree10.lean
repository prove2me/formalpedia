-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree10
-- name    : CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree10
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T23:31:58.655081+00:00
-- url     : https://prove2.me/theorems/8cc7a1f1-99aa-4fc1-b7ba-82921949fa46
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree10` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree10` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree10` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionSmallBiasContactDegree10 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionSmallBiasContactDegree10.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree10Checks1
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree10Checks2

-- ===== source module GeneralCK.Certificates.ReflectionSmallBiasContactDegree10 =====
section

namespace GeneralCK.Reflection.SmallBiasContactDegrees

open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasHalfSumPowers SmallBiasBivariateBase SmallBiasBivariateInverse

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem body10_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d body10_raw) (finePart d body10) = true := by
  interval_cases d
  · exact body10_degree0
  · exact body10_degree1
  · exact body10_degree2
  · exact body10_degree3
  · exact body10_degree4
  · exact body10_degree5
  · exact body10_degree6
  · exact body10_degree7
  · exact body10_degree8
  · exact body10_degree9
  · exact body10_degree10
  · exact body10_degree11
  · exact body10_degree12
  · exact body10_degree13
  · exact body10_degree14
  · exact body10_degree15
  · exact body10_degree16
  · exact body10_degree17
  · exact body10_degree18
  · exact body10_degree19
  · exact body10_degree20
  · exact body10_degree21
  · exact body10_degree22
  · exact body10_degree23
  · exact body10_degree24
  · exact body10_degree25
  · exact body10_degree26
  · exact body10_degree27
  · exact body10_degree28
  · exact body10_degree29
  · exact body10_degree30
  · exact body10_degree31
  · exact body10_degree32
  · exact body10_degree33
  · exact body10_degree34
  · exact body10_degree35
  · exact body10_degree36
  · exact body10_degree37
  · exact body10_degree38
  · exact body10_degree39
  · exact body10_degree40
  · exact body10_degree41
  · exact body10_degree42
  · exact body10_degree43
  · exact body10_degree44
  · exact body10_degree45
  · exact body10_degree46
  · exact body10_degree47

theorem body10_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (mulTrunc 24 halfPower10 inversePower9) z = eval k body10 z := by
  have he := eval_eq_of_fineParts 48 k body10_raw body10 z
    (fineBound_sound body10_raw_bound) (fineBound_sound body10_result_bound)
    body10_degrees
  change eval k (normalize body10_raw) z = eval k body10 z
  rw [eval_normalize]
  exact he

theorem group10_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d group10_raw) (finePart d group10) = true := by
  interval_cases d
  · exact group10_degree0
  · exact group10_degree1
  · exact group10_degree2
  · exact group10_degree3
  · exact group10_degree4
  · exact group10_degree5
  · exact group10_degree6
  · exact group10_degree7
  · exact group10_degree8
  · exact group10_degree9
  · exact group10_degree10
  · exact group10_degree11
  · exact group10_degree12
  · exact group10_degree13
  · exact group10_degree14
  · exact group10_degree15
  · exact group10_degree16
  · exact group10_degree17
  · exact group10_degree18
  · exact group10_degree19
  · exact group10_degree20
  · exact group10_degree21
  · exact group10_degree22
  · exact group10_degree23
  · exact group10_degree24
  · exact group10_degree25
  · exact group10_degree26
  · exact group10_degree27
  · exact group10_degree28
  · exact group10_degree29
  · exact group10_degree30
  · exact group10_degree31
  · exact group10_degree32
  · exact group10_degree33
  · exact group10_degree34
  · exact group10_degree35
  · exact group10_degree36
  · exact group10_degree37
  · exact group10_degree38
  · exact group10_degree39
  · exact group10_degree40
  · exact group10_degree41
  · exact group10_degree42
  · exact group10_degree43
  · exact group10_degree44
  · exact group10_degree45
  · exact group10_degree46
  · exact group10_degree47

theorem group10_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (mulTrunc 24 coefficient10 body10) z = eval k group10 z := by
  have he := eval_eq_of_fineParts 48 k group10_raw group10 z
    (fineBound_sound group10_raw_bound) (fineBound_sound group10_result_bound)
    group10_degrees
  change eval k (normalize group10_raw) z = eval k group10 z
  rw [eval_normalize]
  exact he

theorem coefficient10_approximates (k : ℂ) :
    Approximates 24 k (fun _ => eval k coefficient10 (0:ℂ × ℂ)) coefficient10 := by
  convert Approximates.exactPolynomial 24 k coefficient10 using 1
  funext z
  simp [coefficient10,eval,evalTerm]

theorem evalContact_group10 (k s e : ℂ) :
    evalContact k phiGroup10 s e = eval k coefficient10 (0:ℂ × ℂ)*(s^10*(e⁻¹)^9) := by
  norm_num [phiGroup10,coefficient10,evalContact,evalContactTerm,eval,evalTerm]
  <;> ring

theorem group10_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => evalContact k phiGroup10 (halfSum z) (meanFunction z)) group10 := by
  have hb := ((halfPower10_approximates hk).mul hk (inversePower9_approximates hk hklog)).replacePolynomial
    (body10_eval k)
  have hh := ((coefficient10_approximates k).mul hk hb).replacePolynomial
    (group10_eval k)
  simpa only [evalContact_group10] using hh

end GeneralCK.Reflection.SmallBiasContactDegrees

end


