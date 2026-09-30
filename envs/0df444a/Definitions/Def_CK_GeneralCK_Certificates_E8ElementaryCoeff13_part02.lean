-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ElementaryCoeff13_part02
-- name    : CK_GeneralCK_Certificates_E8ElementaryCoeff13_part02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:52:20.351714+00:00
-- url     : https://prove2.me/theorems/c4a95f58-7f8d-4f53-bf39-0f9b2acd0851
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ElementaryCoeff13 (part 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ElementaryCoeff13 (part 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ElementaryCoeff13 (part 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ElementaryCoeff13 (part 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ElementaryCoeff13 (part 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ElementaryCoeff13_part01

namespace GeneralCK.Certificates.E8ElementaryCoeff13

open E8AnalyticGerm Reflection.ComplexEntropy E8AnalyticInverseRecurrence
open E8NormalizedCoeff5 E8NormalizedCoeff7 E8ElementaryCoeff5

theorem coeff_biasBExt_twelve : coeff biasBExt 12 = 1 / 12 := by
  rw [show biasBExt = fun z : ℂ => (Real.log 2 : ℂ) -
      (fun w : ℂ => Complex.log (1 - w ^ 2)) z / 2 by rfl,
    coeff_const_sub _ _ 12 (by norm_num), coeff_div_const,
    coeff_log_one_sub_sq_twelve_priv]
  ring

theorem coeff_one_add_priv (n : ℕ) : coeff (fun z : ℂ => 1 + z) n =
    if n = 0 then 1 else if n = 1 then 1 else 0 := by
  rcases n with (_ | _ | n) <;> simp [coeff, iteratedDeriv_succ', iteratedDeriv_const]
theorem coeff_one_sub_priv (n : ℕ) : coeff (fun z : ℂ => 1 - z) n =
    if n = 0 then 1 else if n = 1 then -1 else 0 := by
  rcases n with (_ | _ | n) <;> simp [coeff, iteratedDeriv_succ', iteratedDeriv_const]


end GeneralCK.Certificates.E8ElementaryCoeff13


