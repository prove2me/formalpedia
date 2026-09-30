-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ElementaryCoeff13_part01_q00
-- name    : CK_GeneralCK_Certificates_E8ElementaryCoeff13_part01_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:10:29.840948+00:00
-- url     : https://prove2.me/theorems/9dce1ff6-7468-47e1-a9ea-a074112d2d56
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ElementaryCoeff13 (part 2 of 4) (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ElementaryCoeff13 (part 2 of 4) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ElementaryCoeff13 (part 2 of 4) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ElementaryCoeff13 (part 2 of 4) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ElementaryCoeff13 (part 2 of 4) (piece 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ElementaryCoeff13_part00


namespace GeneralCK.Certificates.E8ElementaryCoeff13

open E8AnalyticGerm Reflection.ComplexEntropy E8AnalyticInverseRecurrence
open E8NormalizedCoeff5 E8NormalizedCoeff7 E8ElementaryCoeff5

private theorem coeff_sq (n : ℕ) :
    coeff (fun z : ℂ => z ^ 2) n = if n = 2 then 1 else 0 := by
  rw [coeff, iteratedDeriv_fun_pow_zero]
  split <;> simp_all

end GeneralCK.Certificates.E8ElementaryCoeff13


