-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionHighBiasRegion
-- name    : CK_GeneralCK_ReflectionHighBiasRegion
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T11:47:26.706591+00:00
-- url     : https://prove2.me/theorems/0e4da87c-20df-4bab-8360-31586cac05bf
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionHighBiasRegion` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionHighBiasRegion` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionHighBiasRegion` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionHighBiasRegion (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionHighBiasRegion.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_HighBiasCoarseBounds
import Definitions.Def_CK_GeneralCK_Certificates_Generated_HighBiasCoarseConstants

-- ===== source module GeneralCK.ReflectionHighBiasRegion =====
section

namespace GeneralCK.Reflection

/-- The full high-bias / small-partner rectangle, including a arbitrarily close
to one. The compact coefficient enclosure and all scalar bounds are discharged. -/
theorem curvature_high_bias_small_partner {a b : ℝ}
    (ha : (999/1000:ℝ)≤a) (ha' : a<1) (hb : 0<b) (hb' : b≤1/2) :
    0<curvature a b := by
  have ha0 : 0<a := by linarith
  have hab : a*(b/a)=b := by field_simp
  have h := HighBias.curvature_pos_of_certificates
    Certificates.HighBiasCoarse.entropy_high_bias
    Certificates.HighBiasCoarse.entropy_half
    Certificates.HighBiasCoarse.log_two_upper
    (by convert Certificates.HighBiasCoarse.contact_lower using 1; norm_num)
    (by convert Certificates.HighBiasCoarse.contact_upper using 1; norm_num)
    Certificates.HighBiasCoarse.coefficient_bounds
    (a := a) (z := b/a) ⟨ha,ha'⟩ (div_pos hb ha0) (by simpa only [hab] using hb')
  simpa only [hab] using h

end GeneralCK.Reflection

end


