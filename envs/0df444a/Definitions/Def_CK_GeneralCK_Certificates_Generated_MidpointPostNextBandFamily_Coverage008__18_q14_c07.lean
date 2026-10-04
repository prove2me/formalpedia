-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_q14_c07
-- name    : CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_q14_c07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T19:22:11.135647+00:00
-- url     : https://prove2.me/theorems/e02042b9-ff80-43e2-8202-449c72677b08
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (proof part of coverage022)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (proof part of coverage022)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (proof part of coverage022)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (proof part of coverage022) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage008 (proof part of coverage022).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0363__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0367__3

namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000

theorem coverage022_part_07 {a z : ℝ} (ha : Bounds (289/1000) (169/500) a)
    (hz : Bounds (17/200) (43/500) z) (h0 : ¬ (a ≤ (31/100:ℝ))) (h8 : ¬ (a ≤ (161/500:ℝ))) (h12 : ¬ (a ≤ (33/100:ℝ))) :
    0 < curvature a (a*z) := by
  by_cases h14 : a ≤ (167/500:ℝ)
  · exact Cell0366.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
  · exact Cell0367.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz

end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily


