-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_q11_c02
-- name    : CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_q11_c02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T14:48:23.857317+00:00
-- url     : https://prove2.me/theorems/225bff5b-96fc-49ba-96f7-52e1f387755a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (proof part of coverage019)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (proof part of coverage019)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (proof part of coverage019)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (proof part of coverage019) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage008 (proof part of coverage019).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0305__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0309__4

namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000

theorem coverage019_part_02 {a z : ℝ} (ha : Bounds (109/500) (117/500) a)
    (hz : Bounds (17/200) (43/500) z) (h0 : a ≤ (113/500:ℝ)) (h1 : ¬ (a ≤ (111/500:ℝ))) (h5 : a ≤ (28/125:ℝ)) :
    0 < curvature a (a*z) := by
  by_cases h6 : a ≤ (223/1000:ℝ)
  · exact Cell0308.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
  · exact Cell0309.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz

end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily


