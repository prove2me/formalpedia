-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionRemainingRegionsCertified_q00
-- name    : CK_GeneralCK_ReflectionRemainingRegionsCertified_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-09T10:08:07.58011+00:00
-- url     : https://prove2.me/theorems/c800ad4b-b0ff-4223-b224-f11fa2f73c3c
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionRemainingRegionsCertified (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionRemainingRegionsCertified (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionRemainingRegionsCertified (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionRemainingRegionsCertified (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionRemainingRegionsCertified (piece 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_ReflectionRemainingRegionsExtended
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_FullCertificate
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_FullCertificate
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionMidpointCombinedCoverage



/-!
# Reflection remainder after all completed midpoint families

The four kernel-checked midpoint families cover the ratio strip through
`17 / 200`.  This file exposes the smaller compact premise that remains.
-/

namespace GeneralCK.Reflection
open Set

theorem curvature_low_ratio_to_seventeen_two_hundred {a z : ℝ}
    (ha : (3 / 20 : ℝ) ≤ a) (ha1 : a < 1)
    (hz : 0 < z) (hz1 : z ≤ 17 / 200) :
    0 < curvature a (a * z) := by
  by_cases hhigh : (999 / 1000 : ℝ) ≤ a
  · apply curvature_high_bias hhigh ha1
    · exact mul_pos (by linarith) hz
    · nlinarith
  have habox : Certificates.Reflection.Bounds (3 / 20 : ℝ) (999 / 1000) a :=
    ⟨ha, (lt_of_not_ge hhigh).le⟩
  by_cases hbase : z ≤ (1 / 20 : ℝ)
  · exact curvature_low_ratio_to_twentieth ha ha1 hz hbase
  by_cases hext : z ≤ (406621 / 5000000 : ℝ)
  · exact Certificates.ReflectionMidpointExtensionFamily.full_midpoint_extension
      habox ⟨(lt_of_not_ge hbase).le, hext⟩
  · exact Certificates.ReflectionMidpointNextBandFamily.full_midpoint_next_band
      habox ⟨(lt_of_not_ge hext).le, hz1⟩

end GeneralCK.Reflection


