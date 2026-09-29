-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves07
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLeaves07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:56:42.603992+00:00
-- url     : https://prove2.me/theorems/7726e48e-9d2e-4288-aa3c-b979ad21f7cb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLeaves07` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLeaves07` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLeaves07` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLeaves07 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLeaves07.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs

namespace GeneralCK.Certificates.EntropyCurvature
open GeneralCK.EntropyCurvature

theorem leaf_168 (v : ℝ) (hl : (6647 / 153600) ≤ v) (hu : v ≤ (26857 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (6647 / 153600)) (u := (26857 / 614400)) (xl := (385677867 / 250000000)) (xu := (1547973593 / 1000000000))
    (Bl := (3174816431 / 2000000000)) (Bu := (3184425211 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_168.2.1 endpoint_169.1 endpoint_168.2.2.2 endpoint_169.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_169 (v : ℝ) (hl : (26857 / 614400) ≤ v) (hu : v ≤ (4521 / 102400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (26857 / 614400)) (u := (4521 / 102400)) (xl := (3074998811 / 2000000000)) (xu := (1542711471 / 1000000000))
    (Bl := (98915881 / 62500000)) (Bu := (3174816437 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_169.2.1 endpoint_170.1 endpoint_169.2.2.2 endpoint_170.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_170 (v : ℝ) (hl : (4521 / 102400) ≤ v) (hu : v ≤ (1729 / 38400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (4521 / 102400)) (u := (1729 / 38400)) (xl := (1527221521 / 1000000000)) (xu := (3074998817 / 2000000000))
    (Bl := (3146585457 / 2000000000)) (Bu := (1582654099 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_170.2.1 endpoint_171.1 endpoint_170.2.2.2 endpoint_171.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_171 (v : ℝ) (hl : (1729 / 38400) ≤ v) (hu : v ≤ (14101 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1729 / 38400)) (u := (14101 / 307200)) (xl := (758566179 / 500000000)) (xu := (381805381 / 250000000))
    (Bl := (3128241847 / 2000000000)) (Bu := (3146585463 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_171.2.1 endpoint_172.1 endpoint_171.2.2.2 endpoint_172.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_172 (v : ℝ) (hl : (14101 / 307200) ≤ v) (hu : v ≤ (479 / 10240)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (14101 / 307200)) (u := (479 / 10240)) (xl := (753612383 / 500000000)) (xu := (1517132361 / 1000000000))
    (Bl := (3110263063 / 2000000000)) (Bu := (3128241853 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_172.2.1 endpoint_173.1 endpoint_172.2.2.2 endpoint_173.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_173 (v : ℝ) (hl : (479 / 10240) ≤ v) (hu : v ≤ (14639 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (479 / 10240)) (u := (14639 / 307200)) (xl := (748745997 / 500000000)) (xu := (1507224769 / 1000000000))
    (Bl := (3092635607 / 2000000000)) (Bu := (3110263069 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_173.2.1 endpoint_174.1 endpoint_173.2.2.2 endpoint_174.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_174 (v : ℝ) (hl : (14639 / 307200) ≤ v) (hu : v ≤ (3727 / 76800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (14639 / 307200)) (u := (3727 / 76800)) (xl := (1487927659 / 1000000000)) (xu := (1497491997 / 1000000000))
    (Bl := (615069343 / 400000000)) (Bu := (3092635613 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_174.2.1 endpoint_175.1 endpoint_174.2.2.2 endpoint_175.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_175 (v : ℝ) (hl : (3727 / 76800) ≤ v) (hu : v ≤ (5059 / 102400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (3727 / 76800)) (u := (5059 / 102400)) (xl := (36963143 / 25000000)) (xu := (743963831 / 500000000))
    (Bl := (3058384309 / 2000000000)) (Bu := (3075346721 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_175.2.1 endpoint_176.1 endpoint_175.2.2.2 endpoint_176.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_176 (v : ℝ) (hl : (5059 / 102400) ≤ v) (hu : v ≤ (7723 / 153600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (5059 / 102400)) (u := (7723 / 153600)) (xl := (734640227 / 500000000)) (xu := (1478525723 / 1000000000))
    (Bl := (3041736947 / 2000000000)) (Bu := (611676863 / 400000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_176.2.1 endpoint_177.1 endpoint_176.2.2.2 endpoint_177.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_177 (v : ℝ) (hl : (7723 / 153600) ≤ v) (hu : v ≤ (3143 / 61440)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (7723 / 153600)) (u := (3143 / 61440)) (xl := (2920372873 / 2000000000)) (xu := (1469280457 / 1000000000))
    (Bl := (1512696891 / 1000000000)) (Bu := (3041736953 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_177.2.1 endpoint_178.1 endpoint_177.2.2.2 endpoint_178.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_178 (v : ℝ) (hl : (3143 / 61440) ≤ v) (hu : v ≤ (333 / 6400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (3143 / 61440)) (u := (333 / 6400)) (xl := (580495407 / 400000000)) (xu := (2920372879 / 2000000000))
    (Bl := (1504672259 / 1000000000)) (Bu := (756348447 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_178.2.1 endpoint_179.1 endpoint_178.2.2.2 endpoint_179.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_179 (v : ℝ) (hl : (333 / 6400) ≤ v) (hu : v ≤ (16253 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (333 / 6400)) (u := (16253 / 307200)) (xl := (2884863609 / 2000000000)) (xu := (2902477041 / 2000000000))
    (Bl := (748394843 / 500000000)) (Bu := (752336131 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_179.2.1 endpoint_180.1 endpoint_179.2.2.2 endpoint_180.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_180 (v : ℝ) (hl : (16253 / 307200) ≤ v) (hu : v ≤ (8261 / 153600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (16253 / 307200)) (u := (8261 / 153600)) (xl := (89610103 / 62500000)) (xu := (576972723 / 400000000))
    (Bl := (2978089047 / 2000000000)) (Bu := (1496789689 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_180.2.1 endpoint_181.1 endpoint_180.2.2.2 endpoint_181.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_181 (v : ℝ) (hl : (8261 / 153600) ≤ v) (hu : v ≤ (5597 / 102400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (8261 / 153600)) (u := (5597 / 102400)) (xl := (1425223621 / 1000000000)) (xu := (1433761651 / 1000000000))
    (Bl := (2962864697 / 2000000000)) (Bu := (2978089053 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_181.2.1 endpoint_182.1 endpoint_181.2.2.2 endpoint_182.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_182 (v : ℝ) (hl : (5597 / 102400) ≤ v) (hu : v ≤ (853 / 15360)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (5597 / 102400)) (u := (853 / 15360)) (xl := (2833627019 / 2000000000)) (xu := (178152953 / 125000000))
    (Bl := (736974473 / 500000000)) (Bu := (2962864703 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_182.2.1 endpoint_183.1 endpoint_182.2.2.2 endpoint_183.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_183 (v : ℝ) (hl : (853 / 15360) ≤ v) (hu : v ≤ (17329 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (853 / 15360)) (u := (17329 / 307200)) (xl := (563410919 / 400000000)) (xu := (113345081 / 80000000))
    (Bl := (733295151 / 500000000)) (Bu := (1473948949 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_183.2.1 endpoint_184.1 endpoint_183.2.2.2 endpoint_184.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_184 (v : ℝ) (hl : (17329 / 307200) ≤ v) (hu : v ≤ (2933 / 51200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (17329 / 307200)) (u := (2933 / 51200)) (xl := (21880643 / 15625000)) (xu := (2817054601 / 2000000000))
    (Bl := (2918705173 / 2000000000)) (Bu := (293318061 / 200000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_184.2.1 endpoint_185.1 endpoint_184.2.2.2 endpoint_185.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_185 (v : ℝ) (hl : (2933 / 51200) ≤ v) (hu : v ≤ (17867 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (2933 / 51200)) (u := (17867 / 307200)) (xl := (556924567 / 400000000)) (xu := (280072231 / 200000000))
    (Bl := (290446429 / 200000000)) (Bu := (2918705179 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_185.2.1 endpoint_186.1 endpoint_185.2.2.2 endpoint_186.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_186 (v : ℝ) (hl : (17867 / 307200) ≤ v) (hu : v ≤ (2267 / 38400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (17867 / 307200)) (u := (2267 / 38400)) (xl := (6921873 / 5000000)) (xu := (2784622841 / 2000000000))
    (Bl := (2890450969 / 2000000000)) (Bu := (363058037 / 250000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_186.2.1 endpoint_187.1 endpoint_186.2.2.2 endpoint_187.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_187 (v : ℝ) (hl : (2267 / 38400) ≤ v) (hu : v ≤ (1227 / 20480)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (2267 / 38400)) (u := (1227 / 20480)) (xl := (688273681 / 500000000)) (xu := (1384374603 / 1000000000))
    (Bl := (2876658539 / 2000000000)) (Bu := (115618039 / 80000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_187.2.1 endpoint_188.1 endpoint_187.2.2.2 endpoint_188.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_188 (v : ℝ) (hl : (1227 / 20480) ≤ v) (hu : v ≤ (9337 / 153600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1227 / 20480)) (u := (9337 / 153600)) (xl := (2737653017 / 2000000000)) (xu := (275309473 / 200000000))
    (Bl := (1431540307 / 1000000000)) (Bu := (575331709 / 400000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_188.2.1 endpoint_189.1 endpoint_188.2.2.2 endpoint_189.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_189 (v : ℝ) (hl : (9337 / 153600) ≤ v) (hu : v ≤ (18943 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (9337 / 153600)) (u := (18943 / 307200)) (xl := (272241797 / 200000000)) (xu := (2737653023 / 2000000000))
    (Bl := (569942217 / 400000000)) (Bu := (143154031 / 100000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_189.2.1 endpoint_190.1 endpoint_189.2.2.2 endpoint_190.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_190 (v : ℝ) (hl : (18943 / 307200) ≤ v) (hu : v ≤ (1601 / 25600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (18943 / 307200)) (u := (1601 / 25600)) (xl := (1353691863 / 1000000000)) (xu := (340302247 / 250000000))
    (Bl := (2836544103 / 2000000000)) (Bu := (2849711091 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_190.2.1 endpoint_191.1 endpoint_190.2.2.2 endpoint_191.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_191 (v : ℝ) (hl : (1601 / 25600) ≤ v) (hu : v ≤ (19481 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1601 / 25600)) (u := (19481 / 307200)) (xl := (107701787 / 80000000)) (xu := (2707383731 / 2000000000))
    (Bl := (1411787029 / 1000000000)) (Bu := (709136027 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_191.2.1 endpoint_192.1 endpoint_191.2.2.2 endpoint_192.2.2.1
    (by norm_num) (by norm_num)

end GeneralCK.Certificates.EntropyCurvature


