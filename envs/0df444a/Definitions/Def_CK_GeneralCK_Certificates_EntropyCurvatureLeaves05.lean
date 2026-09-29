-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves05
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLeaves05
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:54:52.070997+00:00
-- url     : https://prove2.me/theorems/e132b299-2aca-4756-a5d6-27da4488a090
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLeaves05` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLeaves05` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLeaves05` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLeaves05 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLeaves05.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs

namespace GeneralCK.Certificates.EntropyCurvature
open GeneralCK.EntropyCurvature

theorem leaf_120 (v : ℝ) (hl : (10283 / 409600) ≤ v) (hu : v ≤ (15559 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (10283 / 409600)) (u := (15559 / 614400)) (xl := (3650356867 / 2000000000)) (xu := (457407943 / 250000000))
    (Bl := (370165699 / 200000000)) (Bu := (3710114517 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_120.2.1 endpoint_121.1 endpoint_120.2.2.2 endpoint_121.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_121 (v : ℝ) (hl : (15559 / 614400) ≤ v) (hu : v ≤ (31387 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (15559 / 614400)) (u := (31387 / 1228800)) (xl := (3641524877 / 2000000000)) (xu := (1825178437 / 1000000000))
    (Bl := (923318563 / 500000000)) (Bu := (3701656997 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_121.2.1 endpoint_122.1 endpoint_121.2.2.2 endpoint_122.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_122 (v : ℝ) (hl : (31387 / 1228800) ≤ v) (hu : v ≤ (1319 / 51200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (31387 / 1228800)) (u := (1319 / 51200)) (xl := (3632766291 / 2000000000)) (xu := (910381221 / 500000000))
    (Bl := (1842482509 / 1000000000)) (Bu := (3693274259 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_122.2.1 endpoint_123.1 endpoint_122.2.2.2 endpoint_123.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_123 (v : ℝ) (hl : (1319 / 51200) ≤ v) (hu : v ≤ (1277 / 49152)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1319 / 51200)) (u := (1277 / 49152)) (xl := (1812039933 / 1000000000)) (xu := (1816383149 / 1000000000))
    (Bl := (3676728047 / 2000000000)) (Bu := (147398601 / 80000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_123.2.1 endpoint_124.1 endpoint_123.2.2.2 endpoint_124.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_124 (v : ℝ) (hl : (1277 / 49152) ≤ v) (hu : v ≤ (16097 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1277 / 49152)) (u := (16097 / 614400)) (xl := (3615464391 / 2000000000)) (xu := (3624079873 / 2000000000))
    (Bl := (1834281063 / 1000000000)) (Bu := (1838364027 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_124.2.1 endpoint_125.1 endpoint_124.2.2.2 endpoint_125.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_125 (v : ℝ) (hl : (16097 / 614400) ≤ v) (hu : v ≤ (10821 / 409600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (16097 / 614400)) (u := (10821 / 409600)) (xl := (721383737 / 400000000)) (xu := (1807732199 / 1000000000))
    (Bl := (1830233037 / 1000000000)) (Bu := (3668562133 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_125.2.1 endpoint_126.1 endpoint_125.2.2.2 endpoint_126.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_126 (v : ℝ) (hl : (10821 / 409600) ≤ v) (hu : v ≤ (8183 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (10821 / 409600)) (u := (8183 / 307200)) (xl := (449805199 / 250000000)) (xu := (901729673 / 500000000))
    (Bl := (3652438739 / 2000000000)) (Bu := (3660466081 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_126.2.1 endpoint_127.1 endpoint_126.2.2.2 endpoint_127.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_127 (v : ℝ) (hl : (8183 / 307200) ≤ v) (hu : v ≤ (33001 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (8183 / 307200)) (u := (33001 / 1228800)) (xl := (448753999 / 250000000)) (xu := (3598441599 / 2000000000))
    (Bl := (3644478997 / 2000000000)) (Bu := (1826219373 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_127.2.1 endpoint_128.1 endpoint_127.2.2.2 endpoint_128.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_128 (v : ℝ) (hl : (33001 / 1228800) ≤ v) (hu : v ≤ (1109 / 40960)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (33001 / 1228800)) (u := (1109 / 40960)) (xl := (3581688787 / 2000000000)) (xu := (3590031999 / 2000000000))
    (Bl := (14546343 / 8000000)) (Bu := (911119751 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_128.2.1 endpoint_129.1 endpoint_128.2.2.2 endpoint_129.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_129 (v : ℝ) (hl : (1109 / 40960) ≤ v) (hu : v ≤ (33539 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1109 / 40960)) (u := (33539 / 1228800)) (xl := (1786705453 / 1000000000)) (xu := (1790844397 / 1000000000))
    (Bl := (3628757929 / 2000000000)) (Bu := (3636585757 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_129.2.1 endpoint_130.1 endpoint_129.2.2.2 endpoint_130.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_130 (v : ℝ) (hl : (33539 / 1228800) ≤ v) (hu : v ≤ (2113 / 76800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (33539 / 1228800)) (u := (2113 / 76800)) (xl := (713039461 / 400000000)) (xu := (3573410913 / 2000000000))
    (Bl := (362099449 / 200000000)) (Bu := (226797371 / 125000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_130.2.1 endpoint_131.1 endpoint_130.2.2.2 endpoint_131.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_131 (v : ℝ) (hl : (2113 / 76800) ≤ v) (hu : v ≤ (11359 / 409600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (2113 / 76800)) (u := (11359 / 409600)) (xl := (889261741 / 500000000)) (xu := (3481638 / 1953125))
    (Bl := (3613294413 / 2000000000)) (Bu := (3620994497 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_131.2.1 endpoint_132.1 endpoint_131.2.2.2 endpoint_132.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_132 (v : ℝ) (hl : (11359 / 409600) ≤ v) (hu : v ≤ (17173 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (11359 / 409600)) (u := (17173 / 614400)) (xl := (3548958889 / 2000000000)) (xu := (3557046971 / 2000000000))
    (Bl := (1802828351 / 1000000000)) (Bu := (180664721 / 100000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_132.2.1 endpoint_133.1 endpoint_132.2.2.2 endpoint_133.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_133 (v : ℝ) (hl : (17173 / 614400) ≤ v) (hu : v ≤ (2907 / 102400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (17173 / 614400)) (u := (2907 / 102400)) (xl := (706593133 / 400000000)) (xu := (221809931 / 125000000))
    (Bl := (359056451 / 200000000)) (Bu := (3605656709 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_133.2.1 endpoint_134.1 endpoint_133.2.2.2 endpoint_134.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_134 (v : ℝ) (hl : (2907 / 102400) ≤ v) (hu : v ≤ (17711 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (2907 / 102400)) (u := (17711 / 614400)) (xl := (87930253 / 50000000)) (xu := (441620709 / 250000000))
    (Bl := (715142081 / 400000000)) (Bu := (3590564517 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_134.2.1 endpoint_135.1 endpoint_134.2.2.2 endpoint_135.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_135 (v : ℝ) (hl : (17711 / 614400) ≤ v) (hu : v ≤ (899 / 30720)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (17711 / 614400)) (u := (899 / 30720)) (xl := (875421271 / 500000000)) (xu := (3517210127 / 2000000000))
    (Bl := (3561087213 / 2000000000)) (Bu := (893927603 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_135.2.1 endpoint_136.1 endpoint_135.2.2.2 endpoint_136.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_136 (v : ℝ) (hl : (899 / 30720) ≤ v) (hu : v ≤ (6083 / 204800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (899 / 30720)) (u := (6083 / 204800)) (xl := (3486383703 / 2000000000)) (xu := (3501685091 / 2000000000))
    (Bl := (1773344043 / 1000000000)) (Bu := (178054361 / 100000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_136.2.1 endpoint_137.1 endpoint_136.2.2.2 endpoint_137.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_137 (v : ℝ) (hl : (6083 / 204800) ≤ v) (hu : v ≤ (9259 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (6083 / 204800)) (u := (9259 / 307200)) (xl := (1735649713 / 1000000000)) (xu := (348638371 / 200000000))
    (Bl := (3532506467 / 2000000000)) (Bu := (3546688093 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_137.2.1 endpoint_138.1 endpoint_137.2.2.2 endpoint_138.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_138 (v : ℝ) (hl : (9259 / 307200) ≤ v) (hu : v ≤ (18787 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (9259 / 307200)) (u := (18787 / 614400)) (xl := (1728212991 / 1000000000)) (xu := (3471299433 / 2000000000))
    (Bl := (3518536091 / 2000000000)) (Bu := (1766253237 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_138.2.1 endpoint_139.1 endpoint_138.2.2.2 endpoint_139.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_139 (v : ℝ) (hl : (18787 / 614400) ≤ v) (hu : v ≤ (397 / 12800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (18787 / 614400)) (u := (397 / 12800)) (xl := (3441757373 / 2000000000)) (xu := (3456425989 / 2000000000))
    (Bl := (1752385479 / 1000000000)) (Bu := (1759268049 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_139.2.1 endpoint_140.1 endpoint_139.2.2.2 endpoint_140.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_140 (v : ℝ) (hl : (397 / 12800) ≤ v) (hu : v ≤ (773 / 24576)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (397 / 12800)) (u := (773 / 24576)) (xl := (3427287851 / 2000000000)) (xu := (172087869 / 100000000))
    (Bl := (1745602659 / 1000000000)) (Bu := (700954193 / 400000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_140.2.1 endpoint_141.1 endpoint_140.2.2.2 endpoint_141.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_141 (v : ℝ) (hl : (773 / 24576) ≤ v) (hu : v ≤ (9797 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (773 / 24576)) (u := (9797 / 307200)) (xl := (1706505951 / 1000000000)) (xu := (3427287857 / 2000000000))
    (Bl := (3477833661 / 2000000000)) (Bu := (872801331 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_141.2.1 endpoint_142.1 endpoint_141.2.2.2 endpoint_142.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_142 (v : ℝ) (hl : (9797 / 307200) ≤ v) (hu : v ≤ (6621 / 204800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (9797 / 307200)) (u := (6621 / 204800)) (xl := (3398924243 / 2000000000)) (xu := (853252977 / 500000000))
    (Bl := (216540669 / 125000000)) (Bu := (3477833667 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_142.2.1 endpoint_143.1 endpoint_142.2.2.2 endpoint_143.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_143 (v : ℝ) (hl : (6621 / 204800) ≤ v) (hu : v ≤ (5033 / 153600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (6621 / 204800)) (u := (5033 / 153600)) (xl := (846254951 / 500000000)) (xu := (3398924249 / 2000000000))
    (Bl := (27613211 / 16000000)) (Bu := (346465071 / 200000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_143.2.1 endpoint_144.1 endpoint_143.2.2.2 endpoint_144.2.2.1
    (by norm_num) (by norm_num)

end GeneralCK.Certificates.EntropyCurvature


