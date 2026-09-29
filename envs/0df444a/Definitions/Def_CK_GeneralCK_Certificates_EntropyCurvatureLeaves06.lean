-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves06
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLeaves06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:56:16.729185+00:00
-- url     : https://prove2.me/theorems/1b880f51-5808-46c1-99f2-80c5fa2517ff
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLeaves06` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLeaves06` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLeaves06` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLeaves06 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLeaves06.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs

namespace GeneralCK.Certificates.EntropyCurvature
open GeneralCK.EntropyCurvature

theorem leaf_144 (v : ℝ) (hl : (5033 / 153600) ≤ v) (hu : v ≤ (20401 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (5033 / 153600)) (u := (20401 / 614400)) (xl := (1685646857 / 1000000000)) (xu := (338501981 / 200000000))
    (Bl := (687766161 / 400000000)) (Bu := (3451651381 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_144.2.1 endpoint_145.1 endpoint_144.2.2.2 endpoint_145.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_145 (v : ℝ) (hl : (20401 / 614400) ≤ v) (hu : v ≤ (689 / 20480)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (20401 / 614400)) (u := (689 / 20480)) (xl := (3357741293 / 2000000000)) (xu := (84282343 / 50000000))
    (Bl := (856546079 / 500000000)) (Bu := (3438830811 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_145.2.1 endpoint_146.1 endpoint_145.2.2.2 endpoint_146.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_146 (v : ℝ) (hl : (689 / 20480) ≤ v) (hu : v ≤ (20939 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (689 / 20480)) (u := (20939 / 614400)) (xl := (104511189 / 62500000)) (xu := (3357741299 / 2000000000))
    (Bl := (3413707411 / 2000000000)) (Bu := (1713092161 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_146.2.1 endpoint_147.1 endpoint_146.2.2.2 endpoint_147.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_147 (v : ℝ) (hl : (20939 / 614400) ≤ v) (hu : v ≤ (2651 / 76800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (20939 / 614400)) (u := (2651 / 76800)) (xl := (832784913 / 500000000)) (xu := (1672179027 / 1000000000))
    (Bl := (3401395767 / 2000000000)) (Bu := (3413707417 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_147.2.1 endpoint_148.1 endpoint_147.2.2.2 endpoint_148.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_148 (v : ℝ) (hl : (2651 / 76800) ≤ v) (hu : v ≤ (7159 / 204800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (2651 / 76800)) (u := (7159 / 204800)) (xl := (414760243 / 250000000)) (xu := (1665569829 / 1000000000))
    (Bl := (3389245223 / 2000000000)) (Bu := (3401395773 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_148.2.1 endpoint_149.1 endpoint_148.2.2.2 endpoint_149.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_149 (v : ℝ) (hl : (7159 / 204800) ≤ v) (hu : v ≤ (10873 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (7159 / 204800)) (u := (10873 / 307200)) (xl := (82629523 / 50000000)) (xu := (66361639 / 40000000))
    (Bl := (3377251773 / 2000000000)) (Bu := (3389245229 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_149.2.1 endpoint_150.1 endpoint_149.2.2.2 endpoint_150.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_150 (v : ℝ) (hl : (10873 / 307200) ≤ v) (hu : v ≤ (4403 / 122880)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (10873 / 307200)) (u := (4403 / 122880)) (xl := (3292432719 / 2000000000)) (xu := (1652590463 / 1000000000))
    (Bl := (84135289 / 50000000)) (Bu := (3377251779 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_150.2.1 endpoint_151.1 endpoint_150.2.2.2 endpoint_151.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_151 (v : ℝ) (hl : (4403 / 122880) ≤ v) (hu : v ≤ (1857 / 51200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (4403 / 122880)) (u := (1857 / 51200)) (xl := (1639916813 / 1000000000)) (xu := (131697309 / 80000000))
    (Bl := (3353720867 / 2000000000)) (Bu := (1682705783 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_151.2.1 endpoint_152.1 endpoint_151.2.2.2 endpoint_152.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_152 (v : ℝ) (hl : (1857 / 51200) ≤ v) (hu : v ≤ (22553 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1857 / 51200)) (u := (22553 / 614400)) (xl := (3267380057 / 2000000000)) (xu := (102494801 / 62500000))
    (Bl := (334217611 / 200000000)) (Bu := (3353720873 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_152.2.1 endpoint_153.1 endpoint_152.2.2.2 endpoint_153.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_153 (v : ℝ) (hl : (22553 / 614400) ≤ v) (hu : v ≤ (11411 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (22553 / 614400)) (u := (11411 / 307200)) (xl := (3255068557 / 2000000000)) (xu := (3267380063 / 2000000000))
    (Bl := (1665386917 / 1000000000)) (Bu := (835544029 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_153.2.1 endpoint_154.1 endpoint_153.2.2.2 endpoint_154.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_154 (v : ℝ) (hl : (11411 / 307200) ≤ v) (hu : v ≤ (7697 / 204800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (11411 / 307200)) (u := (7697 / 204800)) (xl := (3242895789 / 2000000000)) (xu := (3255068563 / 2000000000))
    (Bl := (1659755353 / 1000000000)) (Bu := (41634673 / 25000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_154.2.1 endpoint_155.1 endpoint_154.2.2.2 endpoint_155.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_155 (v : ℝ) (hl : (7697 / 204800) ≤ v) (hu : v ≤ (73 / 1920)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (7697 / 204800)) (u := (73 / 1920)) (xl := (403857317 / 250000000)) (xu := (648579159 / 400000000))
    (Bl := (661676701 / 400000000)) (Bu := (414938839 / 250000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_155.2.1 endpoint_156.1 endpoint_155.2.2.2 endpoint_156.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_156 (v : ℝ) (hl : (73 / 1920) ≤ v) (hu : v ≤ (23629 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (73 / 1920)) (u := (23629 / 614400)) (xl := (3218953689 / 2000000000)) (xu := (1615429271 / 1000000000))
    (Bl := (1648694563 / 1000000000)) (Bu := (3308383511 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_156.2.1 endpoint_157.1 endpoint_156.2.2.2 endpoint_157.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_157 (v : ℝ) (hl : (23629 / 614400) ≤ v) (hu : v ≤ (3983 / 102400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (23629 / 614400)) (u := (3983 / 102400)) (xl := (1603589123 / 1000000000)) (xu := (643790739 / 400000000))
    (Bl := (657304913 / 400000000)) (Bu := (824347283 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_157.2.1 endpoint_158.1 endpoint_157.2.2.2 endpoint_158.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_158 (v : ℝ) (hl : (3983 / 102400) ≤ v) (hu : v ≤ (24167 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (3983 / 102400)) (u := (24167 / 614400)) (xl := (639105861 / 400000000)) (xu := (801794563 / 500000000))
    (Bl := (81894673 / 50000000)) (Bu := (3286524571 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_158.2.1 endpoint_159.1 endpoint_158.2.2.2 endpoint_159.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_159 (v : ℝ) (hl : (24167 / 614400) ≤ v) (hu : v ≤ (6109 / 153600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (24167 / 614400)) (u := (6109 / 153600)) (xl := (159200203 / 100000000)) (xu := (3195529311 / 2000000000))
    (Bl := (3265173387 / 2000000000)) (Bu := (1637893463 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_159.2.1 endpoint_160.1 endpoint_159.2.2.2 endpoint_160.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_160 (v : ℝ) (hl : (6109 / 153600) ≤ v) (hu : v ≤ (1647 / 40960)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (6109 / 153600)) (u := (1647 / 40960)) (xl := (3172599799 / 2000000000)) (xu := (1592002033 / 1000000000))
    (Bl := (1627340627 / 1000000000)) (Bu := (3265173393 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_160.2.1 endpoint_161.1 endpoint_160.2.2.2 endpoint_161.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_161 (v : ℝ) (hl : (1647 / 40960) ≤ v) (hu : v ≤ (12487 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1647 / 40960)) (u := (12487 / 307200)) (xl := (632262779 / 400000000)) (xu := (634519961 / 400000000))
    (Bl := (1622153947 / 1000000000)) (Bu := (162734063 / 100000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_161.2.1 endpoint_162.1 endpoint_161.2.2.2 endpoint_162.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_162 (v : ℝ) (hl : (12487 / 307200) ≤ v) (hu : v ≤ (25243 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (12487 / 307200)) (u := (25243 / 614400)) (xl := (3150143809 / 2000000000)) (xu := (3161313901 / 2000000000))
    (Bl := (323405077 / 200000000)) (Bu := (32443079 / 20000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_162.2.1 endpoint_163.1 endpoint_162.2.2.2 endpoint_163.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_163 (v : ℝ) (hl : (25243 / 614400) ≤ v) (hu : v ≤ (1063 / 25600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (25243 / 614400)) (u := (1063 / 25600)) (xl := (3139087079 / 2000000000)) (xu := (630028763 / 400000000))
    (Bl := (1611953709 / 1000000000)) (Bu := (404256347 / 250000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_163.2.1 endpoint_164.1 endpoint_163.2.2.2 endpoint_164.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_164 (v : ℝ) (hl : (1063 / 25600) ≤ v) (hu : v ≤ (25781 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1063 / 25600)) (u := (25781 / 614400)) (xl := (1564070663 / 1000000000)) (xu := (627817417 / 400000000))
    (Bl := (3213875459 / 2000000000)) (Bu := (100747107 / 62500000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_164.2.1 endpoint_165.1 endpoint_164.2.2.2 endpoint_165.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_165 (v : ℝ) (hl : (25781 / 614400) ≤ v) (hu : v ≤ (521 / 12288)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (25781 / 614400)) (u := (521 / 12288)) (xl := (1558652119 / 1000000000)) (xu := (782035333 / 500000000))
    (Bl := (3203952583 / 2000000000)) (Bu := (642775093 / 400000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_165.2.1 endpoint_166.1 endpoint_165.2.2.2 endpoint_166.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_166 (v : ℝ) (hl : (521 / 12288) ≤ v) (hu : v ≤ (8773 / 204800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (521 / 12288)) (u := (8773 / 204800)) (xl := (1553286789 / 1000000000)) (xu := (779326061 / 500000000))
    (Bl := (638827311 / 400000000)) (Bu := (3203952589 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_166.2.1 endpoint_167.1 endpoint_166.2.2.2 endpoint_167.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_167 (v : ℝ) (hl : (8773 / 204800) ≤ v) (hu : v ≤ (6647 / 153600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (8773 / 204800)) (u := (6647 / 153600)) (xl := (154797359 / 100000000)) (xu := (194160849 / 125000000))
    (Bl := (636885041 / 400000000)) (Bu := (3194136561 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_167.2.1 endpoint_168.1 endpoint_167.2.2.2 endpoint_168.2.2.1
    (by norm_num) (by norm_num)

end GeneralCK.Certificates.EntropyCurvature


