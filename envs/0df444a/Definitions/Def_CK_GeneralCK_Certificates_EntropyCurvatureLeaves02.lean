-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves02
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLeaves02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:56:11.242221+00:00
-- url     : https://prove2.me/theorems/6cf595f9-0950-4a1a-930d-6319fba6335e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLeaves02` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLeaves02` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLeaves02` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLeaves02 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLeaves02.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs

namespace GeneralCK.Certificates.EntropyCurvature
open GeneralCK.EntropyCurvature

theorem leaf_48 (v : ℝ) (hl : (11151 / 819200) ≤ v) (hu : v ≤ (16861 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (11151 / 819200)) (u := (16861 / 1228800)) (xl := (33398231 / 15625000)) (xu := (4283093523 / 2000000000))
    (Bl := (4302606623 / 2000000000)) (Bu := (538813079 / 250000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_48.2.1 endpoint_49.1 endpoint_48.2.2.2 endpoint_49.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_49 (v : ℝ) (hl : (16861 / 1228800) ≤ v) (hu : v ≤ (33991 / 2457600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (16861 / 1228800)) (u := (33991 / 2457600)) (xl := (2133458621 / 1000000000)) (xu := (534371697 / 250000000))
    (Bl := (4294772267 / 2000000000)) (Bu := (4302606631 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_49.2.1 endpoint_50.1 endpoint_49.2.2.2 endpoint_50.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_50 (v : ℝ) (hl : (33991 / 2457600) ≤ v) (hu : v ≤ (571 / 40960)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (33991 / 2457600)) (u := (571 / 40960)) (xl := (851784707 / 400000000)) (xu := (17067669 / 8000000))
    (Bl := (1071750139 / 500000000)) (Bu := (171790891 / 80000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_50.2.1 endpoint_51.1 endpoint_50.2.2.2 endpoint_51.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_51 (v : ℝ) (hl : (571 / 40960) ≤ v) (hu : v ≤ (34529 / 2457600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (571 / 40960)) (u := (34529 / 2457600)) (xl := (4250991467 / 2000000000)) (xu := (4258923543 / 2000000000))
    (Bl := (1069822627 / 500000000)) (Bu := (1071750141 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_51.2.1 endpoint_52.1 endpoint_51.2.2.2 endpoint_52.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_52 (v : ℝ) (hl : (34529 / 2457600) ≤ v) (hu : v ≤ (17399 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (34529 / 2457600)) (u := (17399 / 1228800)) (xl := (2121560041 / 1000000000)) (xu := (170039659 / 80000000))
    (Bl := (4271641167 / 2000000000)) (Bu := (1069822629 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_52.2.1 endpoint_53.1 endpoint_52.2.2.2 endpoint_53.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_53 (v : ℝ) (hl : (17399 / 1228800) ≤ v) (hu : v ≤ (11689 / 819200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (17399 / 1228800)) (u := (11689 / 819200)) (xl := (847061689 / 400000000)) (xu := (424312009 / 200000000))
    (Bl := (2132025799 / 1000000000)) (Bu := (170865647 / 80000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_53.2.1 endpoint_54.1 endpoint_53.2.2.2 endpoint_54.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_54 (v : ℝ) (hl : (11689 / 819200) ≤ v) (hu : v ≤ (4417 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (11689 / 819200)) (u := (4417 / 307200)) (xl := (4227555641 / 2000000000)) (xu := (4235308453 / 2000000000))
    (Bl := (532065111 / 250000000)) (Bu := (2132025803 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_54.2.1 endpoint_55.1 endpoint_54.2.2.2 endpoint_55.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_55 (v : ℝ) (hl : (4417 / 307200) ≤ v) (hu : v ≤ (7121 / 491520)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (4417 / 307200)) (u := (7121 / 491520)) (xl := (2109930389 / 1000000000)) (xu := (4227555649 / 2000000000))
    (Bl := (849809629 / 400000000)) (Bu := (66508139 / 31250000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_55.2.1 endpoint_56.1 endpoint_55.2.2.2 endpoint_56.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_56 (v : ℝ) (hl : (7121 / 491520) ≤ v) (hu : v ≤ (5979 / 409600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (7121 / 491520)) (u := (5979 / 409600)) (xl := (842444597 / 400000000)) (xu := (2109930393 / 1000000000))
    (Bl := (2120816247 / 1000000000)) (Bu := (4249048153 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_56.2.1 endpoint_57.1 endpoint_56.2.2.2 endpoint_57.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_57 (v : ℝ) (hl : (5979 / 409600) ≤ v) (hu : v ≤ (36143 / 2457600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (5979 / 409600)) (u := (36143 / 2457600)) (xl := (32848761 / 15625000)) (xu := (4212222993 / 2000000000))
    (Bl := (846854617 / 400000000)) (Bu := (2120816251 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_57.2.1 endpoint_58.1 endpoint_57.2.2.2 endpoint_58.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_58 (v : ℝ) (hl : (36143 / 2457600) ≤ v) (hu : v ≤ (9103 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (36143 / 2457600)) (u := (9103 / 614400)) (xl := (1049278803 / 500000000)) (xu := (525580177 / 250000000))
    (Bl := (4226969083 / 2000000000)) (Bu := (4234273093 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_58.2.1 endpoint_59.1 endpoint_58.2.2.2 endpoint_59.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_59 (v : ℝ) (hl : (9103 / 614400) ≤ v) (hu : v ≤ (12227 / 819200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (9103 / 614400)) (u := (12227 / 819200)) (xl := (837928717 / 400000000)) (xu := (209855761 / 100000000))
    (Bl := (527464959 / 250000000)) (Bu := (4226969091 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_59.2.1 endpoint_60.1 endpoint_59.2.2.2 endpoint_60.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_60 (v : ℝ) (hl : (12227 / 819200) ≤ v) (hu : v ≤ (739 / 49152)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (12227 / 819200)) (u := (739 / 49152)) (xl := (4182225727 / 2000000000)) (xu := (4189643593 / 2000000000))
    (Bl := (526565507 / 250000000)) (Bu := (824164 / 390625)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_60.2.1 endpoint_61.1 endpoint_60.2.2.2 endpoint_61.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_61 (v : ℝ) (hl : (739 / 49152) ≤ v) (hu : v ≤ (37219 / 2457600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (739 / 49152)) (u := (37219 / 2457600)) (xl := (4174860857 / 2000000000)) (xu := (836445147 / 400000000))
    (Bl := (2102690727 / 1000000000)) (Bu := (131641377 / 62500000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_61.2.1 endpoint_62.1 endpoint_61.2.2.2 endpoint_62.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_62 (v : ℝ) (hl : (37219 / 2457600) ≤ v) (hu : v ≤ (781 / 51200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (37219 / 2457600)) (u := (781 / 51200)) (xl := (4167548213 / 2000000000)) (xu := (834972173 / 400000000))
    (Bl := (41982911 / 20000000)) (Bu := (2102690731 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_62.2.1 endpoint_63.1 endpoint_62.2.2.2 endpoint_63.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_63 (v : ℝ) (hl : (781 / 51200) ≤ v) (hu : v ≤ (37757 / 2457600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (781 / 51200)) (u := (37757 / 2457600)) (xl := (520035881 / 250000000)) (xu := (4167548221 / 2000000000))
    (Bl := (4191252251 / 2000000000)) (Bu := (1049572777 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_63.2.1 endpoint_64.1 endpoint_63.2.2.2 endpoint_64.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_64 (v : ℝ) (hl : (37757 / 2457600) ≤ v) (hu : v ≤ (19013 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (37757 / 2457600)) (u := (19013 / 1228800)) (xl := (415307663 / 200000000)) (xu := (260017941 / 125000000))
    (Bl := (167370567 / 80000000)) (Bu := (4191252259 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_64.2.1 endpoint_65.1 endpoint_64.2.2.2 endpoint_65.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_65 (v : ℝ) (hl : (19013 / 1228800) ≤ v) (hu : v ≤ (2553 / 163840)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (19013 / 1228800)) (u := (2553 / 163840)) (xl := (1036479061 / 500000000)) (xu := (2076538319 / 1000000000))
    (Bl := (835465231 / 400000000)) (Bu := (4184264183 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_65.2.1 endpoint_66.1 endpoint_65.2.2.2 endpoint_66.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_66 (v : ℝ) (hl : (2553 / 163840) ≤ v) (hu : v ≤ (9641 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (2553 / 163840)) (u := (9641 / 614400)) (xl := (413880519 / 200000000)) (xu := (1036479063 / 500000000))
    (Bl := (4170437491 / 2000000000)) (Bu := (4177326163 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_66.2.1 endpoint_67.1 endpoint_66.2.2.2 endpoint_67.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_67 (v : ℝ) (hl : (9641 / 614400) ≤ v) (hu : v ≤ (38833 / 2457600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (9641 / 614400)) (u := (38833 / 2457600)) (xl := (4131742781 / 2000000000)) (xu := (4138805197 / 2000000000))
    (Bl := (520449687 / 250000000)) (Bu := (2085218749 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_67.2.1 endpoint_68.1 endpoint_67.2.2.2 endpoint_68.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_68 (v : ℝ) (hl : (38833 / 2457600) ≤ v) (hu : v ≤ (6517 / 409600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (38833 / 2457600)) (u := (6517 / 409600)) (xl := (824945669 / 400000000)) (xu := (1032935697 / 500000000))
    (Bl := (8313611 / 4000000)) (Bu := (4163597503 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_68.2.1 endpoint_69.1 endpoint_68.2.2.2 endpoint_69.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_69 (v : ℝ) (hl : (6517 / 409600) ≤ v) (hu : v ≤ (39371 / 2457600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (6517 / 409600)) (u := (39371 / 2457600)) (xl := (164710449 / 80000000)) (xu := (128897761 / 62500000))
    (Bl := (1037515211 / 500000000)) (Bu := (4156805507 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_69.2.1 endpoint_70.1 endpoint_69.2.2.2 endpoint_70.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_70 (v : ℝ) (hl : (39371 / 2457600) ≤ v) (hu : v ≤ (991 / 61440)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (39371 / 2457600)) (u := (991 / 61440)) (xl := (164433631 / 80000000)) (xu := (257360077 / 125000000))
    (Bl := (1035840721 / 500000000)) (Bu := (4150060851 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_70.2.1 endpoint_71.1 endpoint_70.2.2.2 endpoint_71.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_71 (v : ℝ) (hl : (991 / 61440) ≤ v) (hu : v ≤ (13303 / 819200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (991 / 61440)) (u := (13303 / 819200)) (xl := (820793273 / 400000000)) (xu := (2055420391 / 1000000000))
    (Bl := (1034177747 / 500000000)) (Bu := (4143362891 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_71.2.1 endpoint_72.1 endpoint_71.2.2.2 endpoint_72.2.2.1
    (by norm_num) (by norm_num)

end GeneralCK.Certificates.EntropyCurvature


