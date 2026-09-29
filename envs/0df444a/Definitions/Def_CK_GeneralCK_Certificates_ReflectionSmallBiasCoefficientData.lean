-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasCoefficientData
-- name    : CK_GeneralCK_Certificates_ReflectionSmallBiasCoefficientData
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:01:19.338663+00:00
-- url     : https://prove2.me/theorems/c5e2053b-5074-4c14-ab47-8150f8ebc40d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionSmallBiasCoefficientData` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionSmallBiasCoefficientData` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionSmallBiasCoefficientData` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionSmallBiasCoefficientData (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionSmallBiasCoefficientData.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasCoefficientBounds

-- ===== source module GeneralCK.Certificates.ReflectionSmallBiasCoefficientData =====
section

/-! Exact small-bias coefficient data. Analytic agreement is a separate obligation. -/

namespace GeneralCK.Reflection.SmallBiasCoefficientData

open SmallBiasCoefficientBounds

set_option maxHeartbeats 0

def q_0_0 : List PowerTerm :=
  [⟨(1 / 16 : ℚ), 2⟩,
   ⟨(-11 / 96 : ℚ), 1⟩,
   ⟨(1 / 8 : ℚ), 0⟩]

theorem q_0_0_checked : checkCoefficient q_0_0 = true := by
  norm_num [checkCoefficient, q_0_0, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_0_1 : List PowerTerm :=
  [⟨(17 / 384 : ℚ), 2⟩,
   ⟨(-11 / 120 : ℚ), 1⟩,
   ⟨(1 / 8 : ℚ), 0⟩]

theorem q_0_1_checked : checkCoefficient q_0_1 = true := by
  norm_num [checkCoefficient, q_0_1, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_0_2 : List PowerTerm :=
  [⟨(-3 / 1024 : ℚ), 4⟩,
   ⟨(1 / 96 : ℚ), 3⟩,
   ⟨(23 / 1536 : ℚ), 2⟩,
   ⟨(-2029 / 35840 : ℚ), 1⟩,
   ⟨(41 / 384 : ℚ), 0⟩]

theorem q_0_2_checked : checkCoefficient q_0_2 = true := by
  norm_num [checkCoefficient, q_0_2, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_1_1 : List PowerTerm :=
  [⟨(11 / 512 : ℚ), 4⟩,
   ⟨(-23 / 384 : ℚ), 3⟩,
   ⟨(1273 / 11520 : ℚ), 2⟩,
   ⟨(-2411 / 17920 : ℚ), 1⟩,
   ⟨(31 / 192 : ℚ), 0⟩]

theorem q_1_1_checked : checkCoefficient q_1_1 = true := by
  norm_num [checkCoefficient, q_1_1, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_0_3 : List PowerTerm :=
  [⟨(-7 / 2048 : ℚ), 4⟩,
   ⟨(109 / 8192 : ℚ), 3⟩,
   ⟨(5 / 64512 : ℚ), 2⟩,
   ⟨(-21739 / 645120 : ℚ), 1⟩,
   ⟨(23 / 256 : ℚ), 0⟩]

theorem q_0_3_checked : checkCoefficient q_0_3 = true := by
  norm_num [checkCoefficient, q_0_3, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_1_2 : List PowerTerm :=
  [⟨(121 / 6144 : ℚ), 4⟩,
   ⟨(-7043 / 122880 : ℚ), 3⟩,
   ⟨(3643 / 35840 : ℚ), 2⟩,
   ⟨(-78613 / 645120 : ℚ), 1⟩,
   ⟨(41 / 256 : ℚ), 0⟩]

theorem q_1_2_checked : checkCoefficient q_1_2 = true := by
  norm_num [checkCoefficient, q_1_2, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_0_4 : List PowerTerm :=
  [⟨(5 / 32768 : ℚ), 6⟩,
   ⟨(-99 / 131072 : ℚ), 5⟩,
   ⟨(-1357 / 983040 : ℚ), 4⟩,
   ⟨(657611 / 61931520 : ℚ), 3⟩,
   ⟨(-1943 / 430080 : ℚ), 2⟩,
   ⟨(-26351 / 1261568 : ℚ), 1⟩,
   ⟨(157 / 2048 : ℚ), 0⟩]

theorem q_0_4_checked : checkCoefficient q_0_4 = true := by
  norm_num [checkCoefficient, q_0_4, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_1_3 : List PowerTerm :=
  [⟨(-25 / 8192 : ℚ), 6⟩,
   ⟨(1289 / 98304 : ℚ), 5⟩,
   ⟨(-819 / 81920 : ℚ), 4⟩,
   ⟨(-29579 / 1720320 : ℚ), 3⟩,
   ⟨(79019 / 1290240 : ℚ), 2⟩,
   ⟨(-1294333 / 14192640 : ℚ), 1⟩,
   ⟨(75 / 512 : ℚ), 0⟩]

theorem q_1_3_checked : checkCoefficient q_1_3 = true := by
  norm_num [checkCoefficient, q_1_3, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_2_2 : List PowerTerm :=
  [⟨(159 / 16384 : ℚ), 6⟩,
   ⟨(-7291 / 196608 : ℚ), 5⟩,
   ⟨(14203 / 163840 : ℚ), 4⟩,
   ⟨(-464839 / 3440640 : ℚ), 3⟩,
   ⟨(258569 / 1612800 : ℚ), 2⟩,
   ⟨(-4254473 / 28385280 : ℚ), 1⟩,
   ⟨(183 / 1024 : ℚ), 0⟩]

theorem q_2_2_checked : checkCoefficient q_2_2 = true := by
  norm_num [checkCoefficient, q_2_2, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_0_5 : List PowerTerm :=
  [⟨(395 / 1572864 : ℚ), 6⟩,
   ⟨(-15533 / 11796480 : ℚ), 5⟩,
   ⟨(46829 / 82575360 : ℚ), 4⟩,
   ⟨(6475223 / 928972800 : ℚ), 3⟩,
   ⟨(-788969 / 162201600 : ℚ), 2⟩,
   ⟨(-1276063 / 92252160 : ℚ), 1⟩,
   ⟨(341 / 5120 : ℚ), 0⟩]

theorem q_0_5_checked : checkCoefficient q_0_5 = true := by
  norm_num [checkCoefficient, q_0_5, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_1_4 : List PowerTerm :=
  [⟨(-2315 / 524288 : ℚ), 6⟩,
   ⟨(236599 / 11796480 : ℚ), 5⟩,
   ⟨(-7233533 / 247726080 : ℚ), 4⟩,
   ⟨(2447939 / 185794560 : ℚ), 3⟩,
   ⟨(18593699 / 681246720 : ℚ), 2⟩,
   ⟨(-1953617 / 30750720 : ℚ), 1⟩,
   ⟨(2011 / 15360 : ℚ), 0⟩]

theorem q_1_4_checked : checkCoefficient q_1_4 = true := by
  norm_num [checkCoefficient, q_1_4, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_2_3 : List PowerTerm :=
  [⟨(7499 / 786432 : ℚ), 6⟩,
   ⟨(-216773 / 5898240 : ℚ), 5⟩,
   ⟨(693493 / 8257536 : ℚ), 4⟩,
   ⟨(-4024381 / 30965760 : ℚ), 3⟩,
   ⟨(86548349 / 567705600 : ℚ), 2⟩,
   ⟨(-6505783 / 46126080 : ℚ), 1⟩,
   ⟨(1363 / 7680 : ℚ), 0⟩]

theorem q_2_3_checked : checkCoefficient q_2_3 = true := by
  norm_num [checkCoefficient, q_2_3, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_0_6 : List PowerTerm :=
  [⟨(-35 / 4194304 : ℚ), 8⟩,
   ⟨(331 / 6291456 : ℚ), 7⟩,
   ⟨(2057 / 15728640 : ℚ), 6⟩,
   ⟨(-1277251 / 990904320 : ℚ), 5⟩,
   ⟨(8810747 / 5945425920 : ℚ), 4⟩,
   ⟨(7694453 / 1816657920 : ℚ), 3⟩,
   ⟨(-713759569 / 177124147200 : ℚ), 2⟩,
   ⟨(-32986913 / 3373793280 : ℚ), 1⟩,
   ⟨(1927 / 32768 : ℚ), 0⟩]

theorem q_0_6_checked : checkCoefficient q_0_6 = true := by
  norm_num [checkCoefficient, q_0_6, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_1_5 : List PowerTerm :=
  [⟨(665 / 2097152 : ℚ), 8⟩,
   ⟨(-5663 / 3145728 : ℚ), 7⟩,
   ⟨(163 / 983040 : ℚ), 6⟩,
   ⟨(6994381 / 495452160 : ℚ), 5⟩,
   ⟨(-12336467 / 424673280 : ℚ), 4⟩,
   ⟨(64503479 / 2724986880 : ℚ), 3⟩,
   ⟨(26958559 / 3280076800 : ℚ), 2⟩,
   ⟨(-34560725 / 787218432 : ℚ), 1⟩,
   ⟨(1915 / 16384 : ℚ), 0⟩]

theorem q_1_5_checked : checkCoefficient q_1_5 = true := by
  norm_num [checkCoefficient, q_1_5, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_2_4 : List PowerTerm :=
  [⟨(-10381 / 4194304 : ℚ), 8⟩,
   ⟨(80725 / 6291456 : ℚ), 7⟩,
   ⟨(-370769 / 15728640 : ℚ), 6⟩,
   ⟨(17670451 / 990904320 : ℚ), 5⟩,
   ⟨(179297891 / 9909043200 : ℚ), 4⟩,
   ⟨(-1895783147 / 27249868800 : ℚ), 3⟩,
   ⟨(61004899 / 562298880 : ℚ), 2⟩,
   ⟨(-181106791 / 1574436864 : ℚ), 1⟩,
   ⟨(5481 / 32768 : ℚ), 0⟩]

theorem q_2_4_checked : checkCoefficient q_2_4 = true := by
  norm_num [checkCoefficient, q_2_4, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_3_3 : List PowerTerm :=
  [⟨(5567 / 1048576 : ℚ), 8⟩,
   ⟨(-40753 / 1572864 : ℚ), 7⟩,
   ⟨(70691 / 983040 : ℚ), 6⟩,
   ⟨(-11101847 / 82575360 : ℚ), 5⟩,
   ⟨(475487003 / 2477260800 : ℚ), 4⟩,
   ⟨(-14160979 / 64880640 : ℚ), 3⟩,
   ⟨(12713564729 / 61993451520 : ℚ), 2⟩,
   ⟨(-191365609 / 1180827648 : ℚ), 1⟩,
   ⟨(1549 / 8192 : ℚ), 0⟩]

theorem q_3_3_checked : checkCoefficient q_3_3 = true := by
  norm_num [checkCoefficient, q_3_3, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_0_7 : List PowerTerm :=
  [⟨(-7 / 393216 : ℚ), 8⟩,
   ⟨(14723 / 125829120 : ℚ), 7⟩,
   ⟨(-15313 / 198180864 : ℚ), 6⟩,
   ⟨(-316265 / 339738624 : ℚ), 5⟩,
   ⟨(1054795859 / 653996851200 : ℚ), 4⟩,
   ⟨(23111605519 / 9017229312000 : ℚ), 3⟩,
   ⟨(-20557265977 / 6612634828800 : ℚ), 2⟩,
   ⟨(-5855329819 / 802962800640 : ℚ), 1⟩,
   ⟨(3449 / 65536 : ℚ), 0⟩]

theorem q_0_7_checked : checkCoefficient q_0_7 = true := by
  norm_num [checkCoefficient, q_0_7, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_1_6 : List PowerTerm :=
  [⟨(1295 / 2097152 : ℚ), 8⟩,
   ⟨(-92051 / 25165824 : ℚ), 7⟩,
   ⟨(578615 / 99090432 : ℚ), 6⟩,
   ⟨(9288707 / 2378170368 : ℚ), 5⟩,
   ⟨(-369162053 / 18685624320 : ℚ), 4⟩,
   ⟨(20987343119 / 944662118400 : ℚ), 3⟩,
   ⟨(-32101763 / 566797271040 : ℚ), 2⟩,
   ⟨(-24994924217 / 802962800640 : ℚ), 1⟩,
   ⟨(6883 / 65536 : ℚ), 0⟩]

theorem q_1_6_checked : checkCoefficient q_1_6 = true := by
  norm_num [checkCoefficient, q_1_6, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_2_5 : List PowerTerm :=
  [⟨(-8589 / 2097152 : ℚ), 8⟩,
   ⟨(2768843 / 125829120 : ℚ), 7⟩,
   ⟨(-4090619 / 82575360 : ℚ), 6⟩,
   ⟨(153089905 / 2378170368 : ℚ), 5⟩,
   ⟨(-3952341491 / 93428121600 : ℚ), 4⟩,
   ⟨(-146917903829 / 14169931776000 : ℚ), 3⟩,
   ⟨(178786526747 / 2833986355200 : ℚ), 2⟩,
   ⟨(-7795738971 / 89218088960 : ℚ), 1⟩,
   ⟨(10113 / 65536 : ℚ), 0⟩]

theorem q_2_5_checked : checkCoefficient q_2_5 = true := by
  norm_num [checkCoefficient, q_2_5, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_3_4 : List PowerTerm :=
  [⟨(5415 / 1048576 : ℚ), 8⟩,
   ⟨(-1055013 / 41943040 : ℚ), 7⟩,
   ⟨(68834483 / 990904320 : ℚ), 6⟩,
   ⟨(-172059361 / 1321205760 : ℚ), 5⟩,
   ⟨(40513710059 / 217998950400 : ℚ), 4⟩,
   ⟨(-598403476787 / 2833986355200 : ℚ), 3⟩,
   ⟨(356453807077 / 1803445862400 : ℚ), 2⟩,
   ⟨(-24931475813 / 160592560128 : ℚ), 1⟩,
   ⟨(12323 / 65536 : ℚ), 0⟩]

theorem q_3_4_checked : checkCoefficient q_3_4 = true := by
  norm_num [checkCoefficient, q_3_4, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_0_8 : List PowerTerm :=
  [⟨(63 / 134217728 : ℚ), 10⟩,
   ⟨(-2891 / 805306368 : ℚ), 9⟩,
   ⟨(-17479 / 1509949440 : ℚ), 8⟩,
   ⟨(2911879 / 21139292160 : ℚ), 7⟩,
   ⟨(-42763933 / 190253629440 : ℚ), 6⟩,
   ⟨(-137376010859 / 251134790860800 : ℚ), 5⟩,
   ⟨(271599911311 / 194330492928000 : ℚ), 4⟩,
   ⟨(171546011969 / 105802157260800 : ℚ), 3⟩,
   ⟨(-118609931779 / 49962129817600 : ℚ), 2⟩,
   ⟨(-46107125621 / 8136689713152 : ℚ), 1⟩,
   ⟨(174759 / 3670016 : ℚ), 0⟩]

theorem q_0_8_checked : checkCoefficient q_0_8 = true := by
  norm_num [checkCoefficient, q_0_8, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_1_7 : List PowerTerm :=
  [⟨(-483 / 16777216 : ℚ), 10⟩,
   ⟨(20363 / 100663296 : ℚ), 9⟩,
   ⟨(2583 / 20971520 : ℚ), 8⟩,
   ⟨(-27610469 / 7927234560 : ℚ), 7⟩,
   ⟨(194661241 / 23781703680 : ℚ), 6⟩,
   ⟨(-102608517323 / 31391848857600 : ℚ), 5⟩,
   ⟨(-197173829059 / 18893242368000 : ℚ), 4⟩,
   ⟨(2018412273667 / 119027426918400 : ℚ), 3⟩,
   ⟨(-4811654167 / 1756481126400 : ℚ), 2⟩,
   ⟨(-70027203599 / 3051258642432 : ℚ), 1⟩,
   ⟨(130973 / 1376256 : ℚ), 0⟩]

theorem q_1_7_checked : checkCoefficient q_1_7 = true := by
  norm_num [checkCoefficient, q_1_7, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_2_6 : List PowerTerm :=
  [⟨(13545 / 33554432 : ℚ), 10⟩,
   ⟨(-529613 / 201326592 : ℚ), 9⟩,
   ⟨(432313 / 125829120 : ℚ), 8⟩,
   ⟨(53871113 / 5284823040 : ℚ), 7⟩,
   ⟨(-1965751339 / 47563407360 : ℚ), 6⟩,
   ⟨(487669218499 / 6975966412800 : ℚ), 5⟩,
   ⟨(-22226491006921 / 340078362624000 : ℚ), 4⟩,
   ⟨(60305941373 / 2615987404800 : ℚ), 3⟩,
   ⟨(1496447186083 / 48177768038400 : ℚ), 2⟩,
   ⟨(-1976856322549 / 30512586424320 : ℚ), 1⟩,
   ⟨(389531 / 2752512 : ℚ), 0⟩]

theorem q_2_6_checked : checkCoefficient q_2_6 = true := by
  norm_num [checkCoefficient, q_2_6, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_3_5 : List PowerTerm :=
  [⟨(-32085 / 16777216 : ℚ), 10⟩,
   ⟨(393583 / 33554432 : ℚ), 9⟩,
   ⟨(-5774959 / 188743680 : ℚ), 8⟩,
   ⟨(121619471 / 2642411520 : ℚ), 7⟩,
   ⟨(-90455657 / 2642411520 : ℚ), 6⟩,
   ⟨(-439975801277 / 31391848857600 : ℚ), 5⟩,
   ⟨(8880373702799 / 108206751744000 : ℚ), 4⟩,
   ⟨(-1799761193459 / 13225269657600 : ℚ), 3⟩,
   ⟨(3223253640203 / 21077773516800 : ℚ), 2⟩,
   ⟨(-675712010047 / 5085431070720 : ℚ), 1⟩,
   ⟨(82633 / 458752 : ℚ), 0⟩]

theorem q_3_5_checked : checkCoefficient q_3_5 = true := by
  norm_num [checkCoefficient, q_3_5, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def q_4_4 : List PowerTerm :=
  [⟨(222685 / 67108864 : ℚ), 10⟩,
   ⟨(-2643307 / 134217728 : ℚ), 9⟩,
   ⟨(47808667 / 754974720 : ℚ), 8⟩,
   ⟨(-4363315777 / 31708938240 : ℚ), 7⟩,
   ⟨(2401181953 / 10569646080 : ℚ), 6⟩,
   ⟨(-1075573482443 / 3587639869440 : ℚ), 5⟩,
   ⟨(312940652964473 / 952219415347200 : ℚ), 4⟩,
   ⟨(-145591526792389 / 476109707673600 : ℚ), 3⟩,
   ⟨(99414482030603 / 404693251522560 : ℚ), 2⟩,
   ⟨(-700230026719 / 4068344856576 : ℚ), 1⟩,
   ⟨(359925 / 1835008 : ℚ), 0⟩]

theorem q_4_4_checked : checkCoefficient q_4_4 = true := by
  norm_num [checkCoefficient, q_4_4, lower, upper, lowerTerm, upperTerm, invLogLower, invLogUpper]

def rows : List CoefficientRow :=
  [⟨0, 0, q_0_0⟩,
   ⟨0, 1, q_0_1⟩,
   ⟨1, 0, q_0_1⟩,
   ⟨0, 2, q_0_2⟩,
   ⟨1, 1, q_1_1⟩,
   ⟨2, 0, q_0_2⟩,
   ⟨0, 3, q_0_3⟩,
   ⟨1, 2, q_1_2⟩,
   ⟨2, 1, q_1_2⟩,
   ⟨3, 0, q_0_3⟩,
   ⟨0, 4, q_0_4⟩,
   ⟨1, 3, q_1_3⟩,
   ⟨2, 2, q_2_2⟩,
   ⟨3, 1, q_1_3⟩,
   ⟨4, 0, q_0_4⟩,
   ⟨0, 5, q_0_5⟩,
   ⟨1, 4, q_1_4⟩,
   ⟨2, 3, q_2_3⟩,
   ⟨3, 2, q_2_3⟩,
   ⟨4, 1, q_1_4⟩,
   ⟨5, 0, q_0_5⟩,
   ⟨0, 6, q_0_6⟩,
   ⟨1, 5, q_1_5⟩,
   ⟨2, 4, q_2_4⟩,
   ⟨3, 3, q_3_3⟩,
   ⟨4, 2, q_2_4⟩,
   ⟨5, 1, q_1_5⟩,
   ⟨6, 0, q_0_6⟩,
   ⟨0, 7, q_0_7⟩,
   ⟨1, 6, q_1_6⟩,
   ⟨2, 5, q_2_5⟩,
   ⟨3, 4, q_3_4⟩,
   ⟨4, 3, q_3_4⟩,
   ⟨5, 2, q_2_5⟩,
   ⟨6, 1, q_1_6⟩,
   ⟨7, 0, q_0_7⟩,
   ⟨0, 8, q_0_8⟩,
   ⟨1, 7, q_1_7⟩,
   ⟨2, 6, q_2_6⟩,
   ⟨3, 5, q_3_5⟩,
   ⟨4, 4, q_4_4⟩,
   ⟨5, 3, q_3_5⟩,
   ⟨6, 2, q_2_6⟩,
   ⟨7, 1, q_1_7⟩,
   ⟨8, 0, q_0_8⟩]

theorem rows_checked : checkRows rows = true := by
  simp only [checkRows, rows, List.all_cons, List.all_nil, q_0_0_checked, q_0_1_checked, q_0_2_checked, q_1_1_checked, q_0_3_checked, q_1_2_checked, q_0_4_checked, q_1_3_checked, q_2_2_checked, q_0_5_checked, q_1_4_checked, q_2_3_checked, q_0_6_checked, q_1_5_checked, q_2_4_checked, q_3_3_checked, q_0_7_checked, q_1_6_checked, q_2_5_checked, q_3_4_checked, q_0_8_checked, q_1_7_checked, q_2_6_checked, q_3_5_checked, q_4_4_checked, Bool.true_and]

theorem rows_length : rows.length = 45 := by rfl

theorem all_coefficients_positive : ∀ row ∈ rows,
    0 < eval row.coefficients (Real.log 2)⁻¹ ∧ eval row.coefficients (Real.log 2)⁻¹ < 1 :=
  checkRows_sound rows_checked

theorem constant_coefficient_lower : (2 / 25 : ℝ) < eval q_0_0 (Real.log 2)⁻¹ := by
  have hl : (2 / 25 : ℚ) < lower q_0_0 invLogLower invLogUpper := by
    norm_num [q_0_0, lower, lowerTerm, invLogLower, invLogUpper]
  have hl' : (((2 / 25 : ℚ) : ℝ)) < (lower q_0_0 invLogLower invLogUpper : ℝ) := Rat.cast_lt.mpr hl
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl'
  exact hl'.trans_le (eval_at_inv_log_two_bounds q_0_0).1

end GeneralCK.Reflection.SmallBiasCoefficientData

end


