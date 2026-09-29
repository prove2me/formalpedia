-- Prove2me | Definitions.Def_CK_GeneralCK_SmallBoundaryPhiCompactBox
-- name    : CK_GeneralCK_SmallBoundaryPhiCompactBox
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:15:13.492729+00:00
-- url     : https://prove2.me/theorems/0fc5e2ea-2b4c-4646-b820-904810595914
-- title:
--   Courtade–Kumar proof module `GeneralCK.SmallBoundaryPhiCompactBox` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.SmallBoundaryPhiCompactBox` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.SmallBoundaryPhiCompactBox` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.SmallBoundaryPhiCompactBox (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/SmallBoundaryPhiCompactBox.lean)

import Definitions.Def_CK_GeneralCK_SmallBoundaryPhiTailBox

-- ===== source module GeneralCK.SmallBoundaryPhiCompactBox =====
section

namespace GeneralCK.SmallBoundaryPhiCompactBox
open GeneralCK.Certificates.NonnegativeBoxPolynomial GeneralCK.SmallBoundaryPhiTailBox
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def aLowerRemainderData : List Term := [
  ⟨-99, 5, 3, 3⟩,
  ⟨503, 5, 3, 2⟩,
  ⟨1303, 5, 3, 1⟩,
  ⟨701, 5, 3, 0⟩,
  ⟨-2, 4, 3, 3⟩,
  ⟨-2806, 4, 3, 2⟩,
  ⟨-5606, 4, 3, 1⟩,
  ⟨-2802, 4, 3, 0⟩,
  ⟨-297, 4, 2, 2⟩,
  ⟨-2194, 4, 2, 1⟩,
  ⟨-1897, 4, 2, 0⟩,
  ⟨401, 3, 3, 3⟩,
  ⟨5003, 3, 3, 2⟩,
  ⟨8803, 3, 3, 1⟩,
  ⟨4201, 3, 3, 0⟩,
  ⟨794, 3, 2, 2⟩,
  ⟨5588, 3, 2, 1⟩,
  ⟨4794, 3, 2, 0⟩,
  ⟨-297, 3, 1, 1⟩,
  ⟨503, 3, 1, 0⟩,
  ⟨-400, 2, 3, 3⟩,
  ⟨-3700, 2, 3, 2⟩,
  ⟨-6200, 2, 3, 1⟩,
  ⟨-2900, 2, 3, 0⟩,
  ⟨-397, 2, 2, 2⟩,
  ⟨-4394, 2, 2, 1⟩,
  ⟨-3997, 2, 2, 0⟩,
  ⟨794, 2, 1, 1⟩,
  ⟨-406, 2, 1, 0⟩,
  ⟨-99, 2, 0, 0⟩,
  ⟨100, 1, 3, 3⟩,
  ⟨1100, 1, 3, 2⟩,
  ⟨1900, 1, 3, 1⟩,
  ⟨900, 1, 3, 0⟩,
  ⟨-200, 1, 2, 2⟩,
  ⟨1000, 1, 2, 1⟩,
  ⟨1200, 1, 2, 0⟩,
  ⟨-797, 1, 1, 1⟩,
  ⟨-197, 1, 1, 0⟩,
  ⟨-2, 1, 0, 0⟩,
  ⟨-100, 0, 3, 2⟩,
  ⟨-200, 0, 3, 1⟩,
  ⟨100, 0, 2, 2⟩,
  ⟨200, 0, 1, 1⟩,
  ⟨1, 0, 0, 0⟩]

theorem aLowerRemainder_identity (t z beta : ℝ) :
    eval aLowerRemainderData t z beta = 100*aNum t z (1+beta)-99*aDen t z (1+beta)-100*z*(1-z-z^2) := by
  norm_num [aLowerRemainderData, eval, evalTerm, aNum, aDen, kNum, kDen, differenceNum, differenceDen, derivativeNum, derivativeDen, cFactor, pFactor, mFactor] <;> ring

theorem aLowerRemainder_check : (1/4 : ℚ) ≤
    lowerBound aLowerRemainderData (1/10000) (1/9) (1/9999) := by decide +kernel

theorem aLowerRemainder_nonneg {t z beta : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/10000) (hz : 0 ≤ z) (hz' : z ≤ 1/9)
    (hb : 0 ≤ beta) (hb' : beta ≤ 1/9999) :
    0 ≤ 100*aNum t z (1+beta)-99*aDen t z (1+beta)-100*z*(1-z-z^2) := by
  have h := certificate_sound aLowerRemainderData aLowerRemainder_check ht
    (by norm_num; exact ht') hz (by norm_num; exact hz') hb (by norm_num; exact hb')
  rw [aLowerRemainder_identity] at h
  norm_num at h
  linarith

def aUpperData : List Term := [
  ⟨6, 5, 3, 3⟩,
  ⟨-22, 5, 3, 2⟩,
  ⟨-62, 5, 3, 1⟩,
  ⟨-34, 5, 3, 0⟩,
  ⟨-2, 4, 3, 3⟩,
  ⟨134, 4, 3, 2⟩,
  ⟨274, 4, 3, 1⟩,
  ⟨138, 4, 3, 0⟩,
  ⟨18, 4, 2, 2⟩,
  ⟨116, 4, 2, 1⟩,
  ⟨98, 4, 2, 0⟩,
  ⟨-19, 3, 3, 3⟩,
  ⟨-247, 3, 3, 2⟩,
  ⟨-437, 3, 3, 1⟩,
  ⟨-209, 3, 3, 0⟩,
  ⟨-46, 3, 2, 2⟩,
  ⟨-292, 3, 2, 1⟩,
  ⟨-246, 3, 2, 0⟩,
  ⟨18, 3, 1, 1⟩,
  ⟨-22, 3, 1, 0⟩,
  ⟨20, 2, 3, 3⟩,
  ⟨185, 2, 3, 2⟩,
  ⟨310, 2, 3, 1⟩,
  ⟨145, 2, 3, 0⟩,
  ⟨23, 2, 2, 2⟩,
  ⟨226, 2, 2, 1⟩,
  ⟨203, 2, 2, 0⟩,
  ⟨-46, 2, 1, 1⟩,
  ⟨14, 2, 1, 0⟩,
  ⟨6, 2, 0, 0⟩,
  ⟨-5, 1, 3, 3⟩,
  ⟨-55, 1, 3, 2⟩,
  ⟨-95, 1, 3, 1⟩,
  ⟨-45, 1, 3, 0⟩,
  ⟨10, 1, 2, 2⟩,
  ⟨-50, 1, 2, 1⟩,
  ⟨-60, 1, 2, 0⟩,
  ⟨43, 1, 1, 1⟩,
  ⟨13, 1, 1, 0⟩,
  ⟨-2, 1, 0, 0⟩,
  ⟨5, 0, 3, 2⟩,
  ⟨10, 0, 3, 1⟩,
  ⟨5, 0, 3, 0⟩,
  ⟨-5, 0, 2, 2⟩,
  ⟨5, 0, 2, 0⟩,
  ⟨-10, 0, 1, 1⟩,
  ⟨-5, 0, 1, 0⟩,
  ⟨1, 0, 0, 0⟩]

theorem aUpper_identity (t z beta : ℝ) :
    eval aUpperData t z beta = 6*aDen t z (1+beta)-5*aNum t z (1+beta) := by
  norm_num [aUpperData, eval, evalTerm, aNum, aDen, kNum, kDen, differenceNum, differenceDen, derivativeNum, derivativeDen, cFactor, pFactor, mFactor] <;> ring

theorem aUpper_check : (1/4 : ℚ) ≤
    lowerBound aUpperData (1/10000) (1/9) (1/9999) := by decide +kernel

theorem aUpper_nonneg {t z beta : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/10000) (hz : 0 ≤ z) (hz' : z ≤ 1/9)
    (hb : 0 ≤ beta) (hb' : beta ≤ 1/9999) :
    0 ≤ 6*aDen t z (1+beta)-5*aNum t z (1+beta) := by
  have h := certificate_sound aUpperData aUpper_check ht
    (by norm_num; exact ht') hz (by norm_num; exact hz') hb (by norm_num; exact hb')
  rw [aUpper_identity] at h
  norm_num at h
  linarith

def kUpperData : List Term := [
  ⟨4, 5, 3, 3⟩,
  ⟨12, 5, 3, 2⟩,
  ⟨12, 5, 3, 1⟩,
  ⟨4, 5, 3, 0⟩,
  ⟨-18, 4, 3, 3⟩,
  ⟨-54, 4, 3, 2⟩,
  ⟨-54, 4, 3, 1⟩,
  ⟨-18, 4, 3, 0⟩,
  ⟨-12, 4, 2, 2⟩,
  ⟨-24, 4, 2, 1⟩,
  ⟨-12, 4, 2, 0⟩,
  ⟨29, 3, 3, 3⟩,
  ⟨77, 3, 3, 2⟩,
  ⟨67, 3, 3, 1⟩,
  ⟨19, 3, 3, 0⟩,
  ⟨34, 3, 2, 2⟩,
  ⟨68, 3, 2, 1⟩,
  ⟨34, 3, 2, 0⟩,
  ⟨12, 3, 1, 1⟩,
  ⟨12, 3, 1, 0⟩,
  ⟨-20, 2, 3, 3⟩,
  ⟨-35, 2, 3, 2⟩,
  ⟨-10, 2, 3, 1⟩,
  ⟨5, 2, 3, 0⟩,
  ⟨-47, 2, 2, 2⟩,
  ⟨-74, 2, 2, 1⟩,
  ⟨-27, 2, 2, 0⟩,
  ⟨-14, 2, 1, 1⟩,
  ⟨-14, 2, 1, 0⟩,
  ⟨-4, 2, 0, 0⟩,
  ⟨5, 1, 3, 3⟩,
  ⟨-5, 1, 3, 2⟩,
  ⟨-25, 1, 3, 1⟩,
  ⟨-15, 1, 3, 0⟩,
  ⟨30, 1, 2, 2⟩,
  ⟨30, 1, 2, 1⟩,
  ⟨17, 1, 1, 1⟩,
  ⟨7, 1, 1, 0⟩,
  ⟨-2, 1, 0, 0⟩,
  ⟨5, 0, 3, 2⟩,
  ⟨10, 0, 3, 1⟩,
  ⟨5, 0, 3, 0⟩,
  ⟨-5, 0, 2, 2⟩,
  ⟨5, 0, 2, 0⟩,
  ⟨-10, 0, 1, 1⟩,
  ⟨-5, 0, 1, 0⟩,
  ⟨1, 0, 0, 0⟩]

theorem kUpper_identity (t z beta : ℝ) :
    eval kUpperData t z beta = 6*kDen t z (1+beta)-5*kNum t z (1+beta) := by
  norm_num [kUpperData, eval, evalTerm, aNum, aDen, kNum, kDen, differenceNum, differenceDen, derivativeNum, derivativeDen, cFactor, pFactor, mFactor] <;> ring

theorem kUpper_check : (1/4 : ℚ) ≤
    lowerBound kUpperData (1/10000) (1/9) (1/9999) := by decide +kernel

theorem kUpper_nonneg {t z beta : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/10000) (hz : 0 ≤ z) (hz' : z ≤ 1/9)
    (hb : 0 ≤ beta) (hb' : beta ≤ 1/9999) :
    0 ≤ 6*kDen t z (1+beta)-5*kNum t z (1+beta) := by
  have h := certificate_sound kUpperData kUpper_check ht
    (by norm_num; exact ht') hz (by norm_num; exact hz') hb (by norm_num; exact hb')
  rw [kUpper_identity] at h
  norm_num at h
  linarith

def differenceUpperData : List Term := [
  ⟨-1, 8, 6, 6⟩,
  ⟨-6, 8, 6, 5⟩,
  ⟨-15, 8, 6, 4⟩,
  ⟨-20, 8, 6, 3⟩,
  ⟨-15, 8, 6, 2⟩,
  ⟨-6, 8, 6, 1⟩,
  ⟨-1, 8, 6, 0⟩,
  ⟨-8, 7, 6, 6⟩,
  ⟨-8, 7, 6, 5⟩,
  ⟨80, 7, 6, 4⟩,
  ⟨240, 7, 6, 3⟩,
  ⟨280, 7, 6, 2⟩,
  ⟨152, 7, 6, 1⟩,
  ⟨32, 7, 6, 0⟩,
  ⟨19, 6, 6, 6⟩,
  ⟨-26, 6, 6, 5⟩,
  ⟨-415, 6, 6, 4⟩,
  ⟨-1020, 6, 6, 3⟩,
  ⟨-1115, 6, 6, 2⟩,
  ⟨-586, 6, 6, 1⟩,
  ⟨-121, 6, 6, 0⟩,
  ⟨-200, 6, 5, 4⟩,
  ⟨-800, 6, 5, 3⟩,
  ⟨-1200, 6, 5, 2⟩,
  ⟨-800, 6, 5, 1⟩,
  ⟨-200, 6, 5, 0⟩,
  ⟨3, 6, 4, 4⟩,
  ⟨12, 6, 4, 3⟩,
  ⟨18, 6, 4, 2⟩,
  ⟨12, 6, 4, 1⟩,
  ⟨3, 6, 4, 0⟩,
  ⟨-10, 5, 6, 6⟩,
  ⟨140, 5, 6, 5⟩,
  ⟨850, 5, 6, 4⟩,
  ⟨1800, 5, 6, 3⟩,
  ⟨1850, 5, 6, 2⟩,
  ⟨940, 5, 6, 1⟩,
  ⟨190, 5, 6, 0⟩,
  ⟨60, 5, 5, 5⟩,
  ⟨920, 5, 5, 4⟩,
  ⟨3080, 5, 5, 3⟩,
  ⟨4320, 5, 5, 2⟩,
  ⟨2780, 5, 5, 1⟩,
  ⟨680, 5, 5, 0⟩,
  ⟨24, 5, 4, 4⟩,
  ⟨496, 5, 4, 3⟩,
  ⟨1344, 5, 4, 2⟩,
  ⟨1296, 5, 4, 1⟩,
  ⟨424, 5, 4, 0⟩,
  ⟨-150, 4, 6, 5⟩,
  ⟨-750, 4, 6, 4⟩,
  ⟨-1500, 4, 6, 3⟩,
  ⟨-1500, 4, 6, 2⟩,
  ⟨-750, 4, 6, 1⟩,
  ⟨-150, 4, 6, 0⟩,
  ⟨-120, 4, 5, 5⟩,
  ⟨-1340, 4, 5, 4⟩,
  ⟨-4160, 4, 5, 3⟩,
  ⟨-5640, 4, 5, 2⟩,
  ⟨-3560, 4, 5, 1⟩,
  ⟨-860, 4, 5, 0⟩,
  ⟨-117, 4, 4, 4⟩,
  ⟨-1548, 4, 4, 3⟩,
  ⟨-3942, 4, 4, 2⟩,
  ⟨-3708, 4, 4, 1⟩,
  ⟨-1197, 4, 4, 0⟩,
  ⟨-400, 4, 3, 2⟩,
  ⟨-800, 4, 3, 1⟩,
  ⟨-400, 4, 3, 0⟩,
  ⟨-3, 4, 2, 2⟩,
  ⟨-6, 4, 2, 1⟩,
  ⟨-3, 4, 2, 0⟩,
  ⟨60, 3, 6, 5⟩,
  ⟨300, 3, 6, 4⟩,
  ⟨600, 3, 6, 3⟩,
  ⟨600, 3, 6, 2⟩,
  ⟨300, 3, 6, 1⟩,
  ⟨60, 3, 6, 0⟩,
  ⟨80, 3, 5, 5⟩,
  ⟨800, 3, 5, 4⟩,
  ⟨2400, 3, 5, 3⟩,
  ⟨3200, 3, 5, 2⟩,
  ⟨2000, 3, 5, 1⟩,
  ⟨480, 3, 5, 0⟩,
  ⟨120, 3, 4, 4⟩,
  ⟨1600, 3, 4, 3⟩,
  ⟨4080, 3, 4, 2⟩,
  ⟨3840, 3, 4, 1⟩,
  ⟨1240, 3, 4, 0⟩,
  ⟨-40, 3, 3, 3⟩,
  ⟨800, 3, 3, 2⟩,
  ⟨1720, 3, 3, 1⟩,
  ⟨880, 3, 3, 0⟩,
  ⟨-24, 3, 2, 2⟩,
  ⟨152, 3, 2, 1⟩,
  ⟨176, 3, 2, 0⟩,
  ⟨-10, 2, 6, 5⟩,
  ⟨-50, 2, 6, 4⟩,
  ⟨-100, 2, 6, 3⟩,
  ⟨-100, 2, 6, 2⟩,
  ⟨-50, 2, 6, 1⟩,
  ⟨-10, 2, 6, 0⟩,
  ⟨-20, 2, 5, 5⟩,
  ⟨-180, 2, 5, 4⟩,
  ⟨-520, 2, 5, 3⟩,
  ⟨-680, 2, 5, 2⟩,
  ⟨-420, 2, 5, 1⟩,
  ⟨-100, 2, 5, 0⟩,
  ⟨-40, 2, 4, 4⟩,
  ⟨-740, 2, 4, 3⟩,
  ⟨-1980, 2, 4, 2⟩,
  ⟨-1900, 2, 4, 1⟩,
  ⟨-620, 2, 4, 0⟩,
  ⟨100, 2, 3, 3⟩,
  ⟨-540, 2, 3, 2⟩,
  ⟨-1380, 2, 3, 1⟩,
  ⟨-740, 2, 3, 0⟩,
  ⟨97, 2, 2, 2⟩,
  ⟨-186, 2, 2, 1⟩,
  ⟨-283, 2, 2, 0⟩,
  ⟨-40, 2, 1, 0⟩,
  ⟨1, 2, 0, 0⟩,
  ⟨180, 1, 4, 3⟩,
  ⟨540, 1, 4, 2⟩,
  ⟨540, 1, 4, 1⟩,
  ⟨180, 1, 4, 0⟩,
  ⟨-80, 1, 3, 3⟩,
  ⟨160, 1, 3, 2⟩,
  ⟨560, 1, 3, 1⟩,
  ⟨320, 1, 3, 0⟩,
  ⟨-110, 1, 2, 2⟩,
  ⟨60, 1, 2, 1⟩,
  ⟨170, 1, 2, 0⟩,
  ⟨-20, 1, 1, 1⟩,
  ⟨40, 1, 1, 0⟩,
  ⟨8, 1, 0, 0⟩,
  ⟨-30, 0, 4, 3⟩,
  ⟨-90, 0, 4, 2⟩,
  ⟨-90, 0, 4, 1⟩,
  ⟨-30, 0, 4, 0⟩,
  ⟨20, 0, 3, 3⟩,
  ⟨-20, 0, 3, 2⟩,
  ⟨-100, 0, 3, 1⟩,
  ⟨-60, 0, 3, 0⟩,
  ⟨40, 0, 2, 2⟩,
  ⟨10, 0, 2, 1⟩,
  ⟨-30, 0, 2, 0⟩,
  ⟨20, 0, 1, 1⟩,
  ⟨1, 0, 0, 0⟩]

theorem differenceUpper_identity (t z beta : ℝ) :
    eval differenceUpperData t z beta = differenceDen t z (1+beta)-5*differenceNum t z (1+beta) := by
  norm_num [differenceUpperData, eval, evalTerm, aNum, aDen, kNum, kDen, differenceNum, differenceDen, derivativeNum, derivativeDen, cFactor, pFactor, mFactor] <;> ring

theorem differenceUpper_check : (1/4 : ℚ) ≤
    lowerBound differenceUpperData (1/10000) (1/9) (1/9999) := by decide +kernel

theorem differenceUpper_nonneg {t z beta : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/10000) (hz : 0 ≤ z) (hz' : z ≤ 1/9)
    (hb : 0 ≤ beta) (hb' : beta ≤ 1/9999) :
    0 ≤ differenceDen t z (1+beta)-5*differenceNum t z (1+beta) := by
  have h := certificate_sound differenceUpperData differenceUpper_check ht
    (by norm_num; exact ht') hz (by norm_num; exact hz') hb (by norm_num; exact hb')
  rw [differenceUpper_identity] at h
  norm_num at h
  linarith

def derivativeUpperData : List Term := [
  ⟨160, 9, 5, 4⟩,
  ⟨640, 9, 5, 3⟩,
  ⟨960, 9, 5, 2⟩,
  ⟨640, 9, 5, 1⟩,
  ⟨160, 9, 5, 0⟩,
  ⟨39, 8, 5, 5⟩,
  ⟨-525, 8, 5, 4⟩,
  ⟨-1530, 8, 5, 3⟩,
  ⟨-1050, 8, 5, 2⟩,
  ⟨195, 8, 5, 1⟩,
  ⟨279, 8, 5, 0⟩,
  ⟨-320, 8, 4, 3⟩,
  ⟨-960, 8, 4, 2⟩,
  ⟨-960, 8, 4, 1⟩,
  ⟨-320, 8, 4, 0⟩,
  ⟨-217, 7, 5, 5⟩,
  ⟨-85, 7, 5, 4⟩,
  ⟨-3450, 7, 5, 3⟩,
  ⟨-12010, 7, 5, 2⟩,
  ⟨-12925, 7, 5, 1⟩,
  ⟨-4497, 7, 5, 0⟩,
  ⟨-45, 7, 4, 4⟩,
  ⟨1100, 7, 4, 3⟩,
  ⟨690, 7, 4, 2⟩,
  ⟨-2100, 7, 4, 1⟩,
  ⟨-1645, 7, 4, 0⟩,
  ⟨497, 6, 5, 5⟩,
  ⟨2665, 6, 5, 4⟩,
  ⟨18170, 6, 5, 3⟩,
  ⟨43490, 6, 5, 2⟩,
  ⟨40645, 6, 5, 1⟩,
  ⟨13157, 6, 5, 0⟩,
  ⟨35, 6, 4, 4⟩,
  ⟨-1460, 6, 4, 3⟩,
  ⟨8370, 6, 4, 2⟩,
  ⟨21260, 6, 4, 1⟩,
  ⟨11395, 6, 4, 0⟩,
  ⟨-90, 6, 3, 3⟩,
  ⟨-110, 6, 3, 2⟩,
  ⟨2930, 6, 3, 1⟩,
  ⟨2950, 6, 3, 0⟩,
  ⟨320, 6, 2, 1⟩,
  ⟨320, 6, 2, 0⟩,
  ⟨-599, 5, 5, 5⟩,
  ⟨-4975, 5, 5, 4⟩,
  ⟨-30470, 5, 5, 3⟩,
  ⟨-67550, 5, 5, 2⟩,
  ⟨-60595, 5, 5, 1⟩,
  ⟨-19139, 5, 5, 0⟩,
  ⟨265, 5, 4, 4⟩,
  ⟨1460, 5, 4, 3⟩,
  ⟨-21690, 5, 4, 2⟩,
  ⟨-46700, 5, 4, 1⟩,
  ⟨-23815, 5, 4, 0⟩,
  ⟨470, 5, 3, 3⟩,
  ⟨850, 5, 3, 2⟩,
  ⟨-9790, 5, 3, 1⟩,
  ⟨-10170, 5, 3, 0⟩,
  ⟨70, 5, 2, 2⟩,
  ⟨-1140, 5, 2, 1⟩,
  ⟨-2170, 5, 2, 0⟩,
  ⟨-160, 5, 1, 0⟩,
  ⟨400, 4, 5, 5⟩,
  ⟨4340, 4, 5, 4⟩,
  ⟨26860, 4, 5, 3⟩,
  ⟨58540, 4, 5, 2⟩,
  ⟨51860, 4, 5, 1⟩,
  ⟨16240, 4, 5, 0⟩,
  ⟨-615, 4, 4, 4⟩,
  ⟨-2120, 4, 4, 3⟩,
  ⟨22530, 4, 4, 2⟩,
  ⟨48960, 4, 4, 1⟩,
  ⟨24925, 4, 4, 0⟩,
  ⟨-750, 4, 3, 3⟩,
  ⟨-2290, 4, 3, 2⟩,
  ⟨12070, 4, 3, 1⟩,
  ⟨13610, 4, 3, 0⟩,
  ⟨-10, 4, 2, 2⟩,
  ⟨1580, 4, 2, 1⟩,
  ⟨3990, 4, 2, 0⟩,
  ⟨35, 4, 1, 1⟩,
  ⟨595, 4, 1, 0⟩,
  ⟨-140, 3, 5, 5⟩,
  ⟨-2000, 3, 5, 4⟩,
  ⟨-13530, 3, 5, 3⟩,
  ⟨-29990, 3, 5, 2⟩,
  ⟨-26690, 3, 5, 1⟩,
  ⟨-8370, 3, 5, 0⟩,
  ⟨560, 3, 4, 4⟩,
  ⟨2460, 3, 4, 3⟩,
  ⟨-11280, 3, 4, 2⟩,
  ⟨-27700, 3, 4, 1⟩,
  ⟨-14520, 3, 4, 0⟩,
  ⟨470, 3, 3, 3⟩,
  ⟨2910, 3, 3, 2⟩,
  ⟨-6390, 3, 3, 1⟩,
  ⟨-8830, 3, 3, 0⟩,
  ⟨-310, 3, 2, 2⟩,
  ⟨-860, 3, 2, 1⟩,
  ⟨-2950, 3, 2, 0⟩,
  ⟨-205, 3, 1, 1⟩,
  ⟨-645, 3, 1, 0⟩,
  ⟨-41, 3, 0, 0⟩,
  ⟨20, 2, 5, 5⟩,
  ⟨460, 2, 5, 4⟩,
  ⟨3830, 2, 5, 3⟩,
  ⟨8930, 2, 5, 2⟩,
  ⟨8110, 2, 5, 1⟩,
  ⟨2570, 2, 5, 0⟩,
  ⟨-240, 2, 4, 4⟩,
  ⟨-1500, 2, 4, 3⟩,
  ⟨2430, 2, 4, 2⟩,
  ⟨8400, 2, 4, 1⟩,
  ⟨4710, 2, 4, 0⟩,
  ⟨-60, 2, 3, 3⟩,
  ⟨-1820, 2, 3, 2⟩,
  ⟨1040, 2, 3, 1⟩,
  ⟨2800, 2, 3, 0⟩,
  ⟨390, 2, 2, 2⟩,
  ⟨40, 2, 2, 1⟩,
  ⟨850, 2, 2, 0⟩,
  ⟨205, 2, 1, 1⟩,
  ⟨225, 2, 1, 0⟩,
  ⟨23, 2, 0, 0⟩,
  ⟨-40, 1, 5, 4⟩,
  ⟨-550, 1, 5, 3⟩,
  ⟨-1410, 1, 5, 2⟩,
  ⟨-1330, 1, 5, 1⟩,
  ⟨-430, 1, 5, 0⟩,
  ⟨40, 1, 4, 4⟩,
  ⟨420, 1, 4, 3⟩,
  ⟨-60, 1, 4, 2⟩,
  ⟨-1220, 1, 4, 1⟩,
  ⟨-780, 1, 4, 0⟩,
  ⟨-60, 1, 3, 3⟩,
  ⟨500, 1, 3, 2⟩,
  ⟨190, 1, 3, 1⟩,
  ⟨-370, 1, 3, 0⟩,
  ⟨-200, 1, 2, 2⟩,
  ⟨60, 1, 2, 1⟩,
  ⟨-40, 1, 2, 0⟩,
  ⟨-95, 1, 1, 1⟩,
  ⟨-15, 1, 1, 0⟩,
  ⟨-3, 1, 0, 0⟩,
  ⟨30, 0, 5, 3⟩,
  ⟨90, 0, 5, 2⟩,
  ⟨90, 0, 5, 1⟩,
  ⟨30, 0, 5, 0⟩,
  ⟨-40, 0, 4, 3⟩,
  ⟨-30, 0, 4, 2⟩,
  ⟨60, 0, 4, 1⟩,
  ⟨50, 0, 4, 0⟩,
  ⟨20, 0, 3, 3⟩,
  ⟨-40, 0, 3, 2⟩,
  ⟨-50, 0, 3, 1⟩,
  ⟨10, 0, 3, 0⟩,
  ⟨40, 0, 2, 2⟩,
  ⟨-10, 0, 2, 0⟩,
  ⟨20, 0, 1, 1⟩,
  ⟨1, 0, 0, 0⟩]

theorem derivativeUpper_identity (t z beta : ℝ) :
    eval derivativeUpperData t z beta = derivativeDen t z (1+beta)*pFactor t z (1+beta)-10*derivativeNum t z (1+beta)*cFactor t z (1+beta)*(1-2*t) := by
  norm_num [derivativeUpperData, eval, evalTerm, aNum, aDen, kNum, kDen, differenceNum, differenceDen, derivativeNum, derivativeDen, cFactor, pFactor, mFactor] <;> ring

theorem derivativeUpper_check : (1/4 : ℚ) ≤
    lowerBound derivativeUpperData (1/10000) (1/9) (1/9999) := by decide +kernel

theorem derivativeUpper_nonneg {t z beta : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/10000) (hz : 0 ≤ z) (hz' : z ≤ 1/9)
    (hb : 0 ≤ beta) (hb' : beta ≤ 1/9999) :
    0 ≤ derivativeDen t z (1+beta)*pFactor t z (1+beta)-10*derivativeNum t z (1+beta)*cFactor t z (1+beta)*(1-2*t) := by
  have h := certificate_sound derivativeUpperData derivativeUpper_check ht
    (by norm_num; exact ht') hz (by norm_num; exact hz') hb (by norm_num; exact hb')
  rw [derivativeUpper_identity] at h
  norm_num at h
  linarith

theorem aLower_nonneg {t z beta : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/10000) (hz : 0 ≤ z) (hz' : z ≤ 1/9)
    (hb : 0 ≤ beta) (hb' : beta ≤ 1/9999) :
    0 ≤ 100*aNum t z (1+beta)-99*aDen t z (1+beta) := by
  have hrem := aLowerRemainder_nonneg ht ht' hz hz' hb hb'
  have hfac : 0 ≤ 1-z-z^2 := by
    nlinarith [mul_nonneg hz (sub_nonneg.mpr hz')]
  have hpos : 0 ≤ 100*z*(1-z-z^2) := mul_nonneg (by positivity) hfac
  linarith

#print axioms aLowerRemainder_identity
#print axioms aLowerRemainder_check
#print axioms aLowerRemainder_nonneg
#print axioms aUpper_identity
#print axioms aUpper_check
#print axioms aUpper_nonneg
#print axioms kUpper_identity
#print axioms kUpper_check
#print axioms kUpper_nonneg
#print axioms differenceUpper_identity
#print axioms differenceUpper_check
#print axioms differenceUpper_nonneg
#print axioms derivativeUpper_identity
#print axioms derivativeUpper_check
#print axioms derivativeUpper_nonneg
#print axioms aLower_nonneg

end GeneralCK.SmallBoundaryPhiCompactBox

end


