-- Prove2me | Definitions.Def_CK_GeneralCK_SmallBoundaryPhiTailBox
-- name    : CK_GeneralCK_SmallBoundaryPhiTailBox
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:11:30.982423+00:00
-- url     : https://prove2.me/theorems/2c9f5ea3-7a58-4b60-a985-7a700a7b7f72
-- title:
--   Courtade–Kumar proof module `GeneralCK.SmallBoundaryPhiTailBox` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.SmallBoundaryPhiTailBox` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.SmallBoundaryPhiTailBox` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.SmallBoundaryPhiTailBox (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/SmallBoundaryPhiTailBox.lean)

import Definitions.Def_CK_GeneralCK_Certificates_NonnegativeBoxPolynomial

-- ===== source module GeneralCK.SmallBoundaryPhiTailBox =====
section

namespace GeneralCK.SmallBoundaryPhiTailBox
noncomputable section
open GeneralCK.Certificates.NonnegativeBoxPolynomial
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def cFactor (t z b : ℝ) : ℝ := 1+(1-t)*b*z
def pFactor (t z b : ℝ) : ℝ := 1+t*b*z
def mFactor (t z b : ℝ) : ℝ := 1-t*b*z
def aNum (t z b : ℝ) : ℝ :=
  (cFactor t z b)^2*(1-2*t)*(1+t*b*z-(1-2*t)^2*z)
def aDen (t z b : ℝ) : ℝ := (1-t)^2*(pFactor t z b)^3
def kNum (t z b : ℝ) : ℝ :=
  (cFactor t z b)^2*((t^2+(1-t)^2)*(1-t*b*z)-(1-2*t)*z)
def kDen (t z b : ℝ) : ℝ := (1-t)^2*(mFactor t z b)^3
def differenceDen (t z b : ℝ) : ℝ :=
  (1-t)^2*(pFactor t z b)^3*(mFactor t z b)^3
def derivativeDen (t z b : ℝ) : ℝ := (1-t)^3*(pFactor t z b)^4
def differenceNum (t z b : ℝ) : ℝ :=
  (2 * ((-1 + (-1 * b * z) + (b * t * z)) ^ 2) * ((-1 * t) + (2 * z) + (-6 * t * z) + (-2 * b * z) + (3 * b * (z ^ 2)) + (4 * z * (t ^ 2)) + ((b ^ 3) * (t ^ 2) * (z ^ 4)) + ((b ^ 4) * (t ^ 5) * (z ^ 4)) + (-18 * (b ^ 2) * (t ^ 3) * (z ^ 3)) + (-12 * b * t * (z ^ 2)) + (-12 * b * (t ^ 3) * (z ^ 2)) + (-4 * (b ^ 3) * (t ^ 3) * (z ^ 3)) + (-4 * (b ^ 3) * (t ^ 3) * (z ^ 4)) + (-4 * (b ^ 3) * (t ^ 5) * (z ^ 4)) + (-2 * b * z * (t ^ 2)) + (2 * (b ^ 3) * (t ^ 2) * (z ^ 3)) + (2 * (b ^ 3) * (t ^ 4) * (z ^ 3)) + (4 * b * t * z) + (6 * (b ^ 2) * (t ^ 2) * (z ^ 3)) + (6 * (b ^ 3) * (t ^ 4) * (z ^ 4)) + (12 * (b ^ 2) * (t ^ 4) * (z ^ 3)) + (18 * b * (t ^ 2) * (z ^ 2))))
def derivativeNum (t z b : ℝ) : ℝ :=
  (-1 * (-1 + (-1 * b * z) + (b * t * z)) * ((-3 * (z ^ 2)) + (-2 * (t ^ 2)) + (2 * z) + (-72 * (t ^ 2) * (z ^ 2)) + (-48 * (t ^ 4) * (z ^ 2)) + (-10 * z * (t ^ 2)) + (-8 * z * (t ^ 4)) + (-4 * t * z) + (-3 * b * (z ^ 3)) + (-2 * b * z) + (4 * b * (z ^ 2)) + (24 * t * (z ^ 2)) + (24 * z * (t ^ 3)) + (96 * (t ^ 3) * (z ^ 2)) + (-144 * b * (t ^ 4) * (z ^ 3)) + (-96 * b * (t ^ 2) * (z ^ 3)) + (-20 * (b ^ 2) * (t ^ 2) * (z ^ 3)) + (-18 * b * t * (z ^ 2)) + (-16 * b * (t ^ 3) * (z ^ 2)) + (-16 * (b ^ 2) * (t ^ 5) * (z ^ 3)) + (-12 * (b ^ 2) * (t ^ 3) * (z ^ 2)) + (-6 * b * z * (t ^ 2)) + (-6 * (b ^ 2) * (t ^ 4) * (z ^ 3)) + (-6 * (b ^ 3) * (t ^ 4) * (z ^ 3)) + (-4 * t * (b ^ 2) * (z ^ 2)) + (-2 * b * z * (t ^ 3)) + (-2 * (b ^ 3) * (t ^ 2) * (z ^ 3)) + (2 * (b ^ 2) * (t ^ 4) * (z ^ 2)) + (2 * (b ^ 3) * (t ^ 5) * (z ^ 3)) + (4 * t * (b ^ 2) * (z ^ 3)) + (6 * b * t * z) + (6 * (b ^ 3) * (t ^ 3) * (z ^ 3)) + (8 * b * (t ^ 4) * (z ^ 2)) + (8 * (b ^ 2) * (t ^ 6) * (z ^ 3)) + (12 * (b ^ 2) * (t ^ 2) * (z ^ 2)) + (26 * b * (t ^ 2) * (z ^ 2)) + (27 * b * t * (z ^ 3)) + (30 * (b ^ 2) * (t ^ 3) * (z ^ 3)) + (48 * b * (t ^ 5) * (z ^ 3)) + (168 * b * (t ^ 3) * (z ^ 3))))
def A (t z b : ℝ) : ℝ := aNum t z b / aDen t z b
def K (t z b : ℝ) : ℝ := kNum t z b / kDen t z b
def EL (t z b : ℝ) : ℝ := pFactor t z b / (cFactor t z b*(1-2*t))
def normalizedDerivative (t z b : ℝ) : ℝ := derivativeNum t z b / derivativeDen t z b

theorem differenceNum_identity (t z b : ℝ) :
    t*differenceNum t z b = aNum t z b*(mFactor t z b)^3-
      kNum t z b*(pFactor t z b)^3 := by
  unfold differenceNum aNum kNum mFactor pFactor cFactor
  ring

def aLowerData : List Term := [
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
  ⟨-100, 0, 3, 0⟩,
  ⟨100, 0, 2, 2⟩,
  ⟨-100, 0, 2, 0⟩,
  ⟨200, 0, 1, 1⟩,
  ⟨100, 0, 1, 0⟩,
  ⟨1, 0, 0, 0⟩]

theorem aLower_identity (t z beta : ℝ) :
    eval aLowerData t z beta = 100*aNum t z (1+beta)-99*aDen t z (1+beta) := by
  norm_num [aLowerData, eval, evalTerm, aNum, aDen, kNum, kDen, differenceNum, differenceDen, derivativeNum, derivativeDen, cFactor, pFactor, mFactor] <;> ring

theorem aLower_check : (1/2 : ℚ) ≤
    lowerBound aLowerData (1/10000) (1/49) (1/10000) := by decide +kernel

theorem aLower_nonneg {t z beta : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/10000) (hz : 0 ≤ z) (hz' : z ≤ 1/49)
    (hb : 0 ≤ beta) (hb' : beta ≤ 1/10000) :
    0 ≤ 100*aNum t z (1+beta)-99*aDen t z (1+beta) := by
  have h := certificate_sound aLowerData aLower_check ht
    (by norm_num; exact ht') hz (by norm_num; exact hz') hb (by norm_num; exact hb')
  rw [aLower_identity] at h
  norm_num at h
  linarith

def aUpperData : List Term := [
  ⟨11, 5, 3, 3⟩,
  ⟨-47, 5, 3, 2⟩,
  ⟨-127, 5, 3, 1⟩,
  ⟨-69, 5, 3, 0⟩,
  ⟨-2, 4, 3, 3⟩,
  ⟨274, 4, 3, 2⟩,
  ⟨554, 4, 3, 1⟩,
  ⟨278, 4, 3, 0⟩,
  ⟨33, 4, 2, 2⟩,
  ⟨226, 4, 2, 1⟩,
  ⟨193, 4, 2, 0⟩,
  ⟨-39, 3, 3, 3⟩,
  ⟨-497, 3, 3, 2⟩,
  ⟨-877, 3, 3, 1⟩,
  ⟨-419, 3, 3, 0⟩,
  ⟨-86, 3, 2, 2⟩,
  ⟨-572, 3, 2, 1⟩,
  ⟨-486, 3, 2, 0⟩,
  ⟨33, 3, 1, 1⟩,
  ⟨-47, 3, 1, 0⟩,
  ⟨40, 2, 3, 3⟩,
  ⟨370, 2, 3, 2⟩,
  ⟨620, 2, 3, 1⟩,
  ⟨290, 2, 3, 0⟩,
  ⟨43, 2, 2, 2⟩,
  ⟨446, 2, 2, 1⟩,
  ⟨403, 2, 2, 0⟩,
  ⟨-86, 2, 1, 1⟩,
  ⟨34, 2, 1, 0⟩,
  ⟨11, 2, 0, 0⟩,
  ⟨-10, 1, 3, 3⟩,
  ⟨-110, 1, 3, 2⟩,
  ⟨-190, 1, 3, 1⟩,
  ⟨-90, 1, 3, 0⟩,
  ⟨20, 1, 2, 2⟩,
  ⟨-100, 1, 2, 1⟩,
  ⟨-120, 1, 2, 0⟩,
  ⟨83, 1, 1, 1⟩,
  ⟨23, 1, 1, 0⟩,
  ⟨-2, 1, 0, 0⟩,
  ⟨10, 0, 3, 2⟩,
  ⟨20, 0, 3, 1⟩,
  ⟨10, 0, 3, 0⟩,
  ⟨-10, 0, 2, 2⟩,
  ⟨10, 0, 2, 0⟩,
  ⟨-20, 0, 1, 1⟩,
  ⟨-10, 0, 1, 0⟩,
  ⟨1, 0, 0, 0⟩]

theorem aUpper_identity (t z beta : ℝ) :
    eval aUpperData t z beta = 11*aDen t z (1+beta)-10*aNum t z (1+beta) := by
  norm_num [aUpperData, eval, evalTerm, aNum, aDen, kNum, kDen, differenceNum, differenceDen, derivativeNum, derivativeDen, cFactor, pFactor, mFactor] <;> ring

theorem aUpper_check : (1/2 : ℚ) ≤
    lowerBound aUpperData (1/10000) (1/49) (1/10000) := by decide +kernel

theorem aUpper_nonneg {t z beta : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/10000) (hz : 0 ≤ z) (hz' : z ≤ 1/49)
    (hb : 0 ≤ beta) (hb' : beta ≤ 1/10000) :
    0 ≤ 11*aDen t z (1+beta)-10*aNum t z (1+beta) := by
  have h := certificate_sound aUpperData aUpper_check ht
    (by norm_num; exact ht') hz (by norm_num; exact hz') hb (by norm_num; exact hb')
  rw [aUpper_identity] at h
  norm_num at h
  linarith

def kUpperData : List Term := [
  ⟨9, 5, 3, 3⟩,
  ⟨27, 5, 3, 2⟩,
  ⟨27, 5, 3, 1⟩,
  ⟨9, 5, 3, 0⟩,
  ⟨-38, 4, 3, 3⟩,
  ⟨-114, 4, 3, 2⟩,
  ⟨-114, 4, 3, 1⟩,
  ⟨-38, 4, 3, 0⟩,
  ⟨-27, 4, 2, 2⟩,
  ⟨-54, 4, 2, 1⟩,
  ⟨-27, 4, 2, 0⟩,
  ⟨59, 3, 3, 3⟩,
  ⟨157, 3, 3, 2⟩,
  ⟨137, 3, 3, 1⟩,
  ⟨39, 3, 3, 0⟩,
  ⟨74, 3, 2, 2⟩,
  ⟨148, 3, 2, 1⟩,
  ⟨74, 3, 2, 0⟩,
  ⟨27, 3, 1, 1⟩,
  ⟨27, 3, 1, 0⟩,
  ⟨-40, 2, 3, 3⟩,
  ⟨-70, 2, 3, 2⟩,
  ⟨-20, 2, 3, 1⟩,
  ⟨10, 2, 3, 0⟩,
  ⟨-97, 2, 2, 2⟩,
  ⟨-154, 2, 2, 1⟩,
  ⟨-57, 2, 2, 0⟩,
  ⟨-34, 2, 1, 1⟩,
  ⟨-34, 2, 1, 0⟩,
  ⟨-9, 2, 0, 0⟩,
  ⟨10, 1, 3, 3⟩,
  ⟨-10, 1, 3, 2⟩,
  ⟨-50, 1, 3, 1⟩,
  ⟨-30, 1, 3, 0⟩,
  ⟨60, 1, 2, 2⟩,
  ⟨60, 1, 2, 1⟩,
  ⟨37, 1, 1, 1⟩,
  ⟨17, 1, 1, 0⟩,
  ⟨-2, 1, 0, 0⟩,
  ⟨10, 0, 3, 2⟩,
  ⟨20, 0, 3, 1⟩,
  ⟨10, 0, 3, 0⟩,
  ⟨-10, 0, 2, 2⟩,
  ⟨10, 0, 2, 0⟩,
  ⟨-20, 0, 1, 1⟩,
  ⟨-10, 0, 1, 0⟩,
  ⟨1, 0, 0, 0⟩]

theorem kUpper_identity (t z beta : ℝ) :
    eval kUpperData t z beta = 11*kDen t z (1+beta)-10*kNum t z (1+beta) := by
  norm_num [kUpperData, eval, evalTerm, aNum, aDen, kNum, kDen, differenceNum, differenceDen, derivativeNum, derivativeDen, cFactor, pFactor, mFactor] <;> ring

theorem kUpper_check : (1/2 : ℚ) ≤
    lowerBound kUpperData (1/10000) (1/49) (1/10000) := by decide +kernel

theorem kUpper_nonneg {t z beta : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/10000) (hz : 0 ≤ z) (hz' : z ≤ 1/49)
    (hb : 0 ≤ beta) (hb' : beta ≤ 1/10000) :
    0 ≤ 11*kDen t z (1+beta)-10*kNum t z (1+beta) := by
  have h := certificate_sound kUpperData kUpper_check ht
    (by norm_num; exact ht') hz (by norm_num; exact hz') hb (by norm_num; exact hb')
  rw [kUpper_identity] at h
  norm_num at h
  linarith

def differenceUpperData : List Term := [
  ⟨-2, 8, 6, 6⟩,
  ⟨-12, 8, 6, 5⟩,
  ⟨-30, 8, 6, 4⟩,
  ⟨-40, 8, 6, 3⟩,
  ⟨-30, 8, 6, 2⟩,
  ⟨-12, 8, 6, 1⟩,
  ⟨-2, 8, 6, 0⟩,
  ⟨-6, 7, 6, 6⟩,
  ⟨4, 7, 6, 5⟩,
  ⟨110, 7, 6, 4⟩,
  ⟨280, 7, 6, 3⟩,
  ⟨310, 7, 6, 2⟩,
  ⟨164, 7, 6, 1⟩,
  ⟨34, 7, 6, 0⟩,
  ⟨18, 6, 6, 6⟩,
  ⟨-32, 6, 6, 5⟩,
  ⟨-430, 6, 6, 4⟩,
  ⟨-1040, 6, 6, 3⟩,
  ⟨-1130, 6, 6, 2⟩,
  ⟨-592, 6, 6, 1⟩,
  ⟨-122, 6, 6, 0⟩,
  ⟨-200, 6, 5, 4⟩,
  ⟨-800, 6, 5, 3⟩,
  ⟨-1200, 6, 5, 2⟩,
  ⟨-800, 6, 5, 1⟩,
  ⟨-200, 6, 5, 0⟩,
  ⟨6, 6, 4, 4⟩,
  ⟨24, 6, 4, 3⟩,
  ⟨36, 6, 4, 2⟩,
  ⟨24, 6, 4, 1⟩,
  ⟨6, 6, 4, 0⟩,
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
  ⟨18, 5, 4, 4⟩,
  ⟨472, 5, 4, 3⟩,
  ⟨1308, 5, 4, 2⟩,
  ⟨1272, 5, 4, 1⟩,
  ⟨418, 5, 4, 0⟩,
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
  ⟨-114, 4, 4, 4⟩,
  ⟨-1536, 4, 4, 3⟩,
  ⟨-3924, 4, 4, 2⟩,
  ⟨-3696, 4, 4, 1⟩,
  ⟨-1194, 4, 4, 0⟩,
  ⟨-400, 4, 3, 2⟩,
  ⟨-800, 4, 3, 1⟩,
  ⟨-400, 4, 3, 0⟩,
  ⟨-6, 4, 2, 2⟩,
  ⟨-12, 4, 2, 1⟩,
  ⟨-6, 4, 2, 0⟩,
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
  ⟨-18, 3, 2, 2⟩,
  ⟨164, 3, 2, 1⟩,
  ⟨182, 3, 2, 0⟩,
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
  ⟨94, 2, 2, 2⟩,
  ⟨-192, 2, 2, 1⟩,
  ⟨-286, 2, 2, 0⟩,
  ⟨-40, 2, 1, 0⟩,
  ⟨2, 2, 0, 0⟩,
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
  ⟨6, 1, 0, 0⟩,
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
  ⟨2, 0, 0, 0⟩]

theorem differenceUpper_identity (t z beta : ℝ) :
    eval differenceUpperData t z beta = 2*differenceDen t z (1+beta)-5*differenceNum t z (1+beta) := by
  norm_num [differenceUpperData, eval, evalTerm, aNum, aDen, kNum, kDen, differenceNum, differenceDen, derivativeNum, derivativeDen, cFactor, pFactor, mFactor] <;> ring

theorem differenceUpper_check : (1/2 : ℚ) ≤
    lowerBound differenceUpperData (1/10000) (1/49) (1/10000) := by decide +kernel

theorem differenceUpper_nonneg {t z beta : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/10000) (hz : 0 ≤ z) (hz' : z ≤ 1/49)
    (hb : 0 ≤ beta) (hb' : beta ≤ 1/10000) :
    0 ≤ 2*differenceDen t z (1+beta)-5*differenceNum t z (1+beta) := by
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

theorem derivativeUpper_check : (1/2 : ℚ) ≤
    lowerBound derivativeUpperData (1/10000) (1/49) (1/10000) := by decide +kernel

theorem derivativeUpper_nonneg {t z beta : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/10000) (hz : 0 ≤ z) (hz' : z ≤ 1/49)
    (hb : 0 ≤ beta) (hb' : beta ≤ 1/10000) :
    0 ≤ derivativeDen t z (1+beta)*pFactor t z (1+beta)-10*derivativeNum t z (1+beta)*cFactor t z (1+beta)*(1-2*t) := by
  have h := certificate_sound derivativeUpperData derivativeUpper_check ht
    (by norm_num; exact ht') hz (by norm_num; exact hz') hb (by norm_num; exact hb')
  rw [derivativeUpper_identity] at h
  norm_num at h
  linarith


theorem factors_pos {t z b : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/10000) (hz : 0 ≤ z) (hz' : z ≤ 1/49)
    (hb : 1 ≤ b) (hb' : b ≤ 1+1/10000) :
    0 < 1-t ∧ 0 < 1-2*t ∧ 0 < cFactor t z b ∧
      0 < pFactor t z b ∧ 0 < mFactor t z b := by
  have ht1 : 0 < 1-t := by linarith
  have ht2 : 0 < 1-2*t := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hb2 : b ≤ 2 := by linarith
  have hz1 : z ≤ 1 := by linarith
  have hprod : t*b*z ≤ (1/10000 : ℝ)*2*1 := by gcongr
  refine ⟨ht1, ht2, ?_, ?_, ?_⟩
  · unfold cFactor; positivity
  · unfold pFactor; positivity
  · unfold mFactor; linarith

theorem denominators_pos {t z b : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/10000) (hz : 0 ≤ z) (hz' : z ≤ 1/49)
    (hb : 1 ≤ b) (hb' : b ≤ 1+1/10000) :
    0 < aDen t z b ∧ 0 < kDen t z b ∧ 0 < differenceDen t z b ∧
      0 < derivativeDen t z b ∧ 0 < cFactor t z b*(1-2*t) := by
  rcases factors_pos ht ht' hz hz' hb hb' with ⟨ht1, ht2, hC, hP, hM⟩
  unfold aDen kDen differenceDen derivativeDen
  exact ⟨by positivity, by positivity, by positivity, by positivity, by positivity⟩

theorem A_lower {t z b : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/10000) (hz : 0 ≤ z) (hz' : z ≤ 1/49)
    (hb : 1 ≤ b) (hb' : b ≤ 1+1/10000) : 99/100 ≤ A t z b := by
  have hp := aLower_nonneg ht ht' hz hz' (sub_nonneg.mpr hb)
    (show b-1 ≤ 1/10000 by linarith)
  rw [show 1+(b-1)=b by ring] at hp
  apply (le_div_iff₀ (denominators_pos ht ht' hz hz' hb hb').1).2
  linarith

theorem A_upper {t z b : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/10000) (hz : 0 ≤ z) (hz' : z ≤ 1/49)
    (hb : 1 ≤ b) (hb' : b ≤ 1+1/10000) : A t z b ≤ 11/10 := by
  have hp := aUpper_nonneg ht ht' hz hz' (sub_nonneg.mpr hb)
    (show b-1 ≤ 1/10000 by linarith)
  rw [show 1+(b-1)=b by ring] at hp
  apply (div_le_iff₀ (denominators_pos ht ht' hz hz' hb hb').1).2
  linarith

theorem K_upper {t z b : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/10000) (hz : 0 ≤ z) (hz' : z ≤ 1/49)
    (hb : 1 ≤ b) (hb' : b ≤ 1+1/10000) : K t z b ≤ 11/10 := by
  have hp := kUpper_nonneg ht ht' hz hz' (sub_nonneg.mpr hb)
    (show b-1 ≤ 1/10000 by linarith)
  rw [show 1+(b-1)=b by ring] at hp
  apply (div_le_iff₀ (denominators_pos ht ht' hz hz' hb hb').2.1).2
  linarith

theorem cancelled_difference_upper {t z b : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/10000) (hz : 0 ≤ z) (hz' : z ≤ 1/49)
    (hb : 1 ≤ b) (hb' : b ≤ 1+1/10000) :
    differenceNum t z b / (2*differenceDen t z b) ≤ 1/5 := by
  have hp := differenceUpper_nonneg ht ht' hz hz' (sub_nonneg.mpr hb)
    (show b-1 ≤ 1/10000 by linarith)
  rw [show 1+(b-1)=b by ring] at hp
  have hd := (denominators_pos ht ht' hz hz' hb hb').2.2.1
  apply (div_le_iff₀ (show 0 < 2*differenceDen t z b by positivity)).2
  linarith

theorem A_sub_K_identity {t z b : ℝ}
    (hP : pFactor t z b ≠ 0) (hM : mFactor t z b ≠ 0) :
    A t z b-K t z b = t*differenceNum t z b/differenceDen t z b := by
  have hda : aDen t z b*(mFactor t z b)^3 = differenceDen t z b := rfl
  have hdk : kDen t z b*(pFactor t z b)^3 = differenceDen t z b := by
    unfold kDen differenceDen
    ring
  calc
    A t z b-K t z b =
        (aNum t z b*(mFactor t z b)^3)/(aDen t z b*(mFactor t z b)^3)-
        (kNum t z b*(pFactor t z b)^3)/(kDen t z b*(pFactor t z b)^3) := by
      rw [mul_div_mul_right _ _ (pow_ne_zero _ hM),
        mul_div_mul_right _ _ (pow_ne_zero _ hP)]
      rfl
    _ = (aNum t z b*(mFactor t z b)^3-kNum t z b*(pFactor t z b)^3)/
        differenceDen t z b := by rw [hda, hdk, sub_div]
    _ = t*differenceNum t z b/differenceDen t z b := by
      rw [differenceNum_identity]

theorem difference_identity {t z b : ℝ} (ht : t ≠ 0)
    (ht1 : 1-t ≠ 0) (hP : pFactor t z b ≠ 0) (hM : mFactor t z b ≠ 0) :
    (A t z b-K t z b)/(2*t) = differenceNum t z b/(2*differenceDen t z b) := by
  rw [A_sub_K_identity hP hM]
  have hd : differenceDen t z b ≠ 0 := by
    unfold differenceDen
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ ht1) (pow_ne_zero _ hP))
      (pow_ne_zero _ hM)
  field_simp

theorem A_sub_K_upper {t z b : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/10000) (hz : 0 ≤ z) (hz' : z ≤ 1/49)
    (hb : 1 ≤ b) (hb' : b ≤ 1+1/10000) :
    A t z b-K t z b ≤ (2/5)*t := by
  rcases factors_pos ht ht' hz hz' hb hb' with ⟨_, _, _, hP, hM⟩
  have hp := differenceUpper_nonneg ht ht' hz hz' (sub_nonneg.mpr hb)
    (show b-1 ≤ 1/10000 by linarith)
  rw [show 1+(b-1)=b by ring] at hp
  have hd := (denominators_pos ht ht' hz hz' hb hb').2.2.1
  have hh : differenceNum t z b/differenceDen t z b ≤ 2/5 :=
    (div_le_iff₀ hd).2 (by linarith)
  rw [A_sub_K_identity hP.ne' hM.ne', mul_div_assoc]
  simpa only [mul_comm t (2/5)] using mul_le_mul_of_nonneg_left hh ht

theorem difference_upper {t z b : ℝ}
    (ht : 0 < t) (ht' : t ≤ 1/10000) (hz : 0 ≤ z) (hz' : z ≤ 1/49)
    (hb : 1 ≤ b) (hb' : b ≤ 1+1/10000) :
    (A t z b-K t z b)/(2*t) ≤ 1/5 := by
  rcases factors_pos ht.le ht' hz hz' hb hb' with ⟨ht1, _, _, hP, hM⟩
  rw [difference_identity ht.ne' ht1.ne' hP.ne' hM.ne']
  exact cancelled_difference_upper ht.le ht' hz hz' hb hb'

theorem normalizedDerivative_upper {t z b : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/10000) (hz : 0 ≤ z) (hz' : z ≤ 1/49)
    (hb : 1 ≤ b) (hb' : b ≤ 1+1/10000) : normalizedDerivative t z b ≤ EL t z b/10 := by
  have hp := derivativeUpper_nonneg ht ht' hz hz' (sub_nonneg.mpr hb)
    (show b-1 ≤ 1/10000 by linarith)
  rw [show 1+(b-1)=b by ring] at hp
  rcases denominators_pos ht ht' hz hz' hb hb' with ⟨_, _, _, hD, hE⟩
  unfold normalizedDerivative EL
  rw [div_div]
  apply (div_le_div_iff₀ hD (show 0 < cFactor t z b*(1-2*t)*10 by positivity)).2
  nlinarith

#print axioms differenceNum_identity
#print axioms aLower_nonneg
#print axioms aUpper_nonneg
#print axioms kUpper_nonneg
#print axioms differenceUpper_nonneg
#print axioms derivativeUpper_nonneg
#print axioms denominators_pos
#print axioms A_lower
#print axioms A_upper
#print axioms K_upper
#print axioms difference_identity
#print axioms A_sub_K_identity
#print axioms A_sub_K_upper
#print axioms difference_upper
#print axioms normalizedDerivative_upper

end
end GeneralCK.SmallBoundaryPhiTailBox

end


