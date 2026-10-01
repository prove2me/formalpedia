-- Prove2me | Definitions.Def_CK_CKLaneM09_Checker
-- name    : CK_CKLaneM09_Checker
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:06:44.262578+00:00
-- url     : https://prove2.me/theorems/5f55af23-a5a1-4ff1-a2e9-ce34fefa1e19
-- title:
--   Courtade–Kumar proof module `CKLaneM09.Checker` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM09.Checker` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM09.Checker` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM09.Checker (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM09/Checker.lean)

import Definitions.Def_CK_CKLaneM09_CapCore

-- ===== source module CKLaneM09.Checker =====
section

/-!
# Lane M09: Boolean checker for the archived `global_cap_slope` owner, and its soundness

`capCheck U w` binds the rational box `w` to the archived `(u, v, t)` leaf `U` (exact `Nat`-power
comparisons for `2^-u`, via `CKLaneD.pow2LowerOK/UpperOK`), recomputes in exact `ℚ` every primitive
enclosure from kernel-checkable logarithm certificates (`CKLaneE.FP`), and accepts iff the archive's
cap-slope inequality `P1up(v) - 4 ≤ 2 k_lo` holds, where `k_lo` is the interval lower bound of both
cap-plane coefficients `capA`, `capB` over the box and `P1up(v)` bounds the profile slope on `[0, I_hi]`.

`capCheck_sound : capCheck U w = true → CKLaneD.SemUVT U`: every finite interior law whose means and
mean entropy lie in the exact clipped physical image of the leaf satisfies
`candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.cost`.  No other hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM09

open GeneralCK GeneralCK.PsiEndpointPlane CKLaneD CKLaneE

/-- Rational literal helper. -/
def rq (n : ℤ) (d : ℕ) : ℚ := (n : ℚ) / (d : ℚ)

/-- Per-leaf witness: rational box of the physical image and the slope anchor `v`. -/
structure CapWitness where
  alo : ℚ
  ahi : ℚ
  blo : ℚ
  bhi : ℚ
  v : ℚ
  deriving Repr, DecidableEq

namespace CapWitness

variable (w : CapWitness)

/-- Interval data for `m11 = -log a`, `m12 = -log b`, `m21 = -log (1-a)`, `m22 = -log (1-b)`. -/
def m11lo : ℚ := -FP.lHi w.ahi
def m11hi : ℚ := -FP.lLo w.alo
def m12lo : ℚ := -FP.lHi w.bhi
def m12hi : ℚ := -FP.lLo w.blo
def m21lo : ℚ := -FP.l1Hi w.alo
def m21hi : ℚ := -FP.l1Lo w.ahi
def m22lo : ℚ := -FP.l1Hi w.blo
def m22hi : ℚ := -FP.l1Lo w.bhi
/-- Interval data for `r1 = 1/(2ab)` and `r2 = 1/(2(1-a)(1-b))`. -/
def r1lo : ℚ := 1 / (2 * w.ahi * w.bhi)
def r1hi : ℚ := 1 / (2 * w.alo * w.blo)
def r2lo : ℚ := 1 / (2 * (1 - w.alo) * (1 - w.blo))
def r2hi : ℚ := 1 / (2 * (1 - w.ahi) * (1 - w.bhi))
def detlo : ℚ := w.m11lo * w.m22lo - w.m12hi * w.m21hi
def dethi : ℚ := w.m11hi * w.m22hi - w.m12lo * w.m21lo
def nAlo : ℚ := w.r1lo * w.m22lo - w.r2hi * w.m12hi
def nDlo : ℚ := w.m11lo * w.r2lo - w.m21hi * w.r1hi
def dlo : ℚ := w.blo - w.ahi
/-- Lower bound of `min (capA a b) (capB a b)` over the box (archive: `(b-a)_lo^2 min(A0_lo, D0_lo)`). -/
def klo : ℚ := w.dlo ^ 2 * min (w.nAlo / w.dethi) (w.nDlo / w.dethi)
def C0lo : ℚ := (FP.Hlo w.alo + FP.Hlo w.bhi) / 2
/-- Lower bound of the mean entropy on the leaf (`E ≥ EMIN + t0 (C0 - EMIN)`). -/
def ELo (t0 : ℚ) : ℚ := EMIN + t0 * (w.C0lo - EMIN)
def mhi : ℚ := (w.ahi + w.bhi) / 2
def HmHi : ℚ := if w.mhi < 1 / 2 then FP.Hhi w.mhi else 1
/-- Upper bound of the information `I = H((a+b)/2) - E` on the leaf. -/
def Ihi (t0 : ℚ) : ℚ := w.HmHi - w.ELo t0

end CapWitness

/-- The rational box contains the clipped physical image of the `(u,v,t)` leaf `U`. -/
def boxOk (U : UVT) (w : CapWitness) : Bool :=
  pow2LowerOK w.alo U.u1 && (pow2UpperOK w.ahi U.u0 || decide (1 / 10 ≤ w.ahi)) &&
    pow2UpperOK (1 - w.blo) U.v0 && (pow2LowerOK (1 - w.bhi) U.v1 || decide (1 - w.alo ≤ w.bhi))

/-- The per-leaf Boolean checker. -/
def capCheck (U : UVT) (w : CapWitness) : Bool :=
  boxOk U w &&
  decide (0 < w.alo ∧ w.alo ≤ w.ahi ∧ w.ahi < w.blo ∧ 1 / 2 ≤ w.blo ∧ w.blo ≤ w.bhi ∧
    w.bhi < 1 ∧ w.ahi ≤ 1 / 2 ∧ 0 ≤ U.t0) &&
  FP.ptOk w.alo && FP.ptOk w.ahi && FP.ptOk w.blo && FP.ptOk w.bhi &&
  (decide (1 / 2 ≤ w.mhi) || FP.ptOk w.mhi) &&
  FP.anchorOk w.v (w.Ihi U.t0) &&
  decide (0 ≤ w.m11lo ∧ 0 ≤ w.m12lo ∧ 0 ≤ w.m21lo ∧ 0 ≤ w.m22lo) &&
  decide (0 < w.detlo ∧ 0 < w.nAlo ∧ 0 < w.nDlo) &&
  decide (FP.P1up w.v - 4 ≤ 2 * w.klo)

/-! ## Soundness -/

theorem box_bounds {U : UVT} {w : CapWitness} (h : boxOk U w = true) {a b E : ℝ}
    (hin : InUVT U a b E) :
    (w.alo : ℝ) ≤ a ∧ a ≤ (w.ahi : ℝ) ∧ (w.blo : ℝ) ≤ b ∧ b ≤ (w.bhi : ℝ) := by
  unfold boxOk at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hal, hah⟩, hbl⟩, hbh⟩ := h
  obtain ⟨h1, h2, h3, h4, h5, h6, _, _⟩ := hin
  have hal' := pow2LowerOK_sound hal
  have hbl' := pow2UpperOK_sound hbl
  push_cast at hbl'
  refine ⟨hal'.trans h1, ?_, ?_, ?_⟩
  · rcases hah with hah | hah
    · exact h2.trans (pow2UpperOK_sound hah)
    · have hq : ((1 / 10 : ℚ) : ℝ) ≤ (w.ahi : ℝ) := Rat.cast_le.mpr hah
      have h10 : ((1 / 10 : ℚ) : ℝ) = 1 / 10 := by norm_num
      rw [h10] at hq
      linarith
  · linarith
  · rcases hbh with hbh | hbh
    · have := pow2LowerOK_sound hbh
      push_cast at this
      linarith
    · have : (1 : ℝ) - (w.alo : ℝ) ≤ (w.bhi : ℝ) := by exact_mod_cast hbh
      linarith [hal'.trans h1]

theorem logs_of_mem {lo hi : ℚ} (hlo : FP.ptOk lo = true) (hhi : FP.ptOk hi = true) {x : ℝ}
    (hx1 : (lo : ℝ) ≤ x) (hx2 : x ≤ (hi : ℝ)) :
    ((FP.lLo lo : ℚ) : ℝ) ≤ Real.log x ∧ Real.log x ≤ ((FP.lHi hi : ℚ) : ℝ) ∧
      ((FP.l1Lo hi : ℚ) : ℝ) ≤ Real.log (1 - x) ∧ Real.log (1 - x) ≤ ((FP.l1Hi lo : ℚ) : ℝ) := by
  obtain ⟨a1, _, _, a4⟩ := FP.ptOk_sound hlo
  obtain ⟨_, b2, b3, _⟩ := FP.ptOk_sound hhi
  have hl := FP.ptOk_pos hlo
  have hh := FP.ptOk_pos hhi
  have hl0 : (0 : ℝ) < (lo : ℝ) := by exact_mod_cast hl.1
  have hh1 : (hi : ℝ) < 1 := by exact_mod_cast hh.2
  have hx0 : 0 < x := lt_of_lt_of_le hl0 hx1
  have hx1' : x < 1 := lt_of_le_of_lt hx2 hh1
  refine ⟨a1.trans (Real.log_le_log hl0 hx1), (Real.log_le_log hx0 hx2).trans b2,
    b3.trans (Real.log_le_log (by linarith) (by linarith)),
    (Real.log_le_log (by linarith) (by linarith)).trans a4⟩

/-! ### Cast identities for the checker quantities (each its own small declaration) -/

theorem cast_m11lo (w : CapWitness) : ((w.m11lo : ℚ) : ℝ) = -((FP.lHi w.ahi : ℚ) : ℝ) := by
  simp only [CapWitness.m11lo, Rat.cast_neg]
theorem cast_m11hi (w : CapWitness) : ((w.m11hi : ℚ) : ℝ) = -((FP.lLo w.alo : ℚ) : ℝ) := by
  simp only [CapWitness.m11hi, Rat.cast_neg]
theorem cast_m12lo (w : CapWitness) : ((w.m12lo : ℚ) : ℝ) = -((FP.lHi w.bhi : ℚ) : ℝ) := by
  simp only [CapWitness.m12lo, Rat.cast_neg]
theorem cast_m12hi (w : CapWitness) : ((w.m12hi : ℚ) : ℝ) = -((FP.lLo w.blo : ℚ) : ℝ) := by
  simp only [CapWitness.m12hi, Rat.cast_neg]
theorem cast_m21lo (w : CapWitness) : ((w.m21lo : ℚ) : ℝ) = -((FP.l1Hi w.alo : ℚ) : ℝ) := by
  simp only [CapWitness.m21lo, Rat.cast_neg]
theorem cast_m21hi (w : CapWitness) : ((w.m21hi : ℚ) : ℝ) = -((FP.l1Lo w.ahi : ℚ) : ℝ) := by
  simp only [CapWitness.m21hi, Rat.cast_neg]
theorem cast_m22lo (w : CapWitness) : ((w.m22lo : ℚ) : ℝ) = -((FP.l1Hi w.blo : ℚ) : ℝ) := by
  simp only [CapWitness.m22lo, Rat.cast_neg]
theorem cast_m22hi (w : CapWitness) : ((w.m22hi : ℚ) : ℝ) = -((FP.l1Lo w.bhi : ℚ) : ℝ) := by
  simp only [CapWitness.m22hi, Rat.cast_neg]

theorem cast_r1lo (w : CapWitness) :
    ((w.r1lo : ℚ) : ℝ) = 1 / (2 * (w.ahi : ℝ) * (w.bhi : ℝ)) := by
  simp only [CapWitness.r1lo, Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat]
theorem cast_r1hi (w : CapWitness) :
    ((w.r1hi : ℚ) : ℝ) = 1 / (2 * (w.alo : ℝ) * (w.blo : ℝ)) := by
  simp only [CapWitness.r1hi, Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat]
theorem cast_r2lo (w : CapWitness) :
    ((w.r2lo : ℚ) : ℝ) = 1 / (2 * (1 - (w.alo : ℝ)) * (1 - (w.blo : ℝ))) := by
  simp only [CapWitness.r2lo, Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat,
    Rat.cast_sub]
theorem cast_r2hi (w : CapWitness) :
    ((w.r2hi : ℚ) : ℝ) = 1 / (2 * (1 - (w.ahi : ℝ)) * (1 - (w.bhi : ℝ))) := by
  simp only [CapWitness.r2hi, Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat,
    Rat.cast_sub]

theorem cast_detlo (w : CapWitness) : ((w.detlo : ℚ) : ℝ) =
    ((w.m11lo : ℚ) : ℝ) * ((w.m22lo : ℚ) : ℝ) - ((w.m12hi : ℚ) : ℝ) * ((w.m21hi : ℚ) : ℝ) := by
  simp only [CapWitness.detlo, Rat.cast_sub, Rat.cast_mul]
theorem cast_dethi (w : CapWitness) : ((w.dethi : ℚ) : ℝ) =
    ((w.m11hi : ℚ) : ℝ) * ((w.m22hi : ℚ) : ℝ) - ((w.m12lo : ℚ) : ℝ) * ((w.m21lo : ℚ) : ℝ) := by
  simp only [CapWitness.dethi, Rat.cast_sub, Rat.cast_mul]
theorem cast_nAlo (w : CapWitness) : ((w.nAlo : ℚ) : ℝ) =
    ((w.r1lo : ℚ) : ℝ) * ((w.m22lo : ℚ) : ℝ) - ((w.r2hi : ℚ) : ℝ) * ((w.m12hi : ℚ) : ℝ) := by
  simp only [CapWitness.nAlo, Rat.cast_sub, Rat.cast_mul]
theorem cast_nDlo (w : CapWitness) : ((w.nDlo : ℚ) : ℝ) =
    ((w.m11lo : ℚ) : ℝ) * ((w.r2lo : ℚ) : ℝ) - ((w.m21hi : ℚ) : ℝ) * ((w.r1hi : ℚ) : ℝ) := by
  simp only [CapWitness.nDlo, Rat.cast_sub, Rat.cast_mul]
theorem cast_dlo (w : CapWitness) : ((w.dlo : ℚ) : ℝ) = (w.blo : ℝ) - (w.ahi : ℝ) := by
  simp only [CapWitness.dlo, Rat.cast_sub]
theorem cast_klo (w : CapWitness) : ((w.klo : ℚ) : ℝ) = ((w.dlo : ℚ) : ℝ) ^ 2 *
    min (((w.nAlo : ℚ) : ℝ) / ((w.dethi : ℚ) : ℝ)) (((w.nDlo : ℚ) : ℝ) / ((w.dethi : ℚ) : ℝ)) := by
  simp only [CapWitness.klo, Rat.cast_mul, Rat.cast_pow, Rat.cast_min, Rat.cast_div]

/-! ### Pure real interval algebra for the coefficients -/

theorem coeff_real {a b M11 M12 M21 M22 R1 R2 x11 y11 x12 y12 x21 y21 x22 y22 u1 v1 u2 v2 dl : ℝ}
    (m11a : x11 ≤ M11) (m11b : M11 ≤ y11) (m12a : x12 ≤ M12) (m12b : M12 ≤ y12)
    (m21a : x21 ≤ M21) (m21b : M21 ≤ y21) (m22a : x22 ≤ M22) (m22b : M22 ≤ y22)
    (r1a : u1 ≤ R1) (r1b : R1 ≤ v1) (r2a : u2 ≤ R2) (r2b : R2 ≤ v2)
    (q1 : 0 ≤ x11) (q2 : 0 ≤ x12) (q3 : 0 ≤ x21) (q4 : 0 ≤ x22) (hu1 : 0 ≤ u1) (hu2 : 0 ≤ u2)
    (hd1 : 0 < x11 * x22 - y12 * y21) (hd2 : 0 < u1 * x22 - v2 * y12)
    (hd3 : 0 < x11 * u2 - y21 * v1) (hdl : dl ≤ b - a) (hdl0 : 0 < dl) :
    0 < M11 * M22 - M12 * M21 ∧
    dl ^ 2 * ((u1 * x22 - v2 * y12) / (y11 * y22 - x12 * x21)) ≤
      (b - a) ^ 2 * (R1 * M22 - R2 * M12) / (M11 * M22 - M12 * M21) ∧
    dl ^ 2 * ((x11 * u2 - y21 * v1) / (y11 * y22 - x12 * x21)) ≤
      (b - a) ^ 2 * (M11 * R2 - M21 * R1) / (M11 * M22 - M12 * M21) ∧
    0 < dl ^ 2 * ((u1 * x22 - v2 * y12) / (y11 * y22 - x12 * x21)) ∧
    0 < dl ^ 2 * ((x11 * u2 - y21 * v1) / (y11 * y22 - x12 * x21)) := by
  have M11n : 0 ≤ M11 := q1.trans m11a
  have M12n : 0 ≤ M12 := q2.trans m12a
  have M21n : 0 ≤ M21 := q3.trans m21a
  have M22n : 0 ≤ M22 := q4.trans m22a
  have R1n : 0 ≤ R1 := hu1.trans r1a
  have R2n : 0 ≤ R2 := hu2.trans r2a
  have e1 : x11 * x22 ≤ M11 * M22 := mul_le_mul m11a m22a q4 M11n
  have e2 : M12 * M21 ≤ y12 * y21 := mul_le_mul m12b m21b M21n (M12n.trans m12b)
  have e3 : M11 * M22 ≤ y11 * y22 := mul_le_mul m11b m22b M22n (M11n.trans m11b)
  have e4 : x12 * x21 ≤ M12 * M21 := mul_le_mul m12a m21a q3 M12n
  have f1 : u1 * x22 ≤ R1 * M22 := mul_le_mul r1a m22a q4 R1n
  have f2 : R2 * M12 ≤ v2 * y12 := mul_le_mul r2b m12b M12n (R2n.trans r2b)
  have f3 : x11 * u2 ≤ M11 * R2 := mul_le_mul m11a r2a hu2 M11n
  have f4 : M21 * R1 ≤ y21 * v1 := mul_le_mul m21b r1b R1n (M21n.trans m21b)
  have DETpos : 0 < M11 * M22 - M12 * M21 := by linarith
  have det_le : M11 * M22 - M12 * M21 ≤ y11 * y22 - x12 * x21 := by linarith
  have nA_le : u1 * x22 - v2 * y12 ≤ R1 * M22 - R2 * M12 := by linarith
  have nD_le : x11 * u2 - y21 * v1 ≤ M11 * R2 - M21 * R1 := by linarith
  have hdhi : 0 < y11 * y22 - x12 * x21 := lt_of_lt_of_le DETpos det_le
  refine ⟨DETpos, sq_quot_lower hdl hdl0.le nA_le hd2 DETpos det_le,
    sq_quot_lower hdl hdl0.le nD_le hd3 DETpos det_le,
    mul_pos (pow_pos hdl0 2) (div_pos hd2 hdhi), mul_pos (pow_pos hdl0 2) (div_pos hd3 hdhi)⟩

/-! ### Rational enclosures → real enclosures on the box -/

theorem m_bounds {w : CapWitness}
    (hpa : FP.ptOk w.alo = true) (hpb : FP.ptOk w.ahi = true)
    (hpc : FP.ptOk w.blo = true) (hpd : FP.ptOk w.bhi = true)
    {a b : ℝ} (hal : (w.alo : ℝ) ≤ a) (hah : a ≤ (w.ahi : ℝ))
    (hbl : (w.blo : ℝ) ≤ b) (hbh : b ≤ (w.bhi : ℝ)) :
    ((w.m11lo : ℚ) : ℝ) ≤ -Real.log a ∧ -Real.log a ≤ ((w.m11hi : ℚ) : ℝ) ∧
    ((w.m12lo : ℚ) : ℝ) ≤ -Real.log b ∧ -Real.log b ≤ ((w.m12hi : ℚ) : ℝ) ∧
    ((w.m21lo : ℚ) : ℝ) ≤ -Real.log (1 - a) ∧ -Real.log (1 - a) ≤ ((w.m21hi : ℚ) : ℝ) ∧
    ((w.m22lo : ℚ) : ℝ) ≤ -Real.log (1 - b) ∧ -Real.log (1 - b) ≤ ((w.m22hi : ℚ) : ℝ) := by
  obtain ⟨la1, la2, la3, la4⟩ := logs_of_mem hpa hpb hal hah
  obtain ⟨lb1, lb2, lb3, lb4⟩ := logs_of_mem hpc hpd hbl hbh
  rw [cast_m11lo, cast_m11hi, cast_m12lo, cast_m12hi, cast_m21lo, cast_m21hi, cast_m22lo,
    cast_m22hi]
  exact ⟨neg_le_neg la2, neg_le_neg la1, neg_le_neg lb2, neg_le_neg lb1,
    neg_le_neg la4, neg_le_neg la3, neg_le_neg lb4, neg_le_neg lb3⟩

theorem r_bounds {w : CapWitness} (s1 : 0 < w.alo) (s3 : w.ahi < w.blo) (s6 : w.bhi < 1)
    {a b : ℝ} (hal : (w.alo : ℝ) ≤ a) (hah : a ≤ (w.ahi : ℝ))
    (hbl : (w.blo : ℝ) ≤ b) (hbh : b ≤ (w.bhi : ℝ)) (hab : a < b) :
    ((w.r1lo : ℚ) : ℝ) ≤ 1 / (2 * a * b) ∧ 1 / (2 * a * b) ≤ ((w.r1hi : ℚ) : ℝ) ∧
    ((w.r2lo : ℚ) : ℝ) ≤ 1 / (2 * (1 - a) * (1 - b)) ∧
    1 / (2 * (1 - a) * (1 - b)) ≤ ((w.r2hi : ℚ) : ℝ) ∧
    (0 : ℝ) ≤ ((w.r1lo : ℚ) : ℝ) ∧ (0 : ℝ) ≤ ((w.r2lo : ℚ) : ℝ) := by
  have ralo : (0 : ℝ) < (w.alo : ℝ) := by exact_mod_cast s1
  have rbhi : (w.bhi : ℝ) < 1 := by exact_mod_cast s6
  have rab : (w.ahi : ℝ) < (w.blo : ℝ) := by exact_mod_cast s3
  have ha0 : 0 < a := lt_of_lt_of_le ralo hal
  have hb0 : 0 < b := lt_trans ha0 hab
  have hb1 : b < 1 := lt_of_le_of_lt hbh rbhi
  have ha1 : 0 < 1 - a := by linarith
  have hb1' : 0 < 1 - b := by linarith
  have hahi0 : (0 : ℝ) ≤ (w.ahi : ℝ) := ha0.le.trans hah
  have hblo0 : (0 : ℝ) ≤ (w.blo : ℝ) := by linarith
  have hbhi0 : (0 : ℝ) < (w.bhi : ℝ) := lt_of_lt_of_le hb0 hbh
  have p1 : a * b ≤ (w.ahi : ℝ) * (w.bhi : ℝ) := mul_le_mul hah hbh hb0.le hahi0
  have p2 : (w.alo : ℝ) * (w.blo : ℝ) ≤ a * b := mul_le_mul hal hbl hblo0 ha0.le
  have p3 : (1 - a) * (1 - b) ≤ (1 - (w.alo : ℝ)) * (1 - (w.blo : ℝ)) :=
    mul_le_mul (by linarith) (by linarith) hb1'.le (by linarith)
  have p4 : (1 - (w.ahi : ℝ)) * (1 - (w.bhi : ℝ)) ≤ (1 - a) * (1 - b) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) ha1.le
  have g1 : (0 : ℝ) < 2 * a * b := by positivity
  have g2 : (0 : ℝ) < 2 * (w.alo : ℝ) * (w.blo : ℝ) := by
    have : (0 : ℝ) < (w.blo : ℝ) := by linarith
    positivity
  have g3 : (0 : ℝ) < 2 * (1 - a) * (1 - b) := by positivity
  have g4 : (0 : ℝ) < 2 * (1 - (w.ahi : ℝ)) * (1 - (w.bhi : ℝ)) := by
    have : (0 : ℝ) < 1 - (w.ahi : ℝ) := by linarith
    have : (0 : ℝ) < 1 - (w.bhi : ℝ) := by linarith
    positivity
  rw [cast_r1lo, cast_r1hi, cast_r2lo, cast_r2hi]
  refine ⟨one_div_le_one_div_of_le g1 ?_, one_div_le_one_div_of_le g2 ?_,
    one_div_le_one_div_of_le g3 ?_, one_div_le_one_div_of_le g4 ?_, ?_, ?_⟩
  · rw [mul_assoc, mul_assoc]; linarith
  · rw [mul_assoc, mul_assoc]; linarith
  · rw [mul_assoc, mul_assoc]; linarith
  · rw [mul_assoc, mul_assoc]; linarith
  · have : (0 : ℝ) < 2 * (w.ahi : ℝ) * (w.bhi : ℝ) := by
      have : (0 : ℝ) < (w.ahi : ℝ) := lt_of_lt_of_le ha0 hah
      positivity
    positivity
  · have : (0 : ℝ) < 1 - (w.alo : ℝ) := by linarith
    have : (0 : ℝ) < 1 - (w.blo : ℝ) := by linarith
    positivity

/-- Interval bounds of both cap-plane coefficients over the box. -/
theorem coeff_bounds {w : CapWitness}
    (hpa : FP.ptOk w.alo = true) (hpb : FP.ptOk w.ahi = true)
    (hpc : FP.ptOk w.blo = true) (hpd : FP.ptOk w.bhi = true)
    (s1 : 0 < w.alo) (s3 : w.ahi < w.blo) (s6 : w.bhi < 1)
    (p1 : 0 ≤ w.m11lo) (p2 : 0 ≤ w.m12lo) (p3 : 0 ≤ w.m21lo) (p4 : 0 ≤ w.m22lo)
    (d1 : 0 < w.detlo) (d2 : 0 < w.nAlo) (d3 : 0 < w.nDlo)
    {a b : ℝ} (hal : (w.alo : ℝ) ≤ a) (hah : a ≤ (w.ahi : ℝ))
    (hbl : (w.blo : ℝ) ≤ b) (hbh : b ≤ (w.bhi : ℝ)) :
    0 < capDet a b ∧ (w.klo : ℝ) ≤ capA a b ∧ (w.klo : ℝ) ≤ capB a b ∧
      0 < capA a b ∧ 0 < capB a b := by
  have ralo : (0 : ℝ) < (w.alo : ℝ) := by exact_mod_cast s1
  have rab : (w.ahi : ℝ) < (w.blo : ℝ) := by exact_mod_cast s3
  have rbhi : (w.bhi : ℝ) < 1 := by exact_mod_cast s6
  have ha0 : 0 < a := lt_of_lt_of_le ralo hal
  have hab : a < b := by linarith
  have hb1 : b < 1 := lt_of_le_of_lt hbh rbhi
  obtain ⟨m11a, m11b, m12a, m12b, m21a, m21b, m22a, m22b⟩ := m_bounds hpa hpb hpc hpd hal hah hbl hbh
  obtain ⟨r1a, r1b, r2a, r2b, hu1, hu2⟩ := r_bounds s1 s3 s6 hal hah hbl hbh hab
  have q1 : (0 : ℝ) ≤ ((w.m11lo : ℚ) : ℝ) := by exact_mod_cast p1
  have q2 : (0 : ℝ) ≤ ((w.m12lo : ℚ) : ℝ) := by exact_mod_cast p2
  have q3 : (0 : ℝ) ≤ ((w.m21lo : ℚ) : ℝ) := by exact_mod_cast p3
  have q4 : (0 : ℝ) ≤ ((w.m22lo : ℚ) : ℝ) := by exact_mod_cast p4
  have hd1 : (0 : ℝ) < ((w.m11lo : ℚ) : ℝ) * ((w.m22lo : ℚ) : ℝ) -
      ((w.m12hi : ℚ) : ℝ) * ((w.m21hi : ℚ) : ℝ) := by
    rw [← cast_detlo]; exact_mod_cast d1
  have hd2 : (0 : ℝ) < ((w.r1lo : ℚ) : ℝ) * ((w.m22lo : ℚ) : ℝ) -
      ((w.r2hi : ℚ) : ℝ) * ((w.m12hi : ℚ) : ℝ) := by
    rw [← cast_nAlo]; exact_mod_cast d2
  have hd3 : (0 : ℝ) < ((w.m11lo : ℚ) : ℝ) * ((w.r2lo : ℚ) : ℝ) -
      ((w.m21hi : ℚ) : ℝ) * ((w.r1hi : ℚ) : ℝ) := by
    rw [← cast_nDlo]; exact_mod_cast d3
  have hdl : ((w.dlo : ℚ) : ℝ) ≤ b - a := by rw [cast_dlo]; linarith
  have hdl0 : (0 : ℝ) < ((w.dlo : ℚ) : ℝ) := by rw [cast_dlo]; linarith
  obtain ⟨hdet, gA, gB, pA, pB⟩ := coeff_real m11a m11b m12a m12b m21a m21b m22a m22b
    r1a r1b r2a r2b q1 q2 q3 q4 hu1 hu2 hd1 hd2 hd3 hdl hdl0
  rw [← cast_nAlo, ← cast_dethi] at gA pA
  rw [← cast_nDlo, ← cast_dethi] at gB pB
  have hdet_eq := capDet_eq a b
  have hA_eq := capA_eq ha0 hab hb1
  have hB_eq := capB_eq ha0 hab hb1
  rw [← hdet_eq] at hdet gA gB
  have hsq0 : (0 : ℝ) ≤ ((w.dlo : ℚ) : ℝ) ^ 2 := sq_nonneg _
  have kA : ((w.klo : ℚ) : ℝ) ≤ ((w.dlo : ℚ) : ℝ) ^ 2 * (((w.nAlo : ℚ) : ℝ) / ((w.dethi : ℚ) : ℝ)) := by
    rw [cast_klo]; exact mul_le_mul_of_nonneg_left (min_le_left _ _) hsq0
  have kB : ((w.klo : ℚ) : ℝ) ≤ ((w.dlo : ℚ) : ℝ) ^ 2 * (((w.nDlo : ℚ) : ℝ) / ((w.dethi : ℚ) : ℝ)) := by
    rw [cast_klo]; exact mul_le_mul_of_nonneg_left (min_le_right _ _) hsq0
  refine ⟨hdet, ?_, ?_, ?_, ?_⟩
  · rw [hA_eq]; exact kA.trans gA
  · rw [hB_eq]; exact kB.trans gB
  · rw [hA_eq]; exact lt_of_lt_of_le pA gA
  · rw [hB_eq]; exact lt_of_lt_of_le pB gB

/-- Upper bound of the information `H((a+b)/2) - E` on the leaf image. -/
theorem info_bound {U : UVT} {w : CapWitness}
    (hpa : FP.ptOk w.alo = true) (hpd : FP.ptOk w.bhi = true)
    (hpm : (decide (1 / 2 ≤ w.mhi) || FP.ptOk w.mhi) = true)
    (s1 : 0 < w.alo) (s4 : 1 / 2 ≤ w.blo) (s6 : w.bhi < 1) (s7 : w.ahi ≤ 1 / 2)
    (s8 : 0 ≤ U.t0)
    {a b E : ℝ} (hin : InUVT U a b E) (hal : (w.alo : ℝ) ≤ a) (hah : a ≤ (w.ahi : ℝ))
    (hbl : (w.blo : ℝ) ≤ b) (hbh : b ≤ (w.bhi : ℝ)) :
    H ((a + b) / 2) - E ≤ ((w.Ihi U.t0 : ℚ) : ℝ) := by
  obtain ⟨_, _, _, _, _, hsum, hE, _⟩ := hin
  have ralo : (0 : ℝ) < (w.alo : ℝ) := by exact_mod_cast s1
  have rblo : (1 / 2 : ℝ) ≤ (w.blo : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr s4
    push_cast at h
    exact h
  have rbhi : (w.bhi : ℝ) < 1 := by exact_mod_cast s6
  have rahi : (w.ahi : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr s7
    push_cast at h
    exact h
  have rt0 : (0 : ℝ) ≤ (U.t0 : ℝ) := by exact_mod_cast s8
  -- lower bound of C0 = (H a + H b)/2
  have hHa : ((FP.Hlo w.alo : ℚ) : ℝ) ≤ H a :=
    (FP.H_bounds hpa).1.trans (CKLaneD.H_mono_left ralo.le hal (hah.trans rahi))
  have hHb : ((FP.Hlo w.bhi : ℚ) : ℝ) ≤ H b :=
    (FP.H_bounds hpd).1.trans (CKLaneD.H_anti_right (rblo.trans hbl) hbh rbhi.le)
  have cC0 : ((w.C0lo : ℚ) : ℝ) = (((FP.Hlo w.alo : ℚ) : ℝ) + ((FP.Hlo w.bhi : ℚ) : ℝ)) / 2 := by
    simp only [CapWitness.C0lo]; push_cast; ring
  have hC0 : ((w.C0lo : ℚ) : ℝ) ≤ (H a + H b) / 2 := by rw [cC0]; linarith
  have cE : ((w.ELo U.t0 : ℚ) : ℝ) =
      ((EMIN : ℚ) : ℝ) + (U.t0 : ℝ) * (((w.C0lo : ℚ) : ℝ) - ((EMIN : ℚ) : ℝ)) := by
    simp only [CapWitness.ELo]; push_cast; ring
  have hEl : ((w.ELo U.t0 : ℚ) : ℝ) ≤ E := by
    rw [cE]
    have := mul_le_mul_of_nonneg_left (by linarith : ((w.C0lo : ℚ) : ℝ) - ((EMIN : ℚ) : ℝ) ≤
      (H a + H b) / 2 - ((EMIN : ℚ) : ℝ)) rt0
    linarith
  -- upper bound of H((a+b)/2)
  have hm0 : 0 ≤ (a + b) / 2 := by linarith
  have hm12 : (a + b) / 2 ≤ 1 / 2 := by linarith
  have hmhi : (a + b) / 2 ≤ ((w.mhi : ℚ) : ℝ) := by
    simp only [CapWitness.mhi]; push_cast; linarith
  have hHm : H ((a + b) / 2) ≤ ((w.HmHi : ℚ) : ℝ) := by
    by_cases hc : w.mhi < 1 / 2
    · have hpt : FP.ptOk w.mhi = true := by
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hpm
        rcases hpm with h | h
        · exact absurd h (not_le.mpr hc)
        · exact h
      have hmr : ((w.mhi : ℚ) : ℝ) ≤ 1 / 2 := by
        have h := (Rat.cast_le (K := ℝ)).mpr hc.le
        push_cast at h
        exact h
      have hv : ((w.HmHi : ℚ) : ℝ) = ((FP.Hhi w.mhi : ℚ) : ℝ) := by
        simp only [CapWitness.HmHi, if_pos hc]
      rw [hv]
      exact (CKLaneD.H_mono_left hm0 hmhi hmr).trans (FP.H_bounds hpt).2
    · have hv : ((w.HmHi : ℚ) : ℝ) = 1 := by
        simp only [CapWitness.HmHi, if_neg hc, Rat.cast_one]
      rw [hv]
      exact H_le_one _
  have cI : ((w.Ihi U.t0 : ℚ) : ℝ) = ((w.HmHi : ℚ) : ℝ) - ((w.ELo U.t0 : ℚ) : ℝ) := by
    simp only [CapWitness.Ihi]; push_cast; ring
  rw [cI]
  linarith

/-- Soundness of the per-leaf checker: the psi-candidate Bellman inequality on the exact clipped
physical image of the archived leaf `U`. -/
theorem capCheck_sound {U : UVT} {w : CapWitness} (h : capCheck U w = true) : SemUVT U := by
  unfold capCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hbox, hsane⟩, hpa⟩, hpb⟩, hpc⟩, hpd⟩, hpm⟩, hanch⟩, hmpos⟩, hdet⟩, hslope⟩ := h
  obtain ⟨s1, _, s3, s4, _, s6, s7, s8⟩ := of_decide_eq_true hsane
  obtain ⟨p1, p2, p3, p4⟩ := of_decide_eq_true hmpos
  obtain ⟨d1, d2, d3⟩ := of_decide_eq_true hdet
  have hsl := of_decide_eq_true hslope
  intro k μ hin
  obtain ⟨hal, hah, hbl, hbh⟩ := box_bounds hbox hin
  obtain ⟨hdet0, hkA, hkB, hA, hB⟩ :=
    coeff_bounds hpa hpb hpc hpd s1 s3 s6 p1 p2 p3 p4 d1 d2 d3 hal hah hbl hbh
  have ralo : (0 : ℝ) < (w.alo : ℝ) := by exact_mod_cast s1
  have rab : (w.ahi : ℝ) < (w.blo : ℝ) := by exact_mod_cast s3
  have rbhi : (w.bhi : ℝ) < 1 := by exact_mod_cast s6
  have ha0 : 0 < μ.a := lt_of_lt_of_le ralo hal
  have hab : μ.a < μ.b := by linarith
  have hb1 : μ.b < 1 := lt_of_le_of_lt hbh rbhi
  obtain ⟨h1, h0⟩ := cap_contact ha0 hab hb1 hdet0.ne'
  have hI := info_bound hpa hpd hpm s1 s4 s6 s7 s8 hin hal hah hbl hbh
  have hP1 : ∀ x : ℝ, 0 ≤ x → x ≤ ((w.Ihi U.t0 : ℚ) : ℝ) →
      Scalar.P1 x ≤ ((FP.P1up w.v : ℚ) : ℝ) := fun x hx hxy => FP.anchorOk_sound hanch hx hxy
  have hU : ((FP.P1up w.v : ℚ) : ℝ) - 4 ≤ 2 * ((w.klo : ℚ) : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hsl
    push_cast at h
    exact h
  exact cap_slope_bound μ hA hB hab h1 h0 hkA hkB hI hP1 hU

/-- Owner form: on the leaf image, `μ.gap ≤ μ.cost` whenever psi is (weakly) active at the parent. -/
theorem capCheck_gap_le_cost {U : UVT} {w : CapWitness} (h : capCheck U w = true)
    {k : ℕ} (μ : InteriorLaw (Fin k)) (hin : InUVT U μ.a μ.b μ.meanEntropy)
    (hact : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) : μ.gap ≤ μ.cost :=
  (hybrid_gap_le_psi hact).trans (capCheck_sound h k μ hin)

/-- Batch soundness for a shard of `(path, witness)` pairs. -/
theorem capCheckAll_sound (L : List (List ℕ × CapWitness))
    (h : (L.all fun x => capCheck (uvtBox x.1) x.2) = true) :
    ∀ x ∈ L, SemUVT (uvtBox x.1) := by
  intro x hx
  rw [List.all_eq_true] at h
  exact capCheck_sound (h x hx)

end CKLaneM09

end


