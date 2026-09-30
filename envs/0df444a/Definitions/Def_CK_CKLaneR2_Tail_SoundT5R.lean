-- Prove2me | Definitions.Def_CK_CKLaneR2_Tail_SoundT5R
-- name    : CK_CKLaneR2_Tail_SoundT5R
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:41:29.981852+00:00
-- url     : https://prove2.me/theorems/6dd2ac68-d7cb-45b4-acf6-a7f71152da6a
-- title:
--   Courtade–Kumar proof module `CKLaneR2.Tail.SoundT5R` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneR2.Tail.SoundT5R` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneR2.Tail.SoundT5R` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneR2.Tail.SoundT5R (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneR2/Tail/SoundT5R.lean)

import Definitions.Def_CK_CKLaneR2_Tail_SoundT5TM

-- ===== source module CKLaneR2.Tail.SoundT5R =====
section

/-!
# Lane R2 — tail checker soundness, part 5: mode R of the fifth block (TM containment and exact identity)
-/

namespace CKLaneR2.Tail

open CKLaneR2.TM3 CKLaneR2.Cell GeneralCK

/-- Raw value of `t5R` (mirror of the TM operations). -/
noncomputable def rawT5R (t u s3 lam cq gg ρ : ℝ) : ℝ :=
  let X := (lam * g1 (u * ρ) - lam * Real.log ρ) + 1
  let Yc := (lam * -Real.log (1 - u * ρ) - lam * Real.log ρ) + 1
  let om2v := ((-2 : ℤ) : ℝ) * (u * ρ) + 1
  let Yd := Yc - lam * (om2v * om2v)
  let LG1 := lam * gg + 1
  let omega := (1 - lam * cq) * LG1⁻¹
  let Yt := ((X * X) * Yd) * (((1 - u * ρ)⁻¹ * (1 - u * ρ)⁻¹) * ((Yc⁻¹ * Yc⁻¹) * Yc⁻¹))
  let q := ((2 : ℤ) : ℝ) * (t * u) + s3 * omega
  let A1 := (((q * q) * ρ) * (X * Yt)) * (1 / Real.log 2 * LG1⁻¹)
  let A2 := ((s3 * om2v) * (X * lam)) * (1 / Real.log 2 * (((1 - u)⁻¹ * (1 - u * ρ)⁻¹) * (Yc⁻¹ * LG1⁻¹)))
  show ℝ from -((A1 + A2) / 2)

theorem ONEi_real : ((ONEi : ℤ) : ℝ) = (one : ℝ) := by unfold ONEi; rw [Int.cast_natCast]

/-- The ok flag of `t5R` forces its residual certificate flag. -/
theorem t5R_okc (F : Front) (s3 : TM) (Pc : Poly) (r : ℕ) (h : (t5R F s3 Pc r).ok = true) :
    (decide (0 < (TM.addc ⟨Pc, 0, true⟩ (-(r : Int))).lower)
      && (t5Resid F s3 (TM.addc ⟨Pc, 0, true⟩ (-(r : Int)))).R.ok
      && (t5Resid F s3 (TM.addc ⟨Pc, 0, true⟩ (r : Int))).R.ok
      && decide ((t5Resid F s3 (TM.addc ⟨Pc, 0, true⟩ (-(r : Int)))).R.upper < 0)
      && decide (0 < (t5Resid F s3 (TM.addc ⟨Pc, 0, true⟩ (r : Int))).R.lower)
      && (t5Resid F s3 (TM.addc ⟨Pc, 0, true⟩ (r : Int))).v.ok
      && decide ((t5Resid F s3 (TM.addc ⟨Pc, 0, true⟩ (r : Int))).v.upper < ONEi)) = true := by
  simp only [t5R, TM.neg, mulc, TM.mulc, TM.add, Bool.and_eq_true] at h
  have hA1 := h.1
  have h1 := mul_ok_left hA1
  have h2 := mul_ok_left h1
  exact mul_ok_right h2

theorem t5R_contains (F : Front) {s3 : TM} (Pc : Poly) (r : ℕ)
    {s3f tf uf lamf ggf cqf ρf : ℝ → ℝ → ℝ → ℝ}
    (hs3 : Contains one s3 s3f) (hT : Contains one F.T tf) (hU : Contains one F.U uf)
    (hLam : Contains one F.Lam lamf) (hG1 : Contains one F.G1 ggf) (hCq : Contains one F.Cq cqf)
    (homU : Contains one F.omU (fun x y z => 1 - uf x y z))
    (hunn : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → 0 ≤ uf x y z)
    (hρ : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 →
      0 < evalP 0 Pc x y z / one + ((-(r : Int) : Int) : ℝ) / one →
      uf x y z * (evalP 0 Pc x y z / one + (((r : Int) : Int) : ℝ) / one) < 1 →
      residR (s3f x y z) (uf x y z) (lamf x y z) (ggf x y z) (evalP 0 Pc x y z / one + ((-(r : Int) : Int) : ℝ) / one) < 0 →
      0 < residR (s3f x y z) (uf x y z) (lamf x y z) (ggf x y z) (evalP 0 Pc x y z / one + (((r : Int) : Int) : ℝ) / one) →
      evalP 0 Pc x y z / one + ((-(r : Int) : Int) : ℝ) / one ≤ ρf x y z ∧
        ρf x y z ≤ evalP 0 Pc x y z / one + (((r : Int) : Int) : ℝ) / one) :
    Contains one (t5R F s3 Pc r)
      (fun x y z => rawT5R (tf x y z) (uf x y z) (s3f x y z) (lamf x y z) (cqf x y z) (ggf x y z) (ρf x y z)) := by
  intro hok
  have hokc := t5R_okc F s3 Pc r hok
  set rm := TM.addc ⟨Pc, 0, true⟩ (-(r : Int)) with hrmdef
  set rp := TM.addc ⟨Pc, 0, true⟩ (r : Int) with hrpdef
  set ρm := fun x y z => evalP 0 Pc x y z / one + ((-(r : Int) : Int) : ℝ) / one with hρm
  set ρp := fun x y z => evalP 0 Pc x y z / one + (((r : Int) : Int) : ℝ) / one with hρp
  have hrm : Contains one rm ρm := Contains.addc (C_poly Pc) _
  have hrp : Contains one rp ρp := Contains.addc (C_poly Pc) _
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hokc
  obtain ⟨⟨⟨⟨⟨⟨hlow, hRmok⟩, hRpok⟩, hRmup⟩, hRplo⟩, hvok⟩, hvup⟩ := hokc
  have hone' := CKLaneR2.Cell.hone'
  have hrm0 : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → 0 < ρm x y z := fun x y z hx hy hz => by
    have := Contains.lower_le hone hrm rfl x y z hx hy hz
    have h0 : (0 : ℝ) < (rm.lower : ℝ) / one := div_pos (by exact_mod_cast hlow) hone'
    linarith
  have hmp : ∀ x y z : ℝ, ρm x y z ≤ ρp x y z := fun x y z => by
    simp only [hρm, hρp]
    have : ((-(r : Int) : Int) : ℝ) / one ≤ (((r : Int) : Int) : ℝ) / one := by
      apply div_le_div_of_nonneg_right _ hone'.le; push_cast; linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
    linarith
  have hnm : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → 0 ≤ uf x y z * ρm x y z := fun x y z hx hy hz =>
    mul_nonneg (hunn x y z hx hy hz) (hrm0 x y z hx hy hz).le
  have hnp : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → 0 ≤ uf x y z * ρp x y z := fun x y z hx hy hz =>
    mul_nonneg (hunn x y z hx hy hz) ((hrm0 x y z hx hy hz).le.trans (hmp x y z))
  obtain ⟨hRm, hetam, hcvm, hvm⟩ := t5Resid_contains F hs3 hrm hU hLam hG1 hnm
  obtain ⟨hRp, hetap, hcvp, hvp⟩ := t5Resid_contains F hs3 hrp hU hLam hG1 hnp
  -- pointwise residual facts and the bracket
  have hbr : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → ρm x y z ≤ ρf x y z ∧ ρf x y z ≤ ρp x y z := by
    intro x y z hx hy hz
    have h1 := Contains.le_upper hone hRm hRmok x y z hx hy hz
    have h2 := Contains.lower_le hone hRp hRpok x y z hx hy hz
    have h3 := Contains.le_upper hone hvp hvok x y z hx hy hz
    have e1 : ((t5Resid F s3 rm).R.upper : ℝ) / one < 0 := div_neg_of_neg_of_pos (by exact_mod_cast hRmup) hone'
    have e2 : (0 : ℝ) < ((t5Resid F s3 rp).R.lower : ℝ) / one := div_pos (by exact_mod_cast hRplo) hone'
    have e3 : ((t5Resid F s3 rp).v.upper : ℝ) / one < 1 := by
      rw [div_lt_one hone']
      have : ((t5Resid F s3 rp).v.upper : ℝ) < ((ONEi : ℤ) : ℝ) := by exact_mod_cast hvup
      rwa [ONEi_real] at this
    exact hρ x y z hx hy hz (hrm0 x y z hx hy hz) (by simp only [hρp] at h3 ⊢; linarith)
      (by simp only [hρm] at h1 ⊢; linarith) (by simp only [hρp] at h2 ⊢; linarith)
  -- the certified ρ
  have hrho : Contains one ⟨Pc, r, (decide (0 < rm.lower) && (t5Resid F s3 rm).R.ok && (t5Resid F s3 rp).R.ok
      && decide ((t5Resid F s3 rm).R.upper < 0) && decide (0 < (t5Resid F s3 rp).R.lower)
      && (t5Resid F s3 rp).v.ok && decide ((t5Resid F s3 rp).v.upper < ONEi))⟩ ρf := by
    intro _ x y z hx hy hz
    obtain ⟨b1, b2⟩ := hbr x y z hx hy hz
    simp only [hρm, hρp] at b1 b2
    simp only
    rw [abs_le]; push_cast at b1 b2 ⊢
    constructor
    · rw [neg_div] at b1; linarith
    · linarith
  -- eta and cv by averaging
  have heta : Contains one ⟨(TM.average (t5Resid F s3 rm).eta (t5Resid F s3 rp).eta).p,
      (TM.average (t5Resid F s3 rm).eta (t5Resid F s3 rp).eta).r,
      (TM.average (t5Resid F s3 rm).eta (t5Resid F s3 rp).eta).ok && (decide (0 < rm.lower) && (t5Resid F s3 rm).R.ok
        && (t5Resid F s3 rp).R.ok && decide ((t5Resid F s3 rm).R.upper < 0) && decide (0 < (t5Resid F s3 rp).R.lower)
        && (t5Resid F s3 rp).v.ok && decide ((t5Resid F s3 rp).v.upper < ONEi))⟩
      (fun x y z => Real.log (ρf x y z)) := by
    have hav := Contains.average hone hetam hetap (v := fun x y z => Real.log (ρf x y z)) (fun x y z hx hy hz => by
      obtain ⟨b1, b2⟩ := hbr x y z hx hy hz
      have h0 := hrm0 x y z hx hy hz
      left
      exact ⟨Real.log_le_log h0 b1, Real.log_le_log (lt_of_lt_of_le h0 b1) b2⟩)
    intro hok' x y z hx hy hz
    simp only [Bool.and_eq_true] at hok'
    exact hav hok'.1 x y z hx hy hz
  have hcv : Contains one ⟨(TM.average (t5Resid F s3 rm).cv (t5Resid F s3 rp).cv).p,
      (TM.average (t5Resid F s3 rm).cv (t5Resid F s3 rp).cv).r,
      (TM.average (t5Resid F s3 rm).cv (t5Resid F s3 rp).cv).ok && (decide (0 < rm.lower) && (t5Resid F s3 rm).R.ok
        && (t5Resid F s3 rp).R.ok && decide ((t5Resid F s3 rm).R.upper < 0) && decide (0 < (t5Resid F s3 rp).R.lower)
        && (t5Resid F s3 rp).v.ok && decide ((t5Resid F s3 rp).v.upper < ONEi))⟩
      (fun x y z => -Real.log (1 - uf x y z * ρf x y z)) := by
    have hav := Contains.average hone hcvm hcvp (v := fun x y z => -Real.log (1 - uf x y z * ρf x y z))
      (fun x y z hx hy hz => by
        obtain ⟨b1, b2⟩ := hbr x y z hx hy hz
        have hu := hunn x y z hx hy hz
        have h3 := Contains.le_upper hone hvp hvok x y z hx hy hz
        have e3 : ((t5Resid F s3 rp).v.upper : ℝ) / one < 1 := by
          rw [div_lt_one hone']
          have : ((t5Resid F s3 rp).v.upper : ℝ) < ((ONEi : ℤ) : ℝ) := by exact_mod_cast hvup
          rwa [ONEi_real] at this
        have hp1 : 0 < 1 - uf x y z * ρp x y z := by linarith
        have m1 : uf x y z * ρm x y z ≤ uf x y z * ρf x y z := mul_le_mul_of_nonneg_left b1 hu
        have m2 : uf x y z * ρf x y z ≤ uf x y z * ρp x y z := mul_le_mul_of_nonneg_left b2 hu
        left
        constructor
        · have := Real.log_le_log (by linarith) (show 1 - uf x y z * ρf x y z ≤ 1 - uf x y z * ρm x y z by linarith)
          linarith
        · have := Real.log_le_log hp1 (show 1 - uf x y z * ρp x y z ≤ 1 - uf x y z * ρf x y z by linarith)
          linarith)
    intro hok' x y z hx hy hz
    simp only [Bool.and_eq_true] at hok'
    exact hav hok'.1 x y z hx hy hz
  -- the remaining chain
  have hv := C_mul hU hrho
  have homv := C_oneSub hv
  have hg := g1Of_contains F hv homv hcv (fun x y z hx hy hz => mul_nonneg (hunn x y z hx hy hz)
    ((hrm0 x y z hx hy hz).le.trans (hbr x y z hx hy hz).1))
  have hLG1 := C_addOne (C_mul hLam hG1)
  have hX := C_addOne (Contains.sub (C_mul hLam hg) (C_mul hLam heta))
  have hYc := C_addOne (Contains.sub (C_mul hLam hcv) (C_mul hLam heta))
  have hom2v := C_addOne (Contains.scaleInt hv (-2))
  have hYd := Contains.sub hYc (C_mul hLam (C_mul hom2v hom2v))
  have hiLG1 := C_recip hLG1
  have homega := C_mul (C_oneSub (C_mul hLam hCq)) hiLG1
  have hiYc := C_recip hYc
  have hiomv := C_recip homv
  have hYt := C_mul (C_mul (C_mul hX hX) hYd) (C_mul (C_mul hiomv hiomv) (C_mul (C_mul hiYc hiYc) hiYc))
  have hq := Contains.add (Contains.scaleInt (C_mul hT hU) 2) (C_mul hs3 homega)
  have hA1 := C_mul (C_mul (C_mul (C_mul hq hq) hrho) (C_mul hX hYt)) (C_mul invLc_contains hiLG1)
  have hA2 := C_mul (C_mul (C_mul hs3 hom2v) (C_mul hX hLam))
    (C_mul invLc_contains (C_mul (C_mul (C_recip homU) hiomv) (C_mul hiYc hiLG1)))
  have hres := Contains.neg (C_half (Contains.add hA1 hA2))
  have hres' := Contains.congr hres (fun x y z _ _ _ => rfl)
  exact hres' hok

end CKLaneR2.Tail

end


