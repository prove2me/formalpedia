-- Prove2me | Definitions.Def_CK_CKLaneC_RSCell_SoundCell
-- name    : CK_CKLaneC_RSCell_SoundCell
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:34:30.055224+00:00
-- url     : https://prove2.me/theorems/f726271e-3314-4b3e-9e41-7835b8ee23ac
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSCell.SoundCell` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSCell.SoundCell` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSCell.SoundCell` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSCell.SoundCell (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSCell/SoundCell.lean)

import Definitions.Def_CK_CKLaneC_RSCell_SoundContact

-- ===== source module CKLaneC.RSCell.SoundCell =====
section

/-!
# Lane C, RA-stat interior: soundness of the cell checker, part 4 (base block, assembly, cell theorem)

`cellCheck_sound`: suppose the kernel decides `domOK c && cellCheck c q = true`. Then
`0 < rayGamma b t (b - b σ)` at every point of the cell with `σ < 1`.
-/

namespace CKLaneC.RSCell

open CKLaneC.TM3 GeneralCK

variable (c : Cell)

noncomputable def bF (x : ℝ) : ℝ := ((c.bc : ℝ) + c.bh * x) / one
noncomputable def tF (y : ℝ) : ℝ := ((c.tc : ℝ) + c.th * y) / one
noncomputable def sF (z : ℝ) : ℝ := ((c.sc : ℝ) + c.sh * z) / one

/-- Decidable domain conditions: `0 < b ≤ 1/2`, `0 < σ ≤ 1`, `0 ≤ t ≤ 1` on the cell. -/
noncomputable def domOK : Bool :=
  decide (0 ≤ c.bh) && decide (0 ≤ c.th) && decide (0 ≤ c.sh) && decide (0 < c.bc - c.bh)
    && decide (2 * (c.bc + c.bh) ≤ ONEi) && decide (0 < c.sc - c.sh) && decide (c.sc + c.sh ≤ ONEi)
    && decide (0 ≤ c.tc - c.th) && decide (c.tc + c.th ≤ ONEi)

theorem lin_range {c0 h : ℤ} (hh : 0 ≤ h) {x : ℝ} (hx : |x| ≤ 1) :
    ((c0 - h : ℤ) : ℝ) / one ≤ ((c0 : ℝ) + h * x) / one ∧ ((c0 : ℝ) + h * x) / one ≤ ((c0 + h : ℤ) : ℝ) / one := by
  have hh' : (0 : ℝ) ≤ h := by exact_mod_cast hh
  have h1 := neg_abs_le x
  have h2 := le_abs_self x
  have hx1 : -1 ≤ x := by linarith
  have hx2 : x ≤ 1 := by linarith
  constructor
  · apply div_le_div_of_nonneg_right _ hone'.le; push_cast; nlinarith
  · apply div_le_div_of_nonneg_right _ hone'.le; push_cast; nlinarith

structure Dom : Prop where
  b_pos : ∀ x : ℝ, |x| ≤ 1 → 0 < bF c x
  b_le : ∀ x : ℝ, |x| ≤ 1 → bF c x ≤ 1 / 2
  s_pos : ∀ z : ℝ, |z| ≤ 1 → 0 < sF c z
  s_le : ∀ z : ℝ, |z| ≤ 1 → sF c z ≤ 1
  t_nonneg : ∀ y : ℝ, |y| ≤ 1 → 0 ≤ tF c y
  t_le : ∀ y : ℝ, |y| ≤ 1 → tF c y ≤ 1

theorem ONEi_real : ((ONEi : ℤ) : ℝ) = (one : ℝ) := by unfold ONEi; rw [Int.cast_natCast]

theorem dom_of_domOK (h : domOK c = true) : Dom c := by
  simp only [domOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hbh, hth⟩, hsh⟩, hb0⟩, hb1⟩, hs0⟩, hs1⟩, ht0⟩, ht1⟩ := h
  have hO := ONEi_real
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun z hz => ?_, fun z hz => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · have := (lin_range (c0 := c.bc) hbh hx).1
    have h2 : (0 : ℝ) < ((c.bc - c.bh : ℤ) : ℝ) / one := div_pos (by exact_mod_cast hb0) hone'
    unfold bF; linarith
  · have := (lin_range (c0 := c.bc) hbh hx).2
    have h2 : ((c.bc + c.bh : ℤ) : ℝ) / one ≤ 1 / 2 := by
      rw [div_le_iff₀ hone']
      have : ((2 * (c.bc + c.bh) : ℤ) : ℝ) ≤ ((ONEi : ℤ) : ℝ) := by exact_mod_cast hb1
      rw [hO] at this; push_cast at this ⊢; linarith
    unfold bF; linarith
  · have := (lin_range (c0 := c.sc) hsh hz).1
    have h2 : (0 : ℝ) < ((c.sc - c.sh : ℤ) : ℝ) / one := div_pos (by exact_mod_cast hs0) hone'
    unfold sF; linarith
  · have := (lin_range (c0 := c.sc) hsh hz).2
    have h2 : ((c.sc + c.sh : ℤ) : ℝ) / one ≤ 1 := by
      rw [div_le_one hone']
      have : ((c.sc + c.sh : ℤ) : ℝ) ≤ ((ONEi : ℤ) : ℝ) := by exact_mod_cast hs1
      rwa [hO] at this
    unfold sF; linarith
  · have := (lin_range (c0 := c.tc) hth hy).1
    have h2 : (0 : ℝ) ≤ ((c.tc - c.th : ℤ) : ℝ) / one := div_nonneg (by exact_mod_cast ht0) hone'.le
    unfold tF; linarith
  · have := (lin_range (c0 := c.tc) hth hy).2
    have h2 : ((c.tc + c.th : ℤ) : ℝ) / one ≤ 1 := by
      rw [div_le_one hone']
      have : ((c.tc + c.th : ℤ) : ℝ) ≤ ((ONEi : ℤ) : ℝ) := by exact_mod_cast ht1
      rwa [hO] at this
    unfold tF; linarith

/-! ## Base block -/

theorem H_lt_one {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1 / 2) : H p < 1 := by
  have := H_strictMonoOn ⟨h0, h1.le⟩ ⟨by norm_num, le_refl _⟩ h1
  rwa [H_half] at this

theorem H_eq_neg_logs {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    H p = -(p * Real.log p + (1 - p) * Real.log (1 - p)) * (1 / Real.log 2) := by
  unfold H
  rw [Real.binEntropy, Real.log_inv, Real.log_inv]
  ring

theorem J_eq {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    J p = (Real.log (1 - p) - Real.log p) * (1 / Real.log 2) := by
  unfold J; rw [Real.log_div (by linarith) h0.ne']; ring

/-- The pointwise semantic data of the base block. -/
structure BaseSem (x y z : ℝ) : Prop where
  b0 : 0 < bF c x
  b1 : bF c x ≤ 1 / 2
  s0 : 0 < sF c z
  s1 : sF c z ≤ 1
  t0 : 0 ≤ tF c y
  t1 : tF c y ≤ 1

theorem cellG_contains (hdom : Dom c) (q : Cert) :
    Contains one (cellG c q) (fun x y z =>
      let b := bF c x
      let t := tF c y
      let u := bF c x * sF c z
      let d := b - u
      let E := (H u + H b) / 2
      (-3) * CKLaneN23.RS.Jd1 u + (1 - 2 * b + 3 * d) / 2 * CKLaneN23.RS.Jd2 u
        + rawRS (t * d * E⁻¹) E⁻¹ t (-(J u) / 2) (CKLaneN23.RS.Jd1 u / 2)
        + -rawRS (d * E⁻¹) E⁻¹ 1 (-(J u) / 2) (CKLaneN23.RS.Jd1 u / 2)
        + rawRS ((1 - 2 * b + t * d) * E⁻¹) E⁻¹ t (-(J u) / 2) (CKLaneN23.RS.Jd1 u / 2)
        + rawEta E (-(J u) / 2) (CKLaneN23.RS.Jd1 u / 2)
        + -(rawRS ((1 - 2 * b + 2 * (t * d)) * (H u)⁻¹) (H u)⁻¹ (2 * t) (-(J u)) (CKLaneN23.RS.Jd1 u) / 2)) := by
  -- pointwise domain facts
  have hb0 := hdom.b_pos; have hb1 := hdom.b_le; have hs0 := hdom.s_pos; have hs1 := hdom.s_le
  have ht0 := hdom.t_nonneg; have ht1 := hdom.t_le
  have hu0 : ∀ x z : ℝ, |x| ≤ 1 → |z| ≤ 1 → 0 < bF c x * sF c z := fun x z hx hz => mul_pos (hb0 x hx) (hs0 z hz)
  have hu1 : ∀ x z : ℝ, |x| ≤ 1 → |z| ≤ 1 → bF c x * sF c z ≤ bF c x := fun x z hx hz => by
    have := hs1 z hz; have := hb0 x hx; nlinarith
  -- variables
  have hB : Contains one (TM.lin c.bc c.bh 0 0) (fun x _ _ => bF c x) := by
    refine Contains.congr (Contains.lin c.bc c.bh 0 0) (fun x y z _ _ _ => ?_); unfold bF; push_cast; ring
  have hT : Contains one (TM.lin c.tc 0 c.th 0) (fun _ y _ => tF c y) := by
    refine Contains.congr (Contains.lin c.tc 0 c.th 0) (fun x y z _ _ _ => ?_); unfold tF; push_cast; ring
  have hS : Contains one (TM.lin c.sc 0 0 c.sh) (fun _ _ z => sF c z) := by
    refine Contains.congr (Contains.lin c.sc 0 0 c.sh) (fun x y z _ _ _ => ?_); unfold sF; push_cast; ring
  have hU := C_mul hB hS
  have hDd := Contains.sub hB hU
  have hlogB := C_log hB
  have hlog1mB := C_log (C_oneSub hB)
  have hlogS := C_log hS
  have hlogU := Contains.add hlogB hlogS
  have hlog1mU := C_log (C_oneSub hU)
  -- H(u), H(b)
  have hHu : Contains one (mul (TM.neg (TM.add (mul (mul (TM.lin c.bc c.bh 0 0) (TM.lin c.sc 0 0 c.sh))
      (TM.add (log (TM.lin c.bc c.bh 0 0)) (log (TM.lin c.sc 0 0 c.sh))))
      (mul (TM.addc (TM.neg (mul (TM.lin c.bc c.bh 0 0) (TM.lin c.sc 0 0 c.sh))) ONEi)
        (log (TM.addc (TM.neg (mul (TM.lin c.bc c.bh 0 0) (TM.lin c.sc 0 0 c.sh))) ONEi))))) invLc)
      (fun x _ z => H (bF c x * sF c z)) := by
    have := C_mul (Contains.neg (Contains.add (C_mul hU hlogU) (C_mul (C_oneSub hU) hlog1mU))) invLc_contains
    refine Contains.congr this (fun x y z hx hy hz => ?_)
    have h0 := hu0 x z hx hz
    have h1 : bF c x * sF c z < 1 := by linarith [hu1 x z hx hz, hb1 x hx]
    rw [H_eq_neg_logs h0 h1, Real.log_mul (hb0 x hx).ne' (hs0 z hz).ne']
  have hHb : Contains one (mul (TM.neg (TM.add (mul (TM.lin c.bc c.bh 0 0) (log (TM.lin c.bc c.bh 0 0)))
      (mul (TM.addc (TM.neg (TM.lin c.bc c.bh 0 0)) ONEi) (log (TM.addc (TM.neg (TM.lin c.bc c.bh 0 0)) ONEi)))))
      invLc) (fun x _ _ => H (bF c x)) := by
    have := C_mul (Contains.neg (Contains.add (C_mul hB hlogB) (C_mul (C_oneSub hB) hlog1mB))) invLc_contains
    refine Contains.congr this (fun x y z hx hy hz => ?_)
    rw [H_eq_neg_logs (hb0 x hx) (by linarith [hb1 x hx])]
  have hE := C_half (Contains.add hHu hHb)
  have hJu : Contains one (mul (TM.sub (log (TM.addc (TM.neg (mul (TM.lin c.bc c.bh 0 0) (TM.lin c.sc 0 0 c.sh))) ONEi))
      (TM.add (log (TM.lin c.bc c.bh 0 0)) (log (TM.lin c.sc 0 0 c.sh)))) invLc)
      (fun x _ z => J (bF c x * sF c z)) := by
    have := C_mul (Contains.sub hlog1mU hlogU) invLc_contains
    refine Contains.congr this (fun x y z hx hy hz => ?_)
    have h0 := hu0 x z hx hz
    have h1 : bF c x * sF c z < 1 := by linarith [hu1 x z hx hz, hb1 x hx]
    rw [J_eq h0 h1, Real.log_mul (hb0 x hx).ne' (hs0 z hz).ne']
  have hiB := C_recip hB
  have hiS := C_recip hS
  have hiU := C_mul hiB hiS
  have hi1mU := C_recip (C_oneSub hU)
  have hiUU := C_mul hiU hi1mU
  have hJd1 : Contains one (TM.neg (mul (mul (mul (recip (TM.lin c.bc c.bh 0 0)) (recip (TM.lin c.sc 0 0 c.sh)))
      (recip (TM.addc (TM.neg (mul (TM.lin c.bc c.bh 0 0) (TM.lin c.sc 0 0 c.sh))) ONEi))) invLc))
      (fun x _ z => CKLaneN23.RS.Jd1 (bF c x * sF c z)) := by
    have := Contains.neg (C_mul hiUU invLc_contains)
    refine Contains.congr this (fun x y z hx hy hz => ?_)
    have h0 := hu0 x z hx hz
    have h1 : 1 - bF c x * sF c z ≠ 0 := by linarith [hu1 x z hx hz, hb1 x hx]
    have hb := (hb0 x hx).ne'; have hs := (hs0 z hz).ne'
    unfold CKLaneN23.RS.Jd1
    field_simp
  have hJd2 : Contains one (mul (mul (TM.addc (TM.scaleInt (mul (TM.lin c.bc c.bh 0 0) (TM.lin c.sc 0 0 c.sh)) (-2)) ONEi)
      (mul (mul (mul (recip (TM.lin c.bc c.bh 0 0)) (recip (TM.lin c.sc 0 0 c.sh)))
        (recip (TM.addc (TM.neg (mul (TM.lin c.bc c.bh 0 0) (TM.lin c.sc 0 0 c.sh))) ONEi)))
        (mul (mul (recip (TM.lin c.bc c.bh 0 0)) (recip (TM.lin c.sc 0 0 c.sh)))
          (recip (TM.addc (TM.neg (mul (TM.lin c.bc c.bh 0 0) (TM.lin c.sc 0 0 c.sh))) ONEi))))) invLc)
      (fun x _ z => CKLaneN23.RS.Jd2 (bF c x * sF c z)) := by
    have := C_mul (C_mul (C_addOne (Contains.scaleInt hU (-2))) (C_mul hiUU hiUU)) invLc_contains
    refine Contains.congr this (fun x y z hx hy hz => ?_)
    have h1 : 1 - bF c x * sF c z ≠ 0 := by linarith [hu1 x z hx hz, hb1 x hx]
    have hb := (hb0 x hx).ne'; have hs := (hs0 z hz).ne'
    unfold CKLaneN23.RS.Jd2
    push_cast
    field_simp
    ring
  have hr12b := C_addOne (Contains.scaleInt hB (-2))
  have hterm0 := Contains.add (Contains.scaleInt hJd1 (-3)) (C_mul (C_half (Contains.add hr12b (Contains.scaleInt hDd 3))) hJd2)
  have hiE := C_recip hE
  have hiHu := C_recip hHu
  have hTD := C_mul hT hDd
  have hZ0 := C_mul hTD hiE
  have hZ1 := C_mul hDd hiE
  have hZ2 := C_mul (Contains.add hr12b hTD) hiE
  have hZ3 := C_mul (Contains.add hr12b (Contains.scaleInt hTD 2)) hiHu
  have hde := C_half (Contains.neg hJu)
  have hdde := C_half hJd1
  -- positivity facts for the contact arguments
  have hHpos : ∀ x z : ℝ, |x| ≤ 1 → |z| ≤ 1 → 0 < H (bF c x * sF c z) := fun x z hx hz =>
    H_pos (hu0 x z hx hz) (by linarith [hu1 x z hx hz, hb1 x hx])
  have hHbpos : ∀ x : ℝ, |x| ≤ 1 → 0 < H (bF c x) := fun x hx => H_pos (hb0 x hx) (by linarith [hb1 x hx])
  have hEpos : ∀ x z : ℝ, |x| ≤ 1 → |z| ≤ 1 → 0 < (H (bF c x * sF c z) + H (bF c x)) / 2 := fun x z hx hz => by
    have := hHpos x z hx hz; have := hHbpos x hx; positivity
  have hdnn : ∀ x z : ℝ, |x| ≤ 1 → |z| ≤ 1 → 0 ≤ bF c x - bF c x * sF c z := fun x z hx hz => by
    linarith [hu1 x z hx hz]
  have hr12 : ∀ x : ℝ, |x| ≤ 1 → 0 ≤ -2 * bF c x + 1 := fun x hx => by linarith [hb1 x hx]
  have hOne : Contains one (TM.const ONEi 0) (fun _ _ _ => (1 : ℝ)) := by
    apply Contains.const; rw [ONEi_div]; simp
  have h1 := C_raysec_raw q.V0 q.r0 hZ0 hiE hT hde hdde (fun x y z hx hy hz => by
    have := hEpos x z hx hz; have := ht0 y hy; have := hdnn x z hx hz
    have : 0 ≤ ((H (bF c x * sF c z) + H (bF c x)) / 2)⁻¹ := (inv_pos.mpr (hEpos x z hx hz)).le
    positivity)
  have h2 := C_raysec_raw q.V1 q.r1 hZ1 hiE hOne hde hdde (fun x y z hx hy hz => by
    have := hdnn x z hx hz
    have : 0 ≤ ((H (bF c x * sF c z) + H (bF c x)) / 2)⁻¹ := (inv_pos.mpr (hEpos x z hx hz)).le
    positivity)
  have h3 := C_raysec_raw q.V2 q.r2 hZ2 hiE hT hde hdde (fun x y z hx hy hz => by
    have := hr12 x hx; have := ht0 y hy; have := hdnn x z hx hz
    have : 0 ≤ ((H (bF c x * sF c z) + H (bF c x)) / 2)⁻¹ := (inv_pos.mpr (hEpos x z hx hz)).le
    push_cast
    apply mul_nonneg _ this
    have : 0 ≤ tF c y * (bF c x - bF c x * sF c z) := mul_nonneg (ht0 y hy) (hdnn x z hx hz)
    linarith)
  have h4 := C_etaBlock_raw q.Vm q.rm hE hde hdde (fun x y z hx hy hz => by
    refine ⟨hEpos x z hx hz, ?_⟩
    have := H_le_one (bF c x * sF c z); have := H_le_one (bF c x)
    linarith)
  have h5 := C_raysec_raw q.V3 q.r3 hZ3 hiHu (Contains.scaleInt hT 2) (Contains.neg hJu) hJd1
    (fun x y z hx hy hz => by
      have := hr12 x hx
      have : 0 ≤ (H (bF c x * sF c z))⁻¹ := (inv_pos.mpr (hHpos x z hx hz)).le
      push_cast
      apply mul_nonneg _ this
      have : 0 ≤ tF c y * (bF c x - bF c x * sF c z) := mul_nonneg (ht0 y hy) (hdnn x z hx hz)
      linarith)
  have hG := Contains.add (Contains.add (Contains.add (Contains.add (Contains.add hterm0 h1) (Contains.neg h2)) h3) h4)
    (Contains.neg (C_half h5))
  refine Contains.congr hG (fun x y z hx hy hz => ?_)
  simp only
  push_cast
  ring_nf


/-! ## The cell theorem -/

theorem cellCheck_sound (c : Cell) (q : Cert) (hc : (domOK c && cellCheck c q) = true) :
    ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → sF c z < 1 →
      0 < CKLaneN23.RS.rayGamma (bF c x) (tF c y) (bF c x - bF c x * sF c z) := by
  intro x y z hx hy hz hs1
  simp only [Bool.and_eq_true, cellCheck, decide_eq_true_eq] at hc
  obtain ⟨hdomb, hok, hlow⟩ := hc
  have hdom := dom_of_domOK c hdomb
  have hC := cellG_contains c hdom q
  have hv := Contains.lower_le hone hC hok x y z hx hy hz
  have hpos : 0 < ((cellG c q).lower : ℝ) / one := div_pos (by exact_mod_cast hlow) hone'
  have hval := lt_of_lt_of_le hpos hv
  simp only at hval
  -- identify the raw value with rayGamma at this point
  set b := bF c x with hbdef
  set t := tF c y with htdef
  set σ := sF c z with hσdef
  have hb0 := hdom.b_pos x hx; have hb1 := hdom.b_le x hx
  have hσ0 := hdom.s_pos z hz
  have ht0 := hdom.t_nonneg y hy
  set u := b * σ with hudef
  have hu0 : 0 < u := mul_pos hb0 hσ0
  have hub : u < b := by have := mul_lt_mul_of_pos_left hs1 hb0; rw [mul_one] at this; exact this
  set d := b - u with hddef
  have hd0 : 0 < d := by linarith
  have hu1 : u < 1 / 2 := by linarith
  have hHu := H_pos hu0 (by linarith)
  have hHb := H_pos hb0 (by linarith)
  set E := (H u + H b) / 2 with hEdef
  have hE0 : 0 < E := by positivity
  have hE1 : E < 1 := by
    have := H_lt_one hu0.le hu1; have := H_le_one b; linarith
  have hbd : b - d = u := by ring
  unfold CKLaneN23.RS.rayGamma
  rw [hbd]
  have hr12 : 0 ≤ 1 - 2 * b := by linarith
  -- the four contact blocks and the eta block
  have e1 := raySec_eq (s := t * d) (ds := t) (e := E) (de := -(J u) / 2) (dde := CKLaneN23.RS.Jd1 u / 2)
    (zf := t * d * E⁻¹) (ief := E⁻¹) hE0 (by field_simp) (by field_simp) (by positivity) (by
      intro h0
      rcases mul_eq_zero.mp h0 with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact h'
        · linarith
      · exact absurd h (inv_ne_zero hE0.ne'))
  have e2 := raySec_eq (s := d) (ds := 1) (e := E) (de := -(J u) / 2) (dde := CKLaneN23.RS.Jd1 u / 2)
    (zf := d * E⁻¹) (ief := E⁻¹) hE0 (by field_simp) (by field_simp) (by positivity) (by
      intro h0
      exact absurd h0 (mul_pos hd0 (inv_pos.mpr hE0)).ne')
  have e3 := raySec_eq (s := 1 - 2 * b + t * d) (ds := t) (e := E) (de := -(J u) / 2) (dde := CKLaneN23.RS.Jd1 u / 2)
    (zf := (1 - 2 * b + t * d) * E⁻¹) (ief := E⁻¹) hE0 (by field_simp) (by field_simp)
    (by have := mul_nonneg ht0 hd0.le; positivity) (by
      intro h0
      rcases mul_eq_zero.mp h0 with h | h
      · have := mul_nonneg ht0 hd0.le
        have htd : t * d = 0 := by linarith
        rcases mul_eq_zero.mp htd with h' | h'
        · exact h'
        · linarith
      · exact absurd h (inv_ne_zero hE0.ne'))
  have e5 := raySec_eq (s := 1 - 2 * b + 2 * t * d) (ds := 2 * t) (e := H u) (de := -(J u))
    (dde := CKLaneN23.RS.Jd1 u) (zf := (1 - 2 * b + 2 * (t * d)) * (H u)⁻¹) (ief := (H u)⁻¹) hHu
    (by field_simp) (by field_simp) (by have := mul_nonneg ht0 hd0.le; positivity) (by
      intro h0
      rcases mul_eq_zero.mp h0 with h | h
      · have := mul_nonneg ht0 hd0.le
        have htd : t * d = 0 := by linarith
        rcases mul_eq_zero.mp htd with h' | h'
        · rw [h']; ring
        · linarith
      · exact absurd h (inv_ne_zero hHu.ne'))
  obtain ⟨es, ec⟩ := eta_values hE0 hE1
  rw [← e1, ← e2, ← e3, ← e5, ← es, ← ec]
  unfold rawEta rawRS at hval
  linarith [hval]

end CKLaneC.RSCell

end


