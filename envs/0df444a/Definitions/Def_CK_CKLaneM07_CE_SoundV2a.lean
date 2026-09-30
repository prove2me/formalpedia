-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_SoundV2a
-- name    : CK_CKLaneM07_CE_SoundV2a
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:37:24.48599+00:00
-- url     : https://prove2.me/theorems/0098182f-592f-455f-b467-6be312d6b7e7
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.SoundV2a` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.SoundV2a` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.SoundV2a` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.SoundV2a (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/SoundV2a.lean)

import Definitions.Def_CK_CKLaneM07_CE_TMISound6
import Definitions.Def_CK_CKLaneM07_CE_ChainV2

-- ===== source module CKLaneM07.CE.SoundV2a =====
section

/-!
# Lane M07 / CE-stat: soundness of chain v2, part A (bounds, constants, items, bundles, sites)
-/

set_option autoImplicit false

namespace CKLaneM07.CE

open CKLaneD

/-! ## lower and upper bounds of a Taylor model -/

theorem pAbs_center (s : TMI) : (pAbs s.center.p : ℤ) = pAbs s.p - (pC00 s.p).natAbs := by
  rcases s with ⟨p, r⟩
  rcases p with _ | ⟨r0, p⟩
  · simp [TMI.center, pC00, pAbs]
  · rcases r0 with _ | ⟨a, r0⟩
    · simp [TMI.center, pC00, pAbs, rowAbs]
    · simp only [TMI.center, pC00, pAbs, rowAbs, List.foldr_cons, Int.natAbs_zero]
      push_cast
      ring

theorem abs_pEval_sub_c00 {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (s : TMI) :
    |pEval x y s.p - (pC00 s.p : ℝ)| ≤ (pAbs s.p : ℝ) - |(pC00 s.p : ℝ)| := by
  have h := abs_pEval_le hx hy s.center.p
  rw [pEval_center] at h
  have e : ((pAbs s.center.p : ℕ) : ℝ) = (pAbs s.p : ℝ) - |(pC00 s.p : ℝ)| := by
    have h1 : ((pAbs s.center.p : ℤ) : ℝ) = (((pAbs s.p : ℤ) - (pC00 s.p).natAbs : ℤ) : ℝ) := by
      rw [pAbs_center]
    push_cast at h1
    exact h1
  linarith

theorem lo_cast (t : TMI) :
    ((t.lo : ℤ) : ℝ) = (pC00 t.p : ℝ) - ((pAbs t.p : ℝ) - |(pC00 t.p : ℝ)|) - (t.r : ℝ) := by
  unfold TMI.lo
  push_cast
  rfl

theorem hi_cast (t : TMI) :
    ((t.hi : ℤ) : ℝ) = (pC00 t.p : ℝ) + ((pAbs t.p : ℝ) - |(pC00 t.p : ℝ)|) + (t.r : ℝ) := by
  unfold TMI.hi
  push_cast
  rfl

theorem EnclAt.lo_le {x y v : ℝ} {t : TMI} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (h : EnclAt x y v t) :
    ((t.lo : ℤ) : ℝ) / SC ≤ v := by
  have hS := SC_pos
  have h1 := abs_pEval_sub_c00 hx hy t
  unfold EnclAt at h
  rw [lo_cast, div_le_iff₀ hS]
  have h2 := (abs_le.mp h).1
  have h3 := (abs_le.mp h1).1
  have h4 : pEval x y t.p / SC - (t.r : ℝ) / SC ≤ v := by linarith
  have h5 : pEval x y t.p - (t.r : ℝ) ≤ v * SC := by
    have := mul_le_mul_of_nonneg_right h4 hS.le
    rw [sub_mul, div_mul_cancel₀ _ hS.ne', div_mul_cancel₀ _ hS.ne'] at this
    exact this
  linarith

theorem EnclAt.le_hi {x y v : ℝ} {t : TMI} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (h : EnclAt x y v t) :
    v ≤ ((t.hi : ℤ) : ℝ) / SC := by
  have hS := SC_pos
  have h1 := abs_pEval_sub_c00 hx hy t
  unfold EnclAt at h
  rw [hi_cast, le_div_iff₀ hS]
  have h2 := (abs_le.mp h).2
  have h3 := (abs_le.mp h1).2
  have h4 : v ≤ pEval x y t.p / SC + (t.r : ℝ) / SC := by linarith
  have h5 : v * SC ≤ pEval x y t.p + (t.r : ℝ) := by
    have := mul_le_mul_of_nonneg_right h4 hS.le
    rw [add_mul, div_mul_cancel₀ _ hS.ne', div_mul_cancel₀ _ hS.ne'] at this
    exact this
  linarith

theorem pos_of_lo {x y v : ℝ} {t : TMI} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (h : EnclAt x y v t)
    (hl : 0 < t.lo) : 0 < v := by
  have := h.lo_le hx hy
  have h0 : (0 : ℝ) < ((t.lo : ℤ) : ℝ) / SC := div_pos (by exact_mod_cast hl) SC_pos
  linarith

theorem neg_of_hi {x y v : ℝ} {t : TMI} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (h : EnclAt x y v t)
    (hl : t.hi < 0) : v < 0 := by
  have := h.le_hi hx hy
  have h0 : ((t.hi : ℤ) : ℝ) / SC < 0 := div_neg_of_neg_of_pos (by exact_mod_cast hl) SC_pos
  linarith

/-! ## constants -/

theorem pEval_const (x y : ℝ) (c : ℤ) : pEval x y [[c]] = (c : ℝ) := by
  simp [pEval, rowEval]

theorem encl_one (x y : ℝ) : EnclAt x y 1 oneT := by
  have h := EnclAt.const x y ONE
  have e : ((ONE : ℤ) : ℝ) / SC = 1 := div_self SC_pos.ne'
  rw [e] at h
  exact h

theorem TWOk_div : ((TWOk : ℤ) : ℝ) / SC = 2 := by
  unfold TWOk
  have := SC_pos.ne'
  push_cast
  rw [← SC_eq]
  field_simp

theorem HALFk_div : ((HALFk : ℤ) : ℝ) / SC = 1 / 2 := by
  have h : HALFk * 2 = ONE := by unfold HALFk ONE PB; norm_num
  have h2 : ((HALFk : ℤ) : ℝ) * 2 = SC := by
    rw [SC_eq]; exact_mod_cast h
  have := SC_pos.ne'
  field_simp
  linarith

theorem EnclAt.two {x y u : ℝ} {s : TMI} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hs : EnclAt x y u s) :
    EnclAt x y (2 * u) (TMI.mulC TWOk s) := by
  have h := EnclAt.mulC hx hy TWOk hs
  rw [TWOk_div] at h
  exact h

theorem EnclAt.half {x y u : ℝ} {s : TMI} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hs : EnclAt x y u s) :
    EnclAt x y (1 / 2 * u) (TMI.mulC HALFk s) := by
  have h := EnclAt.mulC hx hy HALFk hs
  rw [HALFk_div] at h
  exact h

theorem encl_ln2 (x y : ℝ) : EnclAt x y (Real.log 2) ln2T := by
  unfold EnclAt ln2T TMI.const
  rw [pEval_const]
  have hS := SC_pos
  obtain ⟨hL0, hL1⟩ := log2_bounds
  obtain ⟨hq1, hq2⟩ := qfl_bounds ((L0 + L1) / 2)
  have hc := qcl_ge ((L1 - L0) / 2)
  push_cast at hq1 hq2 hc ⊢
  rw [abs_le]
  constructor
  · have : ((L1 : ℝ) - L0) / 2 ≤ (qcl ((L1 - L0) / 2) : ℝ) / SC := hc
    have e : ((qcl ((L1 - L0) / 2) : ℝ) + 1) / SC = (qcl ((L1 - L0) / 2) : ℝ) / SC + 1 / SC := by ring
    rw [e]; linarith
  · have e : ((qcl ((L1 - L0) / 2) : ℝ) + 1) / SC = (qcl ((L1 - L0) / 2) : ℝ) / SC + 1 / SC := by ring
    rw [e]
    have h1 : (0 : ℝ) ≤ 1 / SC := (one_div_pos.mpr hS).le
    linarith

/-! ## cell inputs -/

theorem encl_cellA (x y : ℝ) (cl : CellV) :
    EnclAt x y (((cl.A0 : ℝ) + (cl.hA : ℝ) * x) / SC) cl.A := by
  unfold EnclAt CellV.A
  simp only [pEval, rowEval]
  have e : ((cl.A0 : ℝ) + (cl.hA : ℝ) * x) / SC -
      ((cl.A0 : ℝ) + y * 0 + x * (((cl.hA : ℝ) + y * 0) + x * 0)) / SC = 0 := by ring
  rw [e]; simp

theorem encl_celltC (x y : ℝ) (cl : CellV) :
    EnclAt x y (((cl.T0 : ℝ) + (cl.hT : ℝ) * y) / SC) cl.tC := by
  unfold EnclAt CellV.tC
  simp only [pEval, rowEval]
  have e : ((cl.T0 : ℝ) + (cl.hT : ℝ) * y) / SC -
      ((cl.T0 : ℝ) + y * ((cl.hT : ℝ) + y * 0) + x * 0) / SC = 0 := by ring
  rw [e]; simp

/-! ## series items -/

theorem logOK_sound {x y v : ℝ} {u : TMI} {K : ℕ} {it : LogI} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hu : EnclAt x y v u) (h : logOK K u it = true) : 0 < v ∧ EnclAt x y (Real.log v) it.out := by
  unfold logOK at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, hl⟩ := h
  have hb := checkLogCert_sound hc
  have hcast : ((((pC00 u.p : ℚ) / (ONE : ℚ) : ℚ)) : ℝ) = c0R u := by
    unfold c0R SC; push_cast; ring
  rw [hcast] at hb
  exact encl_log hx hy hu hb.1 hb.2 hl

theorem recOK_sound {x y v : ℝ} {u : TMI} {K : ℕ} {it : RecI} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hu : EnclAt x y v u) (h : recOK K u it = true) : 0 < v ∧ EnclAt x y (1 / v) it.out := by
  unfold recOK at h
  rw [decide_eq_true_eq] at h
  exact encl_recip hx hy hu h

/-! ## real entropy functions (natural-log units) matching the Taylor-model formulas -/

noncomputable def HnR (z : ℝ) : ℝ := -(z * Real.log z + (1 - z) * Real.log (1 - z))
noncomputable def JnR (z : ℝ) : ℝ := Real.log (1 - z) - Real.log z
noncomputable def LnR (z : ℝ) : ℝ := 2 * (HnR z * (1 / (1 - 2 * z)))
noncomputable def QaR (z : ℝ) : ℝ := -(z * (1 - z) * (Real.log z + Real.log (1 - z)))
noncomputable def UpsR (z : ℝ) : ℝ := JnR z + HnR z * (1 - 2 * z) * (1 / QaR z)

/-- a function bundle encloses `z`, `log z`, `log (1 - z)` -/
def FnsE (x y z : ℝ) (F : Fns) : Prop :=
  EnclAt x y z F.u ∧ EnclAt x y (Real.log z) F.lu ∧ EnclAt x y (Real.log (1 - z)) F.l1u

section bundle

variable {x y z : ℝ} {F : Fns} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
include hx hy

theorem FnsE.Hn (K : ℕ) (h : FnsE x y z F) : EnclAt x y (HnR z) (F.Hn K) := by
  obtain ⟨hu, hl, hl1⟩ := h
  have := ((EnclAt.mul hx hy K hu hl).add (EnclAt.mul hx hy K ((encl_one x y).sub hu) hl1)).neg
  exact this

omit hx hy in
theorem FnsE.Jn (h : FnsE x y z F) : EnclAt x y (JnR z) F.Jn := by
  obtain ⟨_, hl, hl1⟩ := h
  exact hl1.sub hl

theorem FnsE.den (h : FnsE x y z F) : EnclAt x y (1 - 2 * z) F.den :=
  (encl_one x y).sub (EnclAt.two hx hy h.1)

theorem FnsE.LnW (K : ℕ) {rd : TMI} (h : FnsE x y z F) (hr : EnclAt x y (1 / (1 - 2 * z)) rd) :
    EnclAt x y (LnR z) (F.LnW K rd) :=
  EnclAt.two hx hy (EnclAt.mul hx hy K (h.Hn hx hy K) hr)

theorem FnsE.qarg (K : ℕ) (h : FnsE x y z F) : EnclAt x y (QaR z) (F.qarg K) := by
  obtain ⟨hu, hl, hl1⟩ := h
  exact (EnclAt.mul hx hy K (EnclAt.mul hx hy K hu ((encl_one x y).sub hu)) (hl.add hl1)).neg

theorem FnsE.UpsW (K : ℕ) {rq : TMI} (h : FnsE x y z F) (hr : EnclAt x y (1 / QaR z) rq) :
    EnclAt x y (UpsR z) (F.UpsW K rq) :=
  h.Jn.add (EnclAt.mul hx hy K (EnclAt.mul hx hy K (h.Hn hx hy K) (h.den hx hy)) hr)

end bundle

/-! ## sites -/

noncomputable def zpR (x y : ℝ) (s : Site) : ℝ := pEval x y s.P / SC + (s.rho : ℝ) / SC
noncomputable def zmR (x y : ℝ) (s : Site) : ℝ := pEval x y s.P / SC - (s.rho : ℝ) / SC

theorem encl_up (x y : ℝ) (s : Site) : EnclAt x y (zpR x y s) s.up := by
  have h := encl_shiftP x y s.P (s.rho : ℤ)
  unfold zpR Site.up
  push_cast at h
  exact h

theorem encl_dn (x y : ℝ) (s : Site) : EnclAt x y (zmR x y s) s.dn := by
  have h := encl_shiftP x y s.P (-(s.rho : ℤ))
  unfold zmR Site.dn
  push_cast at h
  rw [neg_div, ← sub_eq_add_neg] at h
  exact h

theorem zm_le_zp (x y : ℝ) (s : Site) : zmR x y s ≤ zpR x y s := by
  unfold zmR zpR
  have : (0 : ℝ) ≤ (s.rho : ℝ) / SC := div_nonneg (Nat.cast_nonneg _) SC_pos.le
  linarith

theorem site_P {x y : ℝ} {s : Site} {K : ℕ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (h : s.logsP K = true) :
    0 < zpR x y s ∧ 0 < 1 - zpR x y s ∧ FnsE x y (zpR x y s) s.Fp := by
  unfold Site.logsP at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hu := encl_up x y s
  obtain ⟨hp, hl⟩ := logOK_sound hx hy hu h1
  obtain ⟨hp1, hl1⟩ := logOK_sound hx hy ((encl_one x y).sub hu) h2
  exact ⟨hp, hp1, hu, hl, hl1⟩

theorem site_M {x y : ℝ} {s : Site} {K : ℕ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (h : s.logsM K = true) :
    0 < zmR x y s ∧ 0 < 1 - zmR x y s ∧ FnsE x y (zmR x y s) s.Fm := by
  unfold Site.logsM at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hu := encl_dn x y s
  obtain ⟨hp, hl⟩ := logOK_sound hx hy hu h1
  obtain ⟨hp1, hl1⟩ := logOK_sound hx hy ((encl_one x y).sub hu) h2
  exact ⟨hp, hp1, hu, hl, hl1⟩

theorem site_band {x y : ℝ} {s : Site} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (h : s.band = true) :
    zpR x y s < 1 / 2 := by
  unfold Site.band at h
  rw [decide_eq_true_eq] at h
  have h1 := (encl_up x y s).le_hi hx hy
  have hS := SC_pos
  have h2 : ((2 * s.up.hi : ℤ) : ℝ) < ((ONE : ℤ) : ℝ) := by exact_mod_cast h
  rw [← SC_eq] at h2
  push_cast at h2
  have h3 : ((s.up.hi : ℤ) : ℝ) / SC < 1 / 2 := by
    rw [div_lt_iff₀ hS]; linarith
  linarith

theorem site_dn_nonpos {x y : ℝ} {s : Site} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (h : s.dn.hi ≤ 0) :
    zmR x y s ≤ 0 := by
  have h1 := (encl_dn x y s).le_hi hx hy
  have h2 : ((s.dn.hi : ℤ) : ℝ) / SC ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h) SC_pos.le
  linarith

/-- bracketing by an increasing residual -/
theorem bracket_incr {r : ℝ → ℝ} (hmono : MonotoneOn r (Set.Ioo 0 (1 / 2)))
    {z zm zp : ℝ} (hz : 0 < z) (hz' : z < 1 / 2) (hr : r z = 0)
    (hzm : 0 < zm) (hzmp : zm ≤ zp) (hzp : zp < 1 / 2) (hm : r zm < 0) (hp : 0 < r zp) :
    zm < z ∧ z < zp := by
  constructor
  · by_contra h
    push Not at h
    have := hmono ⟨hz, hz'⟩ ⟨hzm, lt_of_le_of_lt hzmp hzp⟩ h
    linarith
  · by_contra h
    push Not at h
    have := hmono ⟨lt_of_lt_of_le hzm hzmp, hzp⟩ ⟨hz, hz'⟩ h
    linarith

/-- bracketing by a decreasing residual -/
theorem bracket_decr {r : ℝ → ℝ} (hanti : AntitoneOn r (Set.Ioo 0 (1 / 2)))
    {z zm zp : ℝ} (hz : 0 < z) (hz' : z < 1 / 2) (hr : r z = 0)
    (hzm : 0 < zm) (hzmp : zm ≤ zp) (hzp : zp < 1 / 2) (hm : 0 < r zm) (hp : r zp < 0) :
    zm < z ∧ z < zp := by
  constructor
  · by_contra h
    push Not at h
    have := hanti ⟨hz, hz'⟩ ⟨hzm, lt_of_le_of_lt hzmp hzp⟩ h
    linarith
  · by_contra h
    push Not at h
    have := hanti ⟨lt_of_lt_of_le hzm hzmp, hzp⟩ ⟨hz, hz'⟩ h
    linarith

theorem encl_z_of_bracket {x y z : ℝ} {s : Site} (h : zmR x y s < z ∧ z < zpR x y s) :
    EnclAt x y z s.z := by
  unfold EnclAt Site.z
  unfold zmR zpR at h
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

/-- the accepted variable and its logarithm bundle -/
theorem site_encl {x y z : ℝ} {s : Site} {K : ℕ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hP : s.logsP K = true) (hM : s.logsM K = true) (h : zmR x y s < z ∧ z < zpR x y s) :
    EnclAt x y z s.z ∧ FnsE x y z s.F := by
  obtain ⟨hzp0, hzp1, hFp⟩ := site_P hx hy hP
  obtain ⟨hzm0, hzm1, hFm⟩ := site_M hx hy hM
  have hz := encl_z_of_bracket h
  refine ⟨hz, hz, ?_, ?_⟩
  · apply encl_hull hx hy hFm.2.1 hFp.2.1
    left
    exact ⟨Real.log_le_log hzm0 h.1.le, Real.log_le_log (hzm0.trans h.1) h.2.le⟩
  · apply encl_hull hx hy hFp.2.2 hFm.2.2
    left
    constructor
    · exact Real.log_le_log hzp1 (by linarith [h.2])
    · exact Real.log_le_log (by linarith [h.2]) (by linarith [h.1])

end CKLaneM07.CE

end


