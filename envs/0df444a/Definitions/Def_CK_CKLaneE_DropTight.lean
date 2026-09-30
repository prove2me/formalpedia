-- Prove2me | Definitions.Def_CK_CKLaneE_DropTight
-- name    : CK_CKLaneE_DropTight
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:51:26.248784+00:00
-- url     : https://prove2.me/theorems/2188e240-d177-48c0-98d4-3f0285749305
-- title:
--   Courtade–Kumar proof module `CKLaneE.DropTight` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneE.DropTight` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneE.DropTight` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneE.DropTight (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneE/DropTight.lean)

import Definitions.Def_CK_CKLaneE_CertPDVac

-- ===== source module CKLaneE.DropTight =====
section

/-!
# Lane E: a tight box bound for the entropy drop

For a box `B` (ratio `r = a/b ∈ [r1, r2]`, `b ∈ [b1, b2]`) with `r2 ≤ (1 + r1)/2`, every law satisfies

  `Δ(a, b) ≤ Δ(r1 b, b) ≤ Δ(r1 b1, b1) + (b - b1) G`,
  `G = c J(c b1) - (r1 J(r1 b2) + J(b2))/2`,  `c = (1 + r1)/2`,

where `Δ(x, y) = H((x+y)/2) - (H x + H y)/2`.  The first step is monotonicity of `Δ` in the smaller
point (tangent lines of the concave `H` and `J` antitone, valid while `a ≤ (r1 b + b)/2`); the second
linearizes in `b` (tangent line above `H(c b)`, chord-type lower bounds for `H(r1 b)`, `H(b)`).
The rational bound `Dt` evaluates this with the certified `H`/`J` enclosures; `Dx = min(DHi, Dt)` and
`Kx = min(K, Dt / dLo²)` are then valid drop bounds for every law in the box.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneE.DT

open GeneralCK GeneralCK.Scalar CKLaneE.FP CKLaneE.Chart CKLaneE.LS CKLaneE.PD
open CKLaneE.NLS (H_le_H box_geometry)

section defs
variable (B : Box3)

def aMid : ℚ := B.r1 * B.b2
def Jl0 (v : ℚ) : ℚ := if 0 ≤ lamLo v then Jl v else 0
def Gh : ℚ := (1 + B.r1) / 2 * Jh (mLo B) - (B.r1 * Jl0 (aMid B) + Jl0 B.b2) / 2
def Dt : ℚ :=
  Hhi (mLo B) - (Hlo (aLo B) + Hlo B.b1) / 2 + (B.b2 - B.b1) * (if 0 ≤ Gh B then Gh B else 0)
def tOk : Bool :=
  decide (B.r2 ≤ (1 + B.r1) / 2) && ptOk (mLo B) && ptOk (aLo B) && ptOk B.b1 && ptOk (aMid B) &&
    ptOk B.b2
def Dx : ℚ := if tOk B = true ∧ Dt B ≤ DHi B then Dt B else DHi B
def Kx : ℚ :=
  if tOk B = true ∧ 0 < dLo B ∧ Dt B / (dLo B * dLo B) ≤ K B then Dt B / (dLo B * dLo B) else K B

end defs

/-- The tangent line of the concave entropy lies above it. -/
theorem H_tangent {x y : ℝ} (hx : 0 < x) (hx1 : x < 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    H y ≤ H x + J x * (y - x) := by
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun p => -H p) := H_concaveOn_unit.neg
  have hd : HasDerivAt (fun p => -H p) (-J x) x := (Comparison.hasDerivAt_H hx hx1).neg
  have hxm : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.le, hx1.le⟩
  have hym : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy, hy1⟩
  rcases lt_trichotomy y x with h | h | h
  · have hs := hconv.slope_le_of_hasDerivAt hym hxm h hd
    rw [slope_def_field] at hs
    have hxy : 0 < x - y := sub_pos.mpr h
    rw [div_le_iff₀ hxy] at hs
    nlinarith
  · rw [h]; simp
  · have hs := hconv.le_slope_of_hasDerivAt hxm hym h hd
    rw [slope_def_field] at hs
    have hxy : 0 < y - x := sub_pos.mpr h
    rw [le_div_iff₀ hxy] at hs
    nlinarith

/-- Lower bound of `H` on `[y1, y2] ⊆ (0, 1/2]` by the slope at the right end. -/
theorem H_lower_chord {y1 y y2 : ℝ} (h1 : 0 < y1) (h1y : y1 ≤ y) (hy2 : y ≤ y2) (h2 : y2 ≤ 1 / 2) :
    H y1 + J y2 * (y - y1) ≤ H y := by
  have hy0 : 0 < y := h1.trans_le h1y
  have ht := H_tangent (x := y) (y := y1) hy0 (by linarith) h1.le (by linarith)
  have hJ : J y2 ≤ J y := J_antitone hy0 h2 hy2
  have hd : 0 ≤ y - y1 := by linarith
  have := mul_le_mul_of_nonneg_right hJ hd
  nlinarith

/-- `Δ(x, b)` is nonincreasing in the smaller point while it stays below the midpoint. -/
theorem drop_mono {a' a b : ℝ} (ha' : 0 < a') (ha'a : a' ≤ a) (ham : a ≤ (a' + b) / 2)
    (hb : b ≤ 1 / 2) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤ H ((a' + b) / 2) - (H a' + H b) / 2 := by
  have ha0 : 0 < a := ha'.trans_le ha'a
  have hm' : 0 < (a' + b) / 2 := by linarith
  have hm'1 : (a' + b) / 2 ≤ 1 / 2 := by linarith
  have t1 := H_tangent (x := (a' + b) / 2) (y := (a + b) / 2) hm' (by linarith) (by linarith)
    (by linarith)
  have t2 := H_tangent (x := a) (y := a') ha0 (by linarith) ha'.le (by linarith)
  have hJ : J ((a' + b) / 2) ≤ J a := J_antitone ha0 hm'1 ham
  have hd : 0 ≤ a - a' := by linarith
  have e : (a + b) / 2 - (a' + b) / 2 = (a - a') / 2 := by ring
  rw [e] at t1
  have := mul_le_mul_of_nonneg_right hJ hd
  nlinarith

/-- Linearization of `Δ(r1 b, b)` in `b`. -/
theorem drop_lin {r1 b1 b b2 : ℝ} (hr0 : 0 < r1) (hr1 : r1 ≤ 1) (hb0 : 0 < b1) (hb1 : b1 ≤ b)
    (hb2 : b ≤ b2) (hbh : b2 ≤ 1 / 2) :
    H ((r1 * b + b) / 2) - (H (r1 * b) + H b) / 2 ≤
      H ((1 + r1) / 2 * b1) - (H (r1 * b1) + H b1) / 2 +
        (b - b1) * ((1 + r1) / 2 * J ((1 + r1) / 2 * b1) - (r1 * J (r1 * b2) + J b2) / 2) := by
  have hc0 : 0 < (1 + r1) / 2 * b1 := mul_pos (by linarith) hb0
  have hc1 : (1 + r1) / 2 * b1 < 1 := by nlinarith
  have e1 : (r1 * b + b) / 2 = (1 + r1) / 2 * b := by ring
  rw [e1]
  have t1 := H_tangent (x := (1 + r1) / 2 * b1) (y := (1 + r1) / 2 * b) hc0 hc1
    (mul_nonneg (by linarith) (by linarith)) (by nlinarith)
  have t2 := H_lower_chord (y1 := r1 * b1) (y := r1 * b) (y2 := r1 * b2) (mul_pos hr0 hb0)
    (mul_le_mul_of_nonneg_left hb1 hr0.le) (mul_le_mul_of_nonneg_left hb2 hr0.le) (by nlinarith)
  have t3 := H_lower_chord (y1 := b1) (y := b) (y2 := b2) hb0 hb1 hb2 hbh
  have e2 : (1 + r1) / 2 * b - (1 + r1) / 2 * b1 = (1 + r1) / 2 * (b - b1) := by ring
  have e3 : r1 * b - r1 * b1 = r1 * (b - b1) := by ring
  rw [e2] at t1
  rw [e3] at t2
  nlinarith

theorem J_ge_Jl0 {v : ℚ} (hpt : ptOk v = true) (hv12 : (v : ℝ) ≤ 1 / 2) :
    ((Jl0 v : ℚ) : ℝ) ≤ J (v : ℝ) := by
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (ptOk_pos hpt).1
  simp only [Jl0]
  split_ifs with h
  · exact Jl_le hpt h
  · simp only [Rat.cast_zero]; exact J_nonneg hv0 hv12

set_option maxHeartbeats 1000000 in
/-- The tight drop bound for every law of the box. -/
theorem drop_le_Dt (B : Box3) (hbox : boxOk B = true) (ht : tOk B = true) {a b : ℝ}
    (ha0 : 0 < a) (hab : a < b)
    (hr1 : (B.r1 : ℝ) ≤ a / b) (hr2 : a / b ≤ (B.r2 : ℝ))
    (hb1 : (B.b1 : ℝ) ≤ b) (hb2 : b ≤ (B.b2 : ℝ)) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤ ((Dt B : ℚ) : ℝ) := by
  simp only [tOk, Bool.and_eq_true, decide_eq_true_eq] at ht
  obtain ⟨⟨⟨⟨⟨qr, hmLo⟩, haLo⟩, hb1ok⟩, haMid⟩, hb2ok⟩ := ht
  obtain ⟨R1, R12, R2, B1, B12, B2, _⟩ := boxOk_real hbox
  have hb0 : 0 < b := ha0.trans hab
  have hrr : (B.r2 : ℝ) ≤ (1 + B.r1) / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr qr
    push_cast at h; linarith
  have hr1le : (B.r1 : ℝ) ≤ 1 := R12.trans R2
  -- a = (a/b) b
  have har : a = (a / b) * b := by field_simp
  have ha'a : (B.r1 : ℝ) * b ≤ a := by
    rw [har]; exact mul_le_mul_of_nonneg_right hr1 hb0.le
  have ham : a ≤ ((B.r1 : ℝ) * b + b) / 2 := by
    rw [har]
    have : a / b * b ≤ (B.r2 : ℝ) * b := mul_le_mul_of_nonneg_right hr2 hb0.le
    nlinarith
  have hbh : b ≤ 1 / 2 := hb2.trans B2
  have step1 := drop_mono (a' := (B.r1 : ℝ) * b) (a := a) (b := b) (mul_pos R1 hb0) ha'a ham hbh
  have step2 := drop_lin (r1 := (B.r1 : ℝ)) (b1 := (B.b1 : ℝ)) (b := b) (b2 := (B.b2 : ℝ)) R1 hr1le
    B1 hb1 hb2 B2
  -- rational enclosures
  obtain ⟨_, HmH⟩ := H_bounds hmLo
  obtain ⟨HaL, _⟩ := H_bounds haLo
  obtain ⟨Hb1L, _⟩ := H_bounds hb1ok
  have emLo : ((mLo B : ℚ) : ℝ) = (1 + (B.r1 : ℝ)) / 2 * B.b1 := by rw [c_mLo]; ring
  have eaLo : ((aLo B : ℚ) : ℝ) = (B.r1 : ℝ) * B.b1 := c_aLo B
  have eaMid : ((aMid B : ℚ) : ℝ) = (B.r1 : ℝ) * B.b2 := by simp only [aMid]; push_cast; ring
  rw [emLo] at HmH
  rw [eaLo] at HaL
  have hmLo12 : ((mLo B : ℚ) : ℝ) ≤ 1 / 2 := by rw [emLo]; nlinarith
  have hJm := le_Jh hmLo hmLo12
  rw [emLo] at hJm
  have haMid12 : ((aMid B : ℚ) : ℝ) ≤ 1 / 2 := by rw [eaMid]; nlinarith
  have hJa := J_ge_Jl0 haMid haMid12
  rw [eaMid] at hJa
  have hJb := J_ge_Jl0 hb2ok B2
  -- G ≤ Gh
  have hG : (1 + (B.r1 : ℝ)) / 2 * J ((1 + (B.r1 : ℝ)) / 2 * B.b1) -
      ((B.r1 : ℝ) * J ((B.r1 : ℝ) * B.b2) + J (B.b2 : ℝ)) / 2 ≤ ((Gh B : ℚ) : ℝ) := by
    have eG : ((Gh B : ℚ) : ℝ) = (1 + (B.r1 : ℝ)) / 2 * ((Jh (mLo B) : ℚ) : ℝ) -
        ((B.r1 : ℝ) * ((Jl0 (aMid B) : ℚ) : ℝ) + ((Jl0 B.b2 : ℚ) : ℝ)) / 2 := by
      simp only [Gh]; push_cast; ring
    rw [eG]
    have c1 := mul_le_mul_of_nonneg_left hJm (by linarith : (0 : ℝ) ≤ (1 + (B.r1 : ℝ)) / 2)
    have c2 := mul_le_mul_of_nonneg_left hJa R1.le
    linarith
  set G := (1 + (B.r1 : ℝ)) / 2 * J ((1 + (B.r1 : ℝ)) / 2 * B.b1) -
      ((B.r1 : ℝ) * J ((B.r1 : ℝ) * B.b2) + J (B.b2 : ℝ)) / 2 with hGdef
  have hmax : (b - B.b1) * G ≤ ((B.b2 : ℝ) - B.b1) * ((if 0 ≤ Gh B then Gh B else 0 : ℚ) : ℝ) := by
    have hbb : 0 ≤ b - (B.b1 : ℝ) := by linarith
    have hbb2 : b - (B.b1 : ℝ) ≤ (B.b2 : ℝ) - B.b1 := by linarith
    split_ifs with hg
    · have hg' : (0 : ℝ) ≤ ((Gh B : ℚ) : ℝ) := by exact_mod_cast hg
      calc (b - B.b1) * G ≤ (b - B.b1) * ((Gh B : ℚ) : ℝ) := mul_le_mul_of_nonneg_left hG hbb
        _ ≤ ((B.b2 : ℝ) - B.b1) * ((Gh B : ℚ) : ℝ) := mul_le_mul_of_nonneg_right hbb2 hg'
    · have hg' : ((Gh B : ℚ) : ℝ) < 0 := by
        have : Gh B < 0 := lt_of_not_ge hg
        exact_mod_cast this
      simp only [Rat.cast_zero, mul_zero]
      have := mul_le_mul_of_nonneg_left hG hbb
      nlinarith
  have eDt : ((Dt B : ℚ) : ℝ) = ((Hhi (mLo B) : ℚ) : ℝ) - (((Hlo (aLo B) : ℚ) : ℝ) +
      ((Hlo B.b1 : ℚ) : ℝ)) / 2 + ((B.b2 : ℝ) - B.b1) *
        ((if 0 ≤ Gh B then Gh B else 0 : ℚ) : ℝ) := by
    simp only [Dt]; push_cast; ring
  rw [eDt]
  linarith

theorem drop_bounds (B : Box3) (hbox : boxOk B = true) {a b : ℝ}
    (ha0 : 0 < a) (hab : a < b) (hb1' : b < 1)
    (hr1 : (B.r1 : ℝ) ≤ a / b) (hr2 : a / b ≤ (B.r2 : ℝ))
    (hb1 : (B.b1 : ℝ) ≤ b) (hb2 : b ≤ (B.b2 : ℝ))
    (hΔD : H ((a + b) / 2) - (H a + H b) / 2 ≤ ((DHi B : ℚ) : ℝ))
    (hK0 : (0 : ℝ) ≤ ((K B : ℚ) : ℝ))
    (hKb : H ((a + b) / 2) - (H a + H b) / 2 ≤ ((K B : ℚ) : ℝ) * (b - a) ^ 2) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤ ((Dx B : ℚ) : ℝ) ∧
      H ((a + b) / 2) - (H a + H b) / 2 ≤ ((Kx B : ℚ) : ℝ) * (b - a) ^ 2 ∧
      (0 : ℝ) ≤ ((Kx B : ℚ) : ℝ) := by
  obtain ⟨R1, _, R2, B1, _, _, _⟩ := boxOk_real hbox
  have hb0 : 0 < b := ha0.trans hab
  obtain ⟨_, _, _, _, gdL, _, _⟩ := box_geometry R1 R2 B1 hb0 hr1 hr2 hb1 hb2
  have hΔ0 : 0 ≤ H ((a + b) / 2) - (H a + H b) / 2 :=
    by have := entropy_average_le_midpoint ha0.le (by linarith) hb0.le hb1'.le; linarith
  refine ⟨?_, ?_, ?_⟩
  · simp only [Dx]
    split_ifs with h
    · exact drop_le_Dt B hbox h.1 ha0 hab hr1 hr2 hb1 hb2
    · exact hΔD
  · simp only [Kx]
    split_ifs with h
    · obtain ⟨ht, hd, _⟩ := h
      have hDt := drop_le_Dt B hbox ht ha0 hab hr1 hr2 hb1 hb2
      have hdR : (0 : ℝ) < ((dLo B : ℚ) : ℝ) := by exact_mod_cast hd
      have hdd : ((dLo B : ℚ) : ℝ) ≤ b - a := by rw [c_dLo]; exact gdL
      have hDt0 : (0 : ℝ) ≤ ((Dt B : ℚ) : ℝ) := hΔ0.trans hDt
      push_cast
      have hsq : ((dLo B : ℚ) : ℝ) * ((dLo B : ℚ) : ℝ) ≤ (b - a) ^ 2 := by
        rw [sq]; exact mul_le_mul hdd hdd hdR.le (hdR.le.trans hdd)
      have hpos : (0 : ℝ) < ((dLo B : ℚ) : ℝ) * ((dLo B : ℚ) : ℝ) := mul_pos hdR hdR
      calc H ((a + b) / 2) - (H a + H b) / 2 ≤ ((Dt B : ℚ) : ℝ) := hDt
        _ = ((Dt B : ℚ) : ℝ) / (((dLo B : ℚ) : ℝ) * ((dLo B : ℚ) : ℝ)) *
            (((dLo B : ℚ) : ℝ) * ((dLo B : ℚ) : ℝ)) := by field_simp
        _ ≤ ((Dt B : ℚ) : ℝ) / (((dLo B : ℚ) : ℝ) * ((dLo B : ℚ) : ℝ)) * (b - a) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (div_nonneg hDt0 hpos.le)
    · exact hKb
  · simp only [Kx]
    split_ifs with h
    · obtain ⟨ht, hd, _⟩ := h
      have hDt := drop_le_Dt B hbox ht ha0 hab hr1 hr2 hb1 hb2
      have hdR : (0 : ℝ) < ((dLo B : ℚ) : ℝ) := by exact_mod_cast hd
      push_cast
      exact div_nonneg (hΔ0.trans hDt) (mul_pos hdR hdR).le
    · exact hK0

end CKLaneE.DT

#check @CKLaneE.DT.drop_bounds
#print axioms CKLaneE.DT.drop_bounds

end


