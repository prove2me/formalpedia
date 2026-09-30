-- Prove2me | Definitions.Def_CK_CKLaneC3_SlopeTable
-- name    : CK_CKLaneC3_SlopeTable
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:38:09.568018+00:00
-- url     : https://prove2.me/theorems/db6d120e-6fc7-4b38-a4d5-2ee4cf8f2f60
-- title:
--   Courtade–Kumar proof module `CKLaneC3.SlopeTable` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.SlopeTable` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.SlopeTable` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.SlopeTable (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/SlopeTable.lean)

import Definitions.Def_CK_CKLaneC3_TaylorChain
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellInverseCoverage
import Definitions.Def_CK_GeneralCK_Certificates_E8CompactAnchorInterval
import Definitions.Def_CK_GeneralCK_Certificates_E8CompactAnchorTaylor3

-- ===== source module CKLaneC3.SlopeTable =====
section

/-!
# Lane C3 — a checked one-dimensional slope table for the E8 inverse jet

A `Piece` certifies, by executable checks only, enclosures of the canonical inverse
jet `qJet = e8QJet5 e8ThetaCanonicalJet5` on a rational slope interval `[y0, y1]`:

* a tight jet `cenJet` at the slope `y* = Y a_c` of one dyadic parameter point `a_c`,
  with `y*` enclosed by `ystar`;
* a (possibly wide) jet `whlJet` valid at every slope of `[y0, y1]`, obtained from the
  stable interval graph over a parameter interval; coverage of `[y0, y1]` is certified
  by a mean-value argument on `Y` (lower bound `yprime.lo` of `Y'` on the interval).

`tf` turns these into Taylor-form enclosures `Q^(k)(y) ∈ Σ Q^(k+m)(y*) δ^m/m! + Q^(5) δ^{5-k}/(5-k)!`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneC3.SlopeTable

open Set GeneralCK GeneralCK.Certificates DyadicInterval
open E8TAxisStableInterval E8TAxisFirstCellInverseCoverage E8TAxisDeltaDirectionalJet
open CKLaneC3.TaylorChain

abbrev P : ℕ := 160

/-! ## A shared, once-checked enclosure of `log 2` -/

def L2 : DyadicInterval P :=
  ⟨1013035739299659071135698605846798550487025271590,
   1013035739299659071135698605846798552686048527143⟩

def L2w : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem L2_check : logBoxCheck (ofInt P 2) L2 L2w = true := by decide +kernel

/-! ## Primitive stable-graph inputs -/

/-- Executable version of `DenominatorsPositive`. -/
def denomsB (i : Inputs P) : Bool :=
  decide (0 < (onePlusZBox i).d0.lo) &&
  decide (0 < ((onePlusZBox i).mul (onePlusZBox i)).d0.lo) &&
  decide (0 < ((DyadicJet5Enclosure.const P 2).mul (hBox i)).d0.lo) &&
  decide (0 < ((qBox i).mul (ellBox i)).d0.lo) &&
  decide (0 < i.logTwo.lo)

theorem denomsB_sound {i : Inputs P} (h : denomsB i = true) : DenominatorsPositive i := by
  simp only [denomsB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

structure Prim where
  alpha : DyadicInterval P
  expNegTwo : DyadicInterval P
  logOnePlusExp : DyadicInterval P
  we : ExpWitness P
  wl : FastLogBoxWitness

def Prim.inp (w : Prim) : Inputs P := ⟨w.alpha, w.expNegTwo, w.logOnePlusExp, L2⟩

def Prim.check (w : Prim) : Bool :=
  expBoxCheck ((ofInt P (-2)).mul w.alpha) w.expNegTwo w.we &&
  logBoxCheck ((ofInt P 1).add w.expNegTwo) w.logOnePlusExp w.wl &&
  denomsB w.inp

theorem Prim.check_parts {w : Prim} (h : w.check = true) :
    expBoxCheck ((ofInt P (-2)).mul w.inp.alpha) w.inp.expNegTwo w.we = true ∧
    logBoxCheck ((ofInt P 1).add w.inp.expNegTwo) w.inp.logOnePlusExp w.wl = true ∧
    logBoxCheck (ofInt P 2) w.inp.logTwo L2w = true ∧
    DenominatorsPositive w.inp := by
  simp only [Prim.check, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, L2_check, denomsB_sound h.2⟩

/-- Stable graph over the whole parameter box encloses the canonical inverse jet. -/
theorem Prim.jet_sound {w : Prim} (h : w.check = true) (hyp : 0 < (yBox w.inp).d1.lo)
    {a : ℝ} (ha : w.alpha.Contains a) (hapos : 0 < a) :
    (E8TAxisReparamInterval.eval (xBox w.inp) (yBox w.inp)).Contains qJet
      (E8TAxisStableScalar.Y a) := by
  obtain ⟨he, hl, hL, hp⟩ := Prim.check_parts h
  exact checked_stable_contains_canonical he hl hL hp hyp ha hapos

/-- The zero-order component of the `Y` jet encloses `Y a`. -/
theorem Prim.y_sound {w : Prim} (h : w.check = true)
    {a : ℝ} (ha : w.alpha.Contains a) :
    (yBox w.inp).d0.Contains (E8TAxisStableScalar.Y a) := by
  obtain ⟨he, hl, hL, hp⟩ := Prim.check_parts h
  exact checked_yBox_d0_contains he hl hL hp ha

/-- The whole `Y` jet box encloses the stable `Y` jet (in particular `Y'`). -/
theorem Prim.yjet_sound {w : Prim} (h : w.check = true)
    {a : ℝ} (ha : w.alpha.Contains a) :
    (yBox w.inp).Contains E8TAxisStableJet5.yJet a := by
  obtain ⟨he, hl, hL, hp⟩ := Prim.check_parts h
  have hz : w.inp.expNegTwo.Contains (Real.exp (-2 * a)) := by
    simpa using expBoxCheck_sound he (mul_sound (ofInt_sound P (-2)) ha)
  have hc1 : (ofInt P 1).Contains (1 : ℝ) := by simpa using ofInt_sound P 1
  have hc2 : (ofInt P 2).Contains (2 : ℝ) := by simpa using ofInt_sound P 2
  exact (xyBox_sound ha hz (logBoxCheck_sound hl (add_sound hc1 hz))
    (logBoxCheck_sound hL hc2) hp).2

#print axioms Prim.jet_sound
#print axioms Prim.y_sound
#print axioms Prim.yjet_sound

/-! ## Mean-value lower bound for `Y` on a checked parameter box -/

theorem alpha_convex {a1 a2 u : ℝ} {b : DyadicInterval P} (h1 : b.Contains a1) (h2 : b.Contains a2)
    (hu : u ∈ Icc (0 : ℝ) 1) : b.Contains (a1 + u * (a2 - a1)) := by
  obtain ⟨h1l, h1u⟩ := h1
  obtain ⟨h2l, h2u⟩ := h2
  have hs := scale_cast_pos P
  constructor <;> nlinarith [hu.1, hu.2]

theorem Y_diff_lower {w : Prim} (h : w.check = true) {a1 a2 : ℝ}
    (h1 : w.alpha.Contains a1) (h2 : w.alpha.Contains a2) (hpos : 0 < a1) (hle : a1 ≤ a2) :
    ((yBox w.inp).d1.lo : ℝ) / (scale P : ℝ) * (a2 - a1) ≤
      E8TAxisStableScalar.Y a2 - E8TAxisStableScalar.Y a1 := by
  have hs := scale_cast_pos P
  have hY : E8TAxisStableJet5.yJet.d0 = E8TAxisStableScalar.Y :=
    funext E8TAxisStableJet5.yJet_d0
  have hd : ∀ u ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun u : ℝ => E8TAxisStableScalar.Y (a1 + u * (a2 - a1)))
        (E8TAxisStableJet5.yJet.d1 (a1 + u * (a2 - a1)) * (a2 - a1)) u := by
    intro u hu
    have hpt : 0 < a1 + u * (a2 - a1) := by nlinarith [hu.1]
    have hsnd := (E8TAxisStableJet5.yJet_soundAt hpt).1
    rw [hY] at hsnd
    have hlin : HasDerivAt (fun u : ℝ => a1 + u * (a2 - a1)) (a2 - a1) u := by
      simpa using ((hasDerivAt_id u).mul_const (a2 - a1)).const_add a1
    have hcomp : HasDerivAt (E8TAxisStableScalar.Y ∘ fun u : ℝ => a1 + u * (a2 - a1))
        (E8TAxisStableJet5.yJet.d1 (a1 + u * (a2 - a1)) * (a2 - a1)) u :=
      HasDerivAt.comp u hsnd hlin
    exact hcomp
  have hR : ∀ u ∈ Ioo (0 : ℝ) 1,
      ((yBox w.inp).d1.lo : ℝ) / (scale P : ℝ) * (a2 - a1) ≤
        E8TAxisStableJet5.yJet.d1 (a1 + u * (a2 - a1)) * (a2 - a1) := by
    intro u hu
    have hmem := alpha_convex h1 h2 ⟨hu.1.le, hu.2.le⟩
    have hc := (Prim.yjet_sound h hmem).2.1
    have hlo : ((yBox w.inp).d1.lo : ℝ) ≤ (scale P : ℝ) *
        E8TAxisStableJet5.yJet.d1 (a1 + u * (a2 - a1)) := hc.1
    have hm : ((yBox w.inp).d1.lo : ℝ) / (scale P : ℝ) ≤
        E8TAxisStableJet5.yJet.d1 (a1 + u * (a2 - a1)) := by
      rw [div_le_iff₀ hs]
      linarith
    exact mul_le_mul_of_nonneg_right hm (by linarith)
  have hmain := E8CompactAnchorTaylor3.lower_of_first_bound hd hR
  simp only [zero_mul, add_zero, one_mul] at hmain
  simp only [show a1 + (a2 - a1) = a2 by ring] at hmain
  linarith

/-! ## Pieces of the slope table -/

structure Piece where
  y0 : ℚ
  y1 : ℚ
  cen : Prim
  whl : Prim
  cenJet : DyadicJet5Enclosure P
  whlJet : DyadicJet5Enclosure P
  ystar : DyadicInterval P
  yprime : DyadicInterval P

def Piece.check (p : Piece) : Bool :=
  p.cen.check && p.whl.check &&
  decide (p.cen.alpha.lo = p.cen.alpha.hi) &&
  decide (0 < p.whl.alpha.lo) &&
  decide (p.whl.alpha.lo ≤ p.cen.alpha.lo) &&
  decide (p.cen.alpha.lo ≤ p.whl.alpha.hi) &&
  decide (E8TAxisReparamInterval.eval (xBox p.cen.inp) (yBox p.cen.inp) = p.cenJet) &&
  decide (E8TAxisReparamInterval.eval (xBox p.whl.inp) (yBox p.whl.inp) = p.whlJet) &&
  decide ((yBox p.cen.inp).d0 = p.ystar) &&
  decide ((yBox p.whl.inp).d1 = p.yprime) &&
  decide (0 < p.yprime.lo) &&
  decide (0 < (yBox p.cen.inp).d1.lo) &&
  decide (((p.ystar.hi * scale P - p.yprime.lo * (p.cen.alpha.lo - p.whl.alpha.lo) : ℤ) : ℚ) ≤
    p.y0 * ((scale P * scale P : ℤ) : ℚ)) &&
  decide (p.y1 * ((scale P * scale P : ℤ) : ℚ) ≤
    ((p.ystar.lo * scale P + p.yprime.lo * (p.whl.alpha.hi - p.cen.alpha.lo) : ℤ) : ℚ)) &&
  decide (p.y0 * ((scale P : ℤ) : ℚ) ≤ ((p.ystar.lo : ℤ) : ℚ)) &&
  decide (((p.ystar.hi : ℤ) : ℚ) ≤ p.y1 * ((scale P : ℤ) : ℚ))

/-- What a checked piece certifies. -/
structure Piece.Valid (p : Piece) : Prop where
  range : ∀ y : ℝ, (p.y0 : ℝ) ≤ y → y ≤ p.y1 → y ∈ e8SlopeRange
  whole : ∀ y : ℝ, (p.y0 : ℝ) ≤ y → y ≤ p.y1 → p.whlJet.Contains qJet y
  center : ∃ ys : ℝ, p.ystar.Contains ys ∧ (p.y0 : ℝ) ≤ ys ∧ ys ≤ p.y1 ∧
    p.cenJet.Contains qJet ys

theorem point_param_contains {b : DyadicInterval P} (h : b.lo = b.hi) :
    b.Contains ((b.lo : ℝ) / (scale P : ℝ)) := by
  have hs := scale_cast_pos P
  have he : (scale P : ℝ) * ((b.lo : ℝ) / (scale P : ℝ)) = b.lo := by
    field_simp
  constructor
  · rw [he]
  · rw [he]; exact_mod_cast h.le

theorem box_contains_div {b : DyadicInterval P} {n : ℤ} (h0 : b.lo ≤ n) (h1 : n ≤ b.hi) :
    b.Contains ((n : ℝ) / (scale P : ℝ)) := by
  have hs := scale_cast_pos P
  have he : (scale P : ℝ) * ((n : ℝ) / (scale P : ℝ)) = n := by
    field_simp
  constructor
  · rw [he]; exact_mod_cast h0
  · rw [he]; exact_mod_cast h1

/-- Scaled integer inequality to a division bound. -/
theorem le_of_scaled {x A B C y0 S : ℝ} (hS : 0 < S)
    (hx : S * x ≤ A) (hc : A * S - B * C ≤ y0 * (S * S)) :
    x - B / S * (C / S) ≤ y0 := by
  have h1 : x ≤ A / S := by rw [le_div_iff₀ hS]; linarith
  have h2 : A / S - B / S * (C / S) = (A * S - B * C) / (S * S) := by
    field_simp
  have h3 : (A * S - B * C) / (S * S) ≤ y0 := by
    rw [div_le_iff₀ (mul_pos hS hS)]; linarith
  linarith

theorem ge_of_scaled {x A B C y1 S : ℝ} (hS : 0 < S)
    (hx : A ≤ S * x) (hc : y1 * (S * S) ≤ A * S + B * C) :
    y1 ≤ x + B / S * (C / S) := by
  have h1 : A / S ≤ x := by rw [div_le_iff₀ hS]; linarith
  have h2 : A / S + B / S * (C / S) = (A * S + B * C) / (S * S) := by
    field_simp
  have h3 : y1 ≤ (A * S + B * C) / (S * S) := by
    rw [le_div_iff₀ (mul_pos hS hS)]; linarith
  linarith

theorem Piece.check_sound {p : Piece} (h : p.check = true) : p.Valid := by
  simp only [Piece.check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcen, hwhl⟩, hpt⟩, hwpos⟩, hlo_le⟩, hle_hi⟩, hcj⟩, hwj⟩, hys⟩, hyp⟩,
    hyppos⟩, hycpos⟩, hcov1⟩, hcov2⟩, hin1⟩, hin2⟩ := h
  have hs := scale_cast_pos P
  have hcen_alpha : p.cen.alpha.Contains ((p.cen.alpha.lo : ℝ) / (scale P : ℝ)) :=
    point_param_contains hpt
  have hac_whl : p.whl.alpha.Contains ((p.cen.alpha.lo : ℝ) / (scale P : ℝ)) :=
    box_contains_div hlo_le hle_hi
  have hwlo_pos : (0 : ℝ) < (p.whl.alpha.lo : ℝ) := by exact_mod_cast hwpos
  have hcl : (p.whl.alpha.lo : ℝ) ≤ (p.cen.alpha.lo : ℝ) := by exact_mod_cast hlo_le
  have hch : (p.cen.alpha.lo : ℝ) ≤ (p.whl.alpha.hi : ℝ) := by exact_mod_cast hle_hi
  have hac_pos : 0 < (p.cen.alpha.lo : ℝ) / (scale P : ℝ) := div_pos (by linarith) hs
  -- y* and its enclosure
  have hYc : p.ystar.Contains (E8TAxisStableScalar.Y ((p.cen.alpha.lo : ℝ) / (scale P : ℝ))) := by
    rw [← hys]; exact Prim.y_sound hcen hcen_alpha
  -- endpoints of the parameter box
  have hwle : p.whl.alpha.lo ≤ p.whl.alpha.hi := hlo_le.trans hle_hi
  have halo_mem : p.whl.alpha.Contains (lower p.whl.alpha) :=
    box_contains_div le_rfl hwle
  have hahi_mem : p.whl.alpha.Contains (upper p.whl.alpha) :=
    box_contains_div hwle le_rfl
  have halo_pos : 0 < lower p.whl.alpha := div_pos hwlo_pos hs
  have halo_le : lower p.whl.alpha ≤ (p.cen.alpha.lo : ℝ) / (scale P : ℝ) :=
    div_le_div_of_nonneg_right hcl hs.le
  have hac_le : (p.cen.alpha.lo : ℝ) / (scale P : ℝ) ≤ upper p.whl.alpha :=
    div_le_div_of_nonneg_right hch hs.le
  have hmvt1 := Y_diff_lower hwhl halo_mem hac_whl halo_pos halo_le
  have hmvt2 := Y_diff_lower hwhl hac_whl hahi_mem hac_pos hac_le
  rw [hyp] at hmvt1 hmvt2
  have hd1 : (p.cen.alpha.lo : ℝ) / (scale P : ℝ) - lower p.whl.alpha =
      ((p.cen.alpha.lo : ℝ) - p.whl.alpha.lo) / (scale P : ℝ) := by
    simp only [lower]; ring
  have hd2 : upper p.whl.alpha - (p.cen.alpha.lo : ℝ) / (scale P : ℝ) =
      ((p.whl.alpha.hi : ℝ) - p.cen.alpha.lo) / (scale P : ℝ) := by
    simp only [upper]; ring
  rw [hd1] at hmvt1
  rw [hd2] at hmvt2
  -- coverage inequalities in ℝ
  have hcov1R : ((p.ystar.hi : ℝ) * (scale P : ℝ) - (p.yprime.lo : ℝ) *
      ((p.cen.alpha.lo : ℝ) - p.whl.alpha.lo)) ≤ (p.y0 : ℝ) * ((scale P : ℝ) * (scale P : ℝ)) := by
    have := (show ((p.ystar.hi * scale P - p.yprime.lo * (p.cen.alpha.lo - p.whl.alpha.lo) : ℤ) : ℝ) ≤
      (p.y0 : ℝ) * ((scale P * scale P : ℤ) : ℝ) by exact_mod_cast hcov1)
    push_cast at this; linarith
  have hcov2R : (p.y1 : ℝ) * ((scale P : ℝ) * (scale P : ℝ)) ≤
      (p.ystar.lo : ℝ) * (scale P : ℝ) + (p.yprime.lo : ℝ) * ((p.whl.alpha.hi : ℝ) - p.cen.alpha.lo) := by
    have := (show (p.y1 : ℝ) * ((scale P * scale P : ℤ) : ℝ) ≤
      ((p.ystar.lo * scale P + p.yprime.lo * (p.whl.alpha.hi - p.cen.alpha.lo) : ℤ) : ℝ) by
      exact_mod_cast hcov2)
    push_cast at this; linarith
  have hYlo : E8TAxisStableScalar.Y (lower p.whl.alpha) ≤ (p.y0 : ℝ) := by
    have hb := le_of_scaled hs hYc.2 hcov1R
    linarith
  have hYhi : (p.y1 : ℝ) ≤ E8TAxisStableScalar.Y (upper p.whl.alpha) := by
    have hb := ge_of_scaled hs hYc.1 hcov2R
    linarith
  have hcover : ∀ y : ℝ, (p.y0 : ℝ) ≤ y → y ≤ p.y1 →
      ∃ a : ℝ, p.whl.alpha.Contains a ∧ 0 < a ∧ E8TAxisStableScalar.Y a = y := by
    intro y h0 h1
    exact covers_of_endpoint_bounds hwpos hwle hYlo hYhi ⟨h0, h1⟩
  refine ⟨?_, ?_, ?_⟩
  · intro y h0 h1
    obtain ⟨a, _, hapos, hya⟩ := hcover y h0 h1
    rw [← hya]; exact E8TAxisStableJet5.Y_mem_e8SlopeRange hapos
  · intro y h0 h1
    obtain ⟨a, ha, hapos, hya⟩ := hcover y h0 h1
    have hj := Prim.jet_sound hwhl (by rw [hyp]; exact hyppos) ha hapos
    rw [hwj, hya] at hj
    exact hj
  · refine ⟨E8TAxisStableScalar.Y ((p.cen.alpha.lo : ℝ) / (scale P : ℝ)), hYc, ?_, ?_, ?_⟩
    · have h1 : (p.y0 : ℝ) * (scale P : ℝ) ≤ (p.ystar.lo : ℝ) := by exact_mod_cast hin1
      have h2 := hYc.1
      rw [← mul_le_mul_iff_of_pos_right hs]
      linarith
    · have h1 : (p.ystar.hi : ℝ) ≤ (p.y1 : ℝ) * (scale P : ℝ) := by exact_mod_cast hin2
      have h2 := hYc.2
      rw [← mul_le_mul_iff_of_pos_right hs]
      linarith
    · have hj := Prim.jet_sound hcen hycpos hcen_alpha hac_pos
      rw [hcj] at hj
      exact hj

#print axioms Piece.check_sound

end CKLaneC3.SlopeTable

end


