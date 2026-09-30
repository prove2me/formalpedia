-- Prove2me | Definitions.Def_CK_CKLaneC_RSCell_RegionI
-- name    : CK_CKLaneC_RSCell_RegionI
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:51:11.699245+00:00
-- url     : https://prove2.me/theorems/b1a687d8-d263-4193-85d4-905fb6ad03b2
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSCell.RegionI` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSCell.RegionI` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSCell.RegionI` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSCell.RegionI (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSCell/RegionI.lean)

import Definitions.Def_CK_CKLaneC_RSCell_Region
import Definitions.Def_CK_CKLaneC_RSCell_RegionSB

-- ===== source module CKLaneC.RSCell.RegionI =====
section

/-!
# Lane C, RA-stat: integer-coded boxes (compact cover assembly)

`RegionPosI b0 b1 t0 t1 s0 s1` is `RegionPos` on the box with fixed-point endpoints `b0/one, …` (`one = 2^64`).
Leaves come straight from a passing cell check (`of_check`, no per-cell real arithmetic), splits share literal
integer midpoints, and the root is converted to real endpoints once (`toReal`). This keeps per-cell proof terms tiny.
-/

namespace CKLaneC.RSCell

def RegionPosI (b0 b1 t0 t1 s0 s1 : Int) : Prop :=
  RegionPos ((b0 : ℝ) / one) ((b1 : ℝ) / one) ((t0 : ℝ) / one) ((t1 : ℝ) / one) ((s0 : ℝ) / one) ((s1 : ℝ) / one)

theorem RegionPosI.split_b {b0 b1 t0 t1 s0 s1 : Int} (m : Int) (h1 : RegionPosI b0 m t0 t1 s0 s1)
    (h2 : RegionPosI m b1 t0 t1 s0 s1) : RegionPosI b0 b1 t0 t1 s0 s1 :=
  RegionPos.split_b _ h1 h2

theorem RegionPosI.split_t {b0 b1 t0 t1 s0 s1 : Int} (m : Int) (h1 : RegionPosI b0 b1 t0 m s0 s1)
    (h2 : RegionPosI b0 b1 m t1 s0 s1) : RegionPosI b0 b1 t0 t1 s0 s1 :=
  RegionPos.split_t _ h1 h2

theorem RegionPosI.split_s {b0 b1 t0 t1 s0 s1 : Int} (m : Int) (h1 : RegionPosI b0 b1 t0 t1 s0 m)
    (h2 : RegionPosI b0 b1 t0 t1 m s1) : RegionPosI b0 b1 t0 t1 s0 s1 :=
  RegionPos.split_s _ h1 h2

/-- A box wholly inside the corner (`b0 · s0 > (9/20) one²`). -/
theorem RegionPosI.excl (b0 b1 t0 t1 s0 s1 : Int)
    (h : (decide (0 ≤ b0) && decide (0 ≤ s0) && decide (9 * ONEi * ONEi < 20 * b0 * s0)) = true) :
    RegionPosI b0 b1 t0 t1 s0 s1 := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hb, hs⟩, hbs⟩ := h
  apply RegionPos.excl
  · exact div_nonneg (by exact_mod_cast hb) hone'.le
  · exact div_nonneg (by exact_mod_cast hs) hone'.le
  · have hO := ONEi_real
    have h2 : ((9 * ONEi * ONEi : ℤ) : ℝ) < ((20 * b0 * s0 : ℤ) : ℝ) := by exact_mod_cast hbs
    push_cast at h2
    rw [hO] at h2
    rw [div_mul_div_comm, lt_div_iff₀ (mul_pos hone' hone')]
    nlinarith

/-- A passing cell check closes the integer box of the cell. -/
theorem RegionPosI.of_check (c : Cell) (q : Cert) (hc : (domOK c && cellCheck c q) = true)
    (b0 b1 t0 t1 s0 s1 : Int)
    (hbox : (c.bc - c.bh == b0 && c.bc + c.bh == b1 && c.tc - c.th == t0 && c.tc + c.th == t1
      && c.sc - c.sh == s0 && c.sc + c.sh == s1) = true) :
    RegionPosI b0 b1 t0 t1 s0 s1 := by
  simp only [Bool.and_eq_true, beq_iff_eq] at hbox
  obtain ⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩ := hbox
  subst e1 e2 e3 e4 e5 e6
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  have hdom := dom_of_domOK c hc'.1
  have hdomb := hc'.1
  simp only [domOK, Bool.and_eq_true, decide_eq_true_eq] at hdomb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hbh, hth⟩, hsh⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hdomb
  intro b t σ hb0 hb1 ht0 ht1 hs0 hs1 hs _
  -- coordinates (a zero half-width gives a degenerate interval: the point is the centre)
  have coord : ∀ (c0 h : ℤ) (v : ℝ), 0 ≤ h → ((c0 - h : ℤ) : ℝ) / one ≤ v → v ≤ ((c0 + h : ℤ) : ℝ) / one →
      ∃ x : ℝ, |x| ≤ 1 ∧ ((c0 : ℝ) + h * x) / one = v := by
    intro c0 h v hh hlo hhi
    rcases lt_or_eq_of_le hh with hpos | hzero
    · exact cell_coord c0 h hpos v hlo hhi
    · subst hzero
      refine ⟨0, by simp, ?_⟩
      simp only [sub_zero, add_zero, Int.cast_zero, zero_mul] at hlo hhi ⊢
      linarith
  obtain ⟨x, hx, hbx⟩ := coord c.bc c.bh b hbh (by exact_mod_cast hb0) (by exact_mod_cast hb1)
  obtain ⟨y, hy, hty⟩ := coord c.tc c.th t hth (by exact_mod_cast ht0) (by exact_mod_cast ht1)
  obtain ⟨z, hz, hσz⟩ := coord c.sc c.sh σ hsh (by exact_mod_cast hs0) (by exact_mod_cast hs1)
  have h := cellCheck_sound c q hc x y z hx hy hz (by
    show ((c.sc : ℝ) + c.sh * z) / one < 1
    rw [hσz]; exact hs)
  have eb : bF c x = b := hbx
  have et : tF c y = t := hty
  have es : sF c z = σ := hσz
  rwa [eb, et, es] at h

/-- Convert an integer box to the real box with the given endpoints. -/
theorem RegionPosI.toReal {b0 b1 t0 t1 s0 s1 : Int} {B0 B1 T0 T1 S0 S1 : ℝ} (h : RegionPosI b0 b1 t0 t1 s0 s1)
    (e1 : (b0 : ℝ) / one = B0) (e2 : (b1 : ℝ) / one = B1) (e3 : (t0 : ℝ) / one = T0) (e4 : (t1 : ℝ) / one = T1)
    (e5 : (s0 : ℝ) / one = S0) (e6 : (s1 : ℝ) / one = S1) : RegionPos B0 B1 T0 T1 S0 S1 := by
  unfold RegionPosI at h
  rw [e1, e2, e3, e4, e5, e6] at h
  exact h

end CKLaneC.RSCell

end


