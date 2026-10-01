-- Prove2me | Definitions.Def_CK_CKLaneN1b_CapChecker
-- name    : CK_CKLaneN1b_CapChecker
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:03:50.26754+00:00
-- url     : https://prove2.me/theorems/5318b46e-9386-446c-b39d-ea7e449b3916
-- title:
--   Courtade–Kumar proof module `CKLaneN1b.CapChecker` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1b.CapChecker` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1b.CapChecker` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1b.CapChecker (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1b/CapChecker.lean)

import Definitions.Def_CK_CKLaneN1b_PCChecker
import Definitions.Def_CK_CKLaneM09_Checker

-- ===== source module CKLaneN1b.CapChecker =====
section

/-!
# Lane N1b: the cap-cell checker (CAP) and its unconditional soundness

For boxes near the entropy cap (small mean deficit `s = C0 - E`), the manuscript's global
supporting plane is taken at the law's own means (`CKLaneM09.cap_plane_cost`,
`cost ≥ j + A (H a - e) + B (H b - f)` with the explicit contact coefficients `capA, capB`).
The scalar gap `gap j (2 k) Δ s` is concave in `s`, nonnegative at `s = 0` by the deterministic
cap bound `P Δ ≤ j` (`GeneralCK.deterministic_cap_bound`), and it is checked at one deficit
`S ≥ s` (`GeneralCK.Scalar.gap_endpoint_criterion`).  At `S` the check uses `j ≥ P Δ`, the
monotone increments of the convex `P` with the corner bound on the Jensen gap `Δ`, rational
brackets of `P`, and the interval lower bound `k` of both plane coefficients over the box
(`CKLaneM09.coeff_real`).

`CapCell.ok_sound : CapCell.ok B c = true → Sem B` has no other hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneN1b

open GeneralCK GeneralCK.Scalar CKLaneE

/-- A cap cell: log points at the box corners and at `(a0 + b1)/2`, the deficit endpoint `S`,
and rational brackets of `P` at `Δhi + S`, `Δhi`, `S`. -/
structure CapCell where
  pa0 : Pt
  pa1 : Pt
  pb0 : Pt
  pb1 : Pt
  pmid : Pt
  S : ℚ
  xa : Pt
  xd : Pt
  xs : Pt
  deriving Repr, DecidableEq

namespace CapCell

variable (B : Box) (c : CapCell)

/-- Intervals of `-log a`, `-log b`, `-log (1-a)`, `-log (1-b)` over the box. -/
def m11lo : ℚ := -c.pa1.l1
def m11hi : ℚ := -c.pa0.l0
def m12lo : ℚ := -c.pb1.l1
def m12hi : ℚ := -c.pb0.l0
def m21lo : ℚ := -c.pa0.m1
def m21hi : ℚ := -c.pa1.m0
def m22lo : ℚ := -c.pb0.m1
def m22hi : ℚ := -c.pb1.m0
def r1lo : ℚ := 1 / (2 * B.a1 * B.b1)
def r1hi : ℚ := 1 / (2 * B.a0 * B.b0)
def r2lo : ℚ := 1 / (2 * (1 - B.a0) * (1 - B.b0))
def r2hi : ℚ := 1 / (2 * (1 - B.a1) * (1 - B.b1))
def detlo : ℚ := c.m11lo * c.m22lo - c.m12hi * c.m21hi
def dethi : ℚ := c.m11hi * c.m22hi - c.m12lo * c.m21lo
def nAlo : ℚ := r1lo B * c.m22lo - r2hi B * c.m12hi
def nDlo : ℚ := c.m11lo * r2lo B - c.m21hi * r1hi B
def dl : ℚ := max (B.b0 - B.a1) DMIN
/-- Lower bound of both plane coefficients over the box (for `b - a ≥ 1/50`). -/
def klo : ℚ := dl B ^ 2 * min (nAlo B c / c.dethi) (nDlo B c / c.dethi)
def Chi : ℚ := (c.pa1.Hhi + c.pb0.Hhi) / 2
/-- Upper bound of the Jensen gap at the outer corner `(a0, b1)`. -/
def Dhi : ℚ := c.pmid.Hhi - (c.pa0.Hlo + c.pb1.Hlo) / 2
def PU : ℚ := (1 - 2 * c.xa.q) * c.xa.Jhi
def PLD : ℚ := (1 - 2 * c.xd.q) * c.xd.Jlo
def PLS : ℚ := if 0 < c.S then (1 - 2 * c.xs.q) * c.xs.Jlo else 0

/-- The side condition for the lower bracket at `S` (only used when `S > 0`). -/
def sOk : Bool :=
  if 0 < c.S then c.xs.ok && decide (2 * c.xs.q ≤ 1 ∧ 1 - c.S ≤ c.xs.Hlo) else true

/-- The Boolean cap-cell checker. -/
def ok : Bool :=
  decide (0 < B.a0 ∧ B.a0 ≤ B.a1 ∧ B.a1 < B.b0 ∧ B.b0 ≤ B.b1 ∧ B.b1 < 1 ∧ B.a1 ≤ 1 / 2 ∧
    1 / 2 ≤ B.b0 ∧ 0 ≤ B.t0 ∧ B.t0 ≤ 1) &&
  decide (c.pa0.q = B.a0 ∧ c.pa1.q = B.a1 ∧ c.pb0.q = B.b0 ∧ c.pb1.q = B.b1 ∧
    c.pmid.q = (B.a0 + B.b1) / 2) &&
  c.pa0.ok && c.pa1.ok && c.pb0.ok && c.pb1.ok && c.pmid.ok &&
  decide (0 ≤ c.m11lo ∧ 0 ≤ c.m12lo ∧ 0 ≤ c.m21lo ∧ 0 ≤ c.m22lo) &&
  decide (0 < c.detlo ∧ 0 < nAlo B c ∧ 0 < nDlo B c) &&
  decide (0 ≤ c.S ∧ (1 - B.t0) * (c.Chi - E0) ≤ c.S ∧ c.Dhi + c.S < 1) &&
  c.xa.ok && c.xd.ok &&
  decide (2 * c.xa.q ≤ 1 ∧ c.xa.Hhi ≤ 1 - (c.Dhi + c.S) ∧ 2 * c.xd.q ≤ 1 ∧
    1 - c.Dhi ≤ c.xd.Hlo) &&
  c.sOk &&
  decide (0 ≤ 2 * klo B c * c.S + c.PLS - c.PU + c.PLD)

end CapCell

set_option maxHeartbeats 2000000 in
theorem CapCell.ok_sound {B : Box} {c : CapCell} (h : CapCell.ok B c = true) : Sem B := by
  unfold CapCell.ok at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hbox, hq⟩, hpa0⟩, hpa1⟩, hpb0⟩, hpb1⟩, hpmid⟩, hm⟩, hdet⟩, hS⟩, hxa⟩,
    hxd⟩, hbr⟩, hsok⟩, hfin⟩ := h
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := hbox
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  obtain ⟨p1, p2, p3, p4⟩ := hm
  obtain ⟨d1, d2, d3⟩ := hdet
  obtain ⟨hS0, hS1, hS2⟩ := hS
  obtain ⟨x1, x2, x3, x4⟩ := hbr
  intro k μ hin hd
  obtain ⟨ha0, ha1, hb0, hb1, hE0, _⟩ := hin
  -- real box facts
  have ra0 : (0 : ℝ) < (B.a0 : ℝ) := by exact_mod_cast s1
  have rab : (B.a1 : ℝ) < (B.b0 : ℝ) := by exact_mod_cast s3
  have rb1 : (B.b1 : ℝ) < 1 := by exact_mod_cast s5
  have ra1 : (B.a1 : ℝ) ≤ 1 / 2 := cast_le_half s6
  have rb0 : (1 / 2 : ℝ) ≤ (B.b0 : ℝ) := half_le_cast s7
  have rt0 : (0 : ℝ) ≤ (B.t0 : ℝ) := by exact_mod_cast s8
  have rt1 : (B.t0 : ℝ) ≤ 1 := by exact_mod_cast s9
  have hapos : 0 < μ.a := lt_of_lt_of_le ra0 ha0
  have hab : μ.a < μ.b := by linarith
  have hb1' : μ.b < 1 := lt_of_le_of_lt hb1 rb1
  -- log enclosures on the box (the corner points are checked)
  obtain ⟨_, _, la0l, _, _, la0m⟩ := Pt.ok_logs hpa0
  obtain ⟨_, _, _, la1h, la1m, _⟩ := Pt.ok_logs hpa1
  obtain ⟨_, _, lb0l, _, _, lb0m⟩ := Pt.ok_logs hpb0
  obtain ⟨_, _, _, lb1h, lb1m, _⟩ := Pt.ok_logs hpb1
  rw [q1] at la0l la0m
  rw [q2] at la1h la1m
  rw [q3] at lb0l lb0m
  rw [q4] at lb1h lb1m
  have hloga_lo : Real.log (B.a0 : ℝ) ≤ Real.log μ.a := Real.log_le_log ra0 ha0
  have hloga_hi : Real.log μ.a ≤ Real.log (B.a1 : ℝ) := Real.log_le_log hapos ha1
  have hlogb_lo : Real.log (B.b0 : ℝ) ≤ Real.log μ.b :=
    Real.log_le_log (by linarith) hb0
  have hlogb_hi : Real.log μ.b ≤ Real.log (B.b1 : ℝ) := Real.log_le_log (by linarith) hb1
  have hlog1a_lo : Real.log (1 - (B.a1 : ℝ)) ≤ Real.log (1 - μ.a) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog1a_hi : Real.log (1 - μ.a) ≤ Real.log (1 - (B.a0 : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog1b_lo : Real.log (1 - (B.b1 : ℝ)) ≤ Real.log (1 - μ.b) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog1b_hi : Real.log (1 - μ.b) ≤ Real.log (1 - (B.b0 : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have m11a : ((c.m11lo : ℚ) : ℝ) ≤ -Real.log μ.a := by
    simp only [CapCell.m11lo, Rat.cast_neg]; linarith
  have m11b : -Real.log μ.a ≤ ((c.m11hi : ℚ) : ℝ) := by
    simp only [CapCell.m11hi, Rat.cast_neg]; linarith
  have m12a : ((c.m12lo : ℚ) : ℝ) ≤ -Real.log μ.b := by
    simp only [CapCell.m12lo, Rat.cast_neg]; linarith
  have m12b : -Real.log μ.b ≤ ((c.m12hi : ℚ) : ℝ) := by
    simp only [CapCell.m12hi, Rat.cast_neg]; linarith
  have m21a : ((c.m21lo : ℚ) : ℝ) ≤ -Real.log (1 - μ.a) := by
    simp only [CapCell.m21lo, Rat.cast_neg]; linarith
  have m21b : -Real.log (1 - μ.a) ≤ ((c.m21hi : ℚ) : ℝ) := by
    simp only [CapCell.m21hi, Rat.cast_neg]; linarith
  have m22a : ((c.m22lo : ℚ) : ℝ) ≤ -Real.log (1 - μ.b) := by
    simp only [CapCell.m22lo, Rat.cast_neg]; linarith
  have m22b : -Real.log (1 - μ.b) ≤ ((c.m22hi : ℚ) : ℝ) := by
    simp only [CapCell.m22hi, Rat.cast_neg]; linarith
  -- reciprocal factors
  have hb0' : 0 < μ.b := by linarith
  have ha1' : 0 < 1 - μ.a := by linarith
  have hb1'' : 0 < 1 - μ.b := by linarith
  have er1lo : ((CapCell.r1lo B : ℚ) : ℝ) = 1 / (2 * (B.a1 : ℝ) * (B.b1 : ℝ)) := by
    simp only [CapCell.r1lo]; push_cast; ring
  have er1hi : ((CapCell.r1hi B : ℚ) : ℝ) = 1 / (2 * (B.a0 : ℝ) * (B.b0 : ℝ)) := by
    simp only [CapCell.r1hi]; push_cast; ring
  have er2lo : ((CapCell.r2lo B : ℚ) : ℝ) = 1 / (2 * (1 - (B.a0 : ℝ)) * (1 - (B.b0 : ℝ))) := by
    simp only [CapCell.r2lo]; push_cast; ring
  have er2hi : ((CapCell.r2hi B : ℚ) : ℝ) = 1 / (2 * (1 - (B.a1 : ℝ)) * (1 - (B.b1 : ℝ))) := by
    simp only [CapCell.r2hi]; push_cast; ring
  have r1a : ((CapCell.r1lo B : ℚ) : ℝ) ≤ 1 / (2 * μ.a * μ.b) := by
    rw [er1lo]
    apply one_div_le_one_div_of_le (by positivity)
    have h1 := mul_le_mul ha1 hb1 hb0'.le (by linarith)
    linarith only [h1]
  have r1b : 1 / (2 * μ.a * μ.b) ≤ ((CapCell.r1hi B : ℚ) : ℝ) := by
    rw [er1hi]
    have hb00 : (0 : ℝ) < (B.b0 : ℝ) := by linarith
    apply one_div_le_one_div_of_le (by positivity)
    have h1 := mul_le_mul ha0 hb0 hb00.le hapos.le
    linarith only [h1]
  have r2a : ((CapCell.r2lo B : ℚ) : ℝ) ≤ 1 / (2 * (1 - μ.a) * (1 - μ.b)) := by
    rw [er2lo]
    apply one_div_le_one_div_of_le (by positivity)
    have h1 := mul_le_mul (by linarith : 1 - μ.a ≤ 1 - (B.a0 : ℝ))
      (by linarith : 1 - μ.b ≤ 1 - (B.b0 : ℝ)) hb1''.le (by linarith)
    linarith only [h1]
  have r2b : 1 / (2 * (1 - μ.a) * (1 - μ.b)) ≤ ((CapCell.r2hi B : ℚ) : ℝ) := by
    rw [er2hi]
    have h1 : (0 : ℝ) < 1 - (B.a1 : ℝ) := by linarith
    have h2 : (0 : ℝ) < 1 - (B.b1 : ℝ) := by linarith
    apply one_div_le_one_div_of_le (by positivity)
    have h3 := mul_le_mul (by linarith : 1 - (B.a1 : ℝ) ≤ 1 - μ.a)
      (by linarith : 1 - (B.b1 : ℝ) ≤ 1 - μ.b) h2.le ha1'.le
    linarith only [h3]
  have hu1 : (0 : ℝ) ≤ ((CapCell.r1lo B : ℚ) : ℝ) := by
    rw [er1lo]
    have : (0 : ℝ) < (B.a1 : ℝ) := by linarith
    have : (0 : ℝ) < (B.b1 : ℝ) := by linarith
    positivity
  have hu2 : (0 : ℝ) ≤ ((CapCell.r2lo B : ℚ) : ℝ) := by
    rw [er2lo]
    have : (0 : ℝ) < 1 - (B.a0 : ℝ) := by linarith
    have : (0 : ℝ) < 1 - (B.b0 : ℝ) := by linarith
    positivity
  have q1' : (0 : ℝ) ≤ ((c.m11lo : ℚ) : ℝ) := by exact_mod_cast p1
  have q2' : (0 : ℝ) ≤ ((c.m12lo : ℚ) : ℝ) := by exact_mod_cast p2
  have q3' : (0 : ℝ) ≤ ((c.m21lo : ℚ) : ℝ) := by exact_mod_cast p3
  have q4' : (0 : ℝ) ≤ ((c.m22lo : ℚ) : ℝ) := by exact_mod_cast p4
  have hd1 : (0 : ℝ) < ((c.m11lo : ℚ) : ℝ) * ((c.m22lo : ℚ) : ℝ) -
      ((c.m12hi : ℚ) : ℝ) * ((c.m21hi : ℚ) : ℝ) := by
    have e : ((CapCell.detlo c : ℚ) : ℝ) = ((c.m11lo : ℚ) : ℝ) * ((c.m22lo : ℚ) : ℝ) -
        ((c.m12hi : ℚ) : ℝ) * ((c.m21hi : ℚ) : ℝ) := by
      simp only [CapCell.detlo]; push_cast; ring
    rw [← e]; exact_mod_cast d1
  have hd2 : (0 : ℝ) < ((CapCell.r1lo B : ℚ) : ℝ) * ((c.m22lo : ℚ) : ℝ) -
      ((CapCell.r2hi B : ℚ) : ℝ) * ((c.m12hi : ℚ) : ℝ) := by
    have e : ((CapCell.nAlo B c : ℚ) : ℝ) = ((CapCell.r1lo B : ℚ) : ℝ) * ((c.m22lo : ℚ) : ℝ) -
        ((CapCell.r2hi B : ℚ) : ℝ) * ((c.m12hi : ℚ) : ℝ) := by
      simp only [CapCell.nAlo]; push_cast; ring
    rw [← e]; exact_mod_cast d2
  have hd3 : (0 : ℝ) < ((c.m11lo : ℚ) : ℝ) * ((CapCell.r2lo B : ℚ) : ℝ) -
      ((c.m21hi : ℚ) : ℝ) * ((CapCell.r1hi B : ℚ) : ℝ) := by
    have e : ((CapCell.nDlo B c : ℚ) : ℝ) = ((c.m11lo : ℚ) : ℝ) * ((CapCell.r2lo B : ℚ) : ℝ) -
        ((c.m21hi : ℚ) : ℝ) * ((CapCell.r1hi B : ℚ) : ℝ) := by
      simp only [CapCell.nDlo]; push_cast; ring
    rw [← e]; exact_mod_cast d3
  have hDM : ((DMIN : ℚ) : ℝ) = 1 / 50 := by norm_num [DMIN]
  have edl : ((CapCell.dl B : ℚ) : ℝ) = max ((B.b0 : ℝ) - (B.a1 : ℝ)) ((DMIN : ℚ) : ℝ) := by
    simp only [CapCell.dl]; push_cast; ring_nf
  have hdl : ((CapCell.dl B : ℚ) : ℝ) ≤ μ.b - μ.a := by
    rw [edl]; exact max_le (by linarith) hd
  have hdl0 : (0 : ℝ) < ((CapCell.dl B : ℚ) : ℝ) := by
    rw [edl]; exact lt_of_lt_of_le (by rw [hDM]; norm_num) (le_max_right _ _)
  obtain ⟨hdet0, gA, gB, _, _⟩ := CKLaneM09.coeff_real m11a m11b m12a m12b m21a m21b m22a m22b
    r1a r1b r2a r2b q1' q2' q3' q4' hu1 hu2 hd1 hd2 hd3 hdl hdl0
  have hdet_eq := CKLaneM09.capDet_eq μ.a μ.b
  have hA_eq := CKLaneM09.capA_eq hapos hab hb1'
  have hB_eq := CKLaneM09.capB_eq hapos hab hb1'
  rw [← hdet_eq] at hdet0 gA gB
  rw [← hA_eq] at gA
  rw [← hB_eq] at gB
  have edethi : ((CapCell.dethi c : ℚ) : ℝ) = ((c.m11hi : ℚ) : ℝ) * ((c.m22hi : ℚ) : ℝ) -
      ((c.m12lo : ℚ) : ℝ) * ((c.m21lo : ℚ) : ℝ) := by
    simp only [CapCell.dethi]; push_cast; ring
  have enAlo : ((CapCell.nAlo B c : ℚ) : ℝ) = ((CapCell.r1lo B : ℚ) : ℝ) * ((c.m22lo : ℚ) : ℝ) -
      ((CapCell.r2hi B : ℚ) : ℝ) * ((c.m12hi : ℚ) : ℝ) := by
    simp only [CapCell.nAlo]; push_cast; ring
  have enDlo : ((CapCell.nDlo B c : ℚ) : ℝ) = ((c.m11lo : ℚ) : ℝ) * ((CapCell.r2lo B : ℚ) : ℝ) -
      ((c.m21hi : ℚ) : ℝ) * ((CapCell.r1hi B : ℚ) : ℝ) := by
    simp only [CapCell.nDlo]; push_cast; ring
  rw [← edethi, ← enAlo] at gA
  rw [← edethi, ← enDlo] at gB
  have eklo : ((CapCell.klo B c : ℚ) : ℝ) = ((CapCell.dl B : ℚ) : ℝ) ^ 2 *
      min (((CapCell.nAlo B c : ℚ) : ℝ) / ((CapCell.dethi c : ℚ) : ℝ))
        (((CapCell.nDlo B c : ℚ) : ℝ) / ((CapCell.dethi c : ℚ) : ℝ)) := by
    simp only [CapCell.klo]; push_cast; ring
  have hsq0 : (0 : ℝ) ≤ ((CapCell.dl B : ℚ) : ℝ) ^ 2 := sq_nonneg _
  have hkA : ((CapCell.klo B c : ℚ) : ℝ) ≤ CKLaneM09.capA μ.a μ.b := by
    rw [eklo]; exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hsq0).trans gA
  have hkB : ((CapCell.klo B c : ℚ) : ℝ) ≤ CKLaneM09.capB μ.a μ.b := by
    rw [eklo]; exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hsq0).trans gB
  have hkpos : (0 : ℝ) < ((CapCell.klo B c : ℚ) : ℝ) := by
    rw [eklo]
    have hdh : (0 : ℝ) < ((CapCell.dethi c : ℚ) : ℝ) := by
      rw [edethi]
      have k1 := mul_le_mul (m11a.trans m11b) (m22a.trans m22b) q4' (q1'.trans (m11a.trans m11b))
      have k2 := mul_le_mul (m12a.trans m12b) (m21a.trans m21b) q3' (q2'.trans (m12a.trans m12b))
      linarith only [k1, k2, hd1]
    have hnA : (0 : ℝ) < ((CapCell.nAlo B c : ℚ) : ℝ) := by rw [enAlo]; exact hd2
    have hnD : (0 : ℝ) < ((CapCell.nDlo B c : ℚ) : ℝ) := by rw [enDlo]; exact hd3
    exact mul_pos (pow_pos hdl0 2) (lt_min (div_pos hnA hdh) (div_pos hnD hdh))
  have hA0 : 0 < CKLaneM09.capA μ.a μ.b := hkpos.trans_le hkA
  have hB0 : 0 < CKLaneM09.capB μ.a μ.b := hkpos.trans_le hkB
  obtain ⟨hc1, hc0⟩ := CKLaneM09.cap_contact hapos hab hb1' hdet0.ne'
  have hplane := CKLaneM09.cap_plane_cost μ hA0 hB0 hab hc1 hc0
  -- the scalar gap
  have hjen := CKLaneD.law_gap_le_P μ
  have hdef := CKLaneD.law_deficit_mem μ
  have he := μ.e_le_cap
  have hf := μ.f_le_cap
  have hEdef : μ.meanEntropy = (μ.e + μ.f) / 2 := rfl
  have hΔ := jensenGap_nonneg hapos.le μ.a_interior.2.le hb0'.le hb1'.le
  -- the corner bound on the Jensen gap
  obtain ⟨Ha0l, _⟩ := Pt.H_bounds hpa0
  obtain ⟨_, Ha1h⟩ := Pt.H_bounds hpa1
  obtain ⟨_, Hb0h⟩ := Pt.H_bounds hpb0
  obtain ⟨Hb1l, _⟩ := Pt.H_bounds hpb1
  obtain ⟨_, Hmh⟩ := Pt.H_bounds hpmid
  rw [q1] at Ha0l
  rw [q2] at Ha1h
  rw [q3] at Hb0h
  rw [q4] at Hb1l
  have emid : ((c.pmid.q : ℚ) : ℝ) = ((B.a0 : ℝ) + (B.b1 : ℝ)) / 2 := by rw [q5]; push_cast; ring
  rw [emid] at Hmh
  have hcorner := jensenGap_le_corner ra0 ha0 hab.le hb1 rb1
  have eDhi : ((CapCell.Dhi c : ℚ) : ℝ) = ((c.pmid.Hhi : ℚ) : ℝ) -
      (((c.pa0.Hlo : ℚ) : ℝ) + ((c.pb1.Hlo : ℚ) : ℝ)) / 2 := by
    simp only [CapCell.Dhi]; push_cast; ring
  have hΔhi : H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 ≤ ((CapCell.Dhi c : ℚ) : ℝ) := by
    rw [eDhi]; linarith
  -- the deficit endpoint
  have rS0 : (0 : ℝ) ≤ (c.S : ℝ) := by exact_mod_cast hS0
  have rS1 : (1 - (B.t0 : ℝ)) * (((CapCell.Chi c : ℚ) : ℝ) - (E0 : ℝ)) ≤ (c.S : ℝ) := by
    exact_mod_cast hS1
  have rS2 : ((CapCell.Dhi c : ℚ) : ℝ) + (c.S : ℝ) < 1 := by exact_mod_cast hS2
  have eChi : ((CapCell.Chi c : ℚ) : ℝ) = (((c.pa1.Hhi : ℚ) : ℝ) + ((c.pb0.Hhi : ℚ) : ℝ)) / 2 := by
    simp only [CapCell.Chi]; push_cast; ring
  have hHa_hi : H μ.a ≤ H (B.a1 : ℝ) := CKLaneD.H_mono_left hapos.le ha1 ra1
  have hHb_hi : H μ.b ≤ H (B.b0 : ℝ) := CKLaneD.H_anti_right rb0 hb0 hb1'.le
  have hChi : (H μ.a + H μ.b) / 2 ≤ ((CapCell.Chi c : ℚ) : ℝ) := by rw [eChi]; linarith
  have hsS : (H μ.a + H μ.b) / 2 - μ.meanEntropy ≤ (c.S : ℝ) := by
    have h1 : (1 - (B.t0 : ℝ)) * ((H μ.a + H μ.b) / 2 - (E0 : ℝ)) ≤
        (1 - (B.t0 : ℝ)) * (((CapCell.Chi c : ℚ) : ℝ) - (E0 : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h2 : (H μ.a + H μ.b) / 2 - μ.meanEntropy ≤
        (1 - (B.t0 : ℝ)) * ((H μ.a + H μ.b) / 2 - (E0 : ℝ)) := by linarith
    linarith
  -- brackets of P
  obtain ⟨xa0, _, _, _, _, _⟩ := Pt.ok_logs hxa
  obtain ⟨xd0, _, _, _, _, _⟩ := Pt.ok_logs hxd
  obtain ⟨_, HxaH⟩ := Pt.H_bounds hxa
  obtain ⟨_, JxaH⟩ := Pt.J_bounds hxa
  obtain ⟨HxdL, _⟩ := Pt.H_bounds hxd
  obtain ⟨JxdL, _⟩ := Pt.J_bounds hxd
  have rx1 : 2 * (c.xa.q : ℝ) ≤ 1 := by exact_mod_cast x1
  have rx2 : ((c.xa.Hhi : ℚ) : ℝ) ≤ 1 - (((CapCell.Dhi c : ℚ) : ℝ) + (c.S : ℝ)) := by
    exact_mod_cast x2
  have rx3 : 2 * (c.xd.q : ℝ) ≤ 1 := by exact_mod_cast x3
  have rx4 : 1 - ((CapCell.Dhi c : ℚ) : ℝ) ≤ ((c.xd.Hlo : ℚ) : ℝ) := by exact_mod_cast x4
  have xa0' : (0 : ℝ) < (c.xa.q : ℝ) := by exact_mod_cast xa0
  have xd0' : (0 : ℝ) < (c.xd.q : ℝ) := by exact_mod_cast xd0
  have hDhi0 : (0 : ℝ) ≤ ((CapCell.Dhi c : ℚ) : ℝ) := hΔ.trans hΔhi
  have hPU : P (((CapCell.Dhi c : ℚ) : ℝ) + (c.S : ℝ)) ≤ ((CapCell.PU c : ℚ) : ℝ) := by
    have hbr := CKLaneD.P_le_bracket (by linarith) rS2 xa0' (by linarith) (HxaH.trans rx2)
    have ee : ((CapCell.PU c : ℚ) : ℝ) = (1 - 2 * (c.xa.q : ℝ)) * ((c.xa.Jhi : ℚ) : ℝ) := by
      simp only [CapCell.PU]; push_cast; ring
    have := mul_le_mul_of_nonneg_left JxaH (by linarith : (0 : ℝ) ≤ 1 - 2 * (c.xa.q : ℝ))
    rw [ee]; linarith
  have hPLD : ((CapCell.PLD c : ℚ) : ℝ) ≤ P ((CapCell.Dhi c : ℚ) : ℝ) := by
    have hbr := CKLaneD.P_ge_bracket hDhi0 (by linarith) xd0' (by linarith) (rx4.trans HxdL)
    have ee : ((CapCell.PLD c : ℚ) : ℝ) = (1 - 2 * (c.xd.q : ℝ)) * ((c.xd.Jlo : ℚ) : ℝ) := by
      simp only [CapCell.PLD]; push_cast; ring
    have := mul_le_mul_of_nonneg_left JxdL (by linarith : (0 : ℝ) ≤ 1 - 2 * (c.xd.q : ℝ))
    rw [ee]; linarith
  have hPLS : ((CapCell.PLS c : ℚ) : ℝ) ≤ P (c.S : ℝ) := by
    unfold CapCell.sOk at hsok
    by_cases hpos : 0 < c.S
    · rw [if_pos hpos] at hsok
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hsok
      obtain ⟨hxs, y1, y2⟩ := hsok
      obtain ⟨xs0, _, _, _, _, _⟩ := Pt.ok_logs hxs
      have xs0' : (0 : ℝ) < (c.xs.q : ℝ) := by exact_mod_cast xs0
      obtain ⟨HxsL, _⟩ := Pt.H_bounds hxs
      obtain ⟨JxsL, _⟩ := Pt.J_bounds hxs
      have ry1 : 2 * (c.xs.q : ℝ) ≤ 1 := by exact_mod_cast y1
      have ry2 : 1 - (c.S : ℝ) ≤ ((c.xs.Hlo : ℚ) : ℝ) := by exact_mod_cast y2
      have hbr := CKLaneD.P_ge_bracket rS0 (by linarith) xs0' (by linarith) (ry2.trans HxsL)
      have ee : ((CapCell.PLS c : ℚ) : ℝ) = (1 - 2 * (c.xs.q : ℝ)) * ((c.xs.Jlo : ℚ) : ℝ) := by
        simp only [CapCell.PLS, if_pos hpos]; push_cast; ring
      have := mul_le_mul_of_nonneg_left JxsL (by linarith : (0 : ℝ) ≤ 1 - 2 * (c.xs.q : ℝ))
      rw [ee]; linarith
    · have ee : ((CapCell.PLS c : ℚ) : ℝ) = 0 := by
        simp only [CapCell.PLS, if_neg hpos, Rat.cast_zero]
      rw [ee]
      exact CKLaneD.P_nonneg rS0 (by linarith)
  have rfin : (0 : ℝ) ≤ 2 * ((CapCell.klo B c : ℚ) : ℝ) * (c.S : ℝ) + ((CapCell.PLS c : ℚ) : ℝ) -
      ((CapCell.PU c : ℚ) : ℝ) + ((CapCell.PLD c : ℚ) : ℝ) := by exact_mod_cast hfin
  -- the gap at the endpoint S
  have hcap := deterministic_cap_bound hapos μ.a_interior.2 hb0' hb1'
  have hincr := P_incr_mono hΔ hΔhi rS0 rS2
  have hend : 0 ≤ gap (interiorCost μ.a μ.b) (2 * ((CapCell.klo B c : ℚ) : ℝ))
      (H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2) (c.S : ℝ) := by
    unfold gap
    linarith
  have hcrit := gap_endpoint_criterion hΔ rS0 (by linarith) hcap hend hdef.1 hsS
  -- the plane with the smaller coefficient
  have t1 : ((CapCell.klo B c : ℚ) : ℝ) * (H μ.a - μ.e) ≤ CKLaneM09.capA μ.a μ.b * (H μ.a - μ.e) :=
    mul_le_mul_of_nonneg_right hkA (by linarith)
  have t2 : ((CapCell.klo B c : ℚ) : ℝ) * (H μ.b - μ.f) ≤ CKLaneM09.capB μ.a μ.b * (H μ.b - μ.f) :=
    mul_le_mul_of_nonneg_right hkB (by linarith)
  have hsplit : 2 * ((CapCell.klo B c : ℚ) : ℝ) * ((H μ.a + H μ.b) / 2 - μ.meanEntropy) =
      ((CapCell.klo B c : ℚ) : ℝ) * (H μ.a - μ.e) + ((CapCell.klo B c : ℚ) : ℝ) * (H μ.b - μ.f) := by
    rw [hEdef]; ring
  have hI : H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 + ((H μ.a + H μ.b) / 2 - μ.meanEntropy) =
      H ((μ.a + μ.b) / 2) - μ.meanEntropy := by ring
  rw [hI] at hcrit
  linarith

end CKLaneN1b

end


