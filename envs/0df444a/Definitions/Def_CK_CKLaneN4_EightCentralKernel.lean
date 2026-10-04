-- Prove2me | Definitions.Def_CK_CKLaneN4_EightCentralKernel
-- name    : CK_CKLaneN4_EightCentralKernel
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T12:14:03.69737+00:00
-- url     : https://prove2.me/theorems/5ac844ba-0b2d-4d30-b7bb-351bd945fca4
-- title:
--   Courtade–Kumar proof module `CKLaneN4.EightCentralKernel` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.EightCentralKernel` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.EightCentralKernel` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.EightCentralKernel (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/EightCentralKernel.lean)

import Definitions.Def_CK_CKLaneN4_EightKernel

-- ===== source module CKLaneN4.EightCentralKernel =====
section

/-!
# Lane N4: the CENTRAL eight-ratio parent correction (CK_OPPOSITE_EXTENSION analytic/EIGHT_RATIO.py)

Archive claim (EIGHT_RATIO_PROOF.md (4)): `E [eta(E) - eta(E + C(q))]/q^2 ≥ 7/10` whenever
`0 < E ≤ 11/200`, `0 < q ≤ 8E`, `q + 8E ≤ 4/5`, proved on the rational root
`(E, y) ∈ [1/10000, 11/200] × [0, 8]`, `q = yE`, by the archived 50-leaf partition (all leaves
`parent_correction`, logarithmic test (6)) with the relevant-intersection clipping
`q_+ = min(E_+ y_+, 2/5, 4/5 - 8E_-)` (and `outside` boxes, none archived), plus the tail `E ≤ 10^-4`.

`logb_core_sound` is the logarithmic acceptance test (6) on a rational rectangle `[e0,e1] × [q0,q1]` in
`(E, q)` (the same analytic chain as `checkEY_logb_sound`, parameterized by the `q` range);
`checkEYc B c = true → SemEYc B` (unconditional).
-/

namespace CKLaneN4

open GeneralCK CKLaneD Set

/-- The logarithmic acceptance test (6) on the rectangle `[e0,e1] × [q0,q1]`. -/
def logbChecks (e0 e1 q0 q1 : ℚ) (pM0 pM1 : PtCert) (v0 : ℚ) (pv0 : PtCert) (v1 : ℚ)
    (pv1 : PtCert) (cU : LogCert) : Bool :=
  checkPt ((1 - q0) / 2) pM0 && checkPt ((1 - q1) / 2) pM1 &&
  checkPt v0 pv0 && checkPt v1 pv1 &&
  checkLogCert (1 + capHi q1 pM1 / e0) cU &&
  decide (0 < capHi q1 pM1) &&
  decide (e1 + capHi q1 pM1 < 1) &&
  decide (2 * v0 ≤ 1 ∧ Hhi v0 pv0 ≤ e0) &&
  decide (2 * v1 ≤ 1 ∧ e1 + capHi q1 pM1 ≤ Hlo v1 pv1) &&
  decide (0 < pv0.cy.hi - pv0.cx.lo) &&
  decide (0 ≤ cU.lo) &&
  decide (7 / 10 ≤ tLo q0 pM0 * (2 * e0 + betaLo v1 pv0 * (cU.lo / (capHi q1 pM1 / e0))))

theorem logb_core_sound {e0 e1 q0 q1 : ℚ} {pM0 pM1 : PtCert} {v0 : ℚ} {pv0 : PtCert} {v1 : ℚ}
    {pv1 : PtCert} {cU : LogCert} (h : logbChecks e0 e1 q0 q1 pM0 pM1 v0 pv0 v1 pv1 cU = true)
    (r1 : (0 : ℝ) < e0) (rq0 : (0 : ℝ) ≤ q0) (r5 : ((q1 : ℚ) : ℝ) < 1)
    {E q : ℝ} (he0 : (e0 : ℝ) ≤ E) (he1 : E ≤ e1) (hE : 0 < E) (hqq0 : ((q0 : ℚ) : ℝ) ≤ q)
    (hqq1 : q ≤ ((q1 : ℚ) : ℝ)) (hq : 0 ≤ q) (hq1' : q < 1)
    (hphys : E + (1 - H ((1 - q) / 2)) ≤ 1) :
    (7 / 10) * (q ^ 2 / E) ≤ eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  unfold logbChecks at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpM0, hpM1⟩, hpv0⟩, hpv1⟩, hcU⟩, hcH0⟩, hh1⟩, ⟨hv02, hv0e⟩⟩,
    ⟨hv12, hv1h⟩⟩, hℓpos⟩, hcUlo⟩, hacc⟩ := h
  rcases hq.eq_or_lt with hz | hqpos
  · rw [← hz]; norm_num [H_half]
  -- point enclosures
  obtain ⟨_, _, _, hM0u, _, _⟩ := checkPt_bounds hpM0
  obtain ⟨_, _, hM1l, _, _, _⟩ := checkPt_bounds hpM1
  obtain ⟨hv00, _, _, hv0Hu, _, _⟩ := checkPt_bounds hpv0
  obtain ⟨hv10, _, hv1Hl, _, _, _⟩ := checkPt_bounds hpv1
  obtain ⟨hU1, hU2⟩ := checkLogCert_sound hcU
  have hlogv0 := checkLogCert_sound (show checkLogCert v0 pv0.cx = true by
    unfold checkPt at hpv0; rw [Bool.and_eq_true] at hpv0; exact hpv0.1)
  have hlog1v0 := checkLogCert_sound (show checkLogCert (1 - v0) pv0.cy = true by
    unfold checkPt at hpv0; rw [Bool.and_eq_true] at hpv0; exact hpv0.2)
  -- the capacity
  set c := 1 - H ((1 - q) / 2) with hcdef
  have hc0 : 0 < c := capacity_pos hqpos hq1'.le
  have hL := log2_bounds
  have hLpos : 0 < Real.log 2 := log_two_pos
  set cH : ℚ := capHi q1 pM1 with hcHdef
  have ecH : (cH : ℝ) = 1 - (Hlo ((1 - q1) / 2) pM1 : ℝ) := by
    rw [hcHdef]; unfold capHi; push_cast; ring
  have hM1 : (((1 - q1) / 2 : ℚ) : ℝ) = (1 - ((q1 : ℚ) : ℝ)) / 2 := by push_cast; ring
  rw [hM1] at hM1l
  have hcle : c ≤ (cH : ℝ) := by
    have := capacity_mono hqq1 r5.le hq
    rw [ecH]; linarith
  have rcH0 : (0 : ℝ) < (cH : ℝ) := by exact_mod_cast hcH0
  have rh1 : (e1 : ℝ) + (cH : ℝ) < 1 := by exact_mod_cast hh1
  -- the slope coefficient on [E, E + c]
  have rv0 : (0 : ℝ) < (v0 : ℝ) := by exact_mod_cast hv00
  have rv02 : 2 * (v0 : ℝ) ≤ 1 := by exact_mod_cast hv02
  have rv0e : (Hhi v0 pv0 : ℝ) ≤ (e0 : ℝ) := by exact_mod_cast hv0e
  have rv12 : 2 * (v1 : ℝ) ≤ 1 := by exact_mod_cast hv12
  have rv1h : (e1 : ℝ) + (cH : ℝ) ≤ (Hlo v1 pv1 : ℝ) := by exact_mod_cast hv1h
  have hℓ : Real.log ((1 - (v0 : ℝ)) / (v0 : ℝ)) ≤ ((pv0.cy.hi - pv0.cx.lo : ℚ) : ℝ) := by
    have hv0' : (v0 : ℝ) < 1 := by linarith
    rw [Real.log_div (by linarith) rv0.ne']
    push_cast at hlog1v0 ⊢
    linarith [hlog1v0.2, hlogv0.1]
  set β : ℚ := betaLo v1 pv0 with hβdef
  have eβ : (β : ℝ) = (1 - 2 * (v1 : ℝ)) / (1 - (v1 : ℝ)) *
      (1 + 1 / ((pv0.cy.hi - pv0.cx.lo : ℚ) : ℝ)) / (L1 : ℝ) := by
    rw [hβdef]; unfold betaLo; push_cast; ring
  have hder : ∀ h, E < h → h < E + c → 2 + (β : ℝ) / h ≤ -deriv eta h := by
    intro h hlo hhi
    have h0 : 0 < h := hE.trans hlo
    have hh1' : h < 1 := by linarith
    have rv1pos : (0 : ℝ) < (v1 : ℝ) := by exact_mod_cast hv10
    have hs := slope_coeff_lower h0 hh1' rv0 rv1pos rv12
      ((hv0Hu.trans rv0e).trans (he0.trans hlo.le)) rv02
      (by linarith [hv1Hl]) hℓ hL.2
    rw [← eβ] at hs
    have : (β : ℝ) / h ≤ -deriv eta h - 2 := by
      rw [div_le_iff₀ h0]; linarith
    linarith
  have hβ0 : (0 : ℝ) ≤ (β : ℝ) := by
    rw [eβ]
    have hL1 : (0 : ℝ) < (L1 : ℝ) := hLpos.trans_le hL.2
    have rℓ : (0 : ℝ) < ((pv0.cy.hi - pv0.cx.lo : ℚ) : ℝ) := by exact_mod_cast hℓpos
    have : (0 : ℝ) ≤ 1 - 2 * (v1 : ℝ) := by linarith
    have : (0 : ℝ) < 1 - (v1 : ℝ) := by linarith
    positivity
  have hgain := eta_increment_ge_beta_log hE hc0.le hphys hder
  -- logarithmic factor
  set U : ℚ := cH / e0 with hUdef
  have eU : (U : ℝ) = (cH : ℝ) / (e0 : ℝ) := by rw [hUdef]; push_cast; ring
  have hcE : c / E ≤ (U : ℝ) := by
    rw [eU]
    exact (div_le_div_of_nonneg_right hcle hE.le).trans
      (div_le_div_of_nonneg_left rcH0.le r1 he0)
  have hcEpos : 0 < c / E := div_pos hc0 hE
  have hUpos : (0 : ℝ) < (U : ℝ) := hcEpos.trans_le hcE
  have hl0 := log_one_add_div_antitone hcEpos hcE
  have eU1 : ((1 + cH / e0 : ℚ) : ℝ) = 1 + (U : ℝ) := by rw [eU]; push_cast; ring
  rw [eU1] at hU1
  have rcUlo : (0 : ℝ) ≤ (cU.lo : ℝ) := by exact_mod_cast hcUlo
  have hl0' : (cU.lo : ℝ) / (U : ℝ) ≤ Real.log (1 + c / E) / (c / E) :=
    (div_le_div_of_nonneg_right hU1 hUpos.le).trans hl0
  -- capacity ratio
  have hT : ((tLo q0 pM0 : ℚ) : ℝ) ≤ c / q ^ 2 := by
    unfold tLo
    have hhalf : (((1 / (2 * L1)) : ℚ) : ℝ) ≤ c / q ^ 2 := by
      have := capacity_ratio_ge_half hqpos hq1'.le
      push_cast
      refine le_trans ?_ this
      exact one_div_le_one_div_of_le (by positivity) (by linarith [hL.2])
    split_ifs with hq0z
    · exact hhalf
    · push_cast
      apply max_le
      · simpa using hhalf
      · have rq0' : (0 : ℝ) < ((q0 : ℚ) : ℝ) := by
          have h0 : (0 : ℚ) ≤ q0 := by exact_mod_cast rq0
          exact_mod_cast lt_of_le_of_ne h0 (Ne.symm hq0z)
        have hM0 : (((1 - q0) / 2 : ℚ) : ℝ) = (1 - ((q0 : ℚ) : ℝ)) / 2 := by push_cast; ring
        rw [hM0] at hM0u
        have hmono := capacity_ratio_mono rq0' hqq0 hq1'.le
        refine le_trans ?_ hmono
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        linarith
  have hTpos : (0 : ℝ) < ((tLo q0 pM0 : ℚ) : ℝ) := by
    unfold tLo
    have hL1 : (0 : ℝ) < (L1 : ℝ) := hLpos.trans_le hL.2
    split_ifs
    · push_cast; positivity
    · push_cast
      exact lt_of_lt_of_le (by positivity) (le_max_left _ _)
  -- assemble
  have racc : (7 / 10 : ℝ) ≤ ((tLo q0 pM0 : ℚ) : ℝ) *
      (2 * (e0 : ℝ) + (β : ℝ) * ((cU.lo : ℝ) / (U : ℝ))) := by
    have := (Rat.cast_le (K := ℝ)).mpr hacc
    push_cast at this
    linarith
  have hlogeq : Real.log (1 + c / E) = (c / E) * (Real.log (1 + c / E) / (c / E)) := by
    field_simp
  have hkey : ((tLo q0 pM0 : ℚ) : ℝ) * (2 * (e0 : ℝ) + (β : ℝ) * ((cU.lo : ℝ) / (U : ℝ))) ≤
      (c / q ^ 2) * (2 * E + (β : ℝ) * (Real.log (1 + c / E) / (c / E))) := by
    apply mul_le_mul hT _ (by positivity) (by positivity)
    have := mul_le_mul_of_nonneg_left hl0' hβ0
    linarith
  have hfinal : (c / q ^ 2) * (2 * E + (β : ℝ) * (Real.log (1 + c / E) / (c / E))) * (q ^ 2 / E) =
      2 * c + (β : ℝ) * Real.log (1 + c / E) := by
    rw [hlogeq]
    field_simp
  have hqE : 0 ≤ q ^ 2 / E := by positivity
  calc (7 / 10) * (q ^ 2 / E)
      ≤ (c / q ^ 2) * (2 * E + (β : ℝ) * (Real.log (1 + c / E) / (c / E))) * (q ^ 2 / E) :=
        mul_le_mul_of_nonneg_right (racc.trans hkey) hqE
    _ = 2 * c + (β : ℝ) * Real.log (1 + c / E) := hfinal
    _ ≤ eta E - eta (E + c) := hgain

/-! ## The central checker (relevant intersection `q + 8E ≤ 4/5`) -/

/-- The relevant-domain semantic of the central certificate. -/
def SemEYc (B : EYBox) : Prop :=
  ∀ E q : ℝ, (B.e0 : ℝ) ≤ E → E ≤ B.e1 → (B.y0 : ℝ) * E ≤ q → q ≤ (B.y1 : ℝ) * E → 0 ≤ q →
    q + 8 * E ≤ 4 / 5 → (7 / 10) * (q ^ 2 / E) ≤ eta E - eta (E + (1 - H ((1 - q) / 2)))

/-- The archive's clipped upper bias bound `q_+ = min(E_+ y_+, 2/5, 4/5 - 8 E_-)`. -/
def cq1 (B : EYBox) : ℚ := min (B.e1 * B.y1) (min (2 / 5) (4 / 5 - 8 * B.e0))

/-- Central certificate: `outside` (empty relevant intersection) or the logarithmic test. -/
inductive PGCertC where
  | outside
  | logb (pM0 pM1 : PtCert) (v0 : ℚ) (pv0 : PtCert) (v1 : ℚ) (pv1 : PtCert) (cU : LogCert)
  deriving Repr, DecidableEq

def checkEYc (B : EYBox) : PGCertC → Bool
  | .outside => decide (0 < B.e0 ∧ 0 ≤ B.y0 ∧ B.y1 ≤ 8 ∧
      (4 / 5 < B.e0 * (8 + B.y0) ∨ cq1 B < B.e0 * B.y0))
  | .logb pM0 pM1 v0 pv0 v1 pv1 cU =>
      decide (0 < B.e0 ∧ B.e0 ≤ B.e1 ∧ 0 ≤ B.y0 ∧ B.y0 ≤ B.y1 ∧ B.y1 ≤ 8 ∧
        B.e0 * B.y0 ≤ cq1 B ∧ cq1 B < 1 ∧ B.e1 + cq1 B ^ 2 ≤ 1) &&
      logbChecks B.e0 B.e1 (B.e0 * B.y0) (cq1 B) pM0 pM1 v0 pv0 v1 pv1 cU

/-- On the relevant intersection every bias lies in `[E_- y_-, q_+]`. -/
theorem cq1_bound {B : EYBox} {E q : ℝ} (he0 : (B.e0 : ℝ) ≤ E) (he1 : E ≤ B.e1)
    (hy0 : (B.y0 : ℝ) * E ≤ q) (hy1 : q ≤ (B.y1 : ℝ) * E) (hy8 : (B.y1 : ℝ) ≤ 8)
    (hy0n : (0 : ℝ) ≤ B.y0) (hE : 0 < E) (h48 : q + 8 * E ≤ 4 / 5) :
    q ≤ ((cq1 B : ℚ) : ℝ) ∧ (B.e0 : ℝ) * B.y0 ≤ q := by
  have hy1n : (0 : ℝ) ≤ B.y1 := by
    have h01 : (B.y0 : ℝ) * E ≤ (B.y1 : ℝ) * E := hy0.trans hy1
    have := le_of_mul_le_mul_right h01 hE
    linarith
  have h1 : q ≤ (B.e1 : ℝ) * B.y1 := by nlinarith [mul_le_mul_of_nonneg_right he1 hy1n]
  have h2 : q ≤ 2 / 5 := by nlinarith
  have h3 : q ≤ 4 / 5 - 8 * (B.e0 : ℝ) := by linarith
  refine ⟨?_, by nlinarith [mul_le_mul_of_nonneg_left he0 hy0n]⟩
  unfold cq1
  push_cast
  exact le_min h1 (le_min h2 h3)

theorem checkEYc_sound {B : EYBox} {c : PGCertC} (h : checkEYc B c = true) : SemEYc B := by
  intro E q he0 he1 hy0 hy1 hq h48
  cases c with
  | outside =>
    exfalso
    unfold checkEYc at h
    simp only [decide_eq_true_eq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    have r1 : (0 : ℝ) < B.e0 := by exact_mod_cast h1
    have r2 : (0 : ℝ) ≤ B.y0 := by exact_mod_cast h2
    have r3 : (B.y1 : ℝ) ≤ 8 := by exact_mod_cast h3
    have hE : 0 < E := r1.trans_le he0
    obtain ⟨hq1, hq0⟩ := cq1_bound he0 he1 hy0 hy1 r3 r2 hE h48
    rcases h4 with h4 | h4
    · have r4 : (4 / 5 : ℝ) < (B.e0 : ℝ) * (8 + (B.y0 : ℝ)) := by
        have := (Rat.cast_lt (K := ℝ)).mpr h4
        push_cast at this
        linarith
      nlinarith
    · have r4 : ((cq1 B : ℚ) : ℝ) < (B.e0 : ℝ) * (B.y0 : ℝ) := by
        have := (Rat.cast_lt (K := ℝ)).mpr h4
        push_cast at this ⊢
        linarith
      linarith
  | logb pM0 pM1 v0 pv0 v1 pv1 cU =>
    unfold checkEYc at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, hcore⟩ := h
    have r1 : (0 : ℝ) < B.e0 := by exact_mod_cast h1
    have r3 : (0 : ℝ) ≤ B.y0 := by exact_mod_cast h3
    have r5 : (B.y1 : ℝ) ≤ 8 := by exact_mod_cast h5
    have r7 : ((cq1 B : ℚ) : ℝ) < 1 := by exact_mod_cast h7
    have r8 : (B.e1 : ℝ) + ((cq1 B : ℚ) : ℝ) ^ 2 ≤ 1 := by exact_mod_cast h8
    have hE : 0 < E := r1.trans_le he0
    obtain ⟨hq1, hq0⟩ := cq1_bound he0 he1 hy0 hy1 r5 r3 hE h48
    have rq0 : (0 : ℝ) ≤ (((B.e0 * B.y0 : ℚ)) : ℝ) := by push_cast; positivity
    have hqq0 : (((B.e0 * B.y0 : ℚ)) : ℝ) ≤ q := by push_cast; exact hq0
    have hq1' : q < 1 := hq1.trans_lt r7
    have hphys : E + (1 - H ((1 - q) / 2)) ≤ 1 := by
      rcases hq.eq_or_lt with hz | hqpos
      · rw [← hz]; norm_num [H_half]; nlinarith [sq_nonneg ((cq1 B : ℚ) : ℝ)]
      · have hc := capacity_le_sq hqpos hq1'
        have hsq : q ^ 2 ≤ ((cq1 B : ℚ) : ℝ) ^ 2 := pow_le_pow_left₀ hq hq1 2
        linarith
    exact logb_core_sound hcore r1 rq0 r7 he0 he1 hE hqq0 hq1 hq hq1' hphys

def checkTreeEYc : EYBox → CTree PGCertC → Bool
  | B, .leaf c => checkEYc B c
  | B, .node ax l r => decide (ax ≤ 1) && checkTreeEYc (B.lower ax) l && checkTreeEYc (B.upper ax) r

theorem semEYc_of_halves {B : EYBox} {ax : ℕ} (hax : ax ≤ 1) (hl : SemEYc (B.lower ax))
    (hr : SemEYc (B.upper ax)) : SemEYc B := by
  intro E q he0 he1 hy0 hy1 hq h48
  obtain rfl | rfl : ax = 0 ∨ ax = 1 := by omega
  · by_cases hm : E ≤ (((B.e0 + B.e1) / 2 : ℚ) : ℝ)
    · exact hl E q he0 hm hy0 hy1 hq h48
    · exact hr E q (le_of_not_ge hm) he1 hy0 hy1 hq h48
  · by_cases hm : q ≤ (((B.y0 + B.y1) / 2 : ℚ) : ℝ) * E
    · exact hl E q he0 he1 hy0 hm hq h48
    · exact hr E q he0 he1 (le_of_not_ge hm) hy1 hq h48

theorem checkTreeEYc_sound : ∀ (T : CTree PGCertC) (B : EYBox), checkTreeEYc B T = true →
    SemEYc B
  | .leaf c, B, h => checkEYc_sound h
  | .node ax l r, B, h => by
    unfold checkTreeEYc at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact semEYc_of_halves h.1.1 (checkTreeEYc_sound l _ h.1.2) (checkTreeEYc_sound r _ h.2)

end CKLaneN4

end


