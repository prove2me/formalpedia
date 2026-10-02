-- Prove2me | Definitions.Def_CK_CKLaneM04_Checker
-- name    : CK_CKLaneM04_Checker
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T08:36:13.277972+00:00
-- url     : https://prove2.me/theorems/47559345-e0ea-46e2-9bbe-2ee8c86b947e
-- title:
--   Courtade–Kumar proof module `CKLaneM04.Checker` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM04.Checker` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM04.Checker` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM04.Checker (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM04/Checker.lean)

import Definitions.Def_CK_CKLaneD_FleetBase
import Definitions.Def_CK_GeneralCK_PsiLogSumOwner

-- ===== source module CKLaneM04.Checker =====
section

/-!
# Lane M04: the archived `logsum_direct` method as a Boolean checker with law-level soundness

Archived method (`FULL_ENTROPY_COVER.bound(pb, 'logsum_direct')`, called from
`OUTER_OPPOSITE.gap`): on a physical box `a ∈ [alo,ahi]`, `b ∈ [blo,bhi]`,
`E = EMIN + t (C0 - EMIN)`, `t ∈ [t0,t1]`, `C0 = (H a + H b)/2`, it proves

  `R_psi ≤ P(Δ + s) - P(s) ≤ P(sHi + ΔHi) - P(sHi) ≤ j(a,b) + β (b-a)^2 s ≤ ζ`,

with `s = C0 - E`, `Δ = H((a+b)/2) - C0`, `j = interiorCost`, `β = 1/(2 b (1-a))`
(the Lean log-sum floor `InteriorLaw.psiLogSumCostFloor`).

`check B c = true → Sem B` (`check_sound`) with no other hypotheses: every primitive enclosure
(logarithms, `H`, `J`, the entropy-inverse brackets for `P`, the Jensen-gap bound `ΔHi`) is
recomputed and verified by the checker from the untrusted witness `c`.
`checkLeaf p B c = true → SemUVT (uvtBox p)` binds the witness to the archived `(u,v,t)` leaf `p`.
-/

set_option autoImplicit false

namespace CKLaneM04

open GeneralCK CKLaneD

/-! ## Analytic lemmas -/

/-- `J` is antitone on `(0,1)`. -/
theorem J_anti {x y : ℝ} (hx : 0 < x) (hy : y < 1) (hxy : x ≤ y) : J y ≤ J x := by
  have hy0 : 0 < y := hx.trans_le hxy
  unfold J
  apply (div_le_div_iff_of_pos_right (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
  apply Real.log_le_log (div_pos (by linarith) hy0)
  apply (div_le_div_iff₀ hy0 hx).2
  nlinarith

/-- Right-secant upper bound of the concave `H` to the left of `lo`
(mirror of `CKLaneD.H_leftslope_upper`). -/
theorem H_rightslope_upper {lo h x HU0 HLh : ℝ} (hh : 0 < h) (hx0 : 0 ≤ x) (hxl : x ≤ lo)
    (hlh : lo + h ≤ 1) (hU : H lo ≤ HU0) (hL : HLh ≤ H (lo + h)) :
    H x ≤ HU0 + (HLh - HU0) / h * (x - lo) := by
  rcases eq_or_lt_of_le hxl with heq | hlt
  · subst heq
    have e : HU0 + (HLh - HU0) / h * (x - x) = HU0 := by ring
    rw [e]; exact hU
  · have hs := H_concaveOn.slope_anti_adjacent (x := x) (y := lo) (z := lo + h)
      ⟨hx0, by linarith⟩ ⟨by linarith, hlh⟩ hlt (by linarith)
    rw [show lo + h - lo = h by ring] at hs
    have hd : 0 < lo - x := by linarith
    rw [div_le_div_iff₀ hh hd] at hs
    have e1 : 0 ≤ (HU0 - H lo) * (h + (lo - x)) := mul_nonneg (by linarith) (by linarith)
    have e2 : 0 ≤ (H (lo + h) - HLh) * (lo - x) := mul_nonneg (by linarith) hd.le
    have hnum : 0 ≤ HU0 * h + (HLh - HU0) * (x - lo) - H x * h := by nlinarith [hs, e1, e2]
    have hq : (HLh - HU0) / h * h = HLh - HU0 := div_mul_cancel₀ _ hh.ne'
    have hq' : (HLh - HU0) / h * h * (x - lo) = (HLh - HU0) * (x - lo) := by rw [hq]
    apply le_of_mul_le_mul_right _ hh
    nlinarith [hnum, hq']

/-- Increments of the convex increasing profile `P` over `[s, s+d]` are dominated by the
increment over `[s', s'+d']` whenever `s ≤ s'` and `d ≤ d'`. -/
theorem P_incr_mono {s s' d d' : ℝ} (hs0 : 0 ≤ s) (hss : s ≤ s') (hd0 : 0 ≤ d) (hdd : d ≤ d')
    (h1 : s' + d' < 1) :
    Scalar.P (s + d) - Scalar.P s ≤ Scalar.P (s' + d') - Scalar.P s' := by
  have hm : Scalar.P (s + d) ≤ Scalar.P (s + d') := by
    have := Scalar.P_increment_lower (a := s + d) (b := s + d') (by linarith) (by linarith)
      (by linarith)
    linarith
  have hc : Scalar.P (s + d') + Scalar.P s' ≤ Scalar.P s + Scalar.P (s' + d') := by
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ (s' - s) + d' by linarith) with hL | hL
    · have e1 : s' = s := by linarith
      have e2 : d' = 0 := by linarith
      rw [e1, e2, add_zero]
    · set L := (s' - s) + d' with hLdef
      have hLne : L ≠ 0 := hL.ne'
      have hx : s ∈ Set.Ico (0 : ℝ) 1 := ⟨hs0, by linarith⟩
      have hy : s' + d' ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, h1⟩
      have hl0 : 0 ≤ d' / L := div_nonneg (by linarith) hL.le
      have hl1 : 0 ≤ (s' - s) / L := div_nonneg (by linarith) hL.le
      have hsum : (s' - s) / L + d' / L = 1 := by
        rw [← add_div, div_eq_one_iff_eq hLne]
      have c1 := Scalar.P_convexOn.2 hx hy hl1 hl0 hsum
      have c2 := Scalar.P_convexOn.2 hx hy hl0 hl1 (by linarith)
      simp only [smul_eq_mul] at c1 c2
      have a1 : (s' - s) / L * s + d' / L * (s' + d') = s + d' := by
        field_simp
        ring
      have a2 : d' / L * s + (s' - s) / L * (s' + d') = s' := by
        field_simp
        ring
      rw [a1] at c1
      rw [a2] at c2
      have : (s' - s) / L * Scalar.P s + d' / L * Scalar.P (s' + d') +
          (d' / L * Scalar.P s + (s' - s) / L * Scalar.P (s' + d')) =
          Scalar.P s + Scalar.P (s' + d') := by
        have e : (s' - s) / L + d' / L = 1 := hsum
        linear_combination (Scalar.P s + Scalar.P (s' + d')) * e
      linarith
  linarith

/-- `q * x` is at most the larger corner value. -/
theorem mul_le_max {q lo hi : ℚ} {x : ℝ} (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) :
    (q : ℝ) * x ≤ ((max (q * lo) (q * hi) : ℚ) : ℝ) := by
  rw [Rat.cast_max]
  push_cast
  rcases le_total 0 (q : ℝ) with hq | hq
  · exact (mul_le_mul_of_nonneg_left hhi hq).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_left hlo hq).trans (le_max_left _ _)

/-! ## Witness and derived quantities (all recomputed by the checker) -/

/-- Untrusted per-leaf witness data. -/
structure LDCert where
  pA0 : PtCert
  pA1 : PtCert
  pB0 : PtCert
  pB1 : PtCert
  m0 : ℚ
  hs : ℚ
  pM : PtCert
  pML : PtCert
  pMR : PtCert
  dHi : ℚ
  xa : ℚ
  pxa : PtCert
  xc : ℚ
  pxc : PtCert
  deriving Repr, DecidableEq

def C0Lo (B : Box) (c : LDCert) : ℚ := (Hlo B.alo c.pA0 + Hlo B.bhi c.pB1) / 2
def C0Hi (B : Box) (c : LDCert) : ℚ := (Hhi B.ahi c.pA1 + Hhi B.blo c.pB0) / 2
def sHi (B : Box) (c : LDCert) : ℚ := (C0Hi B c - EMIN) * (1 - B.t0)
def sLo (B : Box) (c : LDCert) : ℚ := (C0Lo B c - EMIN) * (1 - B.t1)
def mua (B : Box) (c : LDCert) : ℚ := (Hlo B.ahi c.pA1 - Hlo B.alo c.pA0) / (B.ahi - B.alo)
def mub (B : Box) (c : LDCert) : ℚ := (Hlo B.bhi c.pB1 - Hlo B.blo c.pB0) / (B.bhi - B.blo)
def sigL (c : LDCert) : ℚ := (Hhi c.m0 c.pM - Hlo (c.m0 - c.hs) c.pML) / c.hs
def sigR (c : LDCert) : ℚ := (Hlo (c.m0 + c.hs) c.pMR - Hhi c.m0 c.pM) / c.hs
def dconst (B : Box) (c : LDCert) (σ : ℚ) : ℚ :=
  Hhi c.m0 c.pM - σ * c.m0 - (Hlo B.alo c.pA0 - mua B c * B.alo) / 2 -
    (Hlo B.blo c.pB0 - mub B c * B.blo) / 2
def dca (B : Box) (c : LDCert) (σ : ℚ) : ℚ := (σ - mua B c) / 2
def dcb (B : Box) (c : LDCert) (σ : ℚ) : ℚ := (σ - mub B c) / 2
/-- Maximum over the box of the affine Jensen-gap majorant with secant slope `σ`. -/
def dmax (B : Box) (c : LDCert) (σ : ℚ) : ℚ :=
  dconst B c σ + max (dca B c σ * B.alo) (dca B c σ * B.ahi) +
    max (dcb B c σ * B.blo) (dcb B c σ * B.bhi)
def xUp (B : Box) (c : LDCert) : ℚ := sHi B c + c.dHi
def PU (c : LDCert) : ℚ := (1 - 2 * c.xa) * Jhi c.xa c.pxa
def PL (c : LDCert) : ℚ := (1 - 2 * c.xc) * Jlo c.xc c.pxc
def jLo (B : Box) (c : LDCert) : ℚ :=
  (B.blo - B.ahi) * (Jlo B.ahi c.pA1 - Jhi B.blo c.pB0) / 2
def lsLo (B : Box) (c : LDCert) : ℚ :=
  (B.blo - B.ahi) ^ 2 / (4 * (B.bhi * (1 - B.alo))) * (2 * sLo B c)
/-- Certified lower bound of `j + β d² s - [P(Δ+s) - P(s)]` on the box. -/
def margin (B : Box) (c : LDCert) : ℚ := jLo B c + lsLo B c - (PU c - PL c)

/-- The Boolean `logsum_direct` checker. Binds the box, every log/entropy/inverse enclosure,
the Jensen-gap majorant and the final comparison. -/
def check (B : Box) (c : LDCert) : Bool :=
  decide (0 < B.alo ∧ B.alo < B.ahi ∧ 2 * B.ahi ≤ 1 ∧ 1 ≤ 2 * B.blo ∧ B.blo < B.bhi ∧
    B.bhi < 1 ∧ 0 ≤ B.t0 ∧ B.t0 ≤ B.t1 ∧ B.t1 ≤ 1) &&
  checkPt B.alo c.pA0 && checkPt B.ahi c.pA1 && checkPt B.blo c.pB0 && checkPt B.bhi c.pB1 &&
  decide (0 < c.hs) &&
  checkPt c.m0 c.pM && checkPt (c.m0 - c.hs) c.pML && checkPt (c.m0 + c.hs) c.pMR &&
  checkPt c.xa c.pxa && checkPt c.xc c.pxc &&
  decide (EMIN ≤ C0Lo B c) &&
  decide (0 ≤ sHi B c) &&
  decide (0 ≤ c.dHi ∧ dmax B c (sigL c) ≤ c.dHi ∧ dmax B c (sigR c) ≤ c.dHi) &&
  decide (xUp B c < 1) &&
  decide (2 * c.xa ≤ 1 ∧ Hhi c.xa c.pxa ≤ 1 - xUp B c) &&
  decide (2 * c.xc ≤ 1 ∧ 1 - sHi B c ≤ Hlo c.xc c.pxc) &&
  decide (0 ≤ Jlo B.ahi c.pA1 - Jhi B.blo c.pB0) &&
  decide (0 ≤ margin B c)

/-! ## Soundness -/

/-- The affine Jensen-gap majorant is bounded by its corner maximum. -/
theorem delta_le_dmax (B : Box) (c : LDCert) (σ : ℚ) {a b : ℝ}
    (ha0 : (B.alo : ℝ) ≤ a) (ha1 : a ≤ (B.ahi : ℝ)) (hb0 : (B.blo : ℝ) ≤ b) (hb1 : b ≤ (B.bhi : ℝ))
    (hm : H ((a + b) / 2) ≤ (Hhi c.m0 c.pM : ℝ) + (σ : ℝ) * ((a + b) / 2 - (c.m0 : ℝ)))
    (hA : (Hlo B.alo c.pA0 : ℝ) + (mua B c : ℝ) * (a - B.alo) ≤ H a)
    (hB : (Hlo B.blo c.pB0 : ℝ) + (mub B c : ℝ) * (b - B.blo) ≤ H b) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤ (dmax B c σ : ℝ) := by
  have e1 := mul_le_max (q := dca B c σ) ha0 ha1
  have e2 := mul_le_max (q := dcb B c σ) hb0 hb1
  have ed : (dmax B c σ : ℝ) = (dconst B c σ : ℝ) +
      ((max (dca B c σ * B.alo) (dca B c σ * B.ahi) : ℚ) : ℝ) +
      ((max (dcb B c σ * B.blo) (dcb B c σ * B.bhi) : ℚ) : ℝ) := by
    unfold dmax; push_cast; ring
  have ec : (dconst B c σ : ℝ) = (Hhi c.m0 c.pM : ℝ) - (σ : ℝ) * (c.m0 : ℝ) -
      ((Hlo B.alo c.pA0 : ℝ) - (mua B c : ℝ) * (B.alo : ℝ)) / 2 -
      ((Hlo B.blo c.pB0 : ℝ) - (mub B c : ℝ) * (B.blo : ℝ)) / 2 := by
    unfold dconst; push_cast; ring
  have eca : (dca B c σ : ℝ) = ((σ : ℝ) - (mua B c : ℝ)) / 2 := by
    unfold dca; push_cast; ring
  have ecb : (dcb B c σ : ℝ) = ((σ : ℝ) - (mub B c : ℝ)) / 2 := by
    unfold dcb; push_cast; ring
  rw [eca] at e1
  rw [ecb] at e2
  rw [ed, ec]
  linarith only [hm, hA, hB, e1, e2]

theorem check_sound {B : Box} {c : LDCert} (hc : check B c = true) : Sem B := by
  intro k μ hbox
  unfold check at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hc
  obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6, _hB7, hB8, hB9, hpA0, hpA1, hpB0, hpB1, hhs, hpM, hpML,
    hpMR, hpxa, hpxc, hC0, hsHi0, hd0, hdL, hdR, hxUp, hxa1, hxa2, hxc1, hxc2, hJ,
    hfin⟩ := hc
  obtain ⟨ha0, ha1, hb0, hb1, hE0, hE1⟩ := hbox
  have hjen := law_gap_le_P μ
  -- casts of box facts
  have rB1 : (0 : ℝ) < B.alo := by exact_mod_cast hB1
  have rB2 : (B.alo : ℝ) < B.ahi := by exact_mod_cast hB2
  have rB3 : 2 * (B.ahi : ℝ) ≤ 1 := by exact_mod_cast hB3
  have rB4 : 1 ≤ 2 * (B.blo : ℝ) := by exact_mod_cast hB4
  have rB5 : (B.blo : ℝ) < B.bhi := by exact_mod_cast hB5
  have rB6 : (B.bhi : ℝ) < 1 := by exact_mod_cast hB6
  have rB8 : (B.t0 : ℝ) ≤ B.t1 := by exact_mod_cast hB8
  have rB9 : (B.t1 : ℝ) ≤ 1 := by exact_mod_cast hB9
  -- point enclosures
  obtain ⟨_, _, hA0l, hA0u, _, _⟩ := checkPt_bounds hpA0
  obtain ⟨_, _, hA1l, hA1u, hA1Jl, _⟩ := checkPt_bounds hpA1
  obtain ⟨_, _, hB0l, hB0u, _, hB0Ju⟩ := checkPt_bounds hpB0
  obtain ⟨_, _, hB1l, hB1u, _, _⟩ := checkPt_bounds hpB1
  obtain ⟨_, _, _, hMu, _, _⟩ := checkPt_bounds hpM
  obtain ⟨hmL0, _, hMLl, _, _, _⟩ := checkPt_bounds hpML
  obtain ⟨_, hmR1, hMRl, _, _, _⟩ := checkPt_bounds hpMR
  obtain ⟨hxa0, _, _, hxaHu, _, hxaJu⟩ := checkPt_bounds hpxa
  obtain ⟨hxc0, _, hxcHl, _, hxcJl, _⟩ := checkPt_bounds hpxc
  -- H at the law means
  have hHa_lo : H (B.alo : ℝ) ≤ H μ.a := H_mono_left rB1.le ha0 (by linarith only [ha1, rB3])
  have hHa_hi : H μ.a ≤ H (B.ahi : ℝ) := H_mono_left (by linarith only [rB1, ha0]) ha1
    (by linarith only [rB3])
  have hHb_lo : H (B.bhi : ℝ) ≤ H μ.b := H_anti_right (by linarith only [hb0, rB4]) hb1
    (by linarith only [rB6])
  have hHb_hi : H μ.b ≤ H (B.blo : ℝ) := H_anti_right (by linarith only [rB4]) hb0
    (by linarith only [hb1, rB6])
  have hC0lo : (C0Lo B c : ℝ) ≤ (H μ.a + H μ.b) / 2 := by
    have e : (C0Lo B c : ℝ) = ((Hlo B.alo c.pA0 : ℝ) + (Hlo B.bhi c.pB1 : ℝ)) / 2 := by
      unfold C0Lo; push_cast; ring
    rw [e]; linarith only [hA0l, hB1l, hHa_lo, hHb_lo]
  have hC0hi : (H μ.a + H μ.b) / 2 ≤ (C0Hi B c : ℝ) := by
    have e : (C0Hi B c : ℝ) = ((Hhi B.ahi c.pA1 : ℝ) + (Hhi B.blo c.pB0 : ℝ)) / 2 := by
      unfold C0Hi; push_cast; ring
    rw [e]; linarith only [hA1u, hB0u, hHa_hi, hHb_hi]
  have rC0 : (EMIN : ℝ) ≤ (C0Lo B c : ℝ) := by exact_mod_cast hC0
  -- deficit range
  have hdef := law_deficit_mem μ
  have hsHi : (H μ.a + H μ.b) / 2 - μ.meanEntropy ≤ (sHi B c : ℝ) := by
    have e : (sHi B c : ℝ) = ((C0Hi B c : ℝ) - EMIN) * (1 - B.t0) := by
      unfold sHi; push_cast; ring
    have h1 : ((H μ.a + H μ.b) / 2 - EMIN) * (1 - (B.t0 : ℝ)) ≤
        ((C0Hi B c : ℝ) - EMIN) * (1 - B.t0) :=
      mul_le_mul_of_nonneg_right (by linarith only [hC0hi]) (by linarith only [rB8, rB9])
    have h2 : ((H μ.a + H μ.b) / 2 - EMIN) * (1 - (B.t0 : ℝ)) =
        (H μ.a + H μ.b) / 2 - EMIN - (B.t0 : ℝ) * ((H μ.a + H μ.b) / 2 - EMIN) := by ring
    rw [e]; linarith only [h1, h2, hE0]
  have hsLo : (sLo B c : ℝ) ≤ (H μ.a + H μ.b) / 2 - μ.meanEntropy := by
    have e : (sLo B c : ℝ) = ((C0Lo B c : ℝ) - EMIN) * (1 - B.t1) := by
      unfold sLo; push_cast; ring
    have h1 : ((C0Lo B c : ℝ) - EMIN) * (1 - B.t1) ≤
        ((H μ.a + H μ.b) / 2 - EMIN) * (1 - (B.t1 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith only [hC0lo]) (by linarith only [rB9])
    have h2 : ((H μ.a + H μ.b) / 2 - EMIN) * (1 - (B.t1 : ℝ)) =
        (H μ.a + H μ.b) / 2 - EMIN - (B.t1 : ℝ) * ((H μ.a + H μ.b) / 2 - EMIN) := by ring
    rw [e]; linarith only [h1, h2, hE1]
  have hsLo0 : (0 : ℝ) ≤ (sLo B c : ℝ) := by
    have e : (sLo B c : ℝ) = ((C0Lo B c : ℝ) - EMIN) * (1 - B.t1) := by
      unfold sLo; push_cast; ring
    rw [e]; exact mul_nonneg (by linarith only [rC0]) (by linarith only [rB9])
  -- Jensen gap
  have hΔ0 : 0 ≤ H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 := μ.entropyDrop_nonneg
  have hchA : (Hlo B.alo c.pA0 : ℝ) + (mua B c : ℝ) * (μ.a - B.alo) ≤ H μ.a := by
    have hch := H_chord_lower (lo := (B.alo : ℝ)) (hi := (B.ahi : ℝ)) (x := μ.a)
      (HL0 := (Hlo B.alo c.pA0 : ℝ)) (HL1 := (Hlo B.ahi c.pA1 : ℝ)) rB1.le ha0 ha1
      (by linarith only [rB3]) hA0l hA1l
    have e : (mua B c : ℝ) =
        ((Hlo B.ahi c.pA1 : ℝ) - (Hlo B.alo c.pA0 : ℝ)) / ((B.ahi : ℝ) - B.alo) := by
      unfold mua; push_cast; ring
    rw [e]; exact hch
  have hchB : (Hlo B.blo c.pB0 : ℝ) + (mub B c : ℝ) * (μ.b - B.blo) ≤ H μ.b := by
    have hch := H_chord_lower (lo := (B.blo : ℝ)) (hi := (B.bhi : ℝ)) (x := μ.b)
      (HL0 := (Hlo B.blo c.pB0 : ℝ)) (HL1 := (Hlo B.bhi c.pB1 : ℝ))
      (by linarith only [rB4]) hb0 hb1 rB6.le hB0l hB1l
    have e : (mub B c : ℝ) =
        ((Hlo B.bhi c.pB1 : ℝ) - (Hlo B.blo c.pB0 : ℝ)) / ((B.bhi : ℝ) - B.blo) := by
      unfold mub; push_cast; ring
    rw [e]; exact hch
  have rhs : (0 : ℝ) < c.hs := by exact_mod_cast hhs
  have rmL0 : (0 : ℝ) ≤ (c.m0 : ℝ) - c.hs := by
    have : ((c.m0 - c.hs : ℚ) : ℝ) > 0 := by exact_mod_cast hmL0
    push_cast at this; linarith
  have rmR1 : (c.m0 : ℝ) + c.hs ≤ 1 := by
    have : ((c.m0 + c.hs : ℚ) : ℝ) < 1 := by exact_mod_cast hmR1
    push_cast at this; linarith
  have hMLl' : (Hlo (c.m0 - c.hs) c.pML : ℝ) ≤ H ((c.m0 : ℝ) - (c.hs : ℝ)) := by
    have := hMLl; push_cast at this; exact this
  have hMRl' : (Hlo (c.m0 + c.hs) c.pMR : ℝ) ≤ H ((c.m0 : ℝ) + (c.hs : ℝ)) := by
    have := hMRl; push_cast at this; exact this
  have hm0 : 0 ≤ (μ.a + μ.b) / 2 := by linarith only [ha0, hb0, rB1, rB4]
  have hm1 : (μ.a + μ.b) / 2 ≤ 1 := by linarith only [ha1, hb1, rB3, rB6]
  have hΔ : H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 ≤ (c.dHi : ℝ) := by
    rcases le_total (c.m0 : ℝ) ((μ.a + μ.b) / 2) with hge | hle
    · have hsl := H_leftslope_upper (lo := (c.m0 : ℝ)) (h := (c.hs : ℝ)) (x := (μ.a + μ.b) / 2)
        (HU0 := (Hhi c.m0 c.pM : ℝ)) (HLh := (Hlo (c.m0 - c.hs) c.pML : ℝ))
        rhs rmL0 hge hm1 hMu hMLl'
      have esig : (sigL c : ℝ) =
          ((Hhi c.m0 c.pM : ℝ) - (Hlo (c.m0 - c.hs) c.pML : ℝ)) / (c.hs : ℝ) := by
        unfold sigL; push_cast; ring
      have hm' : H ((μ.a + μ.b) / 2) ≤
          (Hhi c.m0 c.pM : ℝ) + (sigL c : ℝ) * ((μ.a + μ.b) / 2 - (c.m0 : ℝ)) := by
        rw [esig]; exact hsl
      have hdm := delta_le_dmax B c (sigL c) ha0 ha1 hb0 hb1 hm' hchA hchB
      have hdL' : (dmax B c (sigL c) : ℝ) ≤ c.dHi := by exact_mod_cast hdL
      linarith only [hdm, hdL']
    · have hsr := H_rightslope_upper (lo := (c.m0 : ℝ)) (h := (c.hs : ℝ)) (x := (μ.a + μ.b) / 2)
        (HU0 := (Hhi c.m0 c.pM : ℝ)) (HLh := (Hlo (c.m0 + c.hs) c.pMR : ℝ))
        rhs hm0 hle rmR1 hMu hMRl'
      have esig : (sigR c : ℝ) =
          ((Hlo (c.m0 + c.hs) c.pMR : ℝ) - (Hhi c.m0 c.pM : ℝ)) / (c.hs : ℝ) := by
        unfold sigR; push_cast; ring
      have hm' : H ((μ.a + μ.b) / 2) ≤
          (Hhi c.m0 c.pM : ℝ) + (sigR c : ℝ) * ((μ.a + μ.b) / 2 - (c.m0 : ℝ)) := by
        rw [esig]; exact hsr
      have hdm := delta_le_dmax B c (sigR c) ha0 ha1 hb0 hb1 hm' hchA hchB
      have hdR' : (dmax B c (sigR c) : ℝ) ≤ c.dHi := by exact_mod_cast hdR
      linarith only [hdm, hdR']
  -- P brackets
  have rdHi0 : (0 : ℝ) ≤ c.dHi := by exact_mod_cast hd0
  have rsHi0 : (0 : ℝ) ≤ sHi B c := by exact_mod_cast hsHi0
  have exUp : ((xUp B c : ℚ) : ℝ) = (sHi B c : ℝ) + c.dHi := by
    unfold xUp; push_cast; ring
  have rxUp : (sHi B c : ℝ) + c.dHi < 1 := by
    have : ((xUp B c : ℚ) : ℝ) < 1 := by exact_mod_cast hxUp
    linarith only [this, exUp]
  have hPU : Scalar.P ((sHi B c : ℝ) + c.dHi) ≤ (PU c : ℝ) := by
    have rxa1 : 2 * (c.xa : ℝ) ≤ 1 := by exact_mod_cast hxa1
    have rxa2 : (Hhi c.xa c.pxa : ℝ) ≤ 1 - ((xUp B c : ℚ) : ℝ) := by exact_mod_cast hxa2
    have hxa0' : (0 : ℝ) < c.xa := by exact_mod_cast hxa0
    have hH : H (c.xa : ℝ) ≤ 1 - ((sHi B c : ℝ) + c.dHi) := by
      rw [← exUp]; exact hxaHu.trans rxa2
    have hb := P_le_bracket (by linarith only [rsHi0, rdHi0]) rxUp hxa0'
      (by linarith only [rxa1]) hH
    have e : (PU c : ℝ) = (1 - 2 * (c.xa : ℝ)) * (Jhi c.xa c.pxa : ℝ) := by
      unfold PU; push_cast; ring
    have := mul_le_mul_of_nonneg_left hxaJu (by linarith only [rxa1] : (0 : ℝ) ≤ 1 - 2 * (c.xa : ℝ))
    rw [e]; linarith only [hb, this]
  have hPL : (PL c : ℝ) ≤ Scalar.P (sHi B c : ℝ) := by
    have rxc1 : 2 * (c.xc : ℝ) ≤ 1 := by exact_mod_cast hxc1
    have rxc2 : 1 - (sHi B c : ℝ) ≤ (Hlo c.xc c.pxc : ℝ) := by exact_mod_cast hxc2
    have hxc0' : (0 : ℝ) < c.xc := by exact_mod_cast hxc0
    have hb := P_ge_bracket rsHi0 (by linarith only [rxUp, rdHi0]) hxc0'
      (by linarith only [rxc1]) (rxc2.trans hxcHl)
    have e : (PL c : ℝ) = (1 - 2 * (c.xc : ℝ)) * (Jlo c.xc c.pxc : ℝ) := by
      unfold PL; push_cast; ring
    have := mul_le_mul_of_nonneg_left hxcJl (by linarith only [rxc1] : (0 : ℝ) ≤ 1 - 2 * (c.xc : ℝ))
    rw [e]; linarith only [hb, this]
  -- increment comparison
  have hinc := P_incr_mono hdef.1 hsHi hΔ0 hΔ rxUp
  have hsplit : H ((μ.a + μ.b) / 2) - μ.meanEntropy =
      ((H μ.a + H μ.b) / 2 - μ.meanEntropy) + (H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2) := by
    ring
  rw [hsplit] at hjen
  -- the log-sum cost floor
  have hfloor := μ.psiLogSumCostFloor_le_cost
  unfold InteriorLaw.psiLogSumCostFloor at hfloor
  have hab : μ.a ≤ μ.b := by linarith only [ha1, hb0, rB3, rB4]
  have hV : LogSum.V μ.a μ.b = μ.b * (1 - μ.a) := by
    simp only [LogSum.V, max_eq_right hab, min_eq_left hab]
  rw [hV] at hfloor
  have hJa : J (B.ahi : ℝ) ≤ J μ.a := J_antitone μ.a_interior.1 (by linarith only [rB3]) ha1
  have hJb : J μ.b ≤ J (B.blo : ℝ) := J_anti (by linarith only [rB4]) μ.b_interior.2 hb0
  have rJ : (0 : ℝ) ≤ (Jlo B.ahi c.pA1 : ℝ) - (Jhi B.blo c.pB0 : ℝ) := by
    have : ((Jlo B.ahi c.pA1 - Jhi B.blo c.pB0 : ℚ) : ℝ) ≥ 0 := by exact_mod_cast hJ
    push_cast at this; linarith only [this]
  have hIC : (jLo B c : ℝ) ≤ interiorCost μ.a μ.b := by
    unfold interiorCost
    have e : (jLo B c : ℝ) =
        ((B.blo : ℝ) - B.ahi) * ((Jlo B.ahi c.pA1 : ℝ) - (Jhi B.blo c.pB0 : ℝ)) / 2 := by
      unfold jLo; push_cast; ring
    rw [e]
    have hd : (B.blo : ℝ) - B.ahi ≤ μ.b - μ.a := by linarith only [ha1, hb0]
    have hJJ : (Jlo B.ahi c.pA1 : ℝ) - (Jhi B.blo c.pB0 : ℝ) ≤ J μ.a - J μ.b := by
      linarith only [hA1Jl, hB0Ju, hJa, hJb]
    have hprod := mul_le_mul hd hJJ rJ (by linarith only [ha1, hb0, rB3, rB4])
    linarith only [hprod]
  have hLS : (lsLo B c : ℝ) ≤
      (μ.a - μ.b) ^ 2 / (4 * (μ.b * (1 - μ.a))) * ((H μ.a - μ.e) + (H μ.b - μ.f)) := by
    have e : (lsLo B c : ℝ) =
        ((B.blo : ℝ) - B.ahi) ^ 2 / (4 * ((B.bhi : ℝ) * (1 - B.alo))) * (2 * (sLo B c : ℝ)) := by
      unfold lsLo; push_cast; ring
    rw [e]
    have hs2 : 2 * (sLo B c : ℝ) ≤ (H μ.a - μ.e) + (H μ.b - μ.f) := by
      have em : (H μ.a + H μ.b) / 2 - μ.meanEntropy = ((H μ.a - μ.e) + (H μ.b - μ.f)) / 2 := by
        unfold InteriorLaw.meanEntropy; ring
      linarith only [hsLo, em]
    have hd0 : 0 ≤ (B.blo : ℝ) - B.ahi := by linarith only [rB3, rB4]
    have hd : (B.blo : ℝ) - B.ahi ≤ μ.b - μ.a := by linarith only [ha1, hb0]
    have hnum : ((B.blo : ℝ) - B.ahi) ^ 2 ≤ (μ.a - μ.b) ^ 2 := by
      have : (μ.a - μ.b) ^ 2 = (μ.b - μ.a) ^ 2 := by ring
      rw [this]
      exact pow_le_pow_left₀ hd0 hd 2
    have hb0' : 0 < μ.b := μ.b_interior.1
    have ha1' : 0 < 1 - μ.a := by linarith only [μ.a_interior.2]
    have hden0 : 0 < 4 * (μ.b * (1 - μ.a)) := by positivity
    have hden : 4 * (μ.b * (1 - μ.a)) ≤ 4 * ((B.bhi : ℝ) * (1 - B.alo)) := by
      have h1 : μ.b * (1 - μ.a) ≤ (B.bhi : ℝ) * (1 - μ.a) :=
        mul_le_mul_of_nonneg_right hb1 ha1'.le
      have h2 : (B.bhi : ℝ) * (1 - μ.a) ≤ (B.bhi : ℝ) * (1 - B.alo) :=
        mul_le_mul_of_nonneg_left (by linarith only [ha0]) (by linarith only [hb0, rB4, hb1])
      linarith only [h1, h2]
    have hq : ((B.blo : ℝ) - B.ahi) ^ 2 / (4 * ((B.bhi : ℝ) * (1 - B.alo))) ≤
        (μ.a - μ.b) ^ 2 / (4 * (μ.b * (1 - μ.a))) :=
      div_le_div₀ (sq_nonneg _) hnum hden0 hden
    have hq0 : 0 ≤ ((B.blo : ℝ) - B.ahi) ^ 2 / (4 * ((B.bhi : ℝ) * (1 - B.alo))) := by
      apply div_nonneg (sq_nonneg _)
      linarith only [hden0, hden]
    have hs20 : 0 ≤ 2 * (sLo B c : ℝ) := by linarith only [hsLo0]
    exact mul_le_mul hq hs2 hs20 (hq0.trans hq)
  -- final comparison
  have rfin : (0 : ℝ) ≤ (margin B c : ℝ) := by exact_mod_cast hfin
  have emargin : (margin B c : ℝ) = (jLo B c : ℝ) + (lsLo B c : ℝ) - ((PU c : ℝ) - (PL c : ℝ)) := by
    unfold margin; push_cast; ring
  linarith only [hjen, hinc, hPU, hPL, hIC, hLS, hfloor, rfin, emargin]

/-! ## Binding to archived `(u, v, t)` leaves -/

/-- Per-leaf acceptance: witness valid and its box encloses the archived leaf's physical image. -/
def checkLeaf (p : List ℕ) (B : Box) (c : LDCert) : Bool :=
  imageCheck (uvtBox p) B && check B c

theorem checkLeaf_sound {p : List ℕ} {B : Box} {c : LDCert} (h : checkLeaf p B c = true) :
    SemUVT (uvtBox p) := by
  unfold checkLeaf at h
  rw [Bool.and_eq_true] at h
  exact imageCheck_sound h.1 (check_sound h.2)

/-- Law-level production form: under the psi branch at the parent, `μ.gap ≤ μ.cost`. -/
theorem checkLeaf_gap_le_cost {p : List ℕ} {B : Box} {c : LDCert} (h : checkLeaf p B c = true)
    (k : ℕ) (μ : InteriorLaw (Fin k)) (hin : InUVT (uvtBox p) μ.a μ.b μ.meanEntropy)
    (hact : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost :=
  (hybrid_gap_le_psi hact).trans (checkLeaf_sound h k μ hin)

end CKLaneM04

end


