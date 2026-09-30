-- Prove2me | Definitions.Def_CK_CKLaneD_Checker
-- name    : CK_CKLaneD_Checker
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:07:18.27667+00:00
-- url     : https://prove2.me/theorems/adb0629e-1d07-406f-9295-36e20fe388da
-- title:
--   Courtade–Kumar proof module `CKLaneD.Checker` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneD.Checker` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneD.Checker` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneD.Checker (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneD/Checker.lean)

import Definitions.Def_CK_CKLaneD_Analytic

-- ===== source module CKLaneD.Checker =====
section

/-!
# Lane D: Boolean endpoint checker and its unconditional semantic soundness

`Sem B` is the law-level Bellman statement for the psi candidate on the exact physical box
`B` (means `a ∈ [alo,ahi]`, `b ∈ [blo,bhi]`, mean entropy between the `t0` and `t1`
entropy levels `EMIN + t (C0 - EMIN)`, `C0 = (H a + H b)/2`).

`checkCell B c = true → Sem B` with no other hypotheses (`checkCell_sound`).
-/

namespace CKLaneD

open GeneralCK

/-- Entropy floor of the archived outer-opposite parametrization. -/
def EMIN : ℚ := 1 / 1000000

/-- A rational box in `(a, b, t)` coordinates. -/
structure Box where
  alo : ℚ
  ahi : ℚ
  blo : ℚ
  bhi : ℚ
  t0 : ℚ
  t1 : ℚ
  deriving Repr, DecidableEq

/-- `(a, b, E)` lies in the physical box `B`. -/
def InBox (B : Box) (a b E : ℝ) : Prop :=
  (B.alo : ℝ) ≤ a ∧ a ≤ (B.ahi : ℝ) ∧ (B.blo : ℝ) ≤ b ∧ b ≤ (B.bhi : ℝ) ∧
    (EMIN : ℝ) + (B.t0 : ℝ) * ((H a + H b) / 2 - (EMIN : ℝ)) ≤ E ∧
    E ≤ (EMIN : ℝ) + (B.t1 : ℝ) * ((H a + H b) / 2 - (EMIN : ℝ))

/-- The semantic Bellman statement (psi candidate) at law level on the box `B`. -/
def Sem (B : Box) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), InBox B μ.a μ.b μ.meanEntropy →
    candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.cost

/-- Untrusted per-cell certificate data. -/
structure CellCert where
  v : ℚ
  pv : PtCert
  pA0 : PtCert
  pA1 : PtCert
  pB0 : PtCert
  pB1 : PtCert
  hm : ℚ
  pM0 : PtCert
  pM1 : PtCert
  pMh : PtCert
  pLo : ℚ
  pHi : ℚ
  xa : ℚ
  pxa : PtCert
  xb : ℚ
  pxb : PtCert
  sL : ℚ
  useXc : Bool
  xc : ℚ
  pxc : PtCert
  deriving Repr, DecidableEq

/-! ## Derived quantities (all recomputed by the checker) -/

def mlo (B : Box) : ℚ := (B.alo + B.blo) / 2
def mhi (B : Box) : ℚ := (B.ahi + B.bhi) / 2
def C0Lo (B : Box) (c : CellCert) : ℚ := (Hlo B.alo c.pA0 + Hlo B.bhi c.pB1) / 2
def C0Hi (B : Box) (c : CellCert) : ℚ := (Hhi B.ahi c.pA1 + Hhi B.blo c.pB0) / 2
def ELo (B : Box) (c : CellCert) : ℚ := EMIN + B.t0 * (C0Lo B c - EMIN)
def EHi (B : Box) (c : CellCert) : ℚ := EMIN + B.t1 * (C0Hi B c - EMIN)
def HmLo (B : Box) (c : CellCert) : ℚ := min (Hlo (mlo B) c.pM0) (Hlo (mhi B) c.pM1)
def numM (B : Box) (c : CellCert) : ℚ := (Hhi (mlo B) c.pM0 - Hlo (mlo B - c.hm) c.pMh) / c.hm
def HmHi (B : Box) (c : CellCert) : ℚ := Hhi (mlo B) c.pM0 + max 0 (numM B c * (mhi B - mlo B))
def PuLo (c : CellCert) : ℚ := (1 - 2 * c.xa) * Jhi c.xa c.pxa
def PuHi (c : CellCert) : ℚ := (1 - 2 * c.xb) * Jhi c.xb c.pxb
def PlS (c : CellCert) : ℚ := if c.useXc then (1 - 2 * c.xc) * Jlo c.xc c.pxc else 4 * c.sL
def sig (c : CellCert) : ℚ := (PuHi c - PuLo c) / (c.pHi - c.pLo)
def nLo (c : CellCert) : ℚ := -(c.pv.cx.hi + c.pv.cy.hi)
def nHi (c : CellCert) : ℚ := -(c.pv.cx.lo + c.pv.cy.lo)
def baseK (c : CellCert) : ℚ := (1 - 2 * c.v) ^ 2 / (2 * c.v * (1 - c.v))
def Klo (c : CellCert) : ℚ := baseK c / nHi c
def Khi (c : CellCert) : ℚ := baseK c / nLo c
def ccLo (c : CellCert) : ℚ := Jlo c.v c.pv + 2 * Klo c * Hlo c.v c.pv / (1 - 2 * c.v)
def kap (c : CellCert) : ℚ := sig c - 2 * Khi c - 4
def tstar (B : Box) (c : CellCert) : ℚ := if 0 ≤ kap c then B.t0 else B.t1
def gam (B : Box) (c : CellCert) : ℚ := (kap c * tstar B c + 4) / 2
def mua (B : Box) (c : CellCert) : ℚ := (Hlo B.ahi c.pA1 - Hlo B.alo c.pA0) / (B.ahi - B.alo)
def mub (B : Box) (c : CellCert) : ℚ := (Hlo B.bhi c.pB1 - Hlo B.blo c.pB0) / (B.bhi - B.blo)
def constT (c : CellCert) : ℚ := -PuLo c + sig c * c.pLo + PlS c - 4 * c.sL
def ca (B : Box) (c : CellCert) : ℚ := -ccLo c + gam B c * mua B c - sig c * numM B c / 2
def cb (B : Box) (c : CellCert) : ℚ := ccLo c + gam B c * mub B c - sig c * numM B c / 2
def c0 (B : Box) (c : CellCert) : ℚ :=
  kap c * EMIN * (1 - tstar B c) +
    gam B c * (Hlo B.alo c.pA0 - mua B c * B.alo + Hlo B.blo c.pB0 - mub B c * B.blo) -
    sig c * (Hhi (mlo B) c.pM0 - numM B c * mlo B) + constT c
def finalVal (B : Box) (c : CellCert) : ℚ :=
  c0 B c + min (ca B c * B.alo) (ca B c * B.ahi) + min (cb B c * B.blo) (cb B c * B.bhi)

/-- Optional lower bracket for `P sL`. -/
def xcOK (c : CellCert) : Bool :=
  if c.useXc then checkPt c.xc c.pxc && decide (2 * c.xc ≤ 1 ∧ 1 - c.sL ≤ Hlo c.xc c.pxc)
  else true

/-- The Boolean cell checker. Binds the box, every log/entropy/inverse/contact enclosure,
the plane coefficients and the final affine certificate. -/
def checkCell (B : Box) (c : CellCert) : Bool :=
  decide (0 < B.alo ∧ B.alo ≤ B.ahi ∧ 2 * B.ahi ≤ 1 ∧ 1 ≤ 2 * B.blo ∧ B.blo ≤ B.bhi ∧
    B.bhi < 1 ∧ 0 ≤ B.t0 ∧ B.t0 ≤ B.t1 ∧ B.t1 ≤ 1) &&
  decide (0 < c.hm ∧ c.hm < mlo B) &&
  checkPt B.alo c.pA0 &&
  checkPt B.ahi c.pA1 &&
  checkPt B.blo c.pB0 &&
  checkPt B.bhi c.pB1 &&
  checkPt (mlo B) c.pM0 &&
  checkPt (mhi B) c.pM1 &&
  checkPt (mlo B - c.hm) c.pMh &&
  checkPt c.xa c.pxa &&
  checkPt c.xb c.pxb &&
  checkPt c.v c.pv &&
  xcOK c &&
  decide (EMIN < C0Lo B c) &&
  decide (0 ≤ c.pLo ∧ c.pLo ≤ HmLo B c - EHi B c ∧ HmHi B c - ELo B c ≤ c.pHi ∧
      c.pLo < c.pHi ∧ c.pHi < 1) &&
  decide (2 * c.xa ≤ 1 ∧ Hhi c.xa c.pxa ≤ 1 - c.pLo) &&
  decide (2 * c.xb ≤ 1 ∧ Hhi c.xb c.pxb ≤ 1 - c.pHi) &&
  decide (0 ≤ c.sL ∧ c.sL ≤ (C0Lo B c - EMIN) * (1 - B.t1)) &&
  decide (0 ≤ sig c) &&
  decide (2 * c.v < 1) &&
  decide (0 < nLo c) &&
  decide (0 ≤ Hlo c.v c.pv) &&
  decide (0 ≤ gam B c) &&
  decide (0 ≤ finalVal B c)

/-! ## Soundness -/

theorem chord_mono {f0 f1 g0 g1 Δ x : ℝ} (hΔ : 0 < Δ) (hx0 : 0 ≤ x) (hx1 : x ≤ Δ)
    (h0 : f0 ≤ g0) (h1 : f1 ≤ g1) :
    f0 + (f1 - f0) / Δ * x ≤ g0 + (g1 - g0) / Δ * x := by
  have ht0 : 0 ≤ x / Δ := div_nonneg hx0 hΔ.le
  have ht1 : x / Δ ≤ 1 := by rw [div_le_one hΔ]; exact hx1
  have e1 : f0 + (f1 - f0) / Δ * x = (1 - x / Δ) * f0 + (x / Δ) * f1 := by
    field_simp; ring
  have e2 : g0 + (g1 - g0) / Δ * x = (1 - x / Δ) * g0 + (x / Δ) * g1 := by
    field_simp; ring
  rw [e1, e2]
  have := mul_le_mul_of_nonneg_left h0 (by linarith : (0 : ℝ) ≤ 1 - x / Δ)
  have := mul_le_mul_of_nonneg_left h1 ht0
  linarith

theorem min_mul_le {q lo hi : ℚ} {x : ℝ} (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) :
    ((min (q * lo) (q * hi) : ℚ) : ℝ) ≤ (q : ℝ) * x := by
  rw [Rat.cast_min]
  push_cast
  rcases le_total 0 (q : ℝ) with hq | hq
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hlo hq)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hhi hq)

theorem xcOK_sound {c : CellCert} (hx : xcOK c = true) (hs0 : 0 ≤ (c.sL : ℝ))
    (hs1 : (c.sL : ℝ) < 1) : (PlS c : ℝ) ≤ Scalar.P (c.sL : ℝ) := by
  unfold xcOK at hx
  unfold PlS
  split_ifs at hx ⊢ with hu
  · rw [Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨hp, h2, h3⟩ := hx
    obtain ⟨hx0, _, hHl, _, hJl, _⟩ := checkPt_bounds hp
    have hx0' : (0 : ℝ) < (c.xc : ℝ) := by exact_mod_cast hx0
    have h2' : 2 * (c.xc : ℝ) ≤ 1 := by exact_mod_cast h2
    have h3' : 1 - (c.sL : ℝ) ≤ (Hlo c.xc c.pxc : ℝ) := by exact_mod_cast h3
    have hb := P_ge_bracket hs0 hs1 hx0' (by linarith) (h3'.trans hHl)
    push_cast
    have hJ0 : 0 ≤ 1 - 2 * (c.xc : ℝ) := by linarith
    have := mul_le_mul_of_nonneg_left hJl hJ0
    linarith
  · push_cast
    exact Scalar.four_mul_le_P hs0 hs1

theorem checkCell_sound {B : Box} {c : CellCert} (h : checkCell B c = true) : Sem B := by
  intro k μ hbox
  unfold checkCell at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8, hB9, hhm0, hhm1, hpA0, hpA1, hpB0, hpB1,
    hpM0, hpM1, hpMh, hpxa, hpxb, hpv, hxc, hC0, hpL0, hpL1, hpH1, hpLH, hpH2,
    hxa1, hxa2, hxb1, hxb2, hsL0, hsL1, hsig, hv2, hnLo, hHv, hgam, hfin⟩ := h
  obtain ⟨ha0, ha1, hb0, hb1, hE0, hE1⟩ := hbox
  have hjen := law_gap_le_P μ
  -- casts of box facts
  have rB1 : (0 : ℝ) < B.alo := by exact_mod_cast hB1
  have rB3 : 2 * (B.ahi : ℝ) ≤ 1 := by exact_mod_cast hB3
  have rB4 : 1 ≤ 2 * (B.blo : ℝ) := by exact_mod_cast hB4
  have rB6 : (B.bhi : ℝ) < 1 := by exact_mod_cast hB6
  have rB7 : (0 : ℝ) ≤ B.t0 := by exact_mod_cast hB7
  have rB8 : (B.t0 : ℝ) ≤ B.t1 := by exact_mod_cast hB8
  have rB9 : (B.t1 : ℝ) ≤ 1 := by exact_mod_cast hB9
  -- point enclosures
  obtain ⟨_, _, hA0l, hA0u, _, _⟩ := checkPt_bounds hpA0
  obtain ⟨_, _, hA1l, hA1u, _, _⟩ := checkPt_bounds hpA1
  obtain ⟨_, _, hB0l, hB0u, _, _⟩ := checkPt_bounds hpB0
  obtain ⟨_, _, hB1l, hB1u, _, _⟩ := checkPt_bounds hpB1
  obtain ⟨_, _, hM0l, hM0u, _, _⟩ := checkPt_bounds hpM0
  obtain ⟨_, _, hM1l, hM1u, _, _⟩ := checkPt_bounds hpM1
  obtain ⟨_, _, hMhl, hMhu, _, _⟩ := checkPt_bounds hpMh
  obtain ⟨hxa0, _, _, hxaHu, _, hxaJu⟩ := checkPt_bounds hpxa
  obtain ⟨hxb0, _, _, hxbHu, _, hxbJu⟩ := checkPt_bounds hpxb
  obtain ⟨hv0, hv1, hvHl, _, hvJl, _⟩ := checkPt_bounds hpv
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
      unfold C0Lo; push_cast; try ring
    rw [e]; linarith only [hA0l, hB1l, hHa_lo, hHb_lo]
  have hC0hi : (H μ.a + H μ.b) / 2 ≤ (C0Hi B c : ℝ) := by
    have e : (C0Hi B c : ℝ) = ((Hhi B.ahi c.pA1 : ℝ) + (Hhi B.blo c.pB0 : ℝ)) / 2 := by
      unfold C0Hi; push_cast; try ring
    rw [e]; linarith only [hA1u, hB0u, hHa_hi, hHb_hi]
  have rC0 : (EMIN : ℝ) < (C0Lo B c : ℝ) := by exact_mod_cast hC0
  -- entropy range
  have hElo : (ELo B c : ℝ) ≤ μ.meanEntropy := by
    have e : (ELo B c : ℝ) = (EMIN : ℝ) + (B.t0 : ℝ) * ((C0Lo B c : ℝ) - EMIN) := by
      unfold ELo; push_cast; try ring
    have := mul_le_mul_of_nonneg_left
      (show (C0Lo B c : ℝ) - EMIN ≤ (H μ.a + H μ.b) / 2 - EMIN by linarith only [hC0lo]) rB7
    rw [e]; linarith only [this, hE0]
  have hEhi : μ.meanEntropy ≤ (EHi B c : ℝ) := by
    have e : (EHi B c : ℝ) = (EMIN : ℝ) + (B.t1 : ℝ) * ((C0Hi B c : ℝ) - EMIN) := by
      unfold EHi; push_cast; try ring
    have := mul_le_mul_of_nonneg_left
      (show (H μ.a + H μ.b) / 2 - EMIN ≤ (C0Hi B c : ℝ) - EMIN by linarith only [hC0hi])
      (rB7.trans rB8)
    rw [e]; linarith only [this, hE1]
  -- the parent mean
  have emlo : ((mlo B : ℚ) : ℝ) = ((B.alo : ℝ) + (B.blo : ℝ)) / 2 := by
    unfold mlo; push_cast; try ring
  have emhi : ((mhi B : ℚ) : ℝ) = ((B.ahi : ℝ) + (B.bhi : ℝ)) / 2 := by
    unfold mhi; push_cast; try ring
  have hmlo : ((mlo B : ℚ) : ℝ) ≤ (μ.a + μ.b) / 2 := by rw [emlo]; linarith only [ha0, hb0]
  have hmhi : (μ.a + μ.b) / 2 ≤ ((mhi B : ℚ) : ℝ) := by rw [emhi]; linarith only [ha1, hb1]
  have rhm0 : (0 : ℝ) < c.hm := by exact_mod_cast hhm0
  have rhm1 : (c.hm : ℝ) < (mlo B : ℝ) := by exact_mod_cast hhm1
  have rmhi1 : ((mhi B : ℚ) : ℝ) ≤ 1 := by rw [emhi]; linarith only [rB3, rB6]
  have rmlo0 : (0 : ℝ) ≤ (mlo B : ℝ) := by linarith only [rhm0, rhm1]
  have hHm_lo : (HmLo B c : ℝ) ≤ H ((μ.a + μ.b) / 2) := by
    have hc := H_chord_lower (lo := (mlo B : ℝ)) (hi := (mhi B : ℝ)) (x := (μ.a + μ.b) / 2)
      (HL0 := (HmLo B c : ℝ)) (HL1 := (HmLo B c : ℝ)) rmlo0 hmlo hmhi rmhi1
      (by unfold HmLo; rw [Rat.cast_min]; exact (min_le_left _ _).trans hM0l)
      (by unfold HmLo; rw [Rat.cast_min]; exact (min_le_right _ _).trans hM1l)
    calc (HmLo B c : ℝ) = (HmLo B c : ℝ) + ((HmLo B c : ℝ) - (HmLo B c : ℝ)) /
          ((mhi B : ℝ) - (mlo B : ℝ)) * ((μ.a + μ.b) / 2 - (mlo B : ℝ)) := by ring
      _ ≤ H ((μ.a + μ.b) / 2) := hc
  have hMhl' : (Hlo (mlo B - c.hm) c.pMh : ℝ) ≤ H ((mlo B : ℝ) - (c.hm : ℝ)) := by
    have := hMhl; push_cast at this; exact this
  have enum : (numM B c : ℝ) =
      ((Hhi (mlo B) c.pM0 : ℝ) - (Hlo (mlo B - c.hm) c.pMh : ℝ)) / (c.hm : ℝ) := by
    unfold numM; push_cast; try ring
  have hHm_tan : H ((μ.a + μ.b) / 2) ≤
      (Hhi (mlo B) c.pM0 : ℝ) + (numM B c : ℝ) * ((μ.a + μ.b) / 2 - (mlo B : ℝ)) := by
    have hc := H_leftslope_upper (lo := (mlo B : ℝ)) (h := (c.hm : ℝ)) (x := (μ.a + μ.b) / 2)
      (HU0 := (Hhi (mlo B) c.pM0 : ℝ)) (HLh := (Hlo (mlo B - c.hm) c.pMh : ℝ))
      rhm0 (by linarith only [rhm1]) hmlo (by linarith only [hmhi, rmhi1]) hM0u hMhl'
    rw [enum]; exact hc
  have hHm_hi : H ((μ.a + μ.b) / 2) ≤ (HmHi B c : ℝ) := by
    have hmm : 0 ≤ (μ.a + μ.b) / 2 - (mlo B : ℝ) := by linarith only [hmlo]
    have hmm2 : (μ.a + μ.b) / 2 - (mlo B : ℝ) ≤ (mhi B : ℝ) - (mlo B : ℝ) := by
      linarith only [hmhi]
    have hmax : (numM B c : ℝ) * ((μ.a + μ.b) / 2 - (mlo B : ℝ)) ≤
        max 0 ((numM B c : ℝ) * ((mhi B : ℝ) - (mlo B : ℝ))) := by
      rcases le_total 0 (numM B c : ℝ) with hn | hn
      · exact (mul_le_mul_of_nonneg_left hmm2 hn).trans (le_max_right _ _)
      · exact (mul_nonpos_iff.mpr (Or.inr ⟨hn, hmm⟩)).trans (le_max_left _ _)
    have e : (HmHi B c : ℝ) = (Hhi (mlo B) c.pM0 : ℝ) +
        max 0 ((numM B c : ℝ) * ((mhi B : ℝ) - (mlo B : ℝ))) := by
      unfold HmHi; push_cast; try ring
    rw [e]; linarith only [hHm_tan, hmax]
  -- information range
  have rpL0 : (0 : ℝ) ≤ c.pLo := by exact_mod_cast hpL0
  have rpL1 : (c.pLo : ℝ) ≤ (HmLo B c : ℝ) - (EHi B c : ℝ) := by exact_mod_cast hpL1
  have rpH1 : (HmHi B c : ℝ) - (ELo B c : ℝ) ≤ c.pHi := by exact_mod_cast hpH1
  have rpLH : (c.pLo : ℝ) < c.pHi := by exact_mod_cast hpLH
  have rpH2 : (c.pHi : ℝ) < 1 := by exact_mod_cast hpH2
  have hIlo : (c.pLo : ℝ) ≤ H ((μ.a + μ.b) / 2) - μ.meanEntropy := by
    linarith only [rpL1, hHm_lo, hEhi]
  have hIhi : H ((μ.a + μ.b) / 2) - μ.meanEntropy ≤ (c.pHi : ℝ) := by
    linarith only [rpH1, hHm_hi, hElo]
  -- deficit range
  have hdef := law_deficit_mem μ
  have rsL0 : (0 : ℝ) ≤ c.sL := by exact_mod_cast hsL0
  have rsL1 : (c.sL : ℝ) ≤ ((C0Lo B c : ℝ) - EMIN) * (1 - B.t1) := by exact_mod_cast hsL1
  have hsL : (c.sL : ℝ) ≤ (H μ.a + H μ.b) / 2 - μ.meanEntropy := by
    have h1 : ((C0Lo B c : ℝ) - EMIN) * (1 - B.t1) ≤
        ((H μ.a + H μ.b) / 2 - EMIN) * (1 - B.t1) :=
      mul_le_mul_of_nonneg_right (by linarith only [hC0lo]) (by linarith only [rB9])
    have h2 : ((H μ.a + H μ.b) / 2 - EMIN) * (1 - (B.t1 : ℝ)) =
        (H μ.a + H μ.b) / 2 - EMIN - (B.t1 : ℝ) * ((H μ.a + H μ.b) / 2 - EMIN) := by ring
    linarith only [rsL1, h1, h2, hE1]
  -- P upper bound on the information side
  have rxa1 : 2 * (c.xa : ℝ) ≤ 1 := by exact_mod_cast hxa1
  have rxa2 : (Hhi c.xa c.pxa : ℝ) ≤ 1 - c.pLo := by exact_mod_cast hxa2
  have rxb1 : 2 * (c.xb : ℝ) ≤ 1 := by exact_mod_cast hxb1
  have rxb2 : (Hhi c.xb c.pxb : ℝ) ≤ 1 - c.pHi := by exact_mod_cast hxb2
  have hxa0' : (0 : ℝ) < c.xa := by exact_mod_cast hxa0
  have hxb0' : (0 : ℝ) < c.xb := by exact_mod_cast hxb0
  have hPLo : Scalar.P (c.pLo : ℝ) ≤ (PuLo c : ℝ) := by
    have hb := P_le_bracket rpL0 (by linarith only [rpLH, rpH2]) hxa0' (by linarith only [rxa1])
      (hxaHu.trans rxa2)
    have e : (PuLo c : ℝ) = (1 - 2 * (c.xa : ℝ)) * (Jhi c.xa c.pxa : ℝ) := by
      unfold PuLo; push_cast; try ring
    have := mul_le_mul_of_nonneg_left hxaJu
      (by linarith only [rxa1] : (0 : ℝ) ≤ 1 - 2 * (c.xa : ℝ))
    rw [e]; linarith only [hb, this]
  have hPHi : Scalar.P (c.pHi : ℝ) ≤ (PuHi c : ℝ) := by
    have hb := P_le_bracket (by linarith only [rpL0, rpLH]) rpH2 hxb0' (by linarith only [rxb1])
      (hxbHu.trans rxb2)
    have e : (PuHi c : ℝ) = (1 - 2 * (c.xb : ℝ)) * (Jhi c.xb c.pxb : ℝ) := by
      unfold PuHi; push_cast; try ring
    have := mul_le_mul_of_nonneg_left hxbJu
      (by linarith only [rxb1] : (0 : ℝ) ≤ 1 - 2 * (c.xb : ℝ))
    rw [e]; linarith only [hb, this]
  have esig : (sig c : ℝ) = ((PuHi c : ℝ) - (PuLo c : ℝ)) / ((c.pHi : ℝ) - c.pLo) := by
    unfold sig; push_cast; try ring
  have hPI : Scalar.P (H ((μ.a + μ.b) / 2) - μ.meanEntropy) ≤
      (PuLo c : ℝ) + (sig c : ℝ) * (H ((μ.a + μ.b) / 2) - μ.meanEntropy - c.pLo) := by
    have hch := P_chord rpL0 hIlo hIhi rpH2 rpLH
    have hm2 := chord_mono (f0 := Scalar.P (c.pLo : ℝ)) (f1 := Scalar.P (c.pHi : ℝ))
      (g0 := (PuLo c : ℝ)) (g1 := (PuHi c : ℝ)) (Δ := (c.pHi : ℝ) - c.pLo)
      (x := H ((μ.a + μ.b) / 2) - μ.meanEntropy - c.pLo)
      (by linarith only [rpLH]) (by linarith only [hIlo]) (by linarith only [hIhi]) hPLo hPHi
    rw [esig]; exact hch.trans hm2
  -- P lower bound on the deficit side
  have hPs : (PlS c : ℝ) + 4 * ((H μ.a + H μ.b) / 2 - μ.meanEntropy - c.sL) ≤
      Scalar.P ((H μ.a + H μ.b) / 2 - μ.meanEntropy) := by
    have hinc := Scalar.P_increment_lower rsL0 hdef.2 hsL
    have hbr := xcOK_sound hxc rsL0 (by linarith only [hsL, hdef.2])
    linarith only [hinc, hbr]
  -- the explicit plane
  have rv2 : 2 * (c.v : ℝ) < 1 := by exact_mod_cast hv2
  have hv0' : (0 : ℝ) < c.v := by exact_mod_cast hv0
  have hplane := plane_cost_lower μ hv0' (by linarith only [rv2] : (c.v : ℝ) < 1 / 2)
  have hpv' := hpv
  unfold checkPt at hpv'
  rw [Bool.and_eq_true] at hpv'
  have hlogs := checkLogCert_sound hpv'.1
  have hlogs2 := checkLogCert_sound hpv'.2
  push_cast at hlogs2
  have hv1' : (0 : ℝ) < 1 - (c.v : ℝ) := by linarith only [rv2, hv0']
  have hlogm : Real.log ((c.v : ℝ) * (1 - c.v)) =
      Real.log (c.v : ℝ) + Real.log (1 - (c.v : ℝ)) :=
    Real.log_mul hv0'.ne' hv1'.ne'
  have rnLo : (0 : ℝ) < (nLo c : ℝ) := by exact_mod_cast hnLo
  have hnlo : (nLo c : ℝ) ≤ -Real.log ((c.v : ℝ) * (1 - c.v)) := by
    have e : (nLo c : ℝ) = -((c.pv.cx.hi : ℝ) + (c.pv.cy.hi : ℝ)) := by
      unfold nLo; push_cast; try ring
    rw [e, hlogm]; linarith only [hlogs.2, hlogs2.2]
  have hnhi : -Real.log ((c.v : ℝ) * (1 - c.v)) ≤ (nHi c : ℝ) := by
    have e : (nHi c : ℝ) = -((c.pv.cx.lo : ℝ) + (c.pv.cy.lo : ℝ)) := by
      unfold nHi; push_cast; try ring
    rw [e, hlogm]; linarith only [hlogs.1, hlogs2.1]
  have ebase : (baseK c : ℝ) = (1 - 2 * (c.v : ℝ)) ^ 2 / (2 * (c.v : ℝ) * (1 - (c.v : ℝ))) := by
    unfold baseK; push_cast; try ring
  have hbase : (0 : ℝ) < (baseK c : ℝ) := by
    rw [ebase]
    have : (0 : ℝ) < 1 - 2 * (c.v : ℝ) := by linarith only [rv2]
    positivity
  have hnpos : 0 < -Real.log ((c.v : ℝ) * (1 - c.v)) := rnLo.trans_le hnlo
  have hK_eq : planeK (c.v : ℝ) = (baseK c : ℝ) / (-Real.log ((c.v : ℝ) * (1 - c.v))) := by
    unfold planeK; rw [ebase, div_div]
  have eKhi : (Khi c : ℝ) = (baseK c : ℝ) / (nLo c : ℝ) := by
    unfold Khi; push_cast; try ring
  have eKlo : (Klo c : ℝ) = (baseK c : ℝ) / (nHi c : ℝ) := by
    unfold Klo; push_cast; try ring
  have rnHi : (0 : ℝ) < (nHi c : ℝ) := hnpos.trans_le hnhi
  have hKhi : planeK (c.v : ℝ) ≤ (Khi c : ℝ) := by
    rw [hK_eq, eKhi, div_le_div_iff₀ hnpos rnLo]
    exact mul_le_mul_of_nonneg_left hnlo hbase.le
  have hKlo : (Klo c : ℝ) ≤ planeK (c.v : ℝ) := by
    rw [hK_eq, eKlo, div_le_div_iff₀ rnHi hnpos]
    exact mul_le_mul_of_nonneg_left hnhi hbase.le
  have hKlo0 : (0 : ℝ) ≤ (Klo c : ℝ) := by
    rw [eKlo]; exact div_nonneg hbase.le rnHi.le
  have rHv : (0 : ℝ) ≤ (Hlo c.v c.pv : ℝ) := by exact_mod_cast hHv
  have hcc : (ccLo c : ℝ) ≤ J (c.v : ℝ) + 2 * planeK (c.v : ℝ) * H (c.v : ℝ) / (1 - 2 * c.v) := by
    have e : (ccLo c : ℝ) = (Jlo c.v c.pv : ℝ) +
        2 * (Klo c : ℝ) * (Hlo c.v c.pv : ℝ) / (1 - 2 * (c.v : ℝ)) := by
      unfold ccLo; push_cast; try ring
    rw [e]
    have hr : (0 : ℝ) < 1 - 2 * (c.v : ℝ) := by linarith only [rv2]
    have hprod : (Klo c : ℝ) * (Hlo c.v c.pv : ℝ) ≤ planeK (c.v : ℝ) * H (c.v : ℝ) :=
      mul_le_mul hKlo hvHl rHv (hKlo0.trans hKlo)
    have hdiv : 2 * (Klo c : ℝ) * (Hlo c.v c.pv : ℝ) / (1 - 2 * c.v) ≤
        2 * planeK (c.v : ℝ) * H (c.v : ℝ) / (1 - 2 * c.v) := by
      apply div_le_div_of_nonneg_right _ hr.le
      linarith only [hprod]
    linarith only [hvJl, hdiv]
  have hd0 : 0 ≤ μ.b - μ.a := by linarith only [ha1, hb0, rB3, rB4]
  have hEpos : 0 < μ.meanEntropy := law_meanEntropy_pos μ
  have hcost : (ccLo c : ℝ) * (μ.b - μ.a) - 2 * (Khi c : ℝ) * μ.meanEntropy ≤ μ.cost := by
    have h1 := mul_le_mul_of_nonneg_right hcc hd0
    have h2 := mul_le_mul_of_nonneg_right hKhi hEpos.le
    linarith only [hplane, h1, h2]
  -- relaxation algebra
  have rsig : (0 : ℝ) ≤ (sig c : ℝ) := by exact_mod_cast hsig
  have rgam : (0 : ℝ) ≤ (gam B c : ℝ) := by exact_mod_cast hgam
  have rfin : (0 : ℝ) ≤ (finalVal B c : ℝ) := by exact_mod_cast hfin
  have hkapE : (kap c : ℝ) * ((EMIN : ℝ) + (tstar B c : ℝ) * ((H μ.a + H μ.b) / 2 - EMIN)) ≤
      (kap c : ℝ) * μ.meanEntropy := by
    unfold tstar
    split_ifs with hk
    · have rk : (0 : ℝ) ≤ (kap c : ℝ) := by exact_mod_cast hk
      exact mul_le_mul_of_nonneg_left hE0 rk
    · have rk : (kap c : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hk))
      exact mul_le_mul_of_nonpos_left hE1 rk
  have hchA : (Hlo B.alo c.pA0 : ℝ) + (mua B c : ℝ) * (μ.a - B.alo) ≤ H μ.a := by
    have hc := H_chord_lower (lo := (B.alo : ℝ)) (hi := (B.ahi : ℝ)) (x := μ.a)
      (HL0 := (Hlo B.alo c.pA0 : ℝ)) (HL1 := (Hlo B.ahi c.pA1 : ℝ)) rB1.le ha0 ha1
      (by linarith only [rB3]) hA0l hA1l
    have e : (mua B c : ℝ) =
        ((Hlo B.ahi c.pA1 : ℝ) - (Hlo B.alo c.pA0 : ℝ)) / ((B.ahi : ℝ) - B.alo) := by
      unfold mua; push_cast; try ring
    rw [e]; exact hc
  have hchB : (Hlo B.blo c.pB0 : ℝ) + (mub B c : ℝ) * (μ.b - B.blo) ≤ H μ.b := by
    have hc := H_chord_lower (lo := (B.blo : ℝ)) (hi := (B.bhi : ℝ)) (x := μ.b)
      (HL0 := (Hlo B.blo c.pB0 : ℝ)) (HL1 := (Hlo B.bhi c.pB1 : ℝ)) (by linarith only [rB4]) hb0 hb1
      rB6.le hB0l hB1l
    have e : (mub B c : ℝ) =
        ((Hlo B.bhi c.pB1 : ℝ) - (Hlo B.blo c.pB0 : ℝ)) / ((B.bhi : ℝ) - B.blo) := by
      unfold mub; push_cast; try ring
    rw [e]; exact hc
  have hgamH := mul_le_mul_of_nonneg_left (add_le_add hchA hchB) rgam
  have hsigH := mul_le_mul_of_nonneg_left hHm_tan rsig
  have hcorner : (0 : ℝ) ≤ (c0 B c : ℝ) + (ca B c : ℝ) * μ.a + (cb B c : ℝ) * μ.b := by
    have e1 := min_mul_le (q := ca B c) ha0 ha1
    have e2 := min_mul_le (q := cb B c) hb0 hb1
    have e : (finalVal B c : ℝ) = (c0 B c : ℝ) +
        ((min (ca B c * B.alo) (ca B c * B.ahi) : ℚ) : ℝ) +
        ((min (cb B c * B.blo) (cb B c * B.bhi) : ℚ) : ℝ) := by
      unfold finalVal; push_cast; try ring
    linarith only [rfin, e, e1, e2]
  have egam : (gam B c : ℝ) = ((kap c : ℝ) * (tstar B c : ℝ) + 4) / 2 := by
    unfold gam; push_cast; try ring
  have ekap : (kap c : ℝ) = (sig c : ℝ) - 2 * (Khi c : ℝ) - 4 := by
    unfold kap; push_cast; try ring
  have econst : (constT c : ℝ) = -(PuLo c : ℝ) + (sig c : ℝ) * c.pLo + (PlS c : ℝ) - 4 * c.sL := by
    unfold constT; push_cast; try ring
  have ec0 : (c0 B c : ℝ) = (kap c : ℝ) * EMIN * (1 - (tstar B c : ℝ)) +
      (gam B c : ℝ) * ((Hlo B.alo c.pA0 : ℝ) - (mua B c : ℝ) * B.alo + (Hlo B.blo c.pB0 : ℝ) -
        (mub B c : ℝ) * B.blo) -
      (sig c : ℝ) * ((Hhi (mlo B) c.pM0 : ℝ) - (numM B c : ℝ) * (mlo B : ℝ)) + (constT c : ℝ) := by
    unfold c0; push_cast; try ring
  have eca : (ca B c : ℝ) = -(ccLo c : ℝ) + (gam B c : ℝ) * (mua B c : ℝ) -
      (sig c : ℝ) * (numM B c : ℝ) / 2 := by
    unfold ca; push_cast; try ring
  have ecb : (cb B c : ℝ) = (ccLo c : ℝ) + (gam B c : ℝ) * (mub B c : ℝ) -
      (sig c : ℝ) * (numM B c : ℝ) / 2 := by
    unfold cb; push_cast; try ring
  rw [ec0, eca, ecb, econst, egam, ekap] at hcorner
  rw [egam, ekap] at hgamH
  rw [ekap] at hkapE
  generalize Scalar.P (H ((μ.a + μ.b) / 2) - μ.meanEntropy) = PI at hjen hPI
  generalize Scalar.P ((H μ.a + H μ.b) / 2 - μ.meanEntropy) = PS at hjen hPs
  linarith only [hjen, hPI, hPs, hkapE, hgamH, hsigH, hcorner, hcost]

end CKLaneD

end


