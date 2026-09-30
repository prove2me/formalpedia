-- Prove2me | Definitions.Def_CK_CKLaneM2_SLChecker
-- name    : CK_CKLaneM2_SLChecker
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:05:11.215903+00:00
-- url     : https://prove2.me/theorems/338aaaef-b6de-471c-90ae-41752a8f59c1
-- title:
--   Courtade–Kumar proof module `CKLaneM2.SLChecker` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM2.SLChecker` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM2.SLChecker` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM2.SLChecker (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM2/SLChecker.lean)

import Definitions.Def_CK_CKLaneM2_SLPlane

-- ===== source module CKLaneM2.SLChecker =====
section

/-!
# Lane M2b: Boolean checker for the archived method `shifted_logsum` and its soundness

`checkSL B c = true → Sem B` with NO other hypotheses (`checkSL_sound`), where `CKLaneD.Sem B` is the
law-level psi-candidate Bellman statement on the physical box `B` (means in `[alo,ahi] × [blo,bhi]`,
mean entropy between the `t0`/`t1` levels `EMIN + t (C0 - EMIN)`).

Math chain (all proved; no numeric hypotheses):
* `CKLaneD.law_gap_le_P`: `candidateGap psi ≤ P(I) - P(s)`, `I = H(m) - E`, `s = C0 - E`;
* `CKLaneM2.slplane_cost_lower` (shifted log-sum plane at the rational anchor `(al, be)`, θ-sharpened):
  `cost ≥ KLo + UaLo a + VbLo b - 2 A E` with `A = (be-al)²/(4 be (1-al) th)`;
* convex chord of `P` on `[pLo, pHi]` with bracket values (information side);
* `P(s) ≥ PlS + λ (s - sL)` with either `λ = 4` (`Scalar.P_increment_lower`) or the secant slope
  `λ = (PlS - Pu0)/hs` on `[sL - hs, sL]` (convexity of `P`, `ConvexOn.slope_mono_adjacent`);
* concave chords of `H` at the box corners, a left-secant upper bound of `H` at the parent mean;
* exact corner minimisation of the resulting affine function of `(a, b)`.
Everything else is recomputed in exact `ℚ` by the checker (log certificates of `CKLaneD.checkPt`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM2

open GeneralCK CKLaneD GeneralCK.LogSum

/-- Untrusted per-cell certificate data for the shifted log-sum method. -/
structure SLCert where
  al : ℚ
  be : ℚ
  th : ℚ
  pAl : PtCert
  pBe : PtCert
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
  useSec : Bool
  hs : ℚ
  xs : ℚ
  pxs : PtCert
  deriving Repr, DecidableEq

/-! ## Plane coefficients (exact rational lower bounds) -/

def slA (c : SLCert) : ℚ := (c.be - c.al) ^ 2 / (4 * (c.be * (1 - c.al)) * c.th)
def iLo : ℚ := 1 / L1
def iHi : ℚ := 1 / L0
def rAc (c : SLCert) : ℚ := (c.al - c.be) / (2 * c.al * (1 - c.al))
def rBc (c : SLCert) : ℚ := (c.be - c.al) / (2 * c.be * (1 - c.be))
def kKc (c : SLCert) : ℚ := (c.be - c.al) ^ 2 / (2 * (1 - c.al) * (1 - c.be))
def KLo (c : SLCert) : ℚ :=
  slA c * (Hlo c.al c.pAl - c.al * Jhi c.al c.pAl) + slA c * (Hlo c.be c.pBe - c.be * Jhi c.be c.pBe) -
    kKc c * iHi
def UaLo (c : SLCert) : ℚ :=
  Jlo c.be c.pBe / 2 + min ((slA c - 1 / 2) * Jlo c.al c.pAl) ((slA c - 1 / 2) * Jhi c.al c.pAl) +
    rAc c * iHi
def VbLo (c : SLCert) : ℚ :=
  Jlo c.al c.pAl / 2 + min ((slA c - 1 / 2) * Jlo c.be c.pBe) ((slA c - 1 / 2) * Jhi c.be c.pBe) +
    rBc c * iLo

/-! ## Derived box quantities (recomputed by the checker) -/

def sC0Lo (B : Box) (c : SLCert) : ℚ := (Hlo B.alo c.pA0 + Hlo B.bhi c.pB1) / 2
def sC0Hi (B : Box) (c : SLCert) : ℚ := (Hhi B.ahi c.pA1 + Hhi B.blo c.pB0) / 2
def sELo (B : Box) (c : SLCert) : ℚ := EMIN + B.t0 * (sC0Lo B c - EMIN)
def sEHi (B : Box) (c : SLCert) : ℚ := EMIN + B.t1 * (sC0Hi B c - EMIN)
def sHmLo (B : Box) (c : SLCert) : ℚ := min (Hlo (mlo B) c.pM0) (Hlo (mhi B) c.pM1)
def snumM (B : Box) (c : SLCert) : ℚ := (Hhi (mlo B) c.pM0 - Hlo (mlo B - c.hm) c.pMh) / c.hm
def sHmHi (B : Box) (c : SLCert) : ℚ := Hhi (mlo B) c.pM0 + max 0 (snumM B c * (mhi B - mlo B))
def sPuLo (c : SLCert) : ℚ := (1 - 2 * c.xa) * Jhi c.xa c.pxa
def sPuHi (c : SLCert) : ℚ := (1 - 2 * c.xb) * Jhi c.xb c.pxb
def sPlS (c : SLCert) : ℚ := if c.useXc then (1 - 2 * c.xc) * Jlo c.xc c.pxc else 4 * c.sL
def sPu0 (c : SLCert) : ℚ := (1 - 2 * c.xs) * Jhi c.xs c.pxs
def slam (c : SLCert) : ℚ := if c.useSec then (sPlS c - sPu0 c) / c.hs else 4
def ssig (c : SLCert) : ℚ := (sPuHi c - sPuLo c) / (c.pHi - c.pLo)
def skap (c : SLCert) : ℚ := ssig c - 2 * slA c - slam c
def sts (B : Box) (c : SLCert) : ℚ := if 0 ≤ skap c then B.t0 else B.t1
def sgam (B : Box) (c : SLCert) : ℚ := (skap c * sts B c + slam c) / 2
def smua (B : Box) (c : SLCert) : ℚ := (Hlo B.ahi c.pA1 - Hlo B.alo c.pA0) / (B.ahi - B.alo)
def smub (B : Box) (c : SLCert) : ℚ := (Hlo B.bhi c.pB1 - Hlo B.blo c.pB0) / (B.bhi - B.blo)
def sconst (c : SLCert) : ℚ := -sPuLo c + ssig c * c.pLo + sPlS c - slam c * c.sL
def sca (B : Box) (c : SLCert) : ℚ := UaLo c + sgam B c * smua B c - ssig c * snumM B c / 2
def scb (B : Box) (c : SLCert) : ℚ := VbLo c + sgam B c * smub B c - ssig c * snumM B c / 2
def sc0 (B : Box) (c : SLCert) : ℚ :=
  KLo c + skap c * EMIN * (1 - sts B c) +
    sgam B c * (Hlo B.alo c.pA0 - smua B c * B.alo + Hlo B.blo c.pB0 - smub B c * B.blo) -
    ssig c * (Hhi (mlo B) c.pM0 - snumM B c * mlo B) + sconst c
def sfinal (B : Box) (c : SLCert) : ℚ :=
  sc0 B c + min (sca B c * B.alo) (sca B c * B.ahi) + min (scb B c * B.blo) (scb B c * B.bhi)

/-- Optional lower bracket for `P sL`. -/
def xcOKs (c : SLCert) : Bool :=
  if c.useXc then checkPt c.xc c.pxc && decide (2 * c.xc ≤ 1 ∧ 1 - c.sL ≤ Hlo c.xc c.pxc)
  else true

/-- Optional secant data: upper bracket for `P (sL - hs)`. -/
def secOK (c : SLCert) : Bool :=
  if c.useSec then checkPt c.xs c.pxs &&
    decide (0 < c.hs ∧ c.hs ≤ c.sL ∧ 2 * c.xs ≤ 1 ∧ Hhi c.xs c.pxs ≤ 1 - (c.sL - c.hs))
  else true

/-- The Boolean cell checker for the shifted log-sum method. -/
def checkSL (B : Box) (c : SLCert) : Bool :=
  decide (0 < B.alo ∧ B.alo ≤ B.ahi ∧ 2 * B.ahi ≤ 1 ∧ 1 ≤ 2 * B.blo ∧ B.blo ≤ B.bhi ∧
    B.bhi < 1 ∧ 0 ≤ B.t0 ∧ B.t0 ≤ B.t1 ∧ B.t1 ≤ 1) &&
  decide (0 < c.al ∧ c.al < c.be ∧ c.be < 1 ∧ 1 + c.al ≤ 2 * c.th ∧ 2 - c.al ≤ 2 * c.th ∧
    1 + c.be ≤ 2 * c.th ∧ 2 - c.be ≤ 2 * c.th) &&
  decide (0 < c.hm ∧ c.hm < mlo B) &&
  checkPt c.al c.pAl &&
  checkPt c.be c.pBe &&
  checkPt B.alo c.pA0 &&
  checkPt B.ahi c.pA1 &&
  checkPt B.blo c.pB0 &&
  checkPt B.bhi c.pB1 &&
  checkPt (mlo B) c.pM0 &&
  checkPt (mhi B) c.pM1 &&
  checkPt (mlo B - c.hm) c.pMh &&
  checkPt c.xa c.pxa &&
  checkPt c.xb c.pxb &&
  xcOKs c &&
  secOK c &&
  decide (EMIN < sC0Lo B c) &&
  decide (0 ≤ c.pLo ∧ c.pLo ≤ sHmLo B c - sEHi B c ∧ sHmHi B c - sELo B c ≤ c.pHi ∧
      c.pLo < c.pHi ∧ c.pHi < 1) &&
  decide (2 * c.xa ≤ 1 ∧ Hhi c.xa c.pxa ≤ 1 - c.pLo) &&
  decide (2 * c.xb ≤ 1 ∧ Hhi c.xb c.pxb ≤ 1 - c.pHi) &&
  decide (0 ≤ c.sL ∧ c.sL ≤ (sC0Lo B c - EMIN) * (1 - B.t1)) &&
  decide (0 ≤ ssig c) &&
  decide (0 ≤ sgam B c) &&
  decide (0 ≤ sfinal B c)

/-! ## Soundness -/

theorem inv_log2_bounds :
    ((iLo : ℚ) : ℝ) ≤ (Real.log 2)⁻¹ ∧ (Real.log 2)⁻¹ ≤ ((iHi : ℚ) : ℝ) := by
  have hL := log2_bounds
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 := L0_pos_real
  have h1 : (1 : ℝ) / (L1 : ℝ) ≤ 1 / Real.log 2 := one_div_le_one_div_of_le hl2 hL.2
  have h2 : (1 : ℝ) / Real.log 2 ≤ 1 / (L0 : ℝ) := one_div_le_one_div_of_le hL0 hL.1
  rw [one_div (Real.log 2)] at h1 h2
  unfold iLo iHi
  push_cast
  exact ⟨h1, h2⟩

/-- Real-variable form of the plane lower bound with enclosed coefficients. -/
theorem plane_lower_real {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    {α β θ A Hal Jal Jau Hbl Jbl Jbu i0 i1 : ℝ}
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1) (hθa : theta α ≤ θ) (hθb : theta β ≤ θ)
    (hA : A = (β - α) ^ 2 / (4 * (β * (1 - α)) * θ))
    (hHa : Hal ≤ H α) (hJa0 : Jal ≤ J α) (hJa1 : J α ≤ Jau)
    (hHb : Hbl ≤ H β) (hJb0 : Jbl ≤ J β) (hJb1 : J β ≤ Jbu)
    (hi0 : i0 ≤ (Real.log 2)⁻¹) (hi1 : (Real.log 2)⁻¹ ≤ i1) :
    A * (Hal - α * Jau) + A * (Hbl - β * Jbu) - (β - α) ^ 2 / (2 * (1 - α) * (1 - β)) * i1 +
      (Jbl / 2 + min ((A - 1 / 2) * Jal) ((A - 1 / 2) * Jau) +
        (α - β) / (2 * α * (1 - α)) * i1) * μ.a +
      (Jal / 2 + min ((A - 1 / 2) * Jbl) ((A - 1 / 2) * Jbu) +
        (β - α) / (2 * β * (1 - β)) * i0) * μ.b -
      2 * A * μ.meanEntropy ≤ μ.cost := by
  have hα' : 0 < α ∧ α < 1 := ⟨hα, by linarith⟩
  have hβ' : 0 < β ∧ β < 1 := ⟨by linarith, hβ⟩
  have hplane := slplane_cost_lower μ hα' hβ' hθa hθb
  rw [slplane_expand hα' hβ'] at hplane
  have hV : V α β = β * (1 - α) := by
    unfold V; rw [max_eq_right hαβ.le, min_eq_left hαβ.le]
  have hcoef : (α - β) ^ 2 / (4 * V α β * θ) = A := by
    rw [hV, hA]; ring
  rw [hcoef] at hplane
  have hθ : 0 < θ := (theta_pos α hα').trans_le hθa
  have hA0 : 0 ≤ A := by
    rw [hA]
    have : 0 < β * (1 - α) := mul_pos (by linarith) (by linarith)
    positivity
  have ha := μ.a_interior
  have hb := μ.b_interior
  have hE : μ.meanEntropy = (μ.e + μ.f) / 2 := rfl
  -- constant term
  have hK1 : A * (Hal - α * Jau) ≤ A * (H α - α * J α) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hA0
  have hK2 : A * (Hbl - β * Jbu) ≤ A * (H β - β * J β) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hA0
  have hkK : 0 ≤ (β - α) ^ 2 / (2 * (1 - α) * (1 - β)) := by
    have : 0 < 2 * (1 - α) * (1 - β) := by
      have : 0 < 1 - α := by linarith
      have : 0 < 1 - β := by linarith
      positivity
    positivity
  have hK3 : (β - α) ^ 2 / (2 * (1 - α) * (1 - β)) * (Real.log 2)⁻¹ ≤
      (β - α) ^ 2 / (2 * (1 - α) * (1 - β)) * i1 := mul_le_mul_of_nonneg_left hi1 hkK
  -- coefficient of a
  have hrA : (α - β) / (2 * α * (1 - α)) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg (by linarith)
    have : 0 < 1 - α := by linarith
    positivity
  have hU1 : (α - β) / (2 * α * (1 - α)) * i1 ≤ (α - β) / (2 * α * (1 - α)) * (Real.log 2)⁻¹ :=
    mul_le_mul_of_nonpos_left hi1 hrA
  have hU2 : min ((A - 1 / 2) * Jal) ((A - 1 / 2) * Jau) ≤ (A - 1 / 2) * J α := by
    rcases le_total 0 (A - 1 / 2) with hs | hs
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hJa0 hs)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hJa1 hs)
  have hUa : Jbl / 2 + min ((A - 1 / 2) * Jal) ((A - 1 / 2) * Jau) +
      (α - β) / (2 * α * (1 - α)) * i1 ≤
      J β / 2 + (A - 1 / 2) * J α + (α - β) / (2 * α * (1 - α)) * (Real.log 2)⁻¹ := by
    linarith
  -- coefficient of b
  have hrB : 0 ≤ (β - α) / (2 * β * (1 - β)) := by
    apply div_nonneg (by linarith)
    have : 0 < 1 - β := by linarith
    have : 0 < β := by linarith
    positivity
  have hV1 : (β - α) / (2 * β * (1 - β)) * i0 ≤ (β - α) / (2 * β * (1 - β)) * (Real.log 2)⁻¹ :=
    mul_le_mul_of_nonneg_left hi0 hrB
  have hV2 : min ((A - 1 / 2) * Jbl) ((A - 1 / 2) * Jbu) ≤ (A - 1 / 2) * J β := by
    rcases le_total 0 (A - 1 / 2) with hs | hs
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hJb0 hs)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hJb1 hs)
  have hVb : Jal / 2 + min ((A - 1 / 2) * Jbl) ((A - 1 / 2) * Jbu) +
      (β - α) / (2 * β * (1 - β)) * i0 ≤
      J α / 2 + (A - 1 / 2) * J β + (β - α) / (2 * β * (1 - β)) * (Real.log 2)⁻¹ := by
    linarith
  have hUam := mul_le_mul_of_nonneg_right hUa ha.1.le
  have hVbm := mul_le_mul_of_nonneg_right hVb hb.1.le
  rw [hE]
  linarith

/-- Rational form of the plane lower bound, bound to the checker's anchor certificates. -/
theorem plane_lower {c : SLCert}
    (hanc : 0 < c.al ∧ c.al < c.be ∧ c.be < 1 ∧ 1 + c.al ≤ 2 * c.th ∧ 2 - c.al ≤ 2 * c.th ∧
      1 + c.be ≤ 2 * c.th ∧ 2 - c.be ≤ 2 * c.th)
    (hpa : checkPt c.al c.pAl = true) (hpb : checkPt c.be c.pBe = true)
    {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) :
    (KLo c : ℝ) + (UaLo c : ℝ) * μ.a + (VbLo c : ℝ) * μ.b - 2 * (slA c : ℝ) * μ.meanEntropy ≤
      μ.cost := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hanc
  obtain ⟨_, _, hHal, _, hJal, hJau⟩ := checkPt_bounds hpa
  obtain ⟨_, _, hHbl, _, hJbl, hJbu⟩ := checkPt_bounds hpb
  have r0 : (0 : ℝ) < (c.al : ℝ) := by exact_mod_cast h0
  have r1 : (c.al : ℝ) < (c.be : ℝ) := by exact_mod_cast h1
  have r2 : (c.be : ℝ) < 1 := by exact_mod_cast h2
  have r3 : 1 + (c.al : ℝ) ≤ 2 * (c.th : ℝ) := by exact_mod_cast h3
  have r4 : 2 - (c.al : ℝ) ≤ 2 * (c.th : ℝ) := by exact_mod_cast h4
  have r5 : 1 + (c.be : ℝ) ≤ 2 * (c.th : ℝ) := by exact_mod_cast h5
  have r6 : 2 - (c.be : ℝ) ≤ 2 * (c.th : ℝ) := by exact_mod_cast h6
  have hθa : theta (c.al : ℝ) ≤ (c.th : ℝ) := by
    unfold theta
    have := max_le r3 r4
    linarith
  have hθb : theta (c.be : ℝ) ≤ (c.th : ℝ) := by
    unfold theta
    have := max_le r5 r6
    linarith
  have hA : (slA c : ℝ) = ((c.be : ℝ) - c.al) ^ 2 / (4 * ((c.be : ℝ) * (1 - c.al)) * c.th) := by
    unfold slA; push_cast; ring
  obtain ⟨hi0, hi1⟩ := inv_log2_bounds
  have key := plane_lower_real μ r0 r1 r2 hθa hθb hA hHal hJal hJau hHbl hJbl hJbu hi0 hi1
  have eK : (KLo c : ℝ) = (slA c : ℝ) * ((Hlo c.al c.pAl : ℝ) - c.al * (Jhi c.al c.pAl : ℝ)) +
      (slA c : ℝ) * ((Hlo c.be c.pBe : ℝ) - c.be * (Jhi c.be c.pBe : ℝ)) -
      ((c.be : ℝ) - c.al) ^ 2 / (2 * (1 - c.al) * (1 - c.be)) * (iHi : ℝ) := by
    unfold KLo kKc; push_cast; ring
  have eU : (UaLo c : ℝ) = (Jlo c.be c.pBe : ℝ) / 2 +
      min (((slA c : ℝ) - 1 / 2) * (Jlo c.al c.pAl : ℝ)) (((slA c : ℝ) - 1 / 2) * (Jhi c.al c.pAl : ℝ)) +
      ((c.al : ℝ) - c.be) / (2 * c.al * (1 - c.al)) * (iHi : ℝ) := by
    unfold UaLo rAc; push_cast; ring
  have eV : (VbLo c : ℝ) = (Jlo c.al c.pAl : ℝ) / 2 +
      min (((slA c : ℝ) - 1 / 2) * (Jlo c.be c.pBe : ℝ)) (((slA c : ℝ) - 1 / 2) * (Jhi c.be c.pBe : ℝ)) +
      ((c.be : ℝ) - c.al) / (2 * c.be * (1 - c.be)) * (iLo : ℝ) := by
    unfold VbLo rBc; push_cast; ring
  rw [eK, eU, eV]
  exact key

theorem sPlS_le {c : SLCert} (hx : xcOKs c = true) (hs0 : 0 ≤ (c.sL : ℝ))
    (hs1 : (c.sL : ℝ) < 1) : (sPlS c : ℝ) ≤ Scalar.P (c.sL : ℝ) := by
  unfold xcOKs at hx
  unfold sPlS
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

/-- Secant extension of the convex profile `P` to the right of `[s0, s1]`. -/
theorem P_secant_lower {s0 s1 s : ℝ} (h0 : 0 ≤ s0) (h01 : s0 < s1) (h1s : s1 ≤ s) (hs1 : s < 1) :
    Scalar.P s1 + (Scalar.P s1 - Scalar.P s0) / (s1 - s0) * (s - s1) ≤ Scalar.P s := by
  rcases eq_or_lt_of_le h1s with heq | hlt
  · subst heq; simp
  · have hsl := Scalar.P_convexOn.slope_mono_adjacent (x := s0) (y := s1) (z := s)
      ⟨h0, by linarith⟩ ⟨by linarith, hs1⟩ h01 hlt
    have hd : 0 < s - s1 := by linarith
    rw [le_div_iff₀ hd] at hsl
    linarith

/-- Lower affine bound of `P` on the deficit side. -/
theorem slam_lower {c : SLCert} (hx : xcOKs c = true) (hsec : secOK c = true)
    (hs0 : 0 ≤ (c.sL : ℝ)) {s : ℝ} (hss : (c.sL : ℝ) ≤ s) (hs1 : s < 1) :
    (sPlS c : ℝ) + (slam c : ℝ) * (s - c.sL) ≤ Scalar.P s := by
  have hPl := sPlS_le hx hs0 (by linarith)
  unfold slam
  unfold secOK at hsec
  split_ifs at hsec ⊢ with hu
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hsec
    obtain ⟨hp, hh0, hh1, hx2, hxH⟩ := hsec
    obtain ⟨hxs0, _, _, hxsHu, _, hxsJu⟩ := checkPt_bounds hp
    have rh0 : (0 : ℝ) < (c.hs : ℝ) := by exact_mod_cast hh0
    have rh1 : (c.hs : ℝ) ≤ (c.sL : ℝ) := by exact_mod_cast hh1
    have rx2 : 2 * (c.xs : ℝ) ≤ 1 := by exact_mod_cast hx2
    have rxH : (Hhi c.xs c.pxs : ℝ) ≤ 1 - ((c.sL : ℝ) - c.hs) := by exact_mod_cast hxH
    have hxs0' : (0 : ℝ) < (c.xs : ℝ) := by exact_mod_cast hxs0
    have hPu0 : Scalar.P ((c.sL : ℝ) - c.hs) ≤ (sPu0 c : ℝ) := by
      have hb := P_le_bracket (p := (c.sL : ℝ) - c.hs) (xa := (c.xs : ℝ)) (by linarith)
        (by linarith) hxs0' (by linarith) (hxsHu.trans rxH)
      have e : (sPu0 c : ℝ) = (1 - 2 * (c.xs : ℝ)) * (Jhi c.xs c.pxs : ℝ) := by
        unfold sPu0; push_cast; ring
      have := mul_le_mul_of_nonneg_left hxsJu (by linarith : (0 : ℝ) ≤ 1 - 2 * (c.xs : ℝ))
      rw [e]; linarith
    have hsecl := P_secant_lower (s0 := (c.sL : ℝ) - c.hs) (s1 := (c.sL : ℝ)) (s := s)
      (by linarith) (by linarith) hss hs1
    have hslope : ((sPlS c : ℝ) - (sPu0 c : ℝ)) / (c.hs : ℝ) ≤
        (Scalar.P (c.sL : ℝ) - Scalar.P ((c.sL : ℝ) - c.hs)) / ((c.sL : ℝ) - ((c.sL : ℝ) - c.hs)) := by
      have e2 : (c.sL : ℝ) - ((c.sL : ℝ) - c.hs) = (c.hs : ℝ) := by ring
      rw [e2]
      exact div_le_div_of_nonneg_right (by linarith) rh0.le
    have hmul := mul_le_mul_of_nonneg_right hslope (by linarith : (0 : ℝ) ≤ s - c.sL)
    push_cast
    linarith
  · have hinc := Scalar.P_increment_lower hs0 hs1 hss
    push_cast
    linarith

theorem checkSL_sound {B : Box} {c : SLCert} (h : checkSL B c = true) : Sem B := by
  intro k μ hbox
  unfold checkSL at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8, hB9, hn0, hn1, hn2, hn3, hn4, hn5, hn6,
    hhm0, hhm1, hpAl, hpBe, hpA0, hpA1, hpB0, hpB1, hpM0, hpM1, hpMh, hpxa, hpxb, hxc, hsec,
    hC0, hpL0, hpL1, hpH1, hpLH, hpH2, hxa1, hxa2, hxb1, hxb2, hsL0, hsL1, hsig, hgam, hfin⟩ := h
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
  -- H at the law means
  have hHa_lo : H (B.alo : ℝ) ≤ H μ.a := H_mono_left rB1.le ha0 (by linarith only [ha1, rB3])
  have hHa_hi : H μ.a ≤ H (B.ahi : ℝ) := H_mono_left (by linarith only [rB1, ha0]) ha1
    (by linarith only [rB3])
  have hHb_lo : H (B.bhi : ℝ) ≤ H μ.b := H_anti_right (by linarith only [hb0, rB4]) hb1
    (by linarith only [rB6])
  have hHb_hi : H μ.b ≤ H (B.blo : ℝ) := H_anti_right (by linarith only [rB4]) hb0
    (by linarith only [hb1, rB6])
  have hC0lo : (sC0Lo B c : ℝ) ≤ (H μ.a + H μ.b) / 2 := by
    have e : (sC0Lo B c : ℝ) = ((Hlo B.alo c.pA0 : ℝ) + (Hlo B.bhi c.pB1 : ℝ)) / 2 := by
      unfold sC0Lo; push_cast; try ring
    rw [e]; linarith only [hA0l, hB1l, hHa_lo, hHb_lo]
  have hC0hi : (H μ.a + H μ.b) / 2 ≤ (sC0Hi B c : ℝ) := by
    have e : (sC0Hi B c : ℝ) = ((Hhi B.ahi c.pA1 : ℝ) + (Hhi B.blo c.pB0 : ℝ)) / 2 := by
      unfold sC0Hi; push_cast; try ring
    rw [e]; linarith only [hA1u, hB0u, hHa_hi, hHb_hi]
  have rC0 : (EMIN : ℝ) < (sC0Lo B c : ℝ) := by exact_mod_cast hC0
  -- entropy range
  have hElo : (sELo B c : ℝ) ≤ μ.meanEntropy := by
    have e : (sELo B c : ℝ) = (EMIN : ℝ) + (B.t0 : ℝ) * ((sC0Lo B c : ℝ) - EMIN) := by
      unfold sELo; push_cast; try ring
    have := mul_le_mul_of_nonneg_left
      (show (sC0Lo B c : ℝ) - EMIN ≤ (H μ.a + H μ.b) / 2 - EMIN by linarith only [hC0lo]) rB7
    rw [e]; linarith only [this, hE0]
  have hEhi : μ.meanEntropy ≤ (sEHi B c : ℝ) := by
    have e : (sEHi B c : ℝ) = (EMIN : ℝ) + (B.t1 : ℝ) * ((sC0Hi B c : ℝ) - EMIN) := by
      unfold sEHi; push_cast; try ring
    have := mul_le_mul_of_nonneg_left
      (show (H μ.a + H μ.b) / 2 - EMIN ≤ (sC0Hi B c : ℝ) - EMIN by linarith only [hC0hi])
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
  have hHm_lo : (sHmLo B c : ℝ) ≤ H ((μ.a + μ.b) / 2) := by
    have hc := H_chord_lower (lo := (mlo B : ℝ)) (hi := (mhi B : ℝ)) (x := (μ.a + μ.b) / 2)
      (HL0 := (sHmLo B c : ℝ)) (HL1 := (sHmLo B c : ℝ)) rmlo0 hmlo hmhi rmhi1
      (by unfold sHmLo; rw [Rat.cast_min]; exact (min_le_left _ _).trans hM0l)
      (by unfold sHmLo; rw [Rat.cast_min]; exact (min_le_right _ _).trans hM1l)
    calc (sHmLo B c : ℝ) = (sHmLo B c : ℝ) + ((sHmLo B c : ℝ) - (sHmLo B c : ℝ)) /
          ((mhi B : ℝ) - (mlo B : ℝ)) * ((μ.a + μ.b) / 2 - (mlo B : ℝ)) := by ring
      _ ≤ H ((μ.a + μ.b) / 2) := hc
  have hMhl' : (Hlo (mlo B - c.hm) c.pMh : ℝ) ≤ H ((mlo B : ℝ) - (c.hm : ℝ)) := by
    have := hMhl; push_cast at this; exact this
  have enum : (snumM B c : ℝ) =
      ((Hhi (mlo B) c.pM0 : ℝ) - (Hlo (mlo B - c.hm) c.pMh : ℝ)) / (c.hm : ℝ) := by
    unfold snumM; push_cast; try ring
  have hHm_tan : H ((μ.a + μ.b) / 2) ≤
      (Hhi (mlo B) c.pM0 : ℝ) + (snumM B c : ℝ) * ((μ.a + μ.b) / 2 - (mlo B : ℝ)) := by
    have hc := H_leftslope_upper (lo := (mlo B : ℝ)) (h := (c.hm : ℝ)) (x := (μ.a + μ.b) / 2)
      (HU0 := (Hhi (mlo B) c.pM0 : ℝ)) (HLh := (Hlo (mlo B - c.hm) c.pMh : ℝ))
      rhm0 (by linarith only [rhm1]) hmlo (by linarith only [hmhi, rmhi1]) hM0u hMhl'
    rw [enum]; exact hc
  have hHm_hi : H ((μ.a + μ.b) / 2) ≤ (sHmHi B c : ℝ) := by
    have hmm : 0 ≤ (μ.a + μ.b) / 2 - (mlo B : ℝ) := by linarith only [hmlo]
    have hmm2 : (μ.a + μ.b) / 2 - (mlo B : ℝ) ≤ (mhi B : ℝ) - (mlo B : ℝ) := by
      linarith only [hmhi]
    have hmax : (snumM B c : ℝ) * ((μ.a + μ.b) / 2 - (mlo B : ℝ)) ≤
        max 0 ((snumM B c : ℝ) * ((mhi B : ℝ) - (mlo B : ℝ))) := by
      rcases le_total 0 (snumM B c : ℝ) with hn | hn
      · exact (mul_le_mul_of_nonneg_left hmm2 hn).trans (le_max_right _ _)
      · exact (mul_nonpos_iff.mpr (Or.inr ⟨hn, hmm⟩)).trans (le_max_left _ _)
    have e : (sHmHi B c : ℝ) = (Hhi (mlo B) c.pM0 : ℝ) +
        max 0 ((snumM B c : ℝ) * ((mhi B : ℝ) - (mlo B : ℝ))) := by
      unfold sHmHi; push_cast; try ring
    rw [e]; linarith only [hHm_tan, hmax]
  -- information range
  have rpL0 : (0 : ℝ) ≤ c.pLo := by exact_mod_cast hpL0
  have rpL1 : (c.pLo : ℝ) ≤ (sHmLo B c : ℝ) - (sEHi B c : ℝ) := by exact_mod_cast hpL1
  have rpH1 : (sHmHi B c : ℝ) - (sELo B c : ℝ) ≤ c.pHi := by exact_mod_cast hpH1
  have rpLH : (c.pLo : ℝ) < c.pHi := by exact_mod_cast hpLH
  have rpH2 : (c.pHi : ℝ) < 1 := by exact_mod_cast hpH2
  have hIlo : (c.pLo : ℝ) ≤ H ((μ.a + μ.b) / 2) - μ.meanEntropy := by
    linarith only [rpL1, hHm_lo, hEhi]
  have hIhi : H ((μ.a + μ.b) / 2) - μ.meanEntropy ≤ (c.pHi : ℝ) := by
    linarith only [rpH1, hHm_hi, hElo]
  -- deficit range
  have hdef := law_deficit_mem μ
  have rsL0 : (0 : ℝ) ≤ c.sL := by exact_mod_cast hsL0
  have rsL1 : (c.sL : ℝ) ≤ ((sC0Lo B c : ℝ) - EMIN) * (1 - B.t1) := by exact_mod_cast hsL1
  have hsL : (c.sL : ℝ) ≤ (H μ.a + H μ.b) / 2 - μ.meanEntropy := by
    have h1 : ((sC0Lo B c : ℝ) - EMIN) * (1 - B.t1) ≤
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
  have hPLo : Scalar.P (c.pLo : ℝ) ≤ (sPuLo c : ℝ) := by
    have hb := P_le_bracket rpL0 (by linarith only [rpLH, rpH2]) hxa0' (by linarith only [rxa1])
      (hxaHu.trans rxa2)
    have e : (sPuLo c : ℝ) = (1 - 2 * (c.xa : ℝ)) * (Jhi c.xa c.pxa : ℝ) := by
      unfold sPuLo; push_cast; try ring
    have := mul_le_mul_of_nonneg_left hxaJu
      (by linarith only [rxa1] : (0 : ℝ) ≤ 1 - 2 * (c.xa : ℝ))
    rw [e]; linarith only [hb, this]
  have hPHi : Scalar.P (c.pHi : ℝ) ≤ (sPuHi c : ℝ) := by
    have hb := P_le_bracket (by linarith only [rpL0, rpLH]) rpH2 hxb0' (by linarith only [rxb1])
      (hxbHu.trans rxb2)
    have e : (sPuHi c : ℝ) = (1 - 2 * (c.xb : ℝ)) * (Jhi c.xb c.pxb : ℝ) := by
      unfold sPuHi; push_cast; try ring
    have := mul_le_mul_of_nonneg_left hxbJu
      (by linarith only [rxb1] : (0 : ℝ) ≤ 1 - 2 * (c.xb : ℝ))
    rw [e]; linarith only [hb, this]
  have esig : (ssig c : ℝ) = ((sPuHi c : ℝ) - (sPuLo c : ℝ)) / ((c.pHi : ℝ) - c.pLo) := by
    unfold ssig; push_cast; try ring
  have hPI : Scalar.P (H ((μ.a + μ.b) / 2) - μ.meanEntropy) ≤
      (sPuLo c : ℝ) + (ssig c : ℝ) * (H ((μ.a + μ.b) / 2) - μ.meanEntropy - c.pLo) := by
    have hch := P_chord rpL0 hIlo hIhi rpH2 rpLH
    have hm2 := chord_mono (f0 := Scalar.P (c.pLo : ℝ)) (f1 := Scalar.P (c.pHi : ℝ))
      (g0 := (sPuLo c : ℝ)) (g1 := (sPuHi c : ℝ)) (Δ := (c.pHi : ℝ) - c.pLo)
      (x := H ((μ.a + μ.b) / 2) - μ.meanEntropy - c.pLo)
      (by linarith only [rpLH]) (by linarith only [hIlo]) (by linarith only [hIhi]) hPLo hPHi
    rw [esig]; exact hch.trans hm2
  -- P lower bound on the deficit side
  have hPs : (sPlS c : ℝ) + (slam c : ℝ) * ((H μ.a + H μ.b) / 2 - μ.meanEntropy - c.sL) ≤
      Scalar.P ((H μ.a + H μ.b) / 2 - μ.meanEntropy) :=
    slam_lower hxc hsec rsL0 hsL hdef.2
  -- the shifted log-sum plane
  have hcost := plane_lower ⟨hn0, hn1, hn2, hn3, hn4, hn5, hn6⟩ hpAl hpBe μ
  -- relaxation algebra
  have rsig : (0 : ℝ) ≤ (ssig c : ℝ) := by exact_mod_cast hsig
  have rgam : (0 : ℝ) ≤ (sgam B c : ℝ) := by exact_mod_cast hgam
  have rfin : (0 : ℝ) ≤ (sfinal B c : ℝ) := by exact_mod_cast hfin
  have hkapE : (skap c : ℝ) * ((EMIN : ℝ) + (sts B c : ℝ) * ((H μ.a + H μ.b) / 2 - EMIN)) ≤
      (skap c : ℝ) * μ.meanEntropy := by
    unfold sts
    split_ifs with hk
    · have rk : (0 : ℝ) ≤ (skap c : ℝ) := by exact_mod_cast hk
      exact mul_le_mul_of_nonneg_left hE0 rk
    · have rk : (skap c : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hk))
      exact mul_le_mul_of_nonpos_left hE1 rk
  have hchA : (Hlo B.alo c.pA0 : ℝ) + (smua B c : ℝ) * (μ.a - B.alo) ≤ H μ.a := by
    have hc := H_chord_lower (lo := (B.alo : ℝ)) (hi := (B.ahi : ℝ)) (x := μ.a)
      (HL0 := (Hlo B.alo c.pA0 : ℝ)) (HL1 := (Hlo B.ahi c.pA1 : ℝ)) rB1.le ha0 ha1
      (by linarith only [rB3]) hA0l hA1l
    have e : (smua B c : ℝ) =
        ((Hlo B.ahi c.pA1 : ℝ) - (Hlo B.alo c.pA0 : ℝ)) / ((B.ahi : ℝ) - B.alo) := by
      unfold smua; push_cast; try ring
    rw [e]; exact hc
  have hchB : (Hlo B.blo c.pB0 : ℝ) + (smub B c : ℝ) * (μ.b - B.blo) ≤ H μ.b := by
    have hc := H_chord_lower (lo := (B.blo : ℝ)) (hi := (B.bhi : ℝ)) (x := μ.b)
      (HL0 := (Hlo B.blo c.pB0 : ℝ)) (HL1 := (Hlo B.bhi c.pB1 : ℝ)) (by linarith only [rB4]) hb0 hb1
      rB6.le hB0l hB1l
    have e : (smub B c : ℝ) =
        ((Hlo B.bhi c.pB1 : ℝ) - (Hlo B.blo c.pB0 : ℝ)) / ((B.bhi : ℝ) - B.blo) := by
      unfold smub; push_cast; try ring
    rw [e]; exact hc
  have hgamH := mul_le_mul_of_nonneg_left (add_le_add hchA hchB) rgam
  have hsigH := mul_le_mul_of_nonneg_left hHm_tan rsig
  have hcorner : (0 : ℝ) ≤ (sc0 B c : ℝ) + (sca B c : ℝ) * μ.a + (scb B c : ℝ) * μ.b := by
    have e1 := min_mul_le (q := sca B c) ha0 ha1
    have e2 := min_mul_le (q := scb B c) hb0 hb1
    have e : (sfinal B c : ℝ) = (sc0 B c : ℝ) +
        ((min (sca B c * B.alo) (sca B c * B.ahi) : ℚ) : ℝ) +
        ((min (scb B c * B.blo) (scb B c * B.bhi) : ℚ) : ℝ) := by
      unfold sfinal; push_cast; try ring
    linarith only [rfin, e, e1, e2]
  have egam : (sgam B c : ℝ) = ((skap c : ℝ) * (sts B c : ℝ) + (slam c : ℝ)) / 2 := by
    unfold sgam; push_cast; try ring
  have ekap : (skap c : ℝ) = (ssig c : ℝ) - 2 * (slA c : ℝ) - (slam c : ℝ) := by
    unfold skap; push_cast; try ring
  have econst : (sconst c : ℝ) =
      -(sPuLo c : ℝ) + (ssig c : ℝ) * c.pLo + (sPlS c : ℝ) - (slam c : ℝ) * c.sL := by
    unfold sconst; push_cast; try ring
  have ec0 : (sc0 B c : ℝ) = (KLo c : ℝ) + (skap c : ℝ) * EMIN * (1 - (sts B c : ℝ)) +
      (sgam B c : ℝ) * ((Hlo B.alo c.pA0 : ℝ) - (smua B c : ℝ) * B.alo + (Hlo B.blo c.pB0 : ℝ) -
        (smub B c : ℝ) * B.blo) -
      (ssig c : ℝ) * ((Hhi (mlo B) c.pM0 : ℝ) - (snumM B c : ℝ) * (mlo B : ℝ)) + (sconst c : ℝ) := by
    unfold sc0; push_cast; try ring
  have eca : (sca B c : ℝ) = (UaLo c : ℝ) + (sgam B c : ℝ) * (smua B c : ℝ) -
      (ssig c : ℝ) * (snumM B c : ℝ) / 2 := by
    unfold sca; push_cast; try ring
  have ecb : (scb B c : ℝ) = (VbLo c : ℝ) + (sgam B c : ℝ) * (smub B c : ℝ) -
      (ssig c : ℝ) * (snumM B c : ℝ) / 2 := by
    unfold scb; push_cast; try ring
  rw [ec0, eca, ecb, econst, egam, ekap] at hcorner
  rw [egam, ekap] at hgamH
  rw [ekap] at hkapE
  generalize Scalar.P (H ((μ.a + μ.b) / 2) - μ.meanEntropy) = PI at hjen hPI
  generalize Scalar.P ((H μ.a + H μ.b) / 2 - μ.meanEntropy) = PS at hjen hPs
  linarith only [hjen, hPI, hPs, hkapE, hgamH, hsigH, hcorner, hcost]

/-! ## Certificate trees (refinement inside a leaf) and leaf binding -/

/-- A certificate tree: a single shifted log-sum cell or a binary split along `a`, `b` or `t`. -/
inductive SLTree where
  | cell (c : SLCert)
  | splitA (m : ℚ) (l r : SLTree)
  | splitB (m : ℚ) (l r : SLTree)
  | splitT (m : ℚ) (l r : SLTree)
  deriving Repr

def checkSLTree : Box → SLTree → Bool
  | B, .cell c => checkSL B c
  | B, .splitA m l r =>
      decide (B.alo ≤ m ∧ m ≤ B.ahi) && checkSLTree { B with ahi := m } l &&
        checkSLTree { B with alo := m } r
  | B, .splitB m l r =>
      decide (B.blo ≤ m ∧ m ≤ B.bhi) && checkSLTree { B with bhi := m } l &&
        checkSLTree { B with blo := m } r
  | B, .splitT m l r =>
      decide (B.t0 ≤ m ∧ m ≤ B.t1) && checkSLTree { B with t1 := m } l &&
        checkSLTree { B with t0 := m } r

theorem checkSLTree_sound : ∀ (B : Box) (t : SLTree), checkSLTree B t = true → Sem B
  | B, .cell c, h => checkSL_sound h
  | B, .splitA m l r, h => by
      simp only [checkSLTree, Bool.and_eq_true] at h
      exact sem_splitA (checkSLTree_sound _ l h.1.2) (checkSLTree_sound _ r h.2)
  | B, .splitB m l r, h => by
      simp only [checkSLTree, Bool.and_eq_true] at h
      exact sem_splitB (checkSLTree_sound _ l h.1.2) (checkSLTree_sound _ r h.2)
  | B, .splitT m l r, h => by
      simp only [checkSLTree, Bool.and_eq_true] at h
      exact sem_splitT (checkSLTree_sound _ l h.1.2) (checkSLTree_sound _ r h.2)

/-- A shifted log-sum leaf witness: the rational physical box and its certificate tree. -/
structure SLWitness where
  box : Box
  tree : SLTree
  deriving Repr

/-- Per-leaf acceptance: the box contains the archived leaf's exact physical image (`imageCheck`,
exact `Nat` powers for `2^-u`) and the certificate tree is valid on the box. -/
def checkLeafSL (p : List ℕ) (w : SLWitness) : Bool :=
  imageCheck (uvtBox p) w.box && checkSLTree w.box w.tree

/-- Unconditional leaf soundness: the only hypothesis is the Boolean check. -/
theorem checkLeafSL_sound {p : List ℕ} {w : SLWitness} (h : checkLeafSL p w = true) :
    SemUVT (uvtBox p) := by
  unfold checkLeafSL at h
  rw [Bool.and_eq_true] at h
  exact imageCheck_sound h.1 (checkSLTree_sound w.box w.tree h.2)

theorem checkLeavesSL_sound (L : List (List ℕ × SLWitness))
    (h : (L.all fun x => checkLeafSL x.1 x.2) = true) :
    ∀ x ∈ L, SemUVT (uvtBox x.1) := by
  intro x hx
  rw [List.all_eq_true] at h
  exact checkLeafSL_sound (h x hx)

/-- Owner form: with (weak) psi-activity at the parent, `μ.gap ≤ μ.cost` on the leaf image. -/
theorem checkLeafSL_gap_le_cost {p : List ℕ} {w : SLWitness} (h : checkLeafSL p w = true)
    {k : ℕ} (μ : InteriorLaw (Fin k)) (hin : InUVT (uvtBox p) μ.a μ.b μ.meanEntropy)
    (hact : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost :=
  (hybrid_gap_le_psi hact).trans (checkLeafSL_sound h k μ hin)

end CKLaneM2

end


