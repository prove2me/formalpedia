-- Prove2me | Definitions.Def_CK_CKLaneM10_Checker
-- name    : CK_CKLaneM10_Checker
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T12:56:53.231037+00:00
-- url     : https://prove2.me/theorems/03e62f1f-94db-4701-9c32-3588678ee8f8
-- title:
--   Courtade–Kumar proof module `CKLaneM10.Checker` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM10.Checker` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM10.Checker` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM10.Checker (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM10/Checker.lean)

import Definitions.Def_CK_CKLaneM10_Analytic

-- ===== source module CKLaneM10.Checker =====
section

/-!
# Lane M10: Boolean `global_feasible_split` cell checker and its unconditional soundness

`checkFS_sound : checkFS B c = true → CKLaneD.Sem B` with NO other hypotheses, where

`CKLaneD.Sem B = ∀ k (μ : InteriorLaw (Fin k)), InBox B μ.a μ.b μ.meanEntropy →
   candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.cost`

and `InBox` is the exact physical box (means `a ∈ [alo,ahi]`, `b ∈ [blo,bhi]`, mean entropy between
the `t0`/`t1` levels `EMIN + t (C0 - EMIN)` with `C0 = (H a + H b)/2`).  The child entropies `e, f`
are arbitrary (only their mean is constrained); no `e = C t` parametrization is used.

What the checker binds (all recomputed in exact `ℚ` from certificate data):
* the box and every log certificate (via `CKLaneD.checkPt`: `log x`, `log (1-x)` enclosures),
* the entropy caps `cA ≥ H a`, `cB ≥ H b` and the feasible split `rL = max 0 (sL - min cA cB)`,
  which is justified at law level by `GeneralCK.Scalar.feasible_imbalance_lower` (provider),
* the information bracket `xa` (upper `P` bound) and the deficit brackets `x1`, `x2`,
* the asymmetric supporting plane at the contact `(vx, vy)`: log-enclosed closed-form
  coefficients `A, B > 0`, slope `c1`, validated by `supporting_plane_of_contact` (provider),
* the final comparison `upper ≤ plane`.
-/

namespace CKLaneM10

open GeneralCK CKLaneD

/-- Untrusted per-cell certificate data. -/
structure FSCell where
  pA0 : PtCert
  pA1 : PtCert
  pB0 : PtCert
  pB1 : PtCert
  pM : PtCert
  xa : ℚ
  pxa : PtCert
  sL : ℚ
  useX1 : Bool
  x1 : ℚ
  px1 : PtCert
  useX2 : Bool
  x2 : ℚ
  px2 : PtCert
  vx : ℚ
  pvx : PtCert
  vy : ℚ
  pvy : PtCert
  deriving Repr, DecidableEq

/-! ## Derived quantities (recomputed by the checker) -/

def fmhi (B : Box) : ℚ := (B.ahi + B.bhi) / 2
def fC0Lo (B : Box) (c : FSCell) : ℚ := (Hlo B.alo c.pA0 + Hlo B.bhi c.pB1) / 2
def fC0Hi (B : Box) (c : FSCell) : ℚ := (Hhi B.ahi c.pA1 + Hhi B.blo c.pB0) / 2
def fELo (B : Box) (c : FSCell) : ℚ := EMIN + B.t0 * (fC0Lo B c - EMIN)
def fEHi (B : Box) (c : FSCell) : ℚ := EMIN + B.t1 * (fC0Hi B c - EMIN)
def fHmHi (B : Box) (c : FSCell) : ℚ := if 2 * fmhi B ≤ 1 then Hhi (fmhi B) c.pM else 1
def fIHi (B : Box) (c : FSCell) : ℚ := fHmHi B c - fELo B c
def fPU (c : FSCell) : ℚ := (1 - 2 * c.xa) * Jhi c.xa c.pxa
def fcA (B : Box) (c : FSCell) : ℚ := Hhi B.ahi c.pA1
def fcB (B : Box) (c : FSCell) : ℚ := Hhi B.blo c.pB0
def fcm (B : Box) (c : FSCell) : ℚ := min (fcA B c) (fcB B c)
def frL (B : Box) (c : FSCell) : ℚ := max 0 (c.sL - fcm B c)
def fp1 (B : Box) (c : FSCell) : ℚ := c.sL - frL B c
def fp2 (B : Box) (c : FSCell) : ℚ := c.sL + frL B c

/-- Lower bound for `P p`: bracket `(1 - 2x) J x` (when `1 - p ≤ H x`) or `4 p`. -/
def PLow (u : Bool) (x : ℚ) (px : PtCert) (p : ℚ) : ℚ :=
  if u then (1 - 2 * x) * Jlo x px else 4 * p

def lowOK (u : Bool) (x : ℚ) (px : PtCert) (p : ℚ) : Bool :=
  if u then checkPt x px && decide (2 * x ≤ 1 ∧ 1 - p ≤ Hlo x px) else true

def fUpper (B : Box) (c : FSCell) : ℚ :=
  fPU c - (PLow c.useX1 c.x1 c.px1 (fp1 B c) + PLow c.useX2 c.x2 c.px2 (fp2 B c)) / 2

def fL1lo (c : FSCell) : ℚ := -c.pvx.cx.hi
def fL1hi (c : FSCell) : ℚ := -c.pvx.cx.lo
def fM1lo (c : FSCell) : ℚ := -c.pvx.cy.hi
def fM1hi (c : FSCell) : ℚ := -c.pvx.cy.lo
def fL2lo (c : FSCell) : ℚ := -c.pvy.cx.hi
def fL2hi (c : FSCell) : ℚ := -c.pvy.cx.lo
def fM2lo (c : FSCell) : ℚ := -c.pvy.cy.hi
def fM2hi (c : FSCell) : ℚ := -c.pvy.cy.lo
def fr1 (c : FSCell) : ℚ := (c.vx - c.vy) ^ 2 / (2 * c.vx * c.vy)
def fr2 (c : FSCell) : ℚ := (c.vx - c.vy) ^ 2 / (2 * (1 - c.vx) * (1 - c.vy))
def fdetLo (c : FSCell) : ℚ := fL1lo c * fM2lo c - fL2hi c * fM1hi c
def fdetHi (c : FSCell) : ℚ := fL1hi c * fM2hi c - fL2lo c * fM1lo c
def fNALo (c : FSCell) : ℚ := fr1 c * fM2lo c - fr2 c * fL2hi c
def fNAHi (c : FSCell) : ℚ := fr1 c * fM2hi c - fr2 c * fL2lo c
def fNBLo (c : FSCell) : ℚ := fr2 c * fL1lo c - fr1 c * fM1hi c
def fNBHi (c : FSCell) : ℚ := fr2 c * fL1hi c - fr1 c * fM1lo c
def fALo (c : FSCell) : ℚ := fNALo c / fdetHi c
def fAHi (c : FSCell) : ℚ := fNAHi c / fdetLo c
def fBLo (c : FSCell) : ℚ := fNBLo c / fdetHi c
def fBHi (c : FSCell) : ℚ := fNBHi c / fdetLo c
def fc1Lo (c : FSCell) : ℚ :=
  (Jlo c.vx c.pvx - Jhi c.vy c.pvy) / 2 +
    (fALo c * Hlo c.vx c.pvx + fBLo c * Hlo c.vy c.pvy) / (c.vy - c.vx)
def fdlow (B : Box) : ℚ := B.blo - B.ahi
def fPlane (B : Box) (c : FSCell) : ℚ :=
  fc1Lo c * fdlow B - 2 * fBHi c * fEHi B c - max 0 (fAHi c - fBLo c) * fcA B c

def hmOK (B : Box) (c : FSCell) : Bool :=
  if 2 * fmhi B ≤ 1 then checkPt (fmhi B) c.pM else true

/-- The Boolean feasible-split cell checker. -/
def checkFS (B : Box) (c : FSCell) : Bool :=
  decide (0 < B.alo ∧ B.alo ≤ B.ahi ∧ 2 * B.ahi ≤ 1 ∧ 1 ≤ 2 * B.blo ∧ B.blo ≤ B.bhi ∧
    B.bhi < 1 ∧ 0 ≤ B.t0 ∧ B.t0 ≤ B.t1 ∧ B.t1 ≤ 1) &&
  checkPt B.alo c.pA0 &&
  checkPt B.ahi c.pA1 &&
  checkPt B.blo c.pB0 &&
  checkPt B.bhi c.pB1 &&
  hmOK B c &&
  checkPt c.xa c.pxa &&
  checkPt c.vx c.pvx &&
  checkPt c.vy c.pvy &&
  decide (2 * c.xa ≤ 1 ∧ Hhi c.xa c.pxa ≤ 1 - fIHi B c) &&
  decide (0 ≤ c.sL ∧ c.sL ≤ (fC0Lo B c - EMIN) * (1 - B.t1)) &&
  decide (0 ≤ fcm B c ∧ fp2 B c < 1) &&
  lowOK c.useX1 c.x1 c.px1 (fp1 B c) &&
  lowOK c.useX2 c.x2 c.px2 (fp2 B c) &&
  decide (c.vx < c.vy ∧ 0 ≤ fL1lo c ∧ 0 ≤ fL2lo c ∧ 0 ≤ fM1lo c ∧ 0 ≤ fM2lo c ∧
    0 < fdetLo c ∧ 0 < fNALo c ∧ 0 < fNBLo c ∧ 0 ≤ Hlo c.vx c.pvx ∧ 0 ≤ Hlo c.vy c.pvy ∧
    0 ≤ fc1Lo c) &&
  decide (fUpper B c ≤ fPlane B c)

/-! ## Soundness helpers -/

theorem lowOK_sound {u : Bool} {x : ℚ} {px : PtCert} {p : ℚ} (h : lowOK u x px p = true)
    (hp0 : 0 ≤ (p : ℝ)) (hp1 : (p : ℝ) < 1) : (PLow u x px p : ℝ) ≤ Scalar.P (p : ℝ) := by
  unfold lowOK at h
  unfold PLow
  split_ifs at h ⊢ with hu
  · rw [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hp, h2, h3⟩ := h
    obtain ⟨hx0, _, hHl, _, hJl, _⟩ := checkPt_bounds hp
    have hx0' : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx0
    have h2' : 2 * (x : ℝ) ≤ 1 := by exact_mod_cast h2
    have h3' : 1 - (p : ℝ) ≤ (Hlo x px : ℝ) := by exact_mod_cast h3
    have hb := P_ge_bracket hp0 hp1 hx0' (by linarith) (h3'.trans hHl)
    push_cast
    have := mul_le_mul_of_nonneg_left hJl (by linarith : (0 : ℝ) ≤ 1 - 2 * (x : ℝ))
    linarith
  · push_cast
    exact Scalar.four_mul_le_P hp0 hp1

theorem hm_sound {B : Box} {c : FSCell} (h : hmOK B c = true) {m : ℝ} (hm0 : 0 ≤ m)
    (hm : m ≤ (fmhi B : ℝ)) : H m ≤ (fHmHi B c : ℝ) := by
  unfold hmOK at h
  unfold fHmHi
  split_ifs at h ⊢ with h2
  · obtain ⟨_, _, _, hHu, _, _⟩ := checkPt_bounds h
    have h2' : 2 * (fmhi B : ℝ) ≤ 1 := by exact_mod_cast h2
    exact (H_mono_left hm0 hm (by linarith)).trans hHu
  · push_cast
    exact H_le_one m

/-- Raw logarithm bounds carried by a point certificate. -/
theorem checkPt_logs {x : ℚ} {p : PtCert} (h : checkPt x p = true) :
    (p.cx.lo : ℝ) ≤ Real.log (x : ℝ) ∧ Real.log (x : ℝ) ≤ (p.cx.hi : ℝ) ∧
      (p.cy.lo : ℝ) ≤ Real.log (1 - (x : ℝ)) ∧ Real.log (1 - (x : ℝ)) ≤ (p.cy.hi : ℝ) := by
  unfold checkPt at h
  rw [Bool.and_eq_true] at h
  have h1 := checkLogCert_sound h.1
  have h2 := checkLogCert_sound h.2
  push_cast at h2
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

theorem div_bounds {n d nlo nhi dlo dhi : ℝ} (hnlo : nlo ≤ n) (hnhi : n ≤ nhi) (hdlo : dlo ≤ d)
    (hdhi : d ≤ dhi) (hnlo0 : 0 ≤ nlo) (hdlo0 : 0 < dlo) :
    nlo / dhi ≤ n / d ∧ n / d ≤ nhi / dlo := by
  have hd : 0 < d := lt_of_lt_of_le hdlo0 hdlo
  have hdhi0 : 0 < dhi := lt_of_lt_of_le hd hdhi
  have hn : 0 ≤ n := le_trans hnlo0 hnlo
  constructor
  · rw [div_le_div_iff₀ hdhi0 hd]
    nlinarith
  · rw [div_le_div_iff₀ hd hdlo0]
    nlinarith

/-- Plane data: the rational enclosures of the closed-form plane coefficients are valid. -/
theorem plane_bounds {c : FSCell} (hpx : checkPt c.vx c.pvx = true)
    (hpy : checkPt c.vy c.pvy = true) (hv : c.vx < c.vy) (hL1 : 0 ≤ fL1lo c)
    (hL2 : 0 ≤ fL2lo c) (hM1 : 0 ≤ fM1lo c) (hM2 : 0 ≤ fM2lo c) (hdet : 0 < fdetLo c)
    (hNA : 0 < fNALo c) (hNB : 0 < fNBLo c) (hHx : 0 ≤ Hlo c.vx c.pvx)
    (hHy : 0 ≤ Hlo c.vy c.pvy) :
    0 < (c.vx : ℝ) ∧ (c.vx : ℝ) < c.vy ∧ (c.vy : ℝ) < 1 ∧ planeDet (c.vx : ℝ) c.vy ≠ 0 ∧
      0 < planeA (c.vx : ℝ) c.vy ∧ 0 < planeB (c.vx : ℝ) c.vy ∧
      planeA (c.vx : ℝ) c.vy ≤ (fAHi c : ℝ) ∧ (fBLo c : ℝ) ≤ planeB (c.vx : ℝ) c.vy ∧
      planeB (c.vx : ℝ) c.vy ≤ (fBHi c : ℝ) ∧ 0 ≤ (fBLo c : ℝ) ∧
      (fc1Lo c : ℝ) ≤ planeC (c.vx : ℝ) c.vy := by
  obtain ⟨hx0, hx1, hHxl, _, hJxl, _⟩ := checkPt_bounds hpx
  obtain ⟨hy0, hy1, hHyl, _, _, hJyu⟩ := checkPt_bounds hpy
  obtain ⟨lx1, lx2, lx3, lx4⟩ := checkPt_logs hpx
  obtain ⟨ly1, ly2, ly3, ly4⟩ := checkPt_logs hpy
  have rx0 : (0 : ℝ) < (c.vx : ℝ) := by exact_mod_cast hx0
  have rxy : (c.vx : ℝ) < (c.vy : ℝ) := by exact_mod_cast hv
  have ry1 : (c.vy : ℝ) < 1 := by exact_mod_cast hy1
  set x : ℝ := (c.vx : ℝ) with hxdef
  set y : ℝ := (c.vy : ℝ) with hydef
  -- real logs and their rational enclosures
  set L1 : ℝ := -Real.log x with hL1def
  set L2 : ℝ := -Real.log y with hL2def
  set M1 : ℝ := -Real.log (1 - x) with hM1def
  set M2 : ℝ := -Real.log (1 - y) with hM2def
  have eL1lo : (fL1lo c : ℝ) = -(c.pvx.cx.hi : ℝ) := by unfold fL1lo; push_cast; ring
  have eL1hi : (fL1hi c : ℝ) = -(c.pvx.cx.lo : ℝ) := by unfold fL1hi; push_cast; ring
  have eM1lo : (fM1lo c : ℝ) = -(c.pvx.cy.hi : ℝ) := by unfold fM1lo; push_cast; ring
  have eM1hi : (fM1hi c : ℝ) = -(c.pvx.cy.lo : ℝ) := by unfold fM1hi; push_cast; ring
  have eL2lo : (fL2lo c : ℝ) = -(c.pvy.cx.hi : ℝ) := by unfold fL2lo; push_cast; ring
  have eL2hi : (fL2hi c : ℝ) = -(c.pvy.cx.lo : ℝ) := by unfold fL2hi; push_cast; ring
  have eM2lo : (fM2lo c : ℝ) = -(c.pvy.cy.hi : ℝ) := by unfold fM2lo; push_cast; ring
  have eM2hi : (fM2hi c : ℝ) = -(c.pvy.cy.lo : ℝ) := by unfold fM2hi; push_cast; ring
  have bL1lo : (fL1lo c : ℝ) ≤ L1 := by rw [eL1lo]; linarith only [lx2]
  have bL1hi : L1 ≤ (fL1hi c : ℝ) := by rw [eL1hi]; linarith only [lx1]
  have bM1lo : (fM1lo c : ℝ) ≤ M1 := by rw [eM1lo]; linarith only [lx4]
  have bM1hi : M1 ≤ (fM1hi c : ℝ) := by rw [eM1hi]; linarith only [lx3]
  have bL2lo : (fL2lo c : ℝ) ≤ L2 := by rw [eL2lo]; linarith only [ly2]
  have bL2hi : L2 ≤ (fL2hi c : ℝ) := by rw [eL2hi]; linarith only [ly1]
  have bM2lo : (fM2lo c : ℝ) ≤ M2 := by rw [eM2lo]; linarith only [ly4]
  have bM2hi : M2 ≤ (fM2hi c : ℝ) := by rw [eM2hi]; linarith only [ly3]
  have rL1 : (0 : ℝ) ≤ (fL1lo c : ℝ) := by exact_mod_cast hL1
  have rL2 : (0 : ℝ) ≤ (fL2lo c : ℝ) := by exact_mod_cast hL2
  have rM1 : (0 : ℝ) ≤ (fM1lo c : ℝ) := by exact_mod_cast hM1
  have rM2 : (0 : ℝ) ≤ (fM2lo c : ℝ) := by exact_mod_cast hM2
  have pL1 : 0 ≤ L1 := rL1.trans bL1lo
  have pL2 : 0 ≤ L2 := rL2.trans bL2lo
  have pM1 : 0 ≤ M1 := rM1.trans bM1lo
  have pM2 : 0 ≤ M2 := rM2.trans bM2lo
  -- the exact coefficients
  set r1 : ℝ := (x - y) ^ 2 / (2 * x * y) with hr1def
  set r2 : ℝ := (x - y) ^ 2 / (2 * (1 - x) * (1 - y)) with hr2def
  have er1 : (fr1 c : ℝ) = r1 := by unfold fr1; push_cast; ring
  have er2 : (fr2 c : ℝ) = r2 := by unfold fr2; push_cast; ring
  have pr1 : 0 ≤ r1 := by
    have : 0 < 2 * x * y := by nlinarith
    exact div_nonneg (sq_nonneg _) this.le
  have pr2 : 0 ≤ r2 := by
    have h1 : 0 < 1 - x := by linarith
    have h2 : 0 < 1 - y := by linarith
    have : 0 < 2 * (1 - x) * (1 - y) := by positivity
    exact div_nonneg (sq_nonneg _) this.le
  -- determinant
  have edet : planeDet x y = L1 * M2 - L2 * M1 := rfl
  have edetLo : (fdetLo c : ℝ) = (fL1lo c : ℝ) * (fM2lo c : ℝ) - (fL2hi c : ℝ) * (fM1hi c : ℝ) := by
    unfold fdetLo; push_cast; ring
  have edetHi : (fdetHi c : ℝ) = (fL1hi c : ℝ) * (fM2hi c : ℝ) - (fL2lo c : ℝ) * (fM1lo c : ℝ) := by
    unfold fdetHi; push_cast; ring
  have hdetLo : (fdetLo c : ℝ) ≤ L1 * M2 - L2 * M1 := by
    have h1 : (fL1lo c : ℝ) * (fM2lo c : ℝ) ≤ L1 * M2 := mul_le_mul bL1lo bM2lo rM2 pL1
    have h2 : L2 * M1 ≤ (fL2hi c : ℝ) * (fM1hi c : ℝ) :=
      mul_le_mul bL2hi bM1hi pM1 (pL2.trans bL2hi)
    rw [edetLo]; linarith only [h1, h2]
  have hdetHi : L1 * M2 - L2 * M1 ≤ (fdetHi c : ℝ) := by
    have h1 : L1 * M2 ≤ (fL1hi c : ℝ) * (fM2hi c : ℝ) := mul_le_mul bL1hi bM2hi pM2 (pL1.trans bL1hi)
    have h2 : (fL2lo c : ℝ) * (fM1lo c : ℝ) ≤ L2 * M1 := mul_le_mul bL2lo bM1lo rM1 pL2
    rw [edetHi]; linarith only [h1, h2]
  have rdet : (0 : ℝ) < (fdetLo c : ℝ) := by exact_mod_cast hdet
  have hdetpos : 0 < L1 * M2 - L2 * M1 := rdet.trans_le hdetLo
  -- numerators
  have eNALo : (fNALo c : ℝ) = r1 * (fM2lo c : ℝ) - r2 * (fL2hi c : ℝ) := by
    unfold fNALo; push_cast; rw [er1, er2]
  have eNAHi : (fNAHi c : ℝ) = r1 * (fM2hi c : ℝ) - r2 * (fL2lo c : ℝ) := by
    unfold fNAHi; push_cast; rw [er1, er2]
  have eNBLo : (fNBLo c : ℝ) = r2 * (fL1lo c : ℝ) - r1 * (fM1hi c : ℝ) := by
    unfold fNBLo; push_cast; rw [er1, er2]
  have eNBHi : (fNBHi c : ℝ) = r2 * (fL1hi c : ℝ) - r1 * (fM1lo c : ℝ) := by
    unfold fNBHi; push_cast; rw [er1, er2]
  have hNALo : (fNALo c : ℝ) ≤ r1 * M2 - r2 * L2 := by
    have h1 := mul_le_mul_of_nonneg_left bM2lo pr1
    have h2 := mul_le_mul_of_nonneg_left bL2hi pr2
    rw [eNALo]; linarith only [h1, h2]
  have hNAHi : r1 * M2 - r2 * L2 ≤ (fNAHi c : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left bM2hi pr1
    have h2 := mul_le_mul_of_nonneg_left bL2lo pr2
    rw [eNAHi]; linarith only [h1, h2]
  have hNBLo : (fNBLo c : ℝ) ≤ r2 * L1 - r1 * M1 := by
    have h1 := mul_le_mul_of_nonneg_left bL1lo pr2
    have h2 := mul_le_mul_of_nonneg_left bM1hi pr1
    rw [eNBLo]; linarith only [h1, h2]
  have hNBHi : r2 * L1 - r1 * M1 ≤ (fNBHi c : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left bL1hi pr2
    have h2 := mul_le_mul_of_nonneg_left bM1lo pr1
    rw [eNBHi]; linarith only [h1, h2]
  have rNA : (0 : ℝ) < (fNALo c : ℝ) := by exact_mod_cast hNA
  have rNB : (0 : ℝ) < (fNBLo c : ℝ) := by exact_mod_cast hNB
  have eA : planeA x y = (r1 * M2 - r2 * L2) / (L1 * M2 - L2 * M1) := rfl
  have eB : planeB x y = (r2 * L1 - r1 * M1) / (L1 * M2 - L2 * M1) := rfl
  obtain ⟨hAlo, hAhi⟩ := div_bounds hNALo hNAHi hdetLo hdetHi rNA.le rdet
  obtain ⟨hBlo, hBhi⟩ := div_bounds hNBLo hNBHi hdetLo hdetHi rNB.le rdet
  have eALo : (fALo c : ℝ) = (fNALo c : ℝ) / (fdetHi c : ℝ) := by unfold fALo; push_cast; ring
  have eAHi : (fAHi c : ℝ) = (fNAHi c : ℝ) / (fdetLo c : ℝ) := by unfold fAHi; push_cast; ring
  have eBLo : (fBLo c : ℝ) = (fNBLo c : ℝ) / (fdetHi c : ℝ) := by unfold fBLo; push_cast; ring
  have eBHi : (fBHi c : ℝ) = (fNBHi c : ℝ) / (fdetLo c : ℝ) := by unfold fBHi; push_cast; ring
  have rdetHi : (0 : ℝ) < (fdetHi c : ℝ) := hdetpos.trans_le hdetHi
  have pALo : (0 : ℝ) < (fALo c : ℝ) := by rw [eALo]; exact div_pos rNA rdetHi
  have pBLo : (0 : ℝ) < (fBLo c : ℝ) := by rw [eBLo]; exact div_pos rNB rdetHi
  have hA_lo : (fALo c : ℝ) ≤ planeA x y := by rw [eALo, eA]; exact hAlo
  have hA_hi : planeA x y ≤ (fAHi c : ℝ) := by rw [eAHi, eA]; exact hAhi
  have hB_lo : (fBLo c : ℝ) ≤ planeB x y := by rw [eBLo, eB]; exact hBlo
  have hB_hi : planeB x y ≤ (fBHi c : ℝ) := by rw [eBHi, eB]; exact hBhi
  have hApos : 0 < planeA x y := pALo.trans_le hA_lo
  have hBpos : 0 < planeB x y := pBLo.trans_le hB_lo
  -- the slope
  have hyx : 0 < y - x := sub_pos.mpr rxy
  have eC : planeC x y = (J x - J y) / 2 + (planeA x y * H x + planeB x y * H y) / (y - x) := by
    unfold planeC interiorCost
    field_simp
    ring
  have rHx : (0 : ℝ) ≤ (Hlo c.vx c.pvx : ℝ) := by exact_mod_cast hHx
  have rHy : (0 : ℝ) ≤ (Hlo c.vy c.pvy : ℝ) := by exact_mod_cast hHy
  have hAH : (fALo c : ℝ) * (Hlo c.vx c.pvx : ℝ) ≤ planeA x y * H x :=
    mul_le_mul hA_lo hHxl rHx hApos.le
  have hBH : (fBLo c : ℝ) * (Hlo c.vy c.pvy : ℝ) ≤ planeB x y * H y :=
    mul_le_mul hB_lo hHyl rHy hBpos.le
  have hdiv : ((fALo c : ℝ) * (Hlo c.vx c.pvx : ℝ) + (fBLo c : ℝ) * (Hlo c.vy c.pvy : ℝ)) /
      (y - x) ≤ (planeA x y * H x + planeB x y * H y) / (y - x) :=
    div_le_div_of_nonneg_right (by linarith only [hAH, hBH]) hyx.le
  have ec1 : (fc1Lo c : ℝ) = ((Jlo c.vx c.pvx : ℝ) - (Jhi c.vy c.pvy : ℝ)) / 2 +
      ((fALo c : ℝ) * (Hlo c.vx c.pvx : ℝ) + (fBLo c : ℝ) * (Hlo c.vy c.pvy : ℝ)) / (y - x) := by
    unfold fc1Lo; push_cast; ring
  have hc1 : (fc1Lo c : ℝ) ≤ planeC x y := by
    rw [ec1, eC]; linarith only [hdiv, hJxl, hJyu]
  exact ⟨rx0, rxy, ry1, by rw [edet]; exact hdetpos.ne', hApos, hBpos, hA_hi, hB_lo, hB_hi,
    pBLo.le, hc1⟩

/-! ## Soundness -/

theorem checkFS_sound {B : Box} {c : FSCell} (h : checkFS B c = true) : Sem B := by
  intro k μ hbox
  unfold checkFS at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8, hB9, hpA0, hpA1, hpB0, hpB1, hhm, hpxa,
    hpvx, hpvy, hxa1, hxa2, hsL0, hsL1, hcm0, hp2, hlow1, hlow2, hv, hL1, hL2, hM1, hM2, hdet,
    hNA, hNB, hHx, hHy, hc1, hfin⟩ := h
  obtain ⟨ha0, ha1, hb0, hb1, hE0, hE1⟩ := hbox
  -- casts of box facts
  have rB1 : (0 : ℝ) < B.alo := by exact_mod_cast hB1
  have rB3 : 2 * (B.ahi : ℝ) ≤ 1 := by exact_mod_cast hB3
  have rB4 : 1 ≤ 2 * (B.blo : ℝ) := by exact_mod_cast hB4
  have rB6 : (B.bhi : ℝ) < 1 := by exact_mod_cast hB6
  have rB7 : (0 : ℝ) ≤ B.t0 := by exact_mod_cast hB7
  have rB8 : (B.t0 : ℝ) ≤ B.t1 := by exact_mod_cast hB8
  have rB9 : (B.t1 : ℝ) ≤ 1 := by exact_mod_cast hB9
  -- point enclosures
  obtain ⟨_, _, hA0l, _, _, _⟩ := checkPt_bounds hpA0
  obtain ⟨_, _, _, hA1u, _, _⟩ := checkPt_bounds hpA1
  obtain ⟨_, _, _, hB0u, _, _⟩ := checkPt_bounds hpB0
  obtain ⟨_, _, hB1l, _, _, _⟩ := checkPt_bounds hpB1
  obtain ⟨hxa0, _, _, hxaHu, _, hxaJu⟩ := checkPt_bounds hpxa
  -- H at the law means
  have hHa_lo : H (B.alo : ℝ) ≤ H μ.a := H_mono_left rB1.le ha0 (by linarith only [ha1, rB3])
  have hHa_hi : H μ.a ≤ H (B.ahi : ℝ) := H_mono_left (by linarith only [rB1, ha0]) ha1
    (by linarith only [rB3])
  have hHb_lo : H (B.bhi : ℝ) ≤ H μ.b := H_anti_right (by linarith only [hb0, rB4]) hb1
    (by linarith only [rB6])
  have hHb_hi : H μ.b ≤ H (B.blo : ℝ) := H_anti_right (by linarith only [rB4]) hb0
    (by linarith only [hb1, rB6])
  have hcA : H μ.a ≤ (fcA B c : ℝ) := hHa_hi.trans hA1u
  have hcB : H μ.b ≤ (fcB B c : ℝ) := hHb_hi.trans hB0u
  have hC0lo : (fC0Lo B c : ℝ) ≤ (H μ.a + H μ.b) / 2 := by
    have e : (fC0Lo B c : ℝ) = ((Hlo B.alo c.pA0 : ℝ) + (Hlo B.bhi c.pB1 : ℝ)) / 2 := by
      unfold fC0Lo; push_cast; ring
    rw [e]; linarith only [hA0l, hB1l, hHa_lo, hHb_lo]
  have hC0hi : (H μ.a + H μ.b) / 2 ≤ (fC0Hi B c : ℝ) := by
    have e : (fC0Hi B c : ℝ) = ((Hhi B.ahi c.pA1 : ℝ) + (Hhi B.blo c.pB0 : ℝ)) / 2 := by
      unfold fC0Hi; push_cast; ring
    rw [e]; linarith only [hA1u, hB0u, hHa_hi, hHb_hi]
  -- entropy range
  have hElo : (fELo B c : ℝ) ≤ μ.meanEntropy := by
    have e : (fELo B c : ℝ) = (EMIN : ℝ) + (B.t0 : ℝ) * ((fC0Lo B c : ℝ) - EMIN) := by
      unfold fELo; push_cast; ring
    have := mul_le_mul_of_nonneg_left
      (show (fC0Lo B c : ℝ) - EMIN ≤ (H μ.a + H μ.b) / 2 - EMIN by linarith only [hC0lo]) rB7
    rw [e]; linarith only [this, hE0]
  have hEhi : μ.meanEntropy ≤ (fEHi B c : ℝ) := by
    have e : (fEHi B c : ℝ) = (EMIN : ℝ) + (B.t1 : ℝ) * ((fC0Hi B c : ℝ) - EMIN) := by
      unfold fEHi; push_cast; ring
    have := mul_le_mul_of_nonneg_left
      (show (H μ.a + H μ.b) / 2 - EMIN ≤ (fC0Hi B c : ℝ) - EMIN by linarith only [hC0hi])
      (rB7.trans rB8)
    rw [e]; linarith only [this, hE1]
  have hEpos : 0 < μ.meanEntropy := law_meanEntropy_pos μ
  -- the information and its P upper bound
  have hI := μ.information_mem
  have eI : μ.information = H ((μ.a + μ.b) / 2) - μ.meanEntropy := rfl
  rw [eI] at hI
  have hm0 : 0 ≤ (μ.a + μ.b) / 2 := by linarith only [rB1, ha0, hb0, rB4]
  have hmhi : (μ.a + μ.b) / 2 ≤ (fmhi B : ℝ) := by
    have e : (fmhi B : ℝ) = ((B.ahi : ℝ) + (B.bhi : ℝ)) / 2 := by unfold fmhi; push_cast; ring
    rw [e]; linarith only [ha1, hb1]
  have hHm := hm_sound hhm hm0 hmhi
  have hIhi : H ((μ.a + μ.b) / 2) - μ.meanEntropy ≤ (fIHi B c : ℝ) := by
    have e : (fIHi B c : ℝ) = (fHmHi B c : ℝ) - (fELo B c : ℝ) := by unfold fIHi; push_cast; ring
    rw [e]; linarith only [hHm, hElo]
  have rxa0 : (0 : ℝ) < c.xa := by exact_mod_cast hxa0
  have rxa1 : 2 * (c.xa : ℝ) ≤ 1 := by exact_mod_cast hxa1
  have rxa2 : (Hhi c.xa c.pxa : ℝ) ≤ 1 - (fIHi B c : ℝ) := by exact_mod_cast hxa2
  have hPI : Scalar.P (H ((μ.a + μ.b) / 2) - μ.meanEntropy) ≤ (fPU c : ℝ) := by
    have hb := P_le_bracket hI.1 hI.2 rxa0 (by linarith only [rxa1])
      (by linarith only [hxaHu, rxa2, hIhi])
    have e : (fPU c : ℝ) = (1 - 2 * (c.xa : ℝ)) * (Jhi c.xa c.pxa : ℝ) := by
      unfold fPU; push_cast; ring
    have := mul_le_mul_of_nonneg_left hxaJu (by linarith only [rxa1] : (0 : ℝ) ≤ 1 - 2 * (c.xa : ℝ))
    rw [e]; linarith only [hb, this]
  -- the mean deficit and its lower bound
  have rsL0 : (0 : ℝ) ≤ c.sL := by exact_mod_cast hsL0
  have rsL1 : (c.sL : ℝ) ≤ ((fC0Lo B c : ℝ) - EMIN) * (1 - B.t1) := by exact_mod_cast hsL1
  have hsL : (c.sL : ℝ) ≤ (H μ.a + H μ.b) / 2 - μ.meanEntropy := by
    have h1 : ((fC0Lo B c : ℝ) - EMIN) * (1 - B.t1) ≤
        ((H μ.a + H μ.b) / 2 - EMIN) * (1 - B.t1) :=
      mul_le_mul_of_nonneg_right (by linarith only [hC0lo]) (by linarith only [rB9])
    have h2 : ((H μ.a + H μ.b) / 2 - EMIN) * (1 - (B.t1 : ℝ)) =
        (H μ.a + H μ.b) / 2 - EMIN - (B.t1 : ℝ) * ((H μ.a + H μ.b) / 2 - EMIN) := by ring
    linarith only [rsL1, h1, h2, hE1]
  -- the feasible split at law level and its monotone rational relaxation
  set cm : ℝ := min (fcA B c : ℝ) (fcB B c : ℝ) with hcmdef
  set s : ℝ := (H μ.a + H μ.b) / 2 - μ.meanEntropy with hsdef
  have hsplit := law_gap_le_split μ hcA hcB
  have hargs := law_split_args μ hcA hcB
  have hmono := split_mono (sL := (c.sL : ℝ)) (s := s) (c := cm) rsL0 hsL hargs
  have ecm : ((fcm B c : ℚ) : ℝ) = cm := by unfold fcm; rw [Rat.cast_min]
  have erL : ((frL B c : ℚ) : ℝ) = max 0 ((c.sL : ℝ) - cm) := by
    unfold frL; rw [Rat.cast_max, Rat.cast_sub, ecm]; push_cast; ring_nf
  have ep1 : ((fp1 B c : ℚ) : ℝ) = (c.sL : ℝ) - max 0 ((c.sL : ℝ) - cm) := by
    unfold fp1; rw [Rat.cast_sub, erL]
  have ep2 : ((fp2 B c : ℚ) : ℝ) = (c.sL : ℝ) + max 0 ((c.sL : ℝ) - cm) := by
    unfold fp2; rw [Rat.cast_add, erL]
  have rcm0 : (0 : ℝ) ≤ cm := by rw [← ecm]; exact_mod_cast hcm0
  have rp2 : ((fp2 B c : ℚ) : ℝ) < 1 := by exact_mod_cast hp2
  have hp1_0 : (0 : ℝ) ≤ ((fp1 B c : ℚ) : ℝ) := by
    rw [ep1]
    rcases le_total ((c.sL : ℝ) - cm) 0 with hh | hh
    · rw [max_eq_left hh]; linarith only [rsL0]
    · rw [max_eq_right hh]; linarith only [rcm0]
  have hp12 : ((fp1 B c : ℚ) : ℝ) ≤ ((fp2 B c : ℚ) : ℝ) := by
    rw [ep1, ep2]; linarith only [le_max_left 0 ((c.sL : ℝ) - cm)]
  have hPL1 := lowOK_sound hlow1 hp1_0 (hp12.trans_lt rp2)
  have hPL2 := lowOK_sound hlow2 (hp1_0.trans hp12) rp2
  rw [ep1] at hPL1
  rw [ep2] at hPL2
  have eU : (fUpper B c : ℝ) = (fPU c : ℝ) -
      ((PLow c.useX1 c.x1 c.px1 (fp1 B c) : ℝ) + (PLow c.useX2 c.x2 c.px2 (fp2 B c) : ℝ)) / 2 := by
    unfold fUpper; push_cast; ring
  have hgap : candidateGap psi μ.a μ.b μ.e μ.f ≤ (fUpper B c : ℝ) := by
    rw [eU]; linarith only [hsplit, hmono, hPI, hPL1, hPL2]
  -- the cost floor from the asymmetric supporting plane
  obtain ⟨rx0, rxy, ry1, hdet', hApos, hBpos, hA_hi, hB_lo, hB_hi, hBLo0, hc1'⟩ :=
    plane_bounds hpvx hpvy hv hL1 hL2 hM1 hM2 hdet hNA hNB hHx hHy
  have hplane := plane_cost_lower_asym μ rx0 rxy ry1 hdet' hApos hBpos
  set A := planeA (c.vx : ℝ) c.vy
  set Bc := planeB (c.vx : ℝ) c.vy
  set C1 := planeC (c.vx : ℝ) c.vy
  have rc1 : (0 : ℝ) ≤ (fc1Lo c : ℝ) := by exact_mod_cast hc1
  have hd : (fdlow B : ℝ) ≤ μ.b - μ.a := by
    have e : (fdlow B : ℝ) = (B.blo : ℝ) - (B.ahi : ℝ) := by unfold fdlow; push_cast; ring
    rw [e]; linarith only [ha1, hb0]
  have hd0 : (0 : ℝ) ≤ (fdlow B : ℝ) := by
    have e : (fdlow B : ℝ) = (B.blo : ℝ) - (B.ahi : ℝ) := by unfold fdlow; push_cast; ring
    rw [e]; linarith only [rB3, rB4]
  have hCd : (fc1Lo c : ℝ) * (fdlow B : ℝ) ≤ C1 * (μ.b - μ.a) :=
    mul_le_mul hc1' hd hd0 (rc1.trans hc1')
  have hBE : Bc * μ.meanEntropy ≤ (fBHi c : ℝ) * (fEHi B c : ℝ) :=
    mul_le_mul hB_hi hEhi hEpos.le (hBpos.le.trans hB_hi)
  set M := max (0 : ℝ) ((fAHi c : ℝ) - (fBLo c : ℝ)) with hMdef
  have hM0 : (0 : ℝ) ≤ M := le_max_left _ _
  have hAB : A - Bc ≤ M := (by linarith only [hA_hi, hB_lo] :
    A - Bc ≤ (fAHi c : ℝ) - (fBLo c : ℝ)).trans (le_max_right _ _)
  have he0 : 0 ≤ μ.e := μ.e_pos.le
  have hecap : μ.e ≤ (fcA B c : ℝ) := μ.e_le_cap.trans hcA
  have hAe : (A - Bc) * μ.e ≤ M * (fcA B c : ℝ) :=
    (mul_le_mul_of_nonneg_right hAB he0).trans (mul_le_mul_of_nonneg_left hecap hM0)
  have eEm : μ.meanEntropy = (μ.e + μ.f) / 2 := rfl
  have ePl : (fPlane B c : ℝ) = (fc1Lo c : ℝ) * (fdlow B : ℝ) - 2 * (fBHi c : ℝ) * (fEHi B c : ℝ) -
      M * (fcA B c : ℝ) := by
    unfold fPlane; rw [hMdef]; push_cast; ring
  have rfin : (fUpper B c : ℝ) ≤ (fPlane B c : ℝ) := by exact_mod_cast hfin
  have hcost : (fPlane B c : ℝ) ≤ μ.cost := by
    rw [ePl]
    have hsplitE : A * μ.e + Bc * μ.f = 2 * (Bc * μ.meanEntropy) + (A - Bc) * μ.e := by
      rw [eEm]; ring
    linarith only [hplane, hCd, hBE, hAe, hsplitE]
  linarith only [hgap, rfin, hcost]

end CKLaneM10

end


