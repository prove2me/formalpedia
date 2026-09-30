-- Prove2me | Definitions.Def_CK_CKLaneE_NLSChecker
-- name    : CK_CKLaneE_NLSChecker
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:04:47.624565+00:00
-- url     : https://prove2.me/theorems/72a5f94b-a340-4b03-b4c4-c5c690dddc09
-- title:
--   Courtade–Kumar proof module `CKLaneE.NLSChecker` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneE.NLSChecker` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneE.NLSChecker` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneE.NLSChecker (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneE/NLSChecker.lean)

import Definitions.Def_CK_CKLaneE_IntervalLog
import Definitions.Def_CK_CKLaneE_EntropyDropBound
import Definitions.Def_CK_GeneralCK_PsiLogSumOwner
import Definitions.Def_CK_GeneralCK_PureGapCapZeroReduction
import Definitions.Def_CK_GeneralCK_ScalarGap

-- ===== source module CKLaneE.NLSChecker =====
section

/-!
# Lane E: normalized log-sum box checker for the same-side psi chart (upward-entropy form)

A certificate is a mean box `r1 ≤ a/b ≤ r2`, `b1 ≤ b ≤ b2` together with an entropy floor `E1`,
in the actual law coordinates (`a = μ.a`, `b = μ.b`, `E = μ.meanEntropy`); no entropy split is
fixed and the law's children are arbitrary.

Acceptance (archive method `normalized_logsum`, evaluated at the maximal-deficit entropy endpoint
`E = E1`, with the Lean log-sum coefficient `β = 1/(2b(1-a))` and bonus `W = 0`):

    betaLo * sLo ≥ K * max(0, pbar - 4)

where `sLo ≤ S := (H a + H b)/2 - E1`, `Δ ≤ K (b-a)^2` and `pbar ≥ (P1 S + P1 (Δ+S))/2`.
This certifies `G(S) ≥ 0` for `G(s) = j + β(b-a)^2 s - P(Δ+s) + P(s)`; the corpus theorems
`Scalar.gap_endpoint_criterion` (concavity of `G`) and `deterministic_cap_bound` (`G(0) ≥ 0`)
then give `G(s) ≥ 0` for the law's own deficit `s ≤ S`, i.e. for every `E ≥ E1`.

Every primitive enclosure (logs, entropies, slope anchors) is recomputed by the checker.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneE.NLS

open GeneralCK GeneralCK.Scalar CKLaneE.IL

structure Box where
  r1 : ℚ
  r2 : ℚ
  b1 : ℚ
  b2 : ℚ
  E1 : ℚ
  vS : ℚ
  vI : ℚ
  deriving Repr, DecidableEq

namespace Box

variable (w : Box)

def aLo : ℚ := w.r1 * w.b1
def aHi : ℚ := w.r2 * w.b2
def mLo : ℚ := w.b1 * (1 + w.r1) / 2
def mHi : ℚ := w.b2 * (1 + w.r2) / 2
def dLo : ℚ := w.b1 * (1 - w.r2)
def dHi : ℚ := w.b2 * (1 - w.r1)
def CLo : ℚ := (Hlo w.aLo + Hlo w.b1) / 2
def CHi : ℚ := (Hhi w.aHi + Hhi w.b2) / 2
def sLo : ℚ := w.CLo - w.E1
def sHi : ℚ := w.CHi - w.E1
def IHi : ℚ := Hhi w.mHi - w.E1
def DHi : ℚ := Hhi w.mHi - w.CLo
def K1 : ℚ := w.DHi / (w.dLo * w.dLo)
def rhoHi : ℚ := (1 - w.r1) / (1 + w.r1)
def kapHi : ℚ := w.dHi / (2 * (1 - w.mHi))
def K2 : ℚ :=
  ((1 + 2 / 3 * (w.rhoHi * w.rhoHi)) / w.mLo +
    (1 + 2 / 3 * (w.kapHi * w.kapHi)) / (1 - w.mHi)) / (8 * LqLo)
def K : ℚ := if 0 < w.dLo ∧ w.K1 ≤ w.K2 then w.K1 else w.K2
def betaLo : ℚ := 1 / (2 * w.b2 * (1 - w.aLo))
def pbar : ℚ := (P1up w.vS + P1up w.vI) / 2
def excess : ℚ := if 0 ≤ w.pbar - 4 then w.pbar - 4 else 0

def boxOk : Bool :=
  decide (0 < w.r1 ∧ w.r1 ≤ w.r2 ∧ w.r2 ≤ 1 ∧ 0 < w.b1 ∧ w.b1 ≤ w.b2 ∧ w.b2 ≤ 1 / 2 ∧
    0 < w.E1)

def finalOk : Bool :=
  decide (0 ≤ w.sLo ∧ w.IHi < 1 ∧ 0 ≤ w.K ∧ w.K * w.excess ≤ w.betaLo * w.sLo)

def check : Bool :=
  w.boxOk && ptOk w.aLo && ptOk w.aHi && ptOk w.b1 && ptOk w.b2 && ptOk w.mHi &&
    anchorOk w.vS w.sHi && anchorOk w.vI w.IHi && w.finalOk

/-! ### Casts of the derived quantities -/

theorem cast_CLo : ((w.CLo : ℚ) : ℝ) = (((Hlo w.aLo : ℚ) : ℝ) + ((Hlo w.b1 : ℚ) : ℝ)) / 2 := by
  push_cast [CLo]; ring
theorem cast_CHi : ((w.CHi : ℚ) : ℝ) = (((Hhi w.aHi : ℚ) : ℝ) + ((Hhi w.b2 : ℚ) : ℝ)) / 2 := by
  push_cast [CHi]; ring
theorem cast_sLo : ((w.sLo : ℚ) : ℝ) = ((w.CLo : ℚ) : ℝ) - w.E1 := by push_cast [sLo]; ring
theorem cast_sHi : ((w.sHi : ℚ) : ℝ) = ((w.CHi : ℚ) : ℝ) - w.E1 := by push_cast [sHi]; ring
theorem cast_IHi : ((w.IHi : ℚ) : ℝ) = ((Hhi w.mHi : ℚ) : ℝ) - w.E1 := by push_cast [IHi]; ring
theorem cast_DHi : ((w.DHi : ℚ) : ℝ) = ((Hhi w.mHi : ℚ) : ℝ) - ((w.CLo : ℚ) : ℝ) := by
  push_cast [DHi]; ring
theorem cast_aLo : ((w.aLo : ℚ) : ℝ) = (w.r1 : ℝ) * w.b1 := by push_cast [aLo]; ring
theorem cast_aHi : ((w.aHi : ℚ) : ℝ) = (w.r2 : ℝ) * w.b2 := by push_cast [aHi]; ring
theorem cast_dLo : ((w.dLo : ℚ) : ℝ) = (w.b1 : ℝ) * (1 - w.r2) := by push_cast [dLo]; ring
theorem cast_dHi : ((w.dHi : ℚ) : ℝ) = (w.b2 : ℝ) * (1 - w.r1) := by push_cast [dHi]; ring
theorem cast_mLo : ((w.mLo : ℚ) : ℝ) = (w.b1 : ℝ) * (1 + w.r1) / 2 := by push_cast [mLo]; ring
theorem cast_mHi : ((w.mHi : ℚ) : ℝ) = (w.b2 : ℝ) * (1 + w.r2) / 2 := by push_cast [mHi]; ring
theorem cast_K1 :
    ((w.K1 : ℚ) : ℝ) = ((w.DHi : ℚ) : ℝ) / (((w.dLo : ℚ) : ℝ) * ((w.dLo : ℚ) : ℝ)) := by
  push_cast [K1]; ring
theorem cast_rhoHi : ((w.rhoHi : ℚ) : ℝ) = (1 - (w.r1 : ℝ)) / (1 + w.r1) := by
  push_cast [rhoHi]; ring
theorem cast_kapHi :
    ((w.kapHi : ℚ) : ℝ) = ((w.dHi : ℚ) : ℝ) / (2 * (1 - ((w.mHi : ℚ) : ℝ))) := by
  push_cast [kapHi]; ring
theorem cast_K2 : ((w.K2 : ℚ) : ℝ) =
    ((1 + 2 / 3 * (((w.rhoHi : ℚ) : ℝ) * ((w.rhoHi : ℚ) : ℝ))) / ((w.mLo : ℚ) : ℝ) +
      (1 + 2 / 3 * (((w.kapHi : ℚ) : ℝ) * ((w.kapHi : ℚ) : ℝ))) / (1 - ((w.mHi : ℚ) : ℝ))) /
      (8 * ((LqLo : ℚ) : ℝ)) := by
  push_cast [K2]; ring
theorem cast_betaLo :
    ((w.betaLo : ℚ) : ℝ) = 1 / (2 * (w.b2 : ℝ) * (1 - (w.r1 : ℝ) * w.b1)) := by
  push_cast [betaLo, aLo]; ring
theorem cast_pbar :
    ((w.pbar : ℚ) : ℝ) = (((P1up w.vS : ℚ) : ℝ) + ((P1up w.vI : ℚ) : ℝ)) / 2 := by
  push_cast [pbar]; ring

/-- Real form of the box constraints. -/
theorem boxOk_real (h : w.boxOk = true) :
    (0 : ℝ) < w.r1 ∧ (w.r1 : ℝ) ≤ w.r2 ∧ (w.r2 : ℝ) ≤ 1 ∧ (0 : ℝ) < w.b1 ∧ (w.b1 : ℝ) ≤ w.b2 ∧
      (w.b2 : ℝ) ≤ 1 / 2 ∧ (0 : ℝ) < w.E1 := by
  simp only [boxOk, decide_eq_true_eq] at h
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := h
  refine ⟨by exact_mod_cast q1, by exact_mod_cast q2, by exact_mod_cast q3, by exact_mod_cast q4,
    by exact_mod_cast q5, ?_, by exact_mod_cast q7⟩
  have h : ((w.b2 : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast q6
  simpa using h

end Box

/-- `H` is monotone on `[0,1/2]`. -/
theorem H_le_H {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1 / 2) : H x ≤ H y :=
  H_strictMonoOn.monotoneOn ⟨hx, hxy.trans hy⟩ ⟨hx.trans hxy, hy⟩ hxy

/-- Box geometry in real coordinates. -/
theorem box_geometry {r1 r2 b1 b2 a b : ℝ} (hr1 : 0 < r1) (hr2 : r2 ≤ 1)
    (hb1 : 0 < b1) (hb : 0 < b)
    (hra1 : r1 ≤ a / b) (hra2 : a / b ≤ r2) (hbb1 : b1 ≤ b) (hbb2 : b ≤ b2) :
    r1 * b1 ≤ a ∧ a ≤ r2 * b2 ∧ b1 * (1 + r1) / 2 ≤ (a + b) / 2 ∧ (a + b) / 2 ≤ b2 * (1 + r2) / 2 ∧
      b1 * (1 - r2) ≤ b - a ∧ b - a ≤ b2 * (1 - r1) ∧
      (b - a) / (a + b) ≤ (1 - r1) / (1 + r1) := by
  have har : a = (a / b) * b := by field_simp
  set r := a / b with hrdef
  have hr0 : 0 < r := lt_of_lt_of_le hr1 hra1
  have hr2' : 0 < r2 := lt_of_lt_of_le hr0 hra2
  have hb2 : 0 < b2 := lt_of_lt_of_le hb hbb2
  have h1r : 0 ≤ 1 - r := by linarith
  have h1r2 : 0 ≤ 1 - r2 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [har]; exact mul_le_mul hra1 hbb1 hb1.le hr0.le
  · rw [har]; exact mul_le_mul hra2 hbb2 hb.le hr2'.le
  · rw [har]
    have := mul_le_mul hbb1 (show 1 + r1 ≤ 1 + r by linarith) (by linarith) hb.le
    linarith
  · rw [har]
    have := mul_le_mul hbb2 (show 1 + r ≤ 1 + r2 by linarith) (by linarith) hb2.le
    linarith
  · rw [har]
    have := mul_le_mul hbb1 (show 1 - r2 ≤ 1 - r by linarith) h1r2 hb.le
    linarith
  · rw [har]
    have := mul_le_mul hbb2 (show 1 - r ≤ 1 - r1 by linarith) h1r hb2.le
    linarith
  · rw [har]
    have h1 : 0 < r * b + b := by positivity
    have h2 : (0 : ℝ) < 1 + r1 := by linarith
    rw [div_le_div_iff₀ h1 h2]
    have e : (b - r * b) * (1 + r1) = b * ((1 - r) * (1 + r1)) := by ring
    have e' : (1 - r1) * (r * b + b) = b * ((1 - r1) * (1 + r)) := by ring
    rw [e, e']
    apply mul_le_mul_of_nonneg_left _ hb.le
    nlinarith

/-- Pure real assembly: the normalized comparison certifies `inc ≤ j + β (b-a)^2 S`. -/
theorem assemble {inc j Δ S d2 β βlo sLo K pbar exc : ℝ}
    (hinc : inc ≤ Δ * pbar) (hj : 4 * Δ ≤ j)
    (hΔK : Δ * (pbar - 4) ≤ K * d2 * exc)
    (hβ : βlo ≤ β) (hβ0 : 0 ≤ β) (hS : sLo ≤ S) (hsLo : 0 ≤ sLo) (hd2 : 0 ≤ d2)
    (hfin : K * exc ≤ βlo * sLo) : inc ≤ j + d2 * β * S := by
  have h1 : βlo * sLo ≤ β * S := mul_le_mul hβ hS hsLo hβ0
  have h2 : d2 * (K * exc) ≤ d2 * (β * S) := mul_le_mul_of_nonneg_left (hfin.trans h1) hd2
  have e1 : Δ * pbar = 4 * Δ + Δ * (pbar - 4) := by ring
  have e2 : K * d2 * exc = d2 * (K * exc) := by ring
  have e3 : d2 * (β * S) = d2 * β * S := by ring
  linarith

/-- The first (direct) entropy-drop bound. -/
theorem K1_bound {Δ DHi dLo d K1 : ℝ} (hΔ : Δ ≤ DHi) (hdLo : 0 < dLo) (hd : dLo ≤ d)
    (hK1 : K1 = DHi / (dLo * dLo)) (hK1n : 0 ≤ K1) : Δ ≤ K1 * d ^ 2 := by
  have hsq : dLo * dLo ≤ d ^ 2 := by nlinarith
  have heq : DHi = K1 * (dLo * dLo) := by rw [hK1]; field_simp
  calc Δ ≤ DHi := hΔ
    _ = K1 * (dLo * dLo) := heq
    _ ≤ K1 * d ^ 2 := mul_le_mul_of_nonneg_left hsq hK1n

/-- The normalized entropy-drop bound with box constants. -/
theorem K2_bound {a b ρh κh mL mH Lq : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hρ : (b - a) / (a + b) ≤ ρh) (hκ : (b - a) / (2 - a - b) ≤ κh)
    (hmL : 0 < mL) (hmL' : mL ≤ (a + b) / 2) (hmH : (a + b) / 2 ≤ mH) (hmH1 : mH < 1)
    (hLq : 0 < Lq) (hLq' : Lq ≤ Real.log 2) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤
      ((1 + 2 / 3 * (ρh * ρh)) / mL + (1 + 2 / 3 * (κh * κh)) / (1 - mH)) / (8 * Lq) *
        (b - a) ^ 2 := by
  have hnorm := entropyDrop_le_normalized ha hab hb
  have hd0 : 0 < b - a := by linarith
  have hs : 0 < a + b := by linarith
  have ht : 0 < 2 - a - b := by linarith
  have hρ0 : 0 ≤ (b - a) / (a + b) := div_nonneg hd0.le hs.le
  have hκ0 : 0 ≤ (b - a) / (2 - a - b) := div_nonneg hd0.le ht.le
  have hρsq : ((b - a) / (a + b)) ^ 2 ≤ ρh * ρh := by nlinarith
  have hκsq : ((b - a) / (2 - a - b)) ^ 2 ≤ κh * κh := by nlinarith
  have hm0 : 0 < (a + b) / 2 := by linarith
  have hm1 : 0 < 1 - (a + b) / 2 := by linarith
  have hρh2 : 0 ≤ 1 + 2 / 3 * (ρh * ρh) := by nlinarith [mul_self_nonneg ρh]
  have hκh2 : 0 ≤ 1 + 2 / 3 * (κh * κh) := by nlinarith [mul_self_nonneg κh]
  have t1 : (1 + 2 / 3 * ((b - a) / (a + b)) ^ 2) / ((a + b) / 2) ≤
      (1 + 2 / 3 * (ρh * ρh)) / mL :=
    div_le_div₀ hρh2 (by linarith) hmL hmL'
  have t2 : (1 + 2 / 3 * ((b - a) / (2 - a - b)) ^ 2) / (1 - (a + b) / 2) ≤
      (1 + 2 / 3 * (κh * κh)) / (1 - mH) :=
    div_le_div₀ hκh2 (by linarith) (by linarith) (by linarith)
  have hsum := add_le_add t1 t2
  have hLL : (b - a) ^ 2 / (8 * Real.log 2) ≤ (b - a) ^ 2 / (8 * Lq) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hX : 0 ≤ (1 + 2 / 3 * ((b - a) / (a + b)) ^ 2) / ((a + b) / 2) +
      (1 + 2 / 3 * ((b - a) / (2 - a - b)) ^ 2) / (1 - (a + b) / 2) := by positivity
  calc H ((a + b) / 2) - (H a + H b) / 2 ≤ _ := hnorm
    _ ≤ (b - a) ^ 2 / (8 * Lq) *
        ((1 + 2 / 3 * ((b - a) / (a + b)) ^ 2) / ((a + b) / 2) +
          (1 + 2 / 3 * ((b - a) / (2 - a - b)) ^ 2) / (1 - (a + b) / 2)) :=
        mul_le_mul_of_nonneg_right hLL hX
    _ ≤ (b - a) ^ 2 / (8 * Lq) *
        ((1 + 2 / 3 * (ρh * ρh)) / mL + (1 + 2 / 3 * (κh * κh)) / (1 - mH)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- Entropy enclosures of the law's means from the checked rational points. -/
theorem law_H_bounds (w : Box) {a b : ℝ} (ha0 : 0 < a) (hb0 : 0 < b)
    (hbox : w.boxOk = true) (haLo : ptOk w.aLo = true) (haHi : ptOk w.aHi = true)
    (hb1ok : ptOk w.b1 = true) (hb2ok : ptOk w.b2 = true) (hmHi : ptOk w.mHi = true)
    (hr1 : (w.r1 : ℝ) ≤ a / b) (hr2 : a / b ≤ (w.r2 : ℝ))
    (hb1 : (w.b1 : ℝ) ≤ b) (hb2 : b ≤ (w.b2 : ℝ)) :
    ((Hlo w.aLo : ℚ) : ℝ) ≤ H a ∧ H a ≤ ((Hhi w.aHi : ℚ) : ℝ) ∧
      ((Hlo w.b1 : ℚ) : ℝ) ≤ H b ∧ H b ≤ ((Hhi w.b2 : ℚ) : ℝ) ∧
      H ((a + b) / 2) ≤ ((Hhi w.mHi : ℚ) : ℝ) := by
  obtain ⟨R1, _, R2, B1, _, B2, _⟩ := w.boxOk_real hbox
  obtain ⟨gaL, gaH, _, gmH, _, _, _⟩ := box_geometry R1 R2 B1 hb0 hr1 hr2 hb1 hb2
  have hb2pos : (0 : ℝ) < w.b2 := lt_of_lt_of_le hb0 hb2
  have hr2pos : (0 : ℝ) < w.r2 := lt_of_lt_of_le R1 (le_trans hr1 hr2)
  have haHi_half : (w.r2 : ℝ) * w.b2 ≤ 1 / 2 := by nlinarith
  have hmHi_half : (w.b2 : ℝ) * (1 + w.r2) / 2 ≤ 1 / 2 := by nlinarith
  have hb_half : b ≤ 1 / 2 := hb2.trans B2
  have ha_half : a ≤ 1 / 2 := gaH.trans haHi_half
  obtain ⟨HaLo, _⟩ := H_bounds haLo
  obtain ⟨_, HaHi⟩ := H_bounds haHi
  obtain ⟨Hb1L, _⟩ := H_bounds hb1ok
  obtain ⟨_, Hb2H⟩ := H_bounds hb2ok
  obtain ⟨_, HmH⟩ := H_bounds hmHi
  rw [w.cast_aLo] at HaLo
  rw [w.cast_aHi] at HaHi
  rw [w.cast_mHi] at HmH
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact HaLo.trans (H_le_H (by positivity) gaL ha_half)
  · exact (H_le_H ha0.le gaH haHi_half).trans HaHi
  · exact Hb1L.trans (H_le_H B1.le hb1 hb_half)
  · exact (H_le_H hb0.le hb2 B2).trans Hb2H
  · exact (H_le_H (by positivity) gmH hmHi_half).trans HmH

/-- The entropy drop is at most `K (b-a)^2`. -/
theorem K_bound (w : Box) {a b : ℝ} (ha0 : 0 < a) (hab : a < b) (hb1' : b < 1)
    (hbox : w.boxOk = true) (hK : 0 ≤ w.K)
    (hr1 : (w.r1 : ℝ) ≤ a / b) (hr2 : a / b ≤ (w.r2 : ℝ))
    (hb1 : (w.b1 : ℝ) ≤ b) (hb2 : b ≤ (w.b2 : ℝ))
    (hHaL : ((Hlo w.aLo : ℚ) : ℝ) ≤ H a) (hHbL : ((Hlo w.b1 : ℚ) : ℝ) ≤ H b)
    (hHmH : H ((a + b) / 2) ≤ ((Hhi w.mHi : ℚ) : ℝ)) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤ ((w.K : ℚ) : ℝ) * (b - a) ^ 2 := by
  obtain ⟨R1, _, R2, B1, _, B2, _⟩ := w.boxOk_real hbox
  have hb0 : 0 < b := ha0.trans hab
  obtain ⟨_, _, gmL, gmH, gdL, gdH, grho⟩ := box_geometry R1 R2 B1 hb0 hr1 hr2 hb1 hb2
  simp only [Box.K]
  split_ifs with hcase
  · apply K1_bound (DHi := ((w.DHi : ℚ) : ℝ)) (dLo := ((w.dLo : ℚ) : ℝ))
    · rw [w.cast_DHi, w.cast_CLo]; linarith
    · exact_mod_cast hcase.1
    · rw [w.cast_dLo]; exact gdL
    · exact w.cast_K1
    · have h : (0 : ℚ) ≤ w.K := hK
      simp only [Box.K, if_pos hcase] at h
      exact_mod_cast h
  · rw [w.cast_K2]
    obtain ⟨hL1, _⟩ := log_two_mem
    have hLq : (0 : ℝ) < ((LqLo : ℚ) : ℝ) := by simp only [LqLo]; norm_num
    have hb2pos : (0 : ℝ) < w.b2 := lt_of_lt_of_le hb0 hb2
    have hmHhalf : (w.b2 : ℝ) * (1 + w.r2) / 2 ≤ 1 / 2 := by nlinarith
    apply K2_bound ha0 hab hb1'
    · rw [w.cast_rhoHi]; exact grho
    · rw [w.cast_kapHi, w.cast_dHi, w.cast_mHi]
      have hden1 : (0 : ℝ) < 2 - a - b := by linarith
      have hden2 : (0 : ℝ) < 2 * (1 - (w.b2 : ℝ) * (1 + w.r2) / 2) := by linarith
      rw [div_le_div_iff₀ hden1 hden2]
      have h2 : 2 * (1 - (w.b2 : ℝ) * (1 + w.r2) / 2) ≤ 2 - a - b := by linarith
      have hd0 : 0 ≤ b - a := by linarith
      calc (b - a) * (2 * (1 - (w.b2 : ℝ) * (1 + w.r2) / 2)) ≤ (b - a) * (2 - a - b) :=
            mul_le_mul_of_nonneg_left h2 hd0
        _ ≤ (w.b2 : ℝ) * (1 - w.r1) * (2 - a - b) :=
            mul_le_mul_of_nonneg_right gdH hden1.le
    · rw [w.cast_mLo]; positivity
    · rw [w.cast_mLo]; exact gmL
    · rw [w.cast_mHi]; exact gmH
    · rw [w.cast_mHi]; linarith
    · exact hLq
    · exact hL1

/-- `betaLo` is a lower bound for the log-sum coefficient `1/(2 b (1-a))`. -/
theorem beta_bound (w : Box) {a b : ℝ} (hab : a < b) (hb1' : b < 1) (hbox : w.boxOk = true)
    (haL : (w.r1 : ℝ) * w.b1 ≤ a) (hb2 : b ≤ (w.b2 : ℝ)) (hb0 : 0 < b) :
    ((w.betaLo : ℚ) : ℝ) ≤ 1 / (2 * (b * (1 - a))) := by
  obtain ⟨R1, _, _, B1, _, B2, _⟩ := w.boxOk_real hbox
  rw [w.cast_betaLo]
  have hbpos : 0 < b * (1 - a) := mul_pos hb0 (by linarith)
  apply one_div_le_one_div_of_le (by positivity)
  have h1 : 1 - a ≤ 1 - (w.r1 : ℝ) * w.b1 := by linarith
  have h2 : 0 ≤ 1 - a := by linarith
  have h3 : 2 * b * (1 - a) ≤ 2 * (w.b2 : ℝ) * (1 - a) := by nlinarith
  have hb2pos : (0 : ℝ) < w.b2 := lt_of_lt_of_le hb0 hb2
  have h4 : 2 * (w.b2 : ℝ) * (1 - a) ≤ 2 * (w.b2 : ℝ) * (1 - (w.r1 : ℝ) * w.b1) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  calc 2 * (b * (1 - a)) = 2 * b * (1 - a) := by ring
    _ ≤ _ := h3.trans h4

/-- `excess` handles the sign of `pbar - 4`. -/
theorem excess_bound (w : Box) {Δ d2 : ℝ} (hΔ0 : 0 ≤ Δ) (hKb : Δ ≤ ((w.K : ℚ) : ℝ) * d2) :
    Δ * (((w.pbar : ℚ) : ℝ) - 4) ≤ ((w.K : ℚ) : ℝ) * d2 * ((w.excess : ℚ) : ℝ) := by
  simp only [Box.excess]
  split_ifs with hp
  · have hp' : (0 : ℝ) ≤ ((w.pbar : ℚ) : ℝ) - 4 := by
      have := (Rat.cast_le (K := ℝ)).mpr hp
      push_cast at this
      linarith
    push_cast
    exact mul_le_mul_of_nonneg_right hKb hp'
  · have hp' : ((w.pbar : ℚ) : ℝ) - 4 < 0 := by
      have : w.pbar - 4 < 0 := lt_of_not_ge hp
      have := (Rat.cast_lt (K := ℝ)).mpr this
      push_cast at this
      linarith
    push_cast
    have := mul_nonpos_of_nonneg_of_nonpos hΔ0 hp'.le
    linarith

set_option maxHeartbeats 1000000 in
/-- Soundness: a checked certificate proves the same-side psi Bellman inequality for every
finite interior law with means in the box and mean entropy at least `E1`. -/
theorem check_sound (w : Box) (hw : w.check = true) {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hab : μ.a < μ.b)
    (hr1 : (w.r1 : ℝ) ≤ μ.a / μ.b) (hr2 : μ.a / μ.b ≤ (w.r2 : ℝ))
    (hb1 : (w.b1 : ℝ) ≤ μ.b) (hb2 : μ.b ≤ (w.b2 : ℝ))
    (hE1 : (w.E1 : ℝ) ≤ μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  simp only [Box.check, Bool.and_eq_true] at hw
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hbox, haLo⟩, haHi⟩, hb1ok⟩, hb2ok⟩, hmHi⟩, hvS⟩, hvI⟩, hfin⟩ := hw
  have ha0 : 0 < μ.a := μ.a_interior.1
  have hb0 : 0 < μ.b := μ.b_interior.1
  have ha1 : μ.a < 1 := μ.a_interior.2
  have hb1' : μ.b < 1 := μ.b_interior.2
  obtain ⟨hHaL, hHaH, hHbL, hHbH, hHmH⟩ :=
    law_H_bounds w ha0 hb0 hbox haLo haHi hb1ok hb2ok hmHi hr1 hr2 hb1 hb2
  simp only [Box.finalOk, decide_eq_true_eq] at hfin
  obtain ⟨qsLo, qIHi, qK, qfinal⟩ := hfin
  obtain ⟨R1, _, R2, B1, _, _, _⟩ := w.boxOk_real hbox
  obtain ⟨gaL, _, _, _, _, _, _⟩ := box_geometry R1 R2 B1 hb0 hr1 hr2 hb1 hb2
  -- the law's scalar quantities; `S` is the deficit at the entropy floor `E1`
  set Δ := μ.entropyDrop with hΔ
  set s := μ.meanDeficit with hs
  set S : ℝ := (H μ.a + H μ.b) / 2 - w.E1 with hSdef
  have hΔdef : Δ = H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 := rfl
  have hsdef : s = (H μ.a + H μ.b) / 2 - μ.meanEntropy := by
    rw [hs]; unfold InteriorLaw.meanDeficit InteriorLaw.meanEntropy; ring
  have hΔ0 : 0 ≤ Δ := μ.entropyDrop_nonneg
  have hs0 : 0 ≤ s := μ.meanDeficit_mem.1
  have hsS : s ≤ S := by rw [hsdef, hSdef]; linarith
  have hS0 : 0 ≤ S := hs0.trans hsS
  have hS_lo : ((w.sLo : ℚ) : ℝ) ≤ S := by rw [w.cast_sLo, w.cast_CLo, hSdef]; linarith
  have hS_hi : S ≤ ((w.sHi : ℚ) : ℝ) := by rw [w.cast_sHi, w.cast_CHi, hSdef]; linarith
  have hI_hi : Δ + S ≤ ((w.IHi : ℚ) : ℝ) := by rw [w.cast_IHi, hΔdef, hSdef]; linarith
  have hIHi1 : ((w.IHi : ℚ) : ℝ) < 1 := by exact_mod_cast qIHi
  have hI1 : Δ + S < 1 := lt_of_le_of_lt hI_hi hIHi1
  -- increment bound at S via trapezoid and anchors
  have htrap := P_trapezoid hS0 (le_add_of_nonneg_left hΔ0) hI1
  have hPS := anchorOk_sound hvS hS0 hS_hi
  have hPI := anchorOk_sound hvI (by linarith) hI_hi
  have hinc : P (Δ + S) - P S ≤ Δ * ((w.pbar : ℚ) : ℝ) := by
    rw [w.cast_pbar]
    have h1 : (Δ + S - S) = Δ := by ring
    rw [h1] at htrap
    have := mul_le_mul_of_nonneg_left (add_le_add hPS hPI) hΔ0
    linarith
  -- Δ ≤ K (b-a)^2, beta, excess
  have hKb : Δ ≤ ((w.K : ℚ) : ℝ) * (μ.b - μ.a) ^ 2 :=
    K_bound w ha0 hab hb1' hbox qK hr1 hr2 hb1 hb2 hHaL hHbL hHmH
  have hbeta := beta_bound w hab hb1' hbox gaL hb2 hb0
  have hexc := excess_bound w hΔ0 hKb
  have hfinR : ((w.K : ℚ) : ℝ) * ((w.excess : ℚ) : ℝ) ≤
      ((w.betaLo : ℚ) : ℝ) * ((w.sLo : ℚ) : ℝ) := by exact_mod_cast qfinal
  have hsLoR : (0 : ℝ) ≤ ((w.sLo : ℚ) : ℝ) := by exact_mod_cast qsLo
  have hbpos : 0 < μ.b * (1 - μ.a) := mul_pos hb0 (by linarith)
  -- G(S) ≥ 0
  have hj := four_entropyDrop_le_interiorCost ha0 ha1 hb0 hb1'
  rw [← hΔdef] at hj
  have hGS := assemble hinc hj hexc hbeta (by positivity) hS_lo hsLoR (sq_nonneg _) hfinR
  set α : ℝ := (μ.b - μ.a) ^ 2 * (1 / (2 * (μ.b * (1 - μ.a)))) with hα
  have hend : 0 ≤ Scalar.gap (interiorCost μ.a μ.b) α Δ S := by
    unfold Scalar.gap
    linarith
  have hzero : P Δ ≤ interiorCost μ.a μ.b := by
    rw [hΔdef]; exact deterministic_cap_bound ha0 ha1 hb0 hb1'
  have hcrit := Scalar.gap_endpoint_criterion hΔ0 hS0 hI1 hzero hend hs0 hsS
  -- the log-sum cost floor
  have hV : LogSum.V μ.a μ.b = μ.b * (1 - μ.a) := by
    simp only [LogSum.V, max_eq_right hab.le, min_eq_left hab.le]
  have hfloor : μ.psiLogSumCostFloor = interiorCost μ.a μ.b + α * s := by
    unfold InteriorLaw.psiLogSumCostFloor
    rw [hV, hsdef, hα]
    unfold InteriorLaw.meanEntropy
    field_simp
    ring
  have hmain : μ.splitBound ≤ μ.cost := by
    have e : μ.splitBound = P (Δ + s) - P s := rfl
    rw [e]
    calc P (Δ + s) - P s ≤ interiorCost μ.a μ.b + α * s := hcrit
      _ = μ.psiLogSumCostFloor := hfloor.symm
      _ ≤ μ.cost := μ.psiLogSumCostFloor_le_cost
  exact μ.gap_le_of_splitBound hactive hmain

end CKLaneE.NLS

#check @CKLaneE.NLS.check_sound
#print axioms CKLaneE.NLS.check_sound

end


