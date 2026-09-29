-- Prove2me | Definitions.Def_CK_CKLaneM1_MLChecker
-- name    : CK_CKLaneM1_MLChecker
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T12:39:37.019395+00:00
-- url     : https://prove2.me/theorems/1d7454f8-1f62-4b40-a6da-61dc6117a1ce
-- title:
--   Courtade–Kumar proof module `CKLaneM1.MLChecker` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM1.MLChecker` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM1.MLChecker` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM1.MLChecker (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM1/MLChecker.lean)

import Definitions.Def_CK_CKLaneM1_MLSupport
import Definitions.Def_CK_GeneralCK_PsiLogSumOwner
import Definitions.Def_CK_GeneralCK_ScalarGap

-- ===== source module CKLaneM1.MLChecker =====
section

/-!
# Lane M1: Boolean checker for the archived same-side method `mean_logsum`, with law-level soundness

Archive (`same_side/COVER.py`, owner `mean_logsum`): on a leaf box in `x = -log₂(a/b)`, `b`,
`t = E / ((H a + H b)/2)`, accept when

    j_n + β_lo s_lo ≥ K p̄

with `K ≥ Δ/d²`, `j_n ≤ j/d²` evaluated through the exact normalized identities
(`Δ = (m Cn ρ + (1-m) Cn κ)/log 2`, `j = (2mρ A ρ + 2(1-m) κ A κ)/log 2`, `ρ = d/(2m)`, `κ = kρ`,
`k = m/(1-m)`; corpus `SmallMean.normalized_entropy_chain` / `normalized_cost_chain`) and the two
monotone ratios `Cn z / z²`, `A z / z`, and `p̄ ≥ (P1 s + P1 I)/2` from slope anchors.

The Lean log-sum floor (`InteriorLaw.psiLogSumCostFloor`) has coefficient `β = 1/(2 b (1-a))`
(the archive's `κ(a) ≥ 1` enhancement is not in the corpus), so a leaf may carry a finite binary
subdivision (`MTree`) of its box; every cell is checked with the same inequality.

`cellCheck B c = true → SemR B` and `checkLeaf p w = true → SemSS (ssBox p)` where `SemSS` is the
owner statement `μ.a < μ.b → (law in the exact archived box) → φ ≤ ψ at the parent → gap ≤ cost`.
Every primitive enclosure (logs, entropies, both ratios, slope anchors, `2^-x`) is recomputed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM1.ML

open GeneralCK GeneralCK.Scalar Set CKLaneE.FP CKLaneM1

/-! ## Boxes and the semantic statement -/

/-- A rational box in `(r, b, t)` with `r = a/b` and `E = t · (H a + H b)/2`. -/
structure RBox where
  r1 : ℚ
  r2 : ℚ
  b0 : ℚ
  b1 : ℚ
  t0 : ℚ
  t1 : ℚ
  deriving Repr, DecidableEq

def InR (B : RBox) (a b E : ℝ) : Prop :=
  (B.r1 : ℝ) ≤ a / b ∧ a / b ≤ (B.r2 : ℝ) ∧ (B.b0 : ℝ) ≤ b ∧ b ≤ (B.b1 : ℝ) ∧
    (B.t0 : ℝ) * ((H a + H b) / 2) ≤ E ∧ E ≤ (B.t1 : ℝ) * ((H a + H b) / 2)

/-- Law-level psi-owner statement on the box. -/
def SemR (B : RBox) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b → InR B μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

/-- Untrusted per-cell witness: rational points only. -/
structure Cell where
  aL : ℚ
  aH : ℚ
  mH : ℚ
  rhoH : ℚ
  kapH : ℚ
  rhoL : ℚ
  kapL : ℚ
  vS : ℚ
  vI : ℚ
  deriving Repr, DecidableEq

section defs
variable (B : RBox) (c : Cell)

def mLo : ℚ := B.b0 * (1 + B.r1) / 2
def mHi : ℚ := B.b1 * (1 + B.r2) / 2
def kLo : ℚ := mLo B / (1 - mLo B)
def kHi : ℚ := mHi B / (1 - mHi B)
def dHi : ℚ := B.b1 * (1 - B.r1)
def CLo : ℚ := (Hlo c.aL + Hlo B.b0) / 2
def CHi : ℚ := (Hhi c.aH + Hhi B.b1) / 2
def sLo : ℚ := (1 - B.t1) * CLo B c
def sHi : ℚ := (1 - B.t0) * CHi B c
def KHi : ℚ := (cH c.rhoH + kHi B * cH c.kapH) / (4 * mLo B * LqLo)
def IHi : ℚ := min (Hhi c.mH - B.t0 * CLo B c) (sHi B c + KHi B c * (dHi B * dHi B))
def jnLo : ℚ := (aLo c.rhoL + kLo B * aLo c.kapL) / (2 * mHi B * LqHi)
def betaLo : ℚ := 1 / (2 * B.b1 * (1 - c.aL))
def pbar : ℚ := (P1up c.vS + P1up c.vI) / 2

def boxOk : Bool :=
  decide (0 < B.r1 ∧ B.r1 ≤ B.r2 ∧ B.r2 ≤ 1 ∧ 0 < B.b0 ∧ B.b0 ≤ B.b1 ∧ B.b1 ≤ 1 / 2 ∧
    0 ≤ B.t0 ∧ B.t0 ≤ B.t1 ∧ B.t1 ≤ 1)

def pointsOk : Bool :=
  decide (0 < c.aL ∧ c.aL ≤ B.r1 * B.b0 ∧ B.r2 * B.b1 ≤ c.aH ∧ c.aH ≤ 1 / 2 ∧
      mHi B ≤ c.mH ∧ c.mH ≤ 1 / 2) &&
    ptOk c.aL && ptOk c.aH && ptOk B.b0 && ptOk B.b1 && ptOk c.mH

def ratioOk : Bool :=
  decide ((1 - B.r1) / (1 + B.r1) ≤ c.rhoH ∧ 0 ≤ c.rhoL ∧ c.rhoL ≤ (1 - B.r2) / (1 + B.r2) ∧
      kHi B * c.rhoH ≤ c.kapH ∧ 0 ≤ c.kapL ∧ c.kapL ≤ kLo B * c.rhoL) &&
    cHok c.rhoH && cHok c.kapH && aLook c.rhoL && aLook c.kapL

def finalOk : Bool :=
  anchorOk c.vS (sHi B c) && anchorOk c.vI (IHi B c) &&
    decide (0 ≤ sLo B c ∧ IHi B c < 1 ∧ KHi B c * pbar c ≤ jnLo B c + betaLo B c * sLo B c)

/-- The Boolean cell checker (archived `mean_logsum` inequality, Lean log-sum coefficient). -/
def cellCheck : Bool := boxOk B && pointsOk B c && ratioOk B c && finalOk B c

end defs

/-! ## Casts -/
section casts
variable (B : RBox) (c : Cell)
theorem c_mLo : ((mLo B : ℚ) : ℝ) = (B.b0 : ℝ) * (1 + B.r1) / 2 := by push_cast [mLo]; ring
theorem c_mHi : ((mHi B : ℚ) : ℝ) = (B.b1 : ℝ) * (1 + B.r2) / 2 := by push_cast [mHi]; ring
theorem c_kLo : ((kLo B : ℚ) : ℝ) = ((mLo B : ℚ) : ℝ) / (1 - ((mLo B : ℚ) : ℝ)) := by
  push_cast [kLo]; ring
theorem c_kHi : ((kHi B : ℚ) : ℝ) = ((mHi B : ℚ) : ℝ) / (1 - ((mHi B : ℚ) : ℝ)) := by
  push_cast [kHi]; ring
theorem c_dHi : ((dHi B : ℚ) : ℝ) = (B.b1 : ℝ) * (1 - B.r1) := by push_cast [dHi]; ring
theorem c_CLo : ((CLo B c : ℚ) : ℝ) = (((Hlo c.aL : ℚ) : ℝ) + ((Hlo B.b0 : ℚ) : ℝ)) / 2 := by
  push_cast [CLo]; ring
theorem c_CHi : ((CHi B c : ℚ) : ℝ) = (((Hhi c.aH : ℚ) : ℝ) + ((Hhi B.b1 : ℚ) : ℝ)) / 2 := by
  push_cast [CHi]; ring
theorem c_sLo : ((sLo B c : ℚ) : ℝ) = (1 - (B.t1 : ℝ)) * ((CLo B c : ℚ) : ℝ) := by
  push_cast [sLo]; ring
theorem c_sHi : ((sHi B c : ℚ) : ℝ) = (1 - (B.t0 : ℝ)) * ((CHi B c : ℚ) : ℝ) := by
  push_cast [sHi]; ring
theorem c_KHi : ((KHi B c : ℚ) : ℝ) =
    (((cH c.rhoH : ℚ) : ℝ) + ((kHi B : ℚ) : ℝ) * ((cH c.kapH : ℚ) : ℝ)) /
      (4 * ((mLo B : ℚ) : ℝ) * ((LqLo : ℚ) : ℝ)) := by
  push_cast [KHi]; ring
theorem c_IHi : ((IHi B c : ℚ) : ℝ) =
    min (((Hhi c.mH : ℚ) : ℝ) - (B.t0 : ℝ) * ((CLo B c : ℚ) : ℝ))
      (((sHi B c : ℚ) : ℝ) + ((KHi B c : ℚ) : ℝ) * (((dHi B : ℚ) : ℝ) * ((dHi B : ℚ) : ℝ))) := by
  simp only [IHi, Rat.cast_min]; push_cast; ring_nf
theorem c_jnLo : ((jnLo B c : ℚ) : ℝ) =
    (((aLo c.rhoL : ℚ) : ℝ) + ((kLo B : ℚ) : ℝ) * ((aLo c.kapL : ℚ) : ℝ)) /
      (2 * ((mHi B : ℚ) : ℝ) * ((LqHi : ℚ) : ℝ)) := by
  push_cast [jnLo]; ring
theorem c_betaLo : ((betaLo B c : ℚ) : ℝ) = 1 / (2 * (B.b1 : ℝ) * (1 - (c.aL : ℝ))) := by
  push_cast [betaLo]; ring
theorem c_pbar : ((pbar c : ℚ) : ℝ) = (((P1up c.vS : ℚ) : ℝ) + ((P1up c.vI : ℚ) : ℝ)) / 2 := by
  push_cast [pbar]; ring
end casts

/-! ## Real-analytic core -/

theorem H_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1 / 2) : H x ≤ H y :=
  H_strictMonoOn.monotoneOn ⟨hx, hxy.trans hy⟩ ⟨hx.trans hxy, hy⟩ hxy

theorem Hlo_le {q : ℚ} (h : ptOk q = true) {x : ℝ} (hqx : (q : ℝ) ≤ x) (hx : x ≤ 1 / 2) :
    ((Hlo q : ℚ) : ℝ) ≤ H x := by
  have hq := ptOk_pos h
  have hq0 : (0 : ℝ) ≤ q := by exact_mod_cast hq.1.le
  exact (H_bounds h).1.trans (H_mono hq0 hqx hx)

theorem le_Hhi {q : ℚ} (h : ptOk q = true) {x : ℝ} (hx0 : 0 ≤ x) (hxq : x ≤ (q : ℝ))
    (hq : (q : ℝ) ≤ 1 / 2) : H x ≤ ((Hhi q : ℚ) : ℝ) :=
  (H_mono hx0 hxq hq).trans (H_bounds h).2

/-- `(1-r)/(1+r)` is antitone. -/
theorem rho_anti {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) : (1 - s) / (1 + s) ≤ (1 - r) / (1 + r) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- The two normalized identities with box constants: `Δ ≤ K d²`, `j_n d² ≤ j` (times `log 2`). -/
theorem drop_cost_box {a b mL mH kH kL rH rL qH qL cR cK aR aK : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hmL0 : 0 < mL) (hmL : mL ≤ (a + b) / 2) (hmH : (a + b) / 2 ≤ mH) (hmH1 : mH < 1)
    (hkH : kH = mH / (1 - mH)) (hkL : kL = mL / (1 - mL))
    (hrH : (b - a) / (a + b) ≤ rH) (hrL : rL ≤ (b - a) / (a + b)) (hrL0 : 0 ≤ rL)
    (hqH : kH * rH ≤ qH) (hqL : qL ≤ kL * rL) (hqL0 : 0 ≤ qL)
    (hcR : ∀ ρ, 0 < ρ → ρ ≤ rH → SmallMean.Cn ρ / ρ ^ 2 ≤ cR)
    (hcK : ∀ ρ, 0 < ρ → ρ ≤ qH → SmallMean.Cn ρ / ρ ^ 2 ≤ cK)
    (haR : ∀ ρ, rL ≤ ρ → 0 < ρ → ρ < 1 → aR ≤ SmallMean.A ρ / ρ)
    (haK : ∀ ρ, qL ≤ ρ → 0 < ρ → ρ < 1 → aK ≤ SmallMean.A ρ / ρ)
    (hcR0 : 0 ≤ cR) (hcK0 : 0 ≤ cK) (haR0 : 0 ≤ aR) (haK0 : 0 ≤ aK) :
    Real.log 2 * (H ((a + b) / 2) - (H a + H b) / 2) ≤ (cR + kH * cK) / (4 * mL) * (b - a) ^ 2 ∧
    (aR + kL * aK) / (2 * mH) * (b - a) ^ 2 ≤ Real.log 2 * interiorCost a b := by
  have hs : 0 < a + b := by linarith only [ha, hab]
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = (a + b) / 2 := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = (b - a) / (a + b) := ⟨_, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ, k = m / (1 - m) := ⟨_, rfl⟩
  rw [← hmdef] at hmL hmH ⊢
  rw [← hρdef] at hrH hrL
  have hm0 : 0 < m := by rw [hmdef]; linarith only [hs]
  have hm1 : m < 1 := by rw [hmdef]; linarith only [hab, hb]
  have h1m : 0 < 1 - m := by linarith only [hm1]
  have hρ0 : 0 < ρ := by rw [hρdef]; exact div_pos (by linarith only [hab]) hs
  have hρ1 : ρ < 1 := by rw [hρdef]; exact (div_lt_one hs).mpr (by linarith only [ha])
  have hae : m * (1 - ρ) = a := by
    rw [hmdef, hρdef]; field_simp; ring
  have hbe : m * (1 + ρ) = b := by
    rw [hmdef, hρdef]; field_simp; ring
  have hbn : m * (1 + ρ) < 1 := by rw [hbe]; exact hb
  have hE := SmallMean.normalized_entropy_chain hm0 hm1 hρ0.le hρ1 hbn hkdef
  have hC := SmallMean.normalized_cost_chain hm0 hm1 hρ0.le hρ1 hbn hkdef
  rw [hae, hbe] at hE hC
  have hk0 : 0 < k := by rw [hkdef]; exact div_pos hm0 h1m
  have hkm : (1 - m) * k = m := by
    rw [hkdef]; field_simp
  have hκ1 : k * ρ < 1 := by
    rw [hkdef, div_mul_eq_mul_div, div_lt_one h1m]
    linarith only [hbn]
  have hκ0 : 0 < k * ρ := mul_pos hk0 hρ0
  have hk_le : k ≤ kH := by
    rw [hkH, hkdef]
    exact div_le_div₀ (by linarith only [hm0, hmH]) hmH (by linarith only [hmH1])
      (by linarith only [hmH])
  have hk_ge : kL ≤ k := by
    rw [hkL, hkdef]; exact div_le_div₀ hm0.le hmL h1m (by linarith only [hmL])
  have hkH0 : 0 ≤ kH := hk0.le.trans hk_le
  have hκH : k * ρ ≤ qH := (mul_le_mul hk_le hrH hρ0.le hkH0).trans hqH
  have hκL : qL ≤ k * ρ := hqL.trans (mul_le_mul hk_ge hrL hrL0 hk0.le)
  have hCρ : SmallMean.Cn ρ ≤ cR * ρ ^ 2 := by
    have h := hcR ρ hρ0 hrH
    rwa [div_le_iff₀ (by positivity)] at h
  have hCκ : SmallMean.Cn (k * ρ) ≤ cK * (k * ρ) ^ 2 := by
    have h := hcK (k * ρ) hκ0 hκH
    rwa [div_le_iff₀ (by positivity)] at h
  have hAρ : aR * ρ ≤ SmallMean.A ρ := by
    have h := haR ρ hrL hρ0 hρ1
    rwa [le_div_iff₀ hρ0] at h
  have hAκ : aK * (k * ρ) ≤ SmallMean.A (k * ρ) := by
    have h := haK (k * ρ) hκL hκ0 hκ1
    rwa [le_div_iff₀ hκ0] at h
  have hd : b - a = 2 * m * ρ := by rw [← hae, ← hbe]; ring
  constructor
  · rw [hE]
    have hX : 0 ≤ cR + kH * cK := by positivity
    have step1 : m * SmallMean.Cn ρ + (1 - m) * SmallMean.Cn (k * ρ) ≤
        m * (cR * ρ ^ 2) + (1 - m) * (cK * (k * ρ) ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hCρ hm0.le) (mul_le_mul_of_nonneg_left hCκ h1m.le)
    have step2 : m * (cR * ρ ^ 2) + (1 - m) * (cK * (k * ρ) ^ 2) = m * ρ ^ 2 * (cR + k * cK) := by
      linear_combination (cK * k * ρ ^ 2) * hkm
    have step3 : m * ρ ^ 2 * (cR + k * cK) ≤ m * ρ ^ 2 * (cR + kH * cK) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_right hk_le hcK0))
        (by positivity)
    have key : m * ρ ^ 2 * (cR + kH * cK) * mL ≤ m * ρ ^ 2 * (cR + kH * cK) * m :=
      mul_le_mul_of_nonneg_left hmL (by positivity)
    have step4 : m * ρ ^ 2 * (cR + kH * cK) ≤ (cR + kH * cK) / (4 * mL) * (b - a) ^ 2 := by
      rw [hd]
      calc m * ρ ^ 2 * (cR + kH * cK) = m * ρ ^ 2 * (cR + kH * cK) * mL / mL := by
            field_simp
        _ ≤ m * ρ ^ 2 * (cR + kH * cK) * m / mL := div_le_div_of_nonneg_right key hmL0.le
        _ = (cR + kH * cK) / (4 * mL) * (2 * m * ρ) ^ 2 := by
            field_simp; ring
    linarith only [step1, step2, step3, step4]
  · rw [hC]
    have hkL0 : 0 ≤ kL := by rw [hkL]; exact div_nonneg hmL0.le (by linarith only [hmL, hm1])
    have hY : 0 ≤ aR + kL * aK := by positivity
    have step1 : 2 * m * ρ * (aR * ρ) + 2 * (1 - m) * (k * ρ) * (aK * (k * ρ)) ≤
        2 * m * ρ * SmallMean.A ρ + 2 * (1 - m) * (k * ρ) * SmallMean.A (k * ρ) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hAρ (by positivity)
      · exact mul_le_mul_of_nonneg_left hAκ (by positivity)
    have step2 : 2 * m * ρ * (aR * ρ) + 2 * (1 - m) * (k * ρ) * (aK * (k * ρ)) =
        2 * m * ρ ^ 2 * (aR + k * aK) := by
      linear_combination (2 * aK * k * ρ ^ 2) * hkm
    have step3 : 2 * m * ρ ^ 2 * (aR + kL * aK) ≤ 2 * m * ρ ^ 2 * (aR + k * aK) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_right hk_ge haK0))
        (by positivity)
    have key : m * ρ ^ 2 * (aR + kL * aK) * m ≤ m * ρ ^ 2 * (aR + kL * aK) * mH :=
      mul_le_mul_of_nonneg_left hmH (by positivity)
    have hmH0 : 0 < mH := lt_of_lt_of_le hm0 hmH
    have step4 : (aR + kL * aK) / (2 * mH) * (b - a) ^ 2 ≤ 2 * m * ρ ^ 2 * (aR + kL * aK) := by
      rw [hd]
      calc (aR + kL * aK) / (2 * mH) * (2 * m * ρ) ^ 2 =
            2 * (m * ρ ^ 2 * (aR + kL * aK) * m) / mH := by
            field_simp
        _ ≤ 2 * (m * ρ ^ 2 * (aR + kL * aK) * mH) / mH := by
            apply div_le_div_of_nonneg_right _ hmH0.le
            linarith only [key]
        _ = 2 * m * ρ ^ 2 * (aR + kL * aK) := by
            field_simp
    linarith only [step1, step2, step3, step4]

/-! ## Soundness of one cell -/

set_option maxHeartbeats 4000000 in
theorem cellCheck_sound {B : RBox} {c : Cell} (h : cellCheck B c = true) : SemR B := by
  intro k μ hab hin hact
  unfold cellCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hbox, hpts⟩, hrat⟩, hfin⟩ := h
  simp only [boxOk, decide_eq_true_eq] at hbox
  obtain ⟨R1, R12, R2, B0, B01, B1, T0, T01, T1⟩ := hbox
  simp only [pointsOk, Bool.and_eq_true, decide_eq_true_eq] at hpts
  obtain ⟨⟨⟨⟨⟨⟨PaL0, PaL, PaH, PaH2, PmH, PmH2⟩, okaL⟩, okaH⟩, okb0⟩, okb1⟩, okmH⟩ := hpts
  simp only [ratioOk, Bool.and_eq_true, decide_eq_true_eq] at hrat
  obtain ⟨⟨⟨⟨⟨QrH, QrL0, QrL, QkH, QkL0, QkL⟩, okcR⟩, okcK⟩, okaR⟩, okaK⟩ := hrat
  simp only [finalOk, Bool.and_eq_true, decide_eq_true_eq] at hfin
  obtain ⟨⟨okvS, okvI⟩, FsLo, FIHi, Ffin⟩ := hfin
  -- real forms of the rational side conditions
  have r1 : (0 : ℝ) < B.r1 := by exact_mod_cast R1
  have r12 : (B.r1 : ℝ) ≤ B.r2 := by exact_mod_cast R12
  have r2 : (B.r2 : ℝ) ≤ 1 := by exact_mod_cast R2
  have b0 : (0 : ℝ) < B.b0 := by exact_mod_cast B0
  have b1 : (B.b1 : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr B1; push_cast at h; exact h
  have t0 : (0 : ℝ) ≤ B.t0 := by exact_mod_cast T0
  have t1 : (B.t1 : ℝ) ≤ 1 := by exact_mod_cast T1
  have paL0 : (0 : ℝ) < c.aL := by exact_mod_cast PaL0
  have paL : (c.aL : ℝ) ≤ B.r1 * B.b0 := by exact_mod_cast PaL
  have paH : (B.r2 : ℝ) * B.b1 ≤ c.aH := by exact_mod_cast PaH
  have paH2 : (c.aH : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr PaH2; push_cast at h; exact h
  have pmH : ((mHi B : ℚ) : ℝ) ≤ c.mH := by exact_mod_cast PmH
  have pmH2 : (c.mH : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr PmH2; push_cast at h; exact h
  have qrH : (1 - (B.r1 : ℝ)) / (1 + B.r1) ≤ c.rhoH := by
    have h := (Rat.cast_le (K := ℝ)).mpr QrH; push_cast at h; exact h
  have qrL0 : (0 : ℝ) ≤ c.rhoL := by exact_mod_cast QrL0
  have qrL : (c.rhoL : ℝ) ≤ (1 - (B.r2 : ℝ)) / (1 + B.r2) := by
    have h := (Rat.cast_le (K := ℝ)).mpr QrL; push_cast at h; exact h
  have qkH : ((kHi B : ℚ) : ℝ) * c.rhoH ≤ c.kapH := by exact_mod_cast QkH
  have qkL0 : (0 : ℝ) ≤ c.kapL := by exact_mod_cast QkL0
  have qkL : (c.kapL : ℝ) ≤ ((kLo B : ℚ) : ℝ) * c.rhoL := by exact_mod_cast QkL
  have fsLo : (0 : ℝ) ≤ ((sLo B c : ℚ) : ℝ) := by exact_mod_cast FsLo
  have fIHi : ((IHi B c : ℚ) : ℝ) < 1 := by exact_mod_cast FIHi
  have ffin : ((KHi B c : ℚ) : ℝ) * ((pbar c : ℚ) : ℝ) ≤
      ((jnLo B c : ℚ) : ℝ) + ((betaLo B c : ℚ) : ℝ) * ((sLo B c : ℚ) : ℝ) := by exact_mod_cast Ffin
  -- the law
  obtain ⟨hr1, hr2, hbb0, hbb1, hE0, hE1⟩ := hin
  have ha0 : 0 < μ.a := μ.a_interior.1
  have hb0 : 0 < μ.b := μ.b_interior.1
  have ha1 : μ.a < 1 := μ.a_interior.2
  have hb1 : μ.b < 1 := μ.b_interior.2
  have hrpos : 0 ≤ μ.a / μ.b := div_nonneg ha0.le hb0.le
  have hr_eq : μ.a = μ.a / μ.b * μ.b := by field_simp
  have haLo : (c.aL : ℝ) ≤ μ.a := by
    calc (c.aL : ℝ) ≤ B.r1 * B.b0 := paL
      _ ≤ μ.a / μ.b * μ.b := mul_le_mul hr1 hbb0 b0.le hrpos
      _ = μ.a := hr_eq.symm
  have haHi : μ.a ≤ (c.aH : ℝ) := by
    calc μ.a = μ.a / μ.b * μ.b := hr_eq
      _ ≤ B.r2 * B.b1 := mul_le_mul hr2 hbb1 hb0.le (r1.le.trans r12)
      _ ≤ c.aH := paH
  have hbhalf : μ.b ≤ 1 / 2 := hbb1.trans b1
  have HaL : ((Hlo c.aL : ℚ) : ℝ) ≤ H μ.a := Hlo_le okaL haLo (haHi.trans paH2)
  have HaH : H μ.a ≤ ((Hhi c.aH : ℚ) : ℝ) := le_Hhi okaH ha0.le haHi paH2
  have HbL : ((Hlo B.b0 : ℚ) : ℝ) ≤ H μ.b := Hlo_le okb0 hbb0 hbhalf
  have HbH : H μ.b ≤ ((Hhi B.b1 : ℚ) : ℝ) := le_Hhi okb1 hb0.le hbb1 b1
  -- the midpoint
  have hm_eq : (μ.a + μ.b) / 2 = μ.b * (1 + μ.a / μ.b) / 2 := by
    field_simp
    ring
  have hmLo : ((mLo B : ℚ) : ℝ) ≤ (μ.a + μ.b) / 2 := by
    rw [c_mLo, hm_eq]
    have := mul_le_mul hbb0 (show 1 + (B.r1 : ℝ) ≤ 1 + μ.a / μ.b by linarith only [hr1])
      (by linarith only [r1]) hb0.le
    linarith only [this]
  have hmHi : (μ.a + μ.b) / 2 ≤ ((mHi B : ℚ) : ℝ) := by
    rw [c_mHi, hm_eq]
    have := mul_le_mul hbb1 (show 1 + μ.a / μ.b ≤ 1 + (B.r2 : ℝ) by linarith only [hr2])
      (by linarith only [hrpos]) (b0.le.trans (by exact_mod_cast B01))
    linarith only [this]
  have hmLo0 : (0 : ℝ) < ((mLo B : ℚ) : ℝ) := by rw [c_mLo]; positivity
  have hmHi1 : ((mHi B : ℚ) : ℝ) < 1 := by
    rw [c_mHi]
    have h := mul_le_mul b1 (show 1 + (B.r2 : ℝ) ≤ 2 by linarith only [r2])
      (by linarith only [r1, r12]) (by norm_num)
    linarith only [h]
  have HmH : H ((μ.a + μ.b) / 2) ≤ ((Hhi c.mH : ℚ) : ℝ) :=
    le_Hhi okmH (by positivity) (hmHi.trans pmH) pmH2
  -- entropy quantities
  set C : ℝ := (H μ.a + H μ.b) / 2 with hCdef
  have hCLo : ((CLo B c : ℚ) : ℝ) ≤ C := by rw [c_CLo, hCdef]; linarith only [HaL, HbL]
  have hCHi : C ≤ ((CHi B c : ℚ) : ℝ) := by rw [c_CHi, hCdef]; linarith only [HaH, HbH]
  set s := μ.meanDeficit with hsdef'
  have hsdef : s = C - μ.meanEntropy := by
    rw [hsdef', hCdef]; unfold InteriorLaw.meanDeficit InteriorLaw.meanEntropy; ring
  have hs0 : 0 ≤ s := μ.meanDeficit_mem.1
  have hsLo : ((sLo B c : ℚ) : ℝ) ≤ s := by
    rw [c_sLo, hsdef]
    have h1 := mul_le_mul_of_nonneg_left hCLo (show (0 : ℝ) ≤ 1 - B.t1 by linarith only [t1])
    linarith only [h1, hE1]
  have hsHi : s ≤ ((sHi B c : ℚ) : ℝ) := by
    rw [c_sHi, hsdef]
    have h1 := mul_le_mul_of_nonneg_left hCHi (show (0 : ℝ) ≤ 1 - B.t0 by
      linarith only [t1, (show (B.t0 : ℝ) ≤ B.t1 by exact_mod_cast T01)])
    linarith only [h1, hE0]
  set Δ := μ.entropyDrop with hΔdef'
  have hΔdef : Δ = H ((μ.a + μ.b) / 2) - C := rfl
  have hΔ0 : 0 ≤ Δ := μ.entropyDrop_nonneg
  -- ratio facts
  have hrho_eq : (μ.b - μ.a) / (μ.a + μ.b) = (1 - μ.a / μ.b) / (1 + μ.a / μ.b) := by
    field_simp
    ring
  have hrhoH : (μ.b - μ.a) / (μ.a + μ.b) ≤ c.rhoH := by
    rw [hrho_eq]; exact (rho_anti r1.le hr1).trans qrH
  have hrhoL : (c.rhoL : ℝ) ≤ (μ.b - μ.a) / (μ.a + μ.b) := by
    rw [hrho_eq]; exact qrL.trans (rho_anti hrpos hr2)
  obtain ⟨hDrop, hCost⟩ := drop_cost_box ha0 hab hb1 hmLo0 hmLo hmHi hmHi1 (c_kHi B) (c_kLo B)
    hrhoH hrhoL qrL0 qkH qkL qkL0
    (fun ρ h0 h1 => cH_le okcR h0 h1) (fun ρ h0 h1 => cH_le okcK h0 h1)
    (fun ρ h1 h0 h2 => aLo_le okaR h1 h0 h2) (fun ρ h1 h0 h2 => aLo_le okaK h1 h0 h2)
    (cH_nonneg okcR) (cH_nonneg okcK)
    (by have := one_le_aLo c.rhoL; have h' : (1 : ℝ) ≤ ((aLo c.rhoL : ℚ) : ℝ) := by
          exact_mod_cast this
        linarith only [h'])
    (by have := one_le_aLo c.kapL; have h' : (1 : ℝ) ≤ ((aLo c.kapL : ℚ) : ℝ) := by
          exact_mod_cast this
        linarith only [h'])
  have hL := log_two_pos
  obtain ⟨hL1, hL2⟩ := log_two_mem
  have hLq := LqLo_pos
  set d2 : ℝ := (μ.b - μ.a) ^ 2 with hd2def
  have hd20 : 0 ≤ d2 := sq_nonneg _
  -- Δ ≤ KHi d²
  have hX0 : 0 ≤ ((cH c.rhoH : ℚ) : ℝ) + ((kHi B : ℚ) : ℝ) * ((cH c.kapH : ℚ) : ℝ) := by
    have h1 := cH_nonneg okcR
    have h2 := cH_nonneg okcK
    have h3 : (0 : ℝ) ≤ ((kHi B : ℚ) : ℝ) := by
      rw [c_kHi]
      have hmHi0 : (0 : ℝ) < ((mHi B : ℚ) : ℝ) := lt_of_lt_of_le hmLo0 (hmLo.trans hmHi)
      exact div_nonneg hmHi0.le (by linarith only [hmHi1])
    positivity
  have hKHi0 : (0 : ℝ) ≤ ((KHi B c : ℚ) : ℝ) := by rw [c_KHi]; positivity
  have hDelta : Δ ≤ ((KHi B c : ℚ) : ℝ) * d2 := by
    rw [hΔdef, c_KHi]
    set X := ((cH c.rhoH : ℚ) : ℝ) + ((kHi B : ℚ) : ℝ) * ((cH c.kapH : ℚ) : ℝ) with hXdef
    have hY0 : 0 ≤ X / (4 * ((mLo B : ℚ) : ℝ)) * d2 := by positivity
    calc H ((μ.a + μ.b) / 2) - C = (Real.log 2 * (H ((μ.a + μ.b) / 2) - C)) / Real.log 2 := by
          field_simp
      _ ≤ (X / (4 * ((mLo B : ℚ) : ℝ)) * d2) / Real.log 2 :=
          div_le_div_of_nonneg_right hDrop hL.le
      _ ≤ (X / (4 * ((mLo B : ℚ) : ℝ)) * d2) / ((LqLo : ℚ) : ℝ) :=
          div_le_div_of_nonneg_left hY0 hLq hL1
      _ = X / (4 * ((mLo B : ℚ) : ℝ) * ((LqLo : ℚ) : ℝ)) * d2 := by
          field_simp
  -- jnLo d² ≤ j
  have hjn : ((jnLo B c : ℚ) : ℝ) * d2 ≤ interiorCost μ.a μ.b := by
    rw [c_jnLo]
    set Y := ((aLo c.rhoL : ℚ) : ℝ) + ((kLo B : ℚ) : ℝ) * ((aLo c.kapL : ℚ) : ℝ) with hYdef
    have hmHi0 : (0 : ℝ) < ((mHi B : ℚ) : ℝ) := lt_of_lt_of_le hmLo0 (hmLo.trans hmHi)
    have hY0 : 0 ≤ Y / (2 * ((mHi B : ℚ) : ℝ)) * d2 := by
      have hkL0 : (0 : ℝ) ≤ ((kLo B : ℚ) : ℝ) := by
        rw [c_kLo]; exact div_nonneg hmLo0.le (by linarith only [hmLo, hmHi, hmHi1])
      have ha1' : (1 : ℝ) ≤ ((aLo c.rhoL : ℚ) : ℝ) := by exact_mod_cast one_le_aLo c.rhoL
      have ha2' : (1 : ℝ) ≤ ((aLo c.kapL : ℚ) : ℝ) := by exact_mod_cast one_le_aLo c.kapL
      have : 0 ≤ Y := by rw [hYdef]; positivity
      positivity
    have hLqHi : (0 : ℝ) < ((LqHi : ℚ) : ℝ) := hL.trans_le hL2
    calc Y / (2 * ((mHi B : ℚ) : ℝ) * ((LqHi : ℚ) : ℝ)) * d2 =
          (Y / (2 * ((mHi B : ℚ) : ℝ)) * d2) / ((LqHi : ℚ) : ℝ) := by
          field_simp
      _ ≤ (Y / (2 * ((mHi B : ℚ) : ℝ)) * d2) / Real.log 2 :=
          div_le_div_of_nonneg_left hY0 hL hL2
      _ ≤ (Real.log 2 * interiorCost μ.a μ.b) / Real.log 2 :=
          div_le_div_of_nonneg_right hCost hL.le
      _ = interiorCost μ.a μ.b := by field_simp
  -- the information and its enclosure
  have hdd : μ.b - μ.a ≤ ((dHi B : ℚ) : ℝ) := by
    rw [c_dHi]
    have h1 : μ.b - μ.a = μ.b * (1 - μ.a / μ.b) := by field_simp
    rw [h1]
    exact mul_le_mul hbb1 (by linarith only [hr1]) (by linarith only [hr2, r2])
      (b0.le.trans (by exact_mod_cast B01))
  have hd0 : 0 ≤ μ.b - μ.a := by linarith only [hab]
  have hIeq : Δ + s = H ((μ.a + μ.b) / 2) - μ.meanEntropy := by rw [hΔdef, hsdef]; ring
  have hI_1 : Δ + s ≤ ((Hhi c.mH : ℚ) : ℝ) - (B.t0 : ℝ) * ((CLo B c : ℚ) : ℝ) := by
    rw [hIeq]
    have h1 := mul_le_mul_of_nonneg_left hCLo t0
    linarith only [HmH, h1, hE0]
  have hI_2 : Δ + s ≤ ((sHi B c : ℚ) : ℝ) +
      ((KHi B c : ℚ) : ℝ) * (((dHi B : ℚ) : ℝ) * ((dHi B : ℚ) : ℝ)) := by
    have hsq : d2 ≤ ((dHi B : ℚ) : ℝ) * ((dHi B : ℚ) : ℝ) := by
      rw [hd2def, sq]; exact mul_le_mul hdd hdd hd0 (hd0.trans hdd)
    have := mul_le_mul_of_nonneg_left hsq hKHi0
    linarith only [hDelta, this, hsHi]
  have hIle : Δ + s ≤ ((IHi B c : ℚ) : ℝ) := by rw [c_IHi]; exact le_min hI_1 hI_2
  have hI1 : Δ + s < 1 := lt_of_le_of_lt hIle fIHi
  -- increment bound
  have htrap := CKLaneE.P_trapezoid hs0 (le_add_of_nonneg_left hΔ0) hI1
  have hPS := anchorOk_sound okvS hs0 hsHi
  have hPI := anchorOk_sound okvI (add_nonneg hΔ0 hs0) hIle
  have hP0S := anchorOk_sound okvS le_rfl (hs0.trans hsHi)
  have hP0I := anchorOk_sound okvI le_rfl ((add_nonneg hΔ0 hs0).trans hIle)
  rw [P1_zero] at hP0S hP0I
  have hpbar0 : (0 : ℝ) ≤ ((pbar c : ℚ) : ℝ) := by rw [c_pbar]; linarith only [hP0S, hP0I]
  have hinc : P (Δ + s) - P s ≤ Δ * ((pbar c : ℚ) : ℝ) := by
    rw [c_pbar]
    have h1 : Δ + s - s = Δ := by ring
    rw [h1] at htrap
    have := mul_le_mul_of_nonneg_left (add_le_add hPS hPI) hΔ0
    linarith only [htrap, this]
  -- beta
  have hbeta : ((betaLo B c : ℚ) : ℝ) ≤ 1 / (2 * (μ.b * (1 - μ.a))) := by
    rw [c_betaLo]
    have hbpos : 0 < μ.b * (1 - μ.a) := mul_pos hb0 (by linarith only [ha1])
    apply one_div_le_one_div_of_le (by positivity)
    have h1 : 1 - μ.a ≤ 1 - (c.aL : ℝ) := by linarith only [haLo]
    have h3 : 2 * μ.b * (1 - μ.a) ≤ 2 * (B.b1 : ℝ) * (1 - μ.a) :=
      mul_le_mul_of_nonneg_right (by linarith only [hbb1]) (by linarith only [ha1])
    have hb2pos : (0 : ℝ) < B.b1 := lt_of_lt_of_le hb0 hbb1
    have h4 : 2 * (B.b1 : ℝ) * (1 - μ.a) ≤ 2 * (B.b1 : ℝ) * (1 - (c.aL : ℝ)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    calc 2 * (μ.b * (1 - μ.a)) = 2 * μ.b * (1 - μ.a) := by ring
      _ ≤ _ := h3.trans h4
  have hbetaLo0 : (0 : ℝ) ≤ ((betaLo B c : ℚ) : ℝ) := by
    rw [c_betaLo]
    have : (c.aL : ℝ) < 1 := by linarith only [haLo, ha1]
    have hb2pos : (0 : ℝ) < B.b1 := lt_of_lt_of_le hb0 hbb1
    apply div_nonneg zero_le_one
    have := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hb2pos) (show (0 : ℝ) < 1 - c.aL by linarith only [this])
    exact this.le
  set β : ℝ := 1 / (2 * (μ.b * (1 - μ.a))) with hβdef
  have hβ0 : 0 ≤ β := by
    rw [hβdef]; have := mul_pos hb0 (show 0 < 1 - μ.a by linarith only [ha1]); positivity
  -- assemble: splitBound ≤ j + β d² s
  have hmain1 : P (Δ + s) - P s ≤ interiorCost μ.a μ.b + d2 * β * s := by
    have e1 : Δ * ((pbar c : ℚ) : ℝ) ≤ ((KHi B c : ℚ) : ℝ) * d2 * ((pbar c : ℚ) : ℝ) :=
      mul_le_mul_of_nonneg_right hDelta hpbar0
    have e2 : d2 * (((KHi B c : ℚ) : ℝ) * ((pbar c : ℚ) : ℝ)) ≤
        d2 * (((jnLo B c : ℚ) : ℝ) + ((betaLo B c : ℚ) : ℝ) * ((sLo B c : ℚ) : ℝ)) :=
      mul_le_mul_of_nonneg_left ffin hd20
    have e3 : ((betaLo B c : ℚ) : ℝ) * ((sLo B c : ℚ) : ℝ) ≤ β * s :=
      mul_le_mul hbeta hsLo fsLo hβ0
    have e4 := mul_le_mul_of_nonneg_left e3 hd20
    have e5 : ((KHi B c : ℚ) : ℝ) * d2 * ((pbar c : ℚ) : ℝ) =
        d2 * (((KHi B c : ℚ) : ℝ) * ((pbar c : ℚ) : ℝ)) := by ring
    have e6 : d2 * (((jnLo B c : ℚ) : ℝ) + ((betaLo B c : ℚ) : ℝ) * ((sLo B c : ℚ) : ℝ)) =
        ((jnLo B c : ℚ) : ℝ) * d2 + d2 * (((betaLo B c : ℚ) : ℝ) * ((sLo B c : ℚ) : ℝ)) := by ring
    have e7 : d2 * (β * s) = d2 * β * s := by ring
    linarith only [hinc, e1, e2, e4, e5, e6, e7, hjn]
  have hV : LogSum.V μ.a μ.b = μ.b * (1 - μ.a) := by
    simp only [LogSum.V, max_eq_right hab.le, min_eq_left hab.le]
  have hfloor : μ.psiLogSumCostFloor = interiorCost μ.a μ.b + d2 * β * s := by
    unfold InteriorLaw.psiLogSumCostFloor
    rw [hV, hsdef, hβdef, hd2def, hCdef]
    unfold InteriorLaw.meanEntropy
    have hbpos : 0 < μ.b * (1 - μ.a) := mul_pos hb0 (by linarith only [ha1])
    field_simp
    ring
  have hmain : μ.splitBound ≤ μ.cost := by
    have e : μ.splitBound = P (Δ + s) - P s := rfl
    rw [e]
    calc P (Δ + s) - P s ≤ interiorCost μ.a μ.b + d2 * β * s := hmain1
      _ = μ.psiLogSumCostFloor := hfloor.symm
      _ ≤ μ.cost := μ.psiLogSumCostFloor_le_cost
  exact μ.gap_le_of_splitBound hact hmain

/-! ## Finite subdivision trees -/

inductive MTree where
  | leaf (c : Cell)
  | node (ax : ℕ) (v : ℚ) (l r : MTree)
  deriving Repr

def RBox.lower (B : RBox) (ax : ℕ) (v : ℚ) : RBox :=
  if ax = 0 then { B with r2 := v } else if ax = 1 then { B with b1 := v } else { B with t1 := v }

def RBox.upper (B : RBox) (ax : ℕ) (v : ℚ) : RBox :=
  if ax = 0 then { B with r1 := v } else if ax = 1 then { B with b0 := v } else { B with t0 := v }

def MTree.check : MTree → RBox → Bool
  | .leaf c, B => cellCheck B c
  | .node ax v l r, B => MTree.check l (B.lower ax v) && MTree.check r (B.upper ax v)

theorem semR_split (B : RBox) (ax : ℕ) (v : ℚ) (hl : SemR (B.lower ax v))
    (hu : SemR (B.upper ax v)) : SemR B := by
  intro k μ hab hin hact
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hin
  by_cases h0 : ax = 0
  · subst h0
    rcases le_total (μ.a / μ.b) (v : ℝ) with hc | hc
    · exact hl k μ hab (by simp only [RBox.lower, if_true]; exact ⟨h1, hc, h3, h4, h5, h6⟩) hact
    · exact hu k μ hab (by simp only [RBox.upper, if_true]; exact ⟨hc, h2, h3, h4, h5, h6⟩) hact
  · by_cases h1' : ax = 1
    · subst h1'
      rcases le_total μ.b (v : ℝ) with hc | hc
      · exact hl k μ hab (by
          simp only [RBox.lower, if_neg h0, if_true]; exact ⟨h1, h2, h3, hc, h5, h6⟩) hact
      · exact hu k μ hab (by
          simp only [RBox.upper, if_neg h0, if_true]; exact ⟨h1, h2, hc, h4, h5, h6⟩) hact
    · rcases le_total μ.meanEntropy ((v : ℝ) * ((H μ.a + H μ.b) / 2)) with hc | hc
      · exact hl k μ hab (by
          simp only [RBox.lower, if_neg h0, if_neg h1']; exact ⟨h1, h2, h3, h4, h5, hc⟩) hact
      · exact hu k μ hab (by
          simp only [RBox.upper, if_neg h0, if_neg h1']; exact ⟨h1, h2, h3, h4, hc, h6⟩) hact

theorem MTree.check_sound : ∀ (T : MTree) (B : RBox), T.check B = true → SemR B
  | .leaf c, B, h => cellCheck_sound h
  | .node ax v l r, B, h => by
      simp only [MTree.check, Bool.and_eq_true] at h
      exact semR_split B ax v (MTree.check_sound l _ h.1) (MTree.check_sound r _ h.2)

/-! ## Binding to archived same-side leaves -/

/-- An archived same-side leaf box: `x = -log₂(a/b)`, mean `b`, entropy fraction `t`. -/
structure SSBox where
  x0 : ℚ
  x1 : ℚ
  b0 : ℚ
  b1 : ℚ
  t0 : ℚ
  t1 : ℚ
  deriving Repr, DecidableEq

/-- Root of the archived same-side cover (`PARALLEL_FINISH.ROOT`). -/
def ssRoot : SSBox := ⟨0, 32, 1 / 32, 1 / 2, 0, 1⟩

/-- One exact halving step of `COVER.reconstruct` (digit = 2·axis + side). -/
def ssStep (B : SSBox) (d : ℕ) : SSBox :=
  match d with
  | 0 => { B with x1 := (B.x0 + B.x1) / 2 }
  | 1 => { B with x0 := (B.x0 + B.x1) / 2 }
  | 2 => { B with b1 := (B.b0 + B.b1) / 2 }
  | 3 => { B with b0 := (B.b0 + B.b1) / 2 }
  | 4 => { B with t1 := (B.t0 + B.t1) / 2 }
  | 5 => { B with t0 := (B.t0 + B.t1) / 2 }
  | _ => B

/-- The exact box of an archived path. -/
def ssBox (p : List ℕ) : SSBox := p.foldl ssStep ssRoot

/-- Law membership in the exact archived box (real `2^-x`, entropy fraction of the law's own cap). -/
def InSS (B : SSBox) (a b E : ℝ) : Prop :=
  (2 : ℝ) ^ (-(B.x1 : ℝ)) ≤ a / b ∧ a / b ≤ (2 : ℝ) ^ (-(B.x0 : ℝ)) ∧
    (B.b0 : ℝ) ≤ b ∧ b ≤ (B.b1 : ℝ) ∧
    (B.t0 : ℝ) * ((H a + H b) / 2) ≤ E ∧ E ≤ (B.t1 : ℝ) * ((H a + H b) / 2)

/-- The law-level psi-owner statement on an archived same-side box. -/
def SemSS (B : SSBox) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b → InSS B μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

/-- Leaf certificate: rational bounds `r1 ≤ 2^-x1`, `2^-x0 ≤ r2` and a checked subdivision. -/
structure LeafCert where
  r1 : ℚ
  r2 : ℚ
  tree : MTree
  deriving Repr

def leafRBox (B : SSBox) (w : LeafCert) : RBox := ⟨w.r1, w.r2, B.b0, B.b1, B.t0, B.t1⟩

def checkBox (B : SSBox) (w : LeafCert) : Bool :=
  pow2LowerOK w.r1 B.x1 && pow2UpperOK w.r2 B.x0 && w.tree.check (leafRBox B w)

theorem checkBox_sound {B : SSBox} {w : LeafCert} (h : checkBox B w = true) : SemSS B := by
  unfold checkBox at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hs := MTree.check_sound w.tree _ h3
  intro k μ hab hin hact
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := hin
  exact hs k μ hab ⟨(pow2LowerOK_sound h1).trans i1, i2.trans (pow2UpperOK_sound h2), i3, i4, i5, i6⟩
    hact

/-- Per-leaf acceptance bound to the archived path. -/
def checkLeaf (p : List ℕ) (w : LeafCert) : Bool := checkBox (ssBox p) w

theorem checkLeaf_sound {p : List ℕ} {w : LeafCert} (h : checkLeaf p w = true) :
    SemSS (ssBox p) :=
  checkBox_sound h

theorem checkLeaves_sound (L : List (List ℕ × LeafCert))
    (h : (L.all fun x => checkLeaf x.1 x.2) = true) : ∀ x ∈ L, SemSS (ssBox x.1) := by
  intro x hx
  rw [List.all_eq_true] at h
  exact checkLeaf_sound (h x hx)

end CKLaneM1.ML

#check @CKLaneM1.ML.cellCheck_sound
#check @CKLaneM1.ML.MTree.check_sound
#check @CKLaneM1.ML.checkLeaf_sound
#print axioms CKLaneM1.ML.cellCheck_sound
#print axioms CKLaneM1.ML.checkLeaf_sound

end


