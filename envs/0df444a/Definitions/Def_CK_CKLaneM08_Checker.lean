-- Prove2me | Definitions.Def_CK_CKLaneM08_Checker
-- name    : CK_CKLaneM08_Checker
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T19:23:18.188512+00:00
-- url     : https://prove2.me/theorems/8680a51b-b4e5-40d9-be6d-fe9d498af663
-- title:
--   Courtade–Kumar proof module `CKLaneM08.Checker` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM08.Checker` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM08.Checker` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM08.Checker (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM08/Checker.lean)

import Definitions.Def_CK_CKLaneM08_Ratios
import Definitions.Def_CK_CKLaneD_FleetBase

-- ===== source module CKLaneM08.Checker =====
section

/-!
# Lane M08: semantic kernel for the archived same-side method `entropy_endpoints`

Archived same-side coordinates (`same_side/COVER.py`): `x = -log₂(a/b)`, `b`, and the entropy
fraction `t = E / C`, `C = (H a + H b)/2`, `E = meanEntropy = (e+f)/2`.  A box is
`x ∈ [x0,x1], b ∈ [b0,b1], t ∈ [t0,t1]`; law membership (`InBox`) is the exact physical image
(real `rpow`).  Only the mean entropy is constrained (no `e = C t, f = C (2-t)` parametrization).

Method (entropy-endpoint concavity).  For fixed means the log-sum gap
`G(s) = j + α s - P(Δ+s) + P(s)` (`j = interiorCost a b`, `α = (b-a)²/(2 b (1-a))`) is concave in
the deficit `s = C - E` (`GeneralCK.Scalar.gap_concaveOn`).  The corpus criterion
`GeneralCK.Scalar.gap_endpoint_criterion` reduces `P(Δ+s) - P(s) ≤ j + α s` on `0 ≤ s ≤ S` to the
two entropy endpoints: `s = 0` (the cap, `GeneralCK.deterministic_cap_bound`) and the maximal
deficit `S = (1 - t0) C` of the box (lower entropy endpoint `t0`).  The checker certifies
`G(S) ≥ 0` over the whole `(x,b)` box by the normalized mean log-sum comparison, grouped by the
two mean factors so that it is first-order exact:

`G(S)/d² ≥ [A(ρ) - Γ(ρ) p̄/2]/(2 m ln2) + [A(κ) - Γ(κ) p̄/2]/(2 (1-m) ln2) + β S`

with `A = Aratio`, `Γ = Gratio` monotone (`CKLaneM08.Aratio_mono`, `Gratio_mono`), `p̄` the
trapezoid slope bound from certified slope anchors (`CKLaneE.P_trapezoid`,
`CKLaneE.FP.anchorOk_sound`), and every logarithm / entropy value enclosed by the kernel-checked
fixed-point series of `CKLaneE.FP`.  `2^-x` is bound to rationals with exact `Nat` powers
(`CKLaneD.pow2LowerOK/UpperOK`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM08

open GeneralCK CKLaneE.FP

/-- An archived same-side box in `(x, b, t)` coordinates. -/
structure Box where
  x0 : ℚ
  x1 : ℚ
  b0 : ℚ
  b1 : ℚ
  t0 : ℚ
  t1 : ℚ
  deriving Repr, DecidableEq

/-- Exact law membership in the archived box: `a/b = 2^-x`, `x ∈ [x0,x1]`, `b ∈ [b0,b1]`,
`meanEntropy = t·(H a + H b)/2`, `t ∈ [t0,t1]`. -/
def InBox (B : Box) {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) : Prop :=
  (2 : ℝ) ^ (-(B.x1 : ℝ)) ≤ μ.a / μ.b ∧ μ.a / μ.b ≤ (2 : ℝ) ^ (-(B.x0 : ℝ)) ∧
    (B.b0 : ℝ) ≤ μ.b ∧ μ.b ≤ (B.b1 : ℝ) ∧
    (B.t0 : ℝ) * ((H μ.a + H μ.b) / 2) ≤ μ.meanEntropy ∧
    μ.meanEntropy ≤ (B.t1 : ℝ) * ((H μ.a + H μ.b) / 2)

/-- Semantic statement of a box: the psi candidate gap is bounded by the law cost. -/
def Sem (B : Box) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), InBox B μ → candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.cost

/-! ## Rational enclosures of the two ratio functions -/

/-- Lower bound of `Aratio z = atanh z / z` at a rational `z ∈ (0,1)`. -/
def ALo (z : ℚ) : ℚ := -lHi ((1 - z) / (1 + z)) / (2 * z)

/-- Upper bound of `Gratio z = gR z / z²` at a rational `z ∈ (0,1)`. -/
def GHi (z : ℚ) : ℚ := ((1 + z) * (-lLo (1 / (1 + z))) + (1 - z) * l1Hi z) / (2 * (z * z))

def aOk (z : ℚ) : Bool := decide (0 < z ∧ z < 1) && ptOk ((1 - z) / (1 + z))

def gOk (z : ℚ) : Bool := decide (0 < z ∧ z < 1) && ptOk z && ptOk (1 / (1 + z))

theorem ALo_le {z : ℚ} (h : aOk z = true) : ((ALo z : ℚ) : ℝ) ≤ Aratio (z : ℝ) := by
  simp only [aOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hz0, hz1⟩, hq⟩ := h
  have hz0' : (0 : ℝ) < z := by exact_mod_cast hz0
  have hz1' : (z : ℝ) < 1 := by exact_mod_cast hz1
  obtain ⟨_, hlog, _, _⟩ := ptOk_sound hq
  have hcast : (((1 - z) / (1 + z) : ℚ) : ℝ) = (1 - (z : ℝ)) / (1 + (z : ℝ)) := by push_cast; ring
  rw [hcast] at hlog
  have hat : atanhR (z : ℝ) = -Real.log ((1 - (z : ℝ)) / (1 + (z : ℝ))) / 2 := by
    unfold atanhR
    rw [Real.log_div (by linarith) (by linarith)]
    ring
  unfold Aratio
  rw [hat]
  have e : ((ALo z : ℚ) : ℝ) = -((lHi ((1 - z) / (1 + z)) : ℚ) : ℝ) / 2 / (z : ℝ) := by
    simp only [ALo]; push_cast; ring
  rw [e]
  apply div_le_div_of_nonneg_right _ hz0'.le
  linarith

theorem Gratio_le_GHi {z : ℚ} (h : gOk z = true) : Gratio (z : ℝ) ≤ ((GHi z : ℚ) : ℝ) := by
  simp only [gOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hz0, hz1⟩, hp⟩, hq⟩ := h
  have hz0' : (0 : ℝ) < z := by exact_mod_cast hz0
  have hz1' : (z : ℝ) < 1 := by exact_mod_cast hz1
  obtain ⟨_, _, _, hl1⟩ := ptOk_sound hp
  obtain ⟨hlo, _, _, _⟩ := ptOk_sound hq
  have hcast : ((1 / (1 + z) : ℚ) : ℝ) = 1 / (1 + (z : ℝ)) := by push_cast; ring
  rw [hcast] at hlo
  have hlog1 : Real.log (1 + (z : ℝ)) ≤ -((lLo (1 / (1 + z)) : ℚ) : ℝ) := by
    have : Real.log (1 / (1 + (z : ℝ))) = -Real.log (1 + (z : ℝ)) := by
      rw [one_div, Real.log_inv]
    rw [this] at hlo
    linarith
  unfold Gratio gR
  have e : ((GHi z : ℚ) : ℝ) = ((1 + (z : ℝ)) * (-((lLo (1 / (1 + z)) : ℚ) : ℝ)) +
      (1 - (z : ℝ)) * ((l1Hi z : ℚ) : ℝ)) / 2 / ((z : ℝ) * (z : ℝ)) := by
    simp only [GHi]; push_cast; ring
  rw [e]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have a1 := mul_le_mul_of_nonneg_left hlog1 (by linarith : (0 : ℝ) ≤ 1 + (z : ℝ))
  have a2 := mul_le_mul_of_nonneg_left hl1 (by linarith : (0 : ℝ) ≤ 1 - (z : ℝ))
  linarith

/-! ## Leaf certificates -/

/-- Leaf certificate: rational enclosure `r1 ≤ 2^-x1`, `2^-x0 ≤ r2` and two slope anchors. -/
structure Leaf where
  r1 : ℚ
  r2 : ℚ
  vS : ℚ
  vI : ℚ
  deriving Repr, DecidableEq

namespace Leaf

variable (B : Box) (c : Leaf)

def B3 : CKLaneE.Chart.Box3 := ⟨c.r1, c.r2, B.b0, B.b1, 1, 1⟩
def aLo : ℚ := c.r1 * B.b0
def aHi : ℚ := c.r2 * B.b1
def mLo : ℚ := B.b0 * (1 + c.r1) / 2
def mHi : ℚ := B.b1 * (1 + c.r2) / 2
def dHi : ℚ := B.b1 * (1 - c.r1)
def rhoLo : ℚ := (1 - c.r2) / (1 + c.r2)
def rhoHi : ℚ := (1 - c.r1) / (1 + c.r1)
def kapLo : ℚ := B.b0 * (1 - c.r2) / (2 - B.b0 * (1 + c.r2))
def kapHi : ℚ := B.b1 * (1 - c.r1) / (2 - B.b1 * (1 + c.r1))
def CLo : ℚ := (Hlo (aLo B c) + Hlo B.b0) / 2
def CHi : ℚ := (Hhi (aHi B c) + Hhi B.b1) / 2
def sLo : ℚ := (1 - B.t0) * CLo B c
def sHi : ℚ := (1 - B.t0) * CHi B c
def G1 : ℚ := GHi (rhoHi c)
def G2 : ℚ := GHi (kapHi B c)
def A1 : ℚ := ALo (rhoLo c)
def A2 : ℚ := ALo (kapLo B c)
def K : ℚ := (G1 c / (4 * mLo B c) + G2 B c / (4 * (1 - mHi B c))) / LqLo
def IHi : ℚ := min (Hhi (mHi B c) - B.t0 * CLo B c) (sHi B c + K B c * (dHi B c * dHi B c))
def pbar : ℚ := (P1up c.vS + P1up c.vI) / 2
def B1 : ℚ := A1 c - G1 c * pbar c / 2
def B2 : ℚ := A2 B c - G2 B c * pbar c / 2
def c1 : ℚ := if 0 ≤ B1 c then B1 c / (2 * LqHi * mHi B c) else B1 c / (2 * LqLo * mLo B c)
def c2 : ℚ :=
  if 0 ≤ B2 B c then B2 B c / (2 * LqHi * (1 - mLo B c)) else B2 B c / (2 * LqLo * (1 - mHi B c))
def betaLo : ℚ := CKLaneE.LS.betaLo (B3 B c)
def final : ℚ := c1 B c + c2 B c + betaLo B c * sLo B c

/-- The Boolean leaf checker: binds the box (`2^-x` enclosure by exact powers), every log / entropy
/ slope enclosure, and the grouped normalized log-sum inequality at the lower entropy endpoint. -/
def check : Bool :=
  decide (0 ≤ B.x0 ∧ 0 ≤ B.t0 ∧ B.t0 ≤ 1 ∧ c.r2 < 1) &&
    CKLaneE.LS.boxOk (B3 B c) &&
    CKLaneD.pow2LowerOK c.r1 B.x1 && CKLaneD.pow2UpperOK c.r2 B.x0 &&
    ptOk (aLo B c) && ptOk (aHi B c) && ptOk B.b0 && ptOk B.b1 && ptOk (mHi B c) &&
    aOk (rhoLo c) && gOk (rhoHi c) && aOk (kapLo B c) && gOk (kapHi B c) &&
    anchorOk c.vS (sHi B c) && anchorOk c.vI (IHi B c) &&
    decide (0 ≤ sLo B c ∧ IHi B c < 1 ∧ 0 ≤ final B c)

end Leaf

/-! ## Soundness -/

theorem aOk_mem {z : ℚ} (h : aOk z = true) : (z : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
  simp only [aOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨by exact_mod_cast h.1.1, by exact_mod_cast h.1.2⟩

theorem gOk_mem {z : ℚ} (h : gOk z = true) : (z : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
  simp only [gOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨by exact_mod_cast h.1.1.1, by exact_mod_cast h.1.1.2⟩

/-- Geometry of the ratio coordinates over a box. -/
theorem geom2 {r1 r2 b0 b1 a b : ℝ} (hr1 : 0 < r1) (hr2 : r2 < 1) (hb0 : 0 < b0)
    (hb : 0 < b) (hra1 : r1 ≤ a / b) (hra2 : a / b ≤ r2) (hbb0 : b0 ≤ b) (hbb1 : b ≤ b1)
    (hb1 : b1 ≤ 1 / 2) :
    (1 - r2) / (1 + r2) ≤ (b - a) / (a + b) ∧
      b0 * (1 - r2) / (2 - b0 * (1 + r2)) ≤ (b - a) / (2 - a - b) ∧
      (b - a) / (2 - a - b) ≤ b1 * (1 - r1) / (2 - b1 * (1 + r1)) := by
  have har : a = (a / b) * b := by field_simp
  set r := a / b with hrdef
  have hr0 : 0 < r := lt_of_lt_of_le hr1 hra1
  have hr1' : r < 1 := lt_of_le_of_lt hra2 hr2
  have hbb : b ≤ 1 / 2 := hbb1.trans hb1
  rw [har]
  refine ⟨?_, ?_, ?_⟩
  · have h1 : 0 < r * b + b := by positivity
    rw [div_le_div_iff₀ (by linarith) h1]
    nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hra2)]
  · have hd1 : 0 < 2 - b0 * (1 + r2) := by nlinarith
    have hd2 : 0 < 2 - r * b - b := by nlinarith
    rw [div_le_div_iff₀ hd1 hd2]
    nlinarith [mul_nonneg (sub_nonneg.mpr hr2.le) (sub_nonneg.mpr hbb0),
      mul_nonneg (mul_nonneg hb.le (sub_nonneg.mpr hra2)) (by linarith : (0 : ℝ) ≤ 1 - b0)]
  · have hd1 : 0 < 2 - r * b - b := by nlinarith
    have hd2 : 0 < 2 - b1 * (1 + r1) := by nlinarith
    rw [div_le_div_iff₀ hd1 hd2]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - r) (sub_nonneg.mpr hbb1),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ b1) (sub_nonneg.mpr hra1))
        (by linarith : (0 : ℝ) ≤ 1 - b)]

/-- Sign-split division bound used for the two grouped mean factors. -/
theorem cq_le {Bq mL mH Ll Lh : ℚ} {X m L : ℝ} (hXB : (Bq : ℝ) ≤ X) (hmL : (0 : ℝ) < mL)
    (hm1 : (mL : ℝ) ≤ m) (hm2 : m ≤ mH) (hLl : (0 : ℝ) < Ll) (hL1 : (Ll : ℝ) ≤ L)
    (hL2 : L ≤ Lh) :
    (((if 0 ≤ Bq then Bq / (2 * Lh * mH) else Bq / (2 * Ll * mL) : ℚ)) : ℝ) ≤
      X / (2 * m * L) := by
  have hm0 : 0 < m := lt_of_lt_of_le hmL hm1
  have hL0 : 0 < L := lt_of_lt_of_le hLl hL1
  have hden : 0 < 2 * m * L := by positivity
  split_ifs with h
  · have hB : (0 : ℝ) ≤ Bq := by exact_mod_cast h
    push_cast
    have hmL' := mul_le_mul hm2 hL2 hL0.le (le_trans hm0.le hm2)
    have hle : 2 * m * L ≤ 2 * (Lh : ℝ) * mH := by nlinarith
    calc (Bq : ℝ) / (2 * Lh * mH) ≤ Bq / (2 * m * L) := div_le_div_of_nonneg_left hB hden hle
      _ ≤ X / (2 * m * L) := div_le_div_of_nonneg_right hXB hden.le
  · have hB : (Bq : ℝ) < 0 := by exact_mod_cast lt_of_not_ge h
    push_cast
    have hden' : 0 < 2 * (Ll : ℝ) * mL := by positivity
    have hmL' := mul_le_mul hm1 hL1 hLl.le hm0.le
    have hle : 2 * (Ll : ℝ) * mL ≤ 2 * m * L := by nlinarith
    have hmul := mul_le_mul_of_nonpos_left hle hB.le
    calc (Bq : ℝ) / (2 * Ll * mL) ≤ Bq / (2 * m * L) := by
          rw [div_le_div_iff₀ hden' hden]; linarith
      _ ≤ X / (2 * m * L) := div_le_div_of_nonneg_right hXB hden.le

/-- Pure real assembly of the grouped normalized mean log-sum comparison. -/
theorem assemble_main {j Δ S α inc pbar Aρ Aκ Gρ Gκ m L d β βlo sLo c1 c2 : ℝ}
    (hj : j = d ^ 2 * (Aρ / (2 * m) + Aκ / (2 * (1 - m))) / L)
    (hΔ : Δ = d ^ 2 * (Gρ / (4 * m) + Gκ / (4 * (1 - m))) / L)
    (hinc : inc ≤ Δ * pbar)
    (hc1 : c1 ≤ (Aρ - Gρ * pbar / 2) / (2 * m * L))
    (hc2 : c2 ≤ (Aκ - Gκ * pbar / 2) / (2 * (1 - m) * L))
    (hα : α = d ^ 2 * β) (hβ : βlo ≤ β) (hβlo : 0 ≤ βlo) (hS : sLo ≤ S) (hsLo : 0 ≤ sLo)
    (hfin : 0 ≤ c1 + c2 + βlo * sLo) (hm : 0 < m) (hm1 : m < 1) (hL : 0 < L) :
    0 ≤ j + α * S - inc := by
  have hβ0 : 0 ≤ β := hβlo.trans hβ
  have key : j - Δ * pbar = d ^ 2 * ((Aρ - Gρ * pbar / 2) / (2 * m * L) +
      (Aκ - Gκ * pbar / 2) / (2 * (1 - m) * L)) := by
    rw [hj, hΔ]
    have h1 : 1 - m ≠ 0 := by linarith
    have h2 : m ≠ 0 := hm.ne'
    have h3 : L ≠ 0 := hL.ne'
    field_simp
    ring
  have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
  have h1 : d ^ 2 * (c1 + c2) ≤ j - Δ * pbar := by
    rw [key]; exact mul_le_mul_of_nonneg_left (add_le_add hc1 hc2) hd2
  have h2 : βlo * sLo ≤ β * S := mul_le_mul hβ hS hsLo hβ0
  have h2' := mul_le_mul_of_nonneg_left h2 hd2
  have h3 : d ^ 2 * (βlo * sLo) ≤ α * S := by rw [hα]; linarith
  have h4 : 0 ≤ d ^ 2 * (c1 + c2 + βlo * sLo) := mul_nonneg hd2 hfin
  have e : d ^ 2 * (c1 + c2 + βlo * sLo) = d ^ 2 * (c1 + c2) + d ^ 2 * (βlo * sLo) := by ring
  linarith

open GeneralCK.Scalar in
set_option maxHeartbeats 4000000 in
/-- Core soundness: a checked leaf bounds the split-uniform psi bound by the cost for every law
in the exact box. -/
theorem check_sound_split {B : Box} {c : Leaf} (hw : Leaf.check B c = true)
    {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) (hin : InBox B μ) : μ.splitBound ≤ μ.cost := by
  obtain ⟨hx1, hx0, hbb0, hbb1, hE0, _⟩ := hin
  simp only [Leaf.check, Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsane, hbox⟩, hp1⟩, hp2⟩, haLo⟩, haHi⟩, hb0ok⟩, hb1ok⟩, hmHi⟩,
    hA1⟩, hG1⟩, hA2⟩, hG2⟩, hvS⟩, hvI⟩, hfin⟩ := hw
  obtain ⟨_, ht0, ht01, hr2lt⟩ := hsane
  obtain ⟨qsLo, qIHi, qfinal⟩ := hfin
  -- box binding
  have hr1 : ((c.r1 : ℚ) : ℝ) ≤ μ.a / μ.b := (CKLaneD.pow2LowerOK_sound hp1).trans hx1
  have hr2 : μ.a / μ.b ≤ ((c.r2 : ℚ) : ℝ) := hx0.trans (CKLaneD.pow2UpperOK_sound hp2)
  obtain ⟨R1, _, R2, B0, _, B1h, _⟩ := CKLaneE.LS.boxOk_real hbox
  change (0 : ℝ) < c.r1 at R1
  change (c.r2 : ℝ) ≤ 1 at R2
  change (0 : ℝ) < B.b0 at B0
  change (B.b1 : ℝ) ≤ 1 / 2 at B1h
  have hr2lt' : (c.r2 : ℝ) < 1 := by exact_mod_cast hr2lt
  have ht0' : (0 : ℝ) ≤ B.t0 := by exact_mod_cast ht0
  have ht01' : (B.t0 : ℝ) ≤ 1 := by exact_mod_cast ht01
  have ha0 : 0 < μ.a := μ.a_interior.1
  have hb0 : 0 < μ.b := μ.b_interior.1
  have ha1 : μ.a < 1 := μ.a_interior.2
  have hb1' : μ.b < 1 := by linarith
  have hab : μ.a < μ.b := by
    have h1 := (div_le_iff₀ hb0).mp hr2
    calc μ.a ≤ (c.r2 : ℝ) * μ.b := h1
      _ < 1 * μ.b := mul_lt_mul_of_pos_right hr2lt' hb0
      _ = μ.b := one_mul _
  -- entropy enclosures of the means
  obtain ⟨hHaL, hHaH, hHbL, hHbH, hHmH⟩ :=
    CKLaneE.LS.law_H_bounds (Leaf.B3 B c) ha0 hb0 hbox haLo haHi hb0ok hb1ok hmHi hr1 hr2
      hbb0 hbb1
  change ((Hlo (Leaf.aLo B c) : ℚ) : ℝ) ≤ H μ.a at hHaL
  change H μ.a ≤ ((Hhi (Leaf.aHi B c) : ℚ) : ℝ) at hHaH
  change ((Hlo B.b0 : ℚ) : ℝ) ≤ H μ.b at hHbL
  change H μ.b ≤ ((Hhi B.b1 : ℚ) : ℝ) at hHbH
  change H ((μ.a + μ.b) / 2) ≤ ((Hhi (Leaf.mHi B c) : ℚ) : ℝ) at hHmH
  -- geometry
  obtain ⟨gaL, _, gmL, gmH, _, gdH, gρH⟩ :=
    CKLaneE.NLS.box_geometry R1 R2 B0 hb0 hr1 hr2 hbb0 hbb1
  obtain ⟨gρL, gκL, gκH⟩ := geom2 R1 hr2lt' B0 hb0 hr1 hr2 hbb0 hbb1 B1h
  have hs_ab : 0 < μ.a + μ.b := by linarith
  have ht_ab : 0 < 2 - μ.a - μ.b := by linarith
  have hρ0 : 0 < (μ.b - μ.a) / (μ.a + μ.b) := div_pos (by linarith) hs_ab
  have hρ1 : (μ.b - μ.a) / (μ.a + μ.b) < 1 := (div_lt_one hs_ab).mpr (by linarith)
  have hκ0 : 0 < (μ.b - μ.a) / (2 - μ.a - μ.b) := div_pos (by linarith) ht_ab
  have hκ1 : (μ.b - μ.a) / (2 - μ.a - μ.b) < 1 := (div_lt_one ht_ab).mpr (by linarith)
  have cρLo : ((Leaf.rhoLo c : ℚ) : ℝ) = (1 - (c.r2 : ℝ)) / (1 + c.r2) := by
    simp only [Leaf.rhoLo]; push_cast; ring
  have cρHi : ((Leaf.rhoHi c : ℚ) : ℝ) = (1 - (c.r1 : ℝ)) / (1 + c.r1) := by
    simp only [Leaf.rhoHi]; push_cast; ring
  have cκLo : ((Leaf.kapLo B c : ℚ) : ℝ) = (B.b0 : ℝ) * (1 - c.r2) / (2 - B.b0 * (1 + c.r2)) := by
    simp only [Leaf.kapLo]; push_cast; ring
  have cκHi : ((Leaf.kapHi B c : ℚ) : ℝ) = (B.b1 : ℝ) * (1 - c.r1) / (2 - B.b1 * (1 + c.r1)) := by
    simp only [Leaf.kapHi]; push_cast; ring
  -- ratio enclosures
  have hA1v : ((Leaf.A1 c : ℚ) : ℝ) ≤ Aratio ((μ.b - μ.a) / (μ.a + μ.b)) :=
    (ALo_le hA1).trans (Aratio_mono (aOk_mem hA1) ⟨hρ0, hρ1⟩ (by rw [cρLo]; exact gρL))
  have hG1v : Gratio ((μ.b - μ.a) / (μ.a + μ.b)) ≤ ((Leaf.G1 c : ℚ) : ℝ) :=
    (Gratio_mono ⟨hρ0, hρ1⟩ (gOk_mem hG1) (by rw [cρHi]; exact gρH)).trans (Gratio_le_GHi hG1)
  have hA2v : ((Leaf.A2 B c : ℚ) : ℝ) ≤ Aratio ((μ.b - μ.a) / (2 - μ.a - μ.b)) :=
    (ALo_le hA2).trans (Aratio_mono (aOk_mem hA2) ⟨hκ0, hκ1⟩ (by rw [cκLo]; exact gκL))
  have hG2v : Gratio ((μ.b - μ.a) / (2 - μ.a - μ.b)) ≤ ((Leaf.G2 B c : ℚ) : ℝ) :=
    (Gratio_mono ⟨hκ0, hκ1⟩ (gOk_mem hG2) (by rw [cκHi]; exact gκH)).trans (Gratio_le_GHi hG2)
  have hGρ0 := Gratio_nonneg hρ0 hρ1
  have hGκ0 := Gratio_nonneg hκ0 hκ1
  -- entropy endpoint quantities
  have hCLo : ((Leaf.CLo B c : ℚ) : ℝ) ≤ (H μ.a + H μ.b) / 2 := by
    have e : ((Leaf.CLo B c : ℚ) : ℝ) =
        (((Hlo (Leaf.aLo B c) : ℚ) : ℝ) + ((Hlo B.b0 : ℚ) : ℝ)) / 2 := by
      simp only [Leaf.CLo]; push_cast; ring
    rw [e]; linarith
  have hCHi : (H μ.a + H μ.b) / 2 ≤ ((Leaf.CHi B c : ℚ) : ℝ) := by
    have e : ((Leaf.CHi B c : ℚ) : ℝ) =
        (((Hhi (Leaf.aHi B c) : ℚ) : ℝ) + ((Hhi B.b1 : ℚ) : ℝ)) / 2 := by
      simp only [Leaf.CHi]; push_cast; ring
    rw [e]; linarith
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = (1 - (B.t0 : ℝ)) * ((H μ.a + H μ.b) / 2) := ⟨_, rfl⟩
  have hsLoS : ((Leaf.sLo B c : ℚ) : ℝ) ≤ S := by
    have e : ((Leaf.sLo B c : ℚ) : ℝ) = (1 - (B.t0 : ℝ)) * ((Leaf.CLo B c : ℚ) : ℝ) := by
      simp only [Leaf.sLo]; push_cast; ring
    rw [e, hSdef]; exact mul_le_mul_of_nonneg_left hCLo (by linarith)
  have hSsHi : S ≤ ((Leaf.sHi B c : ℚ) : ℝ) := by
    have e : ((Leaf.sHi B c : ℚ) : ℝ) = (1 - (B.t0 : ℝ)) * ((Leaf.CHi B c : ℚ) : ℝ) := by
      simp only [Leaf.sHi]; push_cast; ring
    rw [e, hSdef]; exact mul_le_mul_of_nonneg_left hCHi (by linarith)
  have hsLo0 : (0 : ℝ) ≤ ((Leaf.sLo B c : ℚ) : ℝ) := by exact_mod_cast qsLo
  have hS0 : 0 ≤ S := hsLo0.trans hsLoS
  have hΔdef : μ.entropyDrop = H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 := rfl
  have hsdef : μ.meanDeficit = (H μ.a + H μ.b) / 2 - μ.meanEntropy := by
    unfold InteriorLaw.meanDeficit InteriorLaw.meanEntropy; ring
  have hΔ0 : 0 ≤ μ.entropyDrop := μ.entropyDrop_nonneg
  have hs0 : 0 ≤ μ.meanDeficit := μ.meanDeficit_mem.1
  have hsS : μ.meanDeficit ≤ S := by rw [hsdef, hSdef]; linarith
  -- normalized forms
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨hLl, hLh⟩ := log_two_mem
  have hLqLo := LqLo_pos
  have hdrop := drop_eq_normalized ha0 hab hb1'
  have hcost := cost_eq_normalized ha0 hab hb1'
  have cmLo : ((Leaf.mLo B c : ℚ) : ℝ) = (B.b0 : ℝ) * (1 + c.r1) / 2 := by
    simp only [Leaf.mLo]; push_cast; ring
  have cmHi : ((Leaf.mHi B c : ℚ) : ℝ) = (B.b1 : ℝ) * (1 + c.r2) / 2 := by
    simp only [Leaf.mHi]; push_cast; ring
  have hmLo : ((Leaf.mLo B c : ℚ) : ℝ) ≤ (μ.a + μ.b) / 2 := by rw [cmLo]; exact gmL
  have hmHi' : (μ.a + μ.b) / 2 ≤ ((Leaf.mHi B c : ℚ) : ℝ) := by rw [cmHi]; exact gmH
  have hmLo0 : (0 : ℝ) < ((Leaf.mLo B c : ℚ) : ℝ) := by rw [cmLo]; positivity
  have hmHi1 : ((Leaf.mHi B c : ℚ) : ℝ) < 1 := by
    rw [cmHi]
    have h := mul_le_mul B1h (by linarith : (1 : ℝ) + c.r2 ≤ 2) (by linarith) (by norm_num)
    linarith
  have hm0 : 0 < (μ.a + μ.b) / 2 := by linarith
  have hm1 : (μ.a + μ.b) / 2 < 1 := by linarith
  -- the drop is at most K d²
  have cK : ((Leaf.K B c : ℚ) : ℝ) = (((Leaf.G1 c : ℚ) : ℝ) / (4 * ((Leaf.mLo B c : ℚ) : ℝ)) +
      ((Leaf.G2 B c : ℚ) : ℝ) / (4 * (1 - ((Leaf.mHi B c : ℚ) : ℝ)))) / ((LqLo : ℚ) : ℝ) := by
    simp only [Leaf.K]; push_cast; ring
  have hG1n : (0 : ℝ) ≤ ((Leaf.G1 c : ℚ) : ℝ) := hGρ0.trans hG1v
  have hG2n : (0 : ℝ) ≤ ((Leaf.G2 B c : ℚ) : ℝ) := hGκ0.trans hG2v
  have hK0 : (0 : ℝ) ≤ ((Leaf.K B c : ℚ) : ℝ) := by
    rw [cK]
    have : (0 : ℝ) < 1 - ((Leaf.mHi B c : ℚ) : ℝ) := by linarith
    positivity
  have hK : μ.entropyDrop ≤ ((Leaf.K B c : ℚ) : ℝ) * (μ.b - μ.a) ^ 2 := by
    rw [hΔdef, hdrop, cK]
    have t1 : Gratio ((μ.b - μ.a) / (μ.a + μ.b)) / (4 * ((μ.a + μ.b) / 2)) ≤
        ((Leaf.G1 c : ℚ) : ℝ) / (4 * ((Leaf.mLo B c : ℚ) : ℝ)) :=
      div_le_div₀ hG1n hG1v (by linarith) (by linarith)
    have t2 : Gratio ((μ.b - μ.a) / (2 - μ.a - μ.b)) / (4 * (1 - (μ.a + μ.b) / 2)) ≤
        ((Leaf.G2 B c : ℚ) : ℝ) / (4 * (1 - ((Leaf.mHi B c : ℚ) : ℝ))) :=
      div_le_div₀ hG2n hG2v (by linarith) (by linarith)
    have hsum := add_le_add t1 t2
    have hsum0 : 0 ≤ Gratio ((μ.b - μ.a) / (μ.a + μ.b)) / (4 * ((μ.a + μ.b) / 2)) +
        Gratio ((μ.b - μ.a) / (2 - μ.a - μ.b)) / (4 * (1 - (μ.a + μ.b) / 2)) := by
      have : 0 < 1 - (μ.a + μ.b) / 2 := by linarith
      positivity
    have t3 := div_le_div₀ (hsum0.trans hsum) hsum hLqLo hLl
    have hd2 : 0 ≤ (μ.b - μ.a) ^ 2 := sq_nonneg _
    calc (μ.b - μ.a) ^ 2 * (Gratio ((μ.b - μ.a) / (μ.a + μ.b)) / (4 * ((μ.a + μ.b) / 2)) +
          Gratio ((μ.b - μ.a) / (2 - μ.a - μ.b)) / (4 * (1 - (μ.a + μ.b) / 2))) / Real.log 2
        = (μ.b - μ.a) ^ 2 * ((Gratio ((μ.b - μ.a) / (μ.a + μ.b)) / (4 * ((μ.a + μ.b) / 2)) +
          Gratio ((μ.b - μ.a) / (2 - μ.a - μ.b)) / (4 * (1 - (μ.a + μ.b) / 2))) / Real.log 2) := by
          ring
      _ ≤ (μ.b - μ.a) ^ 2 * ((((Leaf.G1 c : ℚ) : ℝ) / (4 * ((Leaf.mLo B c : ℚ) : ℝ)) +
          ((Leaf.G2 B c : ℚ) : ℝ) / (4 * (1 - ((Leaf.mHi B c : ℚ) : ℝ)))) / ((LqLo : ℚ) : ℝ)) :=
          mul_le_mul_of_nonneg_left t3 hd2
      _ = _ := by ring
  -- information upper bound
  have cIHi : ((Leaf.IHi B c : ℚ) : ℝ) =
      min (((Hhi (Leaf.mHi B c) : ℚ) : ℝ) - (B.t0 : ℝ) * ((Leaf.CLo B c : ℚ) : ℝ))
        (((Leaf.sHi B c : ℚ) : ℝ) + ((Leaf.K B c : ℚ) : ℝ) *
          (((Leaf.dHi B c : ℚ) : ℝ) * ((Leaf.dHi B c : ℚ) : ℝ))) := by
    simp only [Leaf.IHi, Rat.cast_min, Rat.cast_sub, Rat.cast_add, Rat.cast_mul]
  have cdHi : ((Leaf.dHi B c : ℚ) : ℝ) = (B.b1 : ℝ) * (1 - c.r1) := by
    simp only [Leaf.dHi]; push_cast; ring
  have hIle : μ.entropyDrop + S ≤ ((Leaf.IHi B c : ℚ) : ℝ) := by
    rw [cIHi]
    apply le_min
    · have h1 := mul_le_mul_of_nonneg_left hCLo ht0'
      rw [hΔdef, hSdef]
      linarith
    · have hd0 : 0 ≤ μ.b - μ.a := by linarith
      have hdd : μ.b - μ.a ≤ ((Leaf.dHi B c : ℚ) : ℝ) := by rw [cdHi]; exact gdH
      have hsq : (μ.b - μ.a) ^ 2 ≤ ((Leaf.dHi B c : ℚ) : ℝ) * ((Leaf.dHi B c : ℚ) : ℝ) := by
        rw [sq]; exact mul_le_mul hdd hdd hd0 (hd0.trans hdd)
      have h2 := mul_le_mul_of_nonneg_left hsq hK0
      linarith
  have hI1 : μ.entropyDrop + S < 1 :=
    lt_of_le_of_lt hIle (by exact_mod_cast qIHi)
  -- trapezoid with certified slope anchors
  have htrap := CKLaneE.P_trapezoid hS0 (le_add_of_nonneg_left hΔ0) hI1
  have hPS := anchorOk_sound hvS hS0 hSsHi
  have hPI := anchorOk_sound hvI (by linarith) hIle
  have h4S : (4 : ℝ) ≤ P1 S := by
    rcases eq_or_lt_of_le hS0 with h | h
    · rw [← h, P1_zero]
    · rw [P1_eq_deriv h]; exact four_le_deriv_P h (by linarith)
  have h4I : (4 : ℝ) ≤ P1 (μ.entropyDrop + S) := by
    rcases eq_or_lt_of_le (add_nonneg hΔ0 hS0) with h | h
    · rw [← h, P1_zero]
    · rw [P1_eq_deriv h]; exact four_le_deriv_P h hI1
  have cpbar : ((Leaf.pbar c : ℚ) : ℝ) = (((P1up c.vS : ℚ) : ℝ) + ((P1up c.vI : ℚ) : ℝ)) / 2 := by
    simp only [Leaf.pbar]; push_cast; ring
  have hpbar0 : (0 : ℝ) ≤ ((Leaf.pbar c : ℚ) : ℝ) := by rw [cpbar]; linarith
  have hinc : P (μ.entropyDrop + S) - P S ≤ μ.entropyDrop * ((Leaf.pbar c : ℚ) : ℝ) := by
    rw [cpbar]
    have e : μ.entropyDrop + S - S = μ.entropyDrop := by ring
    rw [e] at htrap
    have := mul_le_mul_of_nonneg_left (add_le_add hPS hPI) hΔ0
    linarith
  -- grouped bracket bounds
  have cB1 : ((Leaf.B1 c : ℚ) : ℝ) = ((Leaf.A1 c : ℚ) : ℝ) -
      ((Leaf.G1 c : ℚ) : ℝ) * ((Leaf.pbar c : ℚ) : ℝ) / 2 := by
    simp only [Leaf.B1]; push_cast; ring
  have cB2 : ((Leaf.B2 B c : ℚ) : ℝ) = ((Leaf.A2 B c : ℚ) : ℝ) -
      ((Leaf.G2 B c : ℚ) : ℝ) * ((Leaf.pbar c : ℚ) : ℝ) / 2 := by
    simp only [Leaf.B2]; push_cast; ring
  have hX1 : ((Leaf.B1 c : ℚ) : ℝ) ≤ Aratio ((μ.b - μ.a) / (μ.a + μ.b)) -
      Gratio ((μ.b - μ.a) / (μ.a + μ.b)) * ((Leaf.pbar c : ℚ) : ℝ) / 2 := by
    rw [cB1]
    have := mul_le_mul_of_nonneg_right hG1v hpbar0
    linarith
  have hX2 : ((Leaf.B2 B c : ℚ) : ℝ) ≤ Aratio ((μ.b - μ.a) / (2 - μ.a - μ.b)) -
      Gratio ((μ.b - μ.a) / (2 - μ.a - μ.b)) * ((Leaf.pbar c : ℚ) : ℝ) / 2 := by
    rw [cB2]
    have := mul_le_mul_of_nonneg_right hG2v hpbar0
    linarith
  have hc1 : ((Leaf.c1 B c : ℚ) : ℝ) ≤ (Aratio ((μ.b - μ.a) / (μ.a + μ.b)) -
      Gratio ((μ.b - μ.a) / (μ.a + μ.b)) * ((Leaf.pbar c : ℚ) : ℝ) / 2) /
        (2 * ((μ.a + μ.b) / 2) * Real.log 2) :=
    cq_le hX1 hmLo0 hmLo hmHi' hLqLo hLl hLh
  have h1mH : (0 : ℝ) < ((1 - Leaf.mHi B c : ℚ) : ℝ) := by push_cast; linarith
  have h1mHle : ((1 - Leaf.mHi B c : ℚ) : ℝ) ≤ 1 - (μ.a + μ.b) / 2 := by push_cast; linarith
  have h1mLle : 1 - (μ.a + μ.b) / 2 ≤ ((1 - Leaf.mLo B c : ℚ) : ℝ) := by push_cast; linarith
  have hc2 : ((Leaf.c2 B c : ℚ) : ℝ) ≤ (Aratio ((μ.b - μ.a) / (2 - μ.a - μ.b)) -
      Gratio ((μ.b - μ.a) / (2 - μ.a - μ.b)) * ((Leaf.pbar c : ℚ) : ℝ) / 2) /
        (2 * (1 - (μ.a + μ.b) / 2) * Real.log 2) :=
    cq_le hX2 h1mH h1mHle h1mLle hLqLo hLl hLh
  -- the log-sum coefficient
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (μ.b - μ.a) ^ 2 * (1 / (2 * (μ.b * (1 - μ.a)))) := ⟨_, rfl⟩
  have hbeta := CKLaneE.LS.beta_bound (Leaf.B3 B c) hab hb1' hbox gaL hbb1 hb0
  have hbetaLo0 := CKLaneE.LS.betaLo_nonneg hbox
  have hfinR : (0 : ℝ) ≤ ((Leaf.c1 B c : ℚ) : ℝ) + ((Leaf.c2 B c : ℚ) : ℝ) +
      ((Leaf.betaLo B c : ℚ) : ℝ) * ((Leaf.sLo B c : ℚ) : ℝ) := by
    have h : (0 : ℝ) ≤ ((Leaf.final B c : ℚ) : ℝ) := by exact_mod_cast qfinal
    simp only [Leaf.final] at h
    push_cast at h
    exact h
  have hmain : 0 ≤ interiorCost μ.a μ.b + α * S - (P (μ.entropyDrop + S) - P S) :=
    assemble_main hcost (by rw [hΔdef]; exact hdrop) hinc hc1 hc2 hα hbeta hbetaLo0 hsLoS hsLo0
      hfinR hm0 hm1 hL
  -- entropy-endpoint reduction by the corpus concavity criterion
  have hend : 0 ≤ gap (interiorCost μ.a μ.b) α μ.entropyDrop S := by
    unfold gap; linarith
  have hzero : P μ.entropyDrop ≤ interiorCost μ.a μ.b := by
    rw [hΔdef]; exact deterministic_cap_bound ha0 ha1 hb0 hb1'
  have hcrit := gap_endpoint_criterion hΔ0 hS0 hI1 hzero hend hs0 hsS
  have hV : LogSum.V μ.a μ.b = μ.b * (1 - μ.a) := by
    simp only [LogSum.V, max_eq_right hab.le, min_eq_left hab.le]
  have hfloor : μ.psiLogSumCostFloor = interiorCost μ.a μ.b + α * μ.meanDeficit := by
    unfold InteriorLaw.psiLogSumCostFloor
    rw [hV, hsdef, hα]
    unfold InteriorLaw.meanEntropy
    have hbpos : 0 < μ.b * (1 - μ.a) := mul_pos hb0 (by linarith)
    field_simp
    ring
  calc μ.splitBound = P (μ.entropyDrop + μ.meanDeficit) - P μ.meanDeficit := rfl
    _ ≤ interiorCost μ.a μ.b + α * μ.meanDeficit := hcrit
    _ = μ.psiLogSumCostFloor := hfloor.symm
    _ ≤ μ.cost := μ.psiLogSumCostFloor_le_cost

/-- Unconditional leaf soundness: `check = true` and exact-box membership give the psi bound. -/
theorem check_sound {B : Box} {c : Leaf} (hw : Leaf.check B c = true) : Sem B :=
  fun _ μ hin => (μ.psi_gap_le_splitBound).trans (check_sound_split hw μ hin)

/-! ## Certificate trees over archived boxes -/

inductive Cert where
  | leaf (c : Leaf)
  | splitX (m : ℚ) (l r : Cert)
  | splitB (m : ℚ) (l r : Cert)
  | splitT (m : ℚ) (l r : Cert)
  deriving Repr

def checkTree : Box → Cert → Bool
  | B, .leaf c => Leaf.check B c
  | B, .splitX m l r => checkTree { B with x1 := m } l && checkTree { B with x0 := m } r
  | B, .splitB m l r => checkTree { B with b1 := m } l && checkTree { B with b0 := m } r
  | B, .splitT m l r => checkTree { B with t1 := m } l && checkTree { B with t0 := m } r

theorem sem_splitX {B : Box} {m : ℚ} (hl : Sem { B with x1 := m }) (hr : Sem { B with x0 := m }) :
    Sem B := by
  intro k μ hin
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hin
  rcases le_total (μ.a / μ.b) ((2 : ℝ) ^ (-(m : ℝ))) with h | h
  · exact hr k μ ⟨h1, h, h3, h4, h5, h6⟩
  · exact hl k μ ⟨h, h2, h3, h4, h5, h6⟩

theorem sem_splitB {B : Box} {m : ℚ} (hl : Sem { B with b1 := m }) (hr : Sem { B with b0 := m }) :
    Sem B := by
  intro k μ hin
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hin
  rcases le_total μ.b (m : ℝ) with h | h
  · exact hl k μ ⟨h1, h2, h3, h, h5, h6⟩
  · exact hr k μ ⟨h1, h2, h, h4, h5, h6⟩

theorem sem_splitT {B : Box} {m : ℚ} (hl : Sem { B with t1 := m }) (hr : Sem { B with t0 := m }) :
    Sem B := by
  intro k μ hin
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hin
  rcases le_total μ.meanEntropy ((m : ℝ) * ((H μ.a + H μ.b) / 2)) with h | h
  · exact hl k μ ⟨h1, h2, h3, h4, h5, h⟩
  · exact hr k μ ⟨h1, h2, h3, h4, h, h6⟩

theorem checkTree_sound : ∀ (B : Box) (t : Cert), checkTree B t = true → Sem B
  | B, .leaf c, h => check_sound h
  | B, .splitX m l r, h => by
      simp only [checkTree, Bool.and_eq_true] at h
      exact sem_splitX (checkTree_sound _ l h.1) (checkTree_sound _ r h.2)
  | B, .splitB m l r, h => by
      simp only [checkTree, Bool.and_eq_true] at h
      exact sem_splitB (checkTree_sound _ l h.1) (checkTree_sound _ r h.2)
  | B, .splitT m l r, h => by
      simp only [checkTree, Bool.and_eq_true] at h
      exact sem_splitT (checkTree_sound _ l h.1) (checkTree_sound _ r h.2)

/-- A method witness: the exact archived box and its certificate tree. -/
structure Witness where
  box : Box
  cert : Cert
  deriving Repr

/-- The Boolean method checker. -/
def check (w : Witness) : Bool := checkTree w.box w.cert

/-- Unconditional semantic soundness of the entropy-endpoint checker. -/
theorem witness_sound (w : Witness) (hw : check w = true) : Sem w.box :=
  checkTree_sound w.box w.cert hw

/-- Owner form: on the box and with psi (weakly) active at the parent, `μ.gap ≤ μ.cost`. -/
theorem sem_gap_le_cost {B : Box} (hB : Sem B) {k : ℕ} (μ : InteriorLaw (Fin k))
    (hbox : InBox B μ)
    (hact : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost :=
  (hybrid_gap_le_psi hact).trans (hB k μ hbox)

/-! ## Archived same-side paths -/

/-- Root of the archived same-side cover: `x ∈ [0,32]`, `b ∈ [1/32,1/2]`, `t ∈ [0,1]`. -/
def root : Box := ⟨0, 32, 1 / 32, 1 / 2, 0, 1⟩

/-- One exact halving step (`same_side/COVER.py`, digit = 2*axis + side). -/
def step (B : Box) (d : ℕ) : Box :=
  match d with
  | 0 => { B with x1 := (B.x0 + B.x1) / 2 }
  | 1 => { B with x0 := (B.x0 + B.x1) / 2 }
  | 2 => { B with b1 := (B.b0 + B.b1) / 2 }
  | 3 => { B with b0 := (B.b0 + B.b1) / 2 }
  | 4 => { B with t1 := (B.t0 + B.t1) / 2 }
  | 5 => { B with t0 := (B.t0 + B.t1) / 2 }
  | _ => B

/-- The exact box of an archived path. -/
def boxOfPath (p : List ℕ) : Box := p.foldl step root

def checkAll (L : List (List ℕ × Cert)) : Bool := L.all fun x => checkTree (boxOfPath x.1) x.2

theorem checkAll_sound (L : List (List ℕ × Cert)) (h : checkAll L = true) :
    ∀ x ∈ L, Sem (boxOfPath x.1) := by
  intro x hx
  unfold checkAll at h
  rw [List.all_eq_true] at h
  exact checkTree_sound _ _ (h x hx)

end CKLaneM08

#check @CKLaneM08.check_sound_split
#check @CKLaneM08.check_sound
#check @CKLaneM08.witness_sound
#check @CKLaneM08.sem_gap_le_cost
#check @CKLaneM08.checkAll_sound
#print axioms CKLaneM08.check_sound_split
#print axioms CKLaneM08.witness_sound
#print axioms CKLaneM08.sem_gap_le_cost
#print axioms CKLaneM08.checkAll_sound

end


