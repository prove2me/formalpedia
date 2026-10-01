-- Prove2me | Definitions.Def_CK_CKLaneM06_Checker
-- name    : CK_CKLaneM06_Checker
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T11:25:21.938638+00:00
-- url     : https://prove2.me/theorems/8ba2df92-92ab-4188-935d-054959ae51c9
-- title:
--   Courtade–Kumar proof module `CKLaneM06.Checker` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM06.Checker` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM06.Checker` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM06.Checker (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM06/Checker.lean)

import Definitions.Def_CK_CKLaneM06_Semantics
import Definitions.Def_CK_CKLaneE_FastPoint
import Definitions.Def_CK_CKLaneD_FleetBase

-- ===== source module CKLaneM06.Checker =====
section

/-!
# Lane M06: reflective Boolean checker for the archived method `parent_tail`

Archive (`same_side/COVER.py`, owner `parent_tail`; `PROOF.md` §4.6 "Elementary parent tail"):
on a box with `m = (a+b)/2`, `E` the mean entropy, accept iff
`(2 m⁻ - E⁺) log₂((2 - E⁺)/E⁺) ≥ P(H(m⁺))` where `P(y) = eta(1 - y)`.
The certified comparison is parent dominance `psi(m,E) ≤ phi(m,E)`.

Semantic chain proved in `check_sound` (no numerical hypothesis):
* `phi m E ≥ (2m - E) · log((2-E)/E)/log 2`      (corpus `PsiParentPhiFloor.phi_lower`, `0 < E < 2m < 1`)
*         `≥ (2 m⁻ - E⁺) · lamLo(E⁺/2)/LqHi`     (monotonicity; `CKLaneE.FP.lam_bounds`, `log_two_mem`)
* `psi m E = eta(E + 1 - H m) ≤ (1 - 2u) · lamHi(u)/LqLo`
                                                  (corpus `LowEntropyLeaf.eta_le_of_witness`, `H u ≤ 1 - H m⁺`)
Every enclosure is recomputed by the kernel from the box and the witness:
* `r = a/b ∈ [rlo, rhi]` from exact `Nat`-power certificates of `2^-x` (`CKLaneD.pow2*OK_sound`),
* `H` / `log` rational enclosures (`CKLaneE.FP.H_bounds`, `lam_bounds`),
* `E ≤ hi2 · C ≤ hi2 · (Hhi(a⁺) + Hhi(b⁺))/2 ≤ Ehi`.
The witness stores only rounding points (`rlo, rhi, Ehi, u`); no margin is stored.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM06

open GeneralCK CKLaneE.FP

/-- Witness data for one box.  Every field is re-verified by `check`; no margin is stored. -/
structure Witness where
  /-- lower bound for `r = a/b` on the box, certified `rlo ≤ 2^-hi0` -/
  rlo : ℚ
  /-- upper bound for `r = a/b` on the box, certified `2^-lo0 ≤ rhi` -/
  rhi : ℚ
  /-- mean-entropy rounding point, certified `hi2 · (Hhi(a⁺) + Hhi(b⁺)) / 2 ≤ Ehi` -/
  Ehi : ℚ
  /-- entropy-inverse witness for `eta` at `1 - H(m⁺)`, certified `Hhi u ≤ 1 - Hhi(m⁺)` -/
  u : ℚ
  deriving DecidableEq, Repr

/-- `a⁺ = hi1 · rhi`, an upper bound of `a = r b` on the box. -/
def aHi (B : Box) (w : Witness) : ℚ := B.hi1 * w.rhi

/-- `m⁻ = lo1 (1 + rlo) / 2`, a lower bound of the midpoint on the box. -/
def mLo (B : Box) (w : Witness) : ℚ := B.lo1 * (1 + w.rlo) / 2

/-- `m⁺ = hi1 (1 + rhi) / 2`, an upper bound of the midpoint on the box. -/
def mHi (B : Box) (w : Witness) : ℚ := B.hi1 * (1 + w.rhi) / 2

/-- Rational lower bound of `phi` on the box: `(2 m⁻ - E⁺) · J(E⁺/2)⁻`. -/
def phiLo (B : Box) (w : Witness) : ℚ := (2 * mLo B w - w.Ehi) * (lamLo (w.Ehi / 2) / LqHi)

/-- Rational upper bound of `psi` on the box: `(1 - 2u) · J(u)⁺`. -/
def psiHi (w : Witness) : ℚ := (1 - 2 * w.u) * (lamHi w.u / LqLo)

/-- The Boolean checker of the `parent_tail` inequality on one box. -/
def check (B : Box) (w : Witness) : Bool :=
  CKLaneD.pow2LowerOK w.rlo B.hi0 && CKLaneD.pow2UpperOK w.rhi B.lo0 &&
  decide (B.hi1 ≤ 1 / 2) && decide (0 ≤ B.hi2) &&
  decide (aHi B w ≤ 1 / 2) && ptOk (aHi B w) && ptOk B.hi1 &&
  decide (B.hi2 * (Hhi (aHi B w) + Hhi B.hi1) / 2 ≤ w.Ehi) &&
  decide (w.Ehi < 2 * mLo B w) && ptOk (w.Ehi / 2) && decide (0 ≤ lamLo (w.Ehi / 2)) &&
  decide (mHi B w < 1 / 2) && ptOk (mHi B w) &&
  ptOk w.u && decide (w.u ≤ 1 / 2) && decide (Hhi w.u ≤ 1 - Hhi (mHi B w)) &&
  decide (0 ≤ lamHi w.u) && decide (psiHi w ≤ phiLo B w)

theorem qcast_le {x y : ℚ} (h : x ≤ y) : (x : ℝ) ≤ (y : ℝ) := Rat.cast_le.mpr h

theorem qcast_lt {x y : ℚ} (h : x < y) : (x : ℝ) < (y : ℝ) := Rat.cast_lt.mpr h

theorem pow2LowerOK_pos {r u : ℚ} (h : CKLaneD.pow2LowerOK r u = true) : 0 < r := by
  unfold CKLaneD.pow2LowerOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem pow2UpperOK_pos {r u : ℚ} (h : CKLaneD.pow2UpperOK r u = true) : 0 < r := by
  unfold CKLaneD.pow2UpperOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

set_option maxHeartbeats 1000000 in
/-- **Soundness.** If the checker accepts `(B, w)`, then `phi` dominates `psi` at the parent for
every law in the exact box `B`. -/
theorem check_sound {B : Box} {w : Witness} (hw : check B w = true)
    {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) (hB : InBox B μ) :
    psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hw
  obtain ⟨hrlo, hrhi, hbhi, hthi, haHi, hptA, hptB, hEcap, hE2m, hptV, hlamV, hmHi, hptM,
    hptU, hu2, hHu, hlamU, hfin⟩ := hw
  obtain ⟨g1, g2, g3, g4, -, g6⟩ := hB.bounds
  have ha := μ.a_interior
  have hb := μ.b_interior
  -- ratio bounds `rlo · b ≤ a ≤ rhi · b`
  have rlo' := CKLaneD.pow2LowerOK_sound hrlo
  have rhi' := CKLaneD.pow2UpperOK_sound hrhi
  have hrlo0 : (0 : ℝ) < (w.rlo : ℝ) := by exact_mod_cast pow2LowerOK_pos hrlo
  have hrhi0 : (0 : ℝ) < (w.rhi : ℝ) := by exact_mod_cast pow2UpperOK_pos hrhi
  have hA1 : (w.rlo : ℝ) * μ.b ≤ μ.a := le_trans (mul_le_mul_of_nonneg_right rlo' hb.1.le) g1
  have hA2 : μ.a ≤ (w.rhi : ℝ) * μ.b := le_trans g2 (mul_le_mul_of_nonneg_right rhi' hb.1.le)
  -- real forms of the rational side conditions
  have hbhiR : (B.hi1 : ℝ) ≤ 1 / 2 := by
    have h := qcast_le hbhi
    push_cast at h
    linarith
  have hthiR : (0 : ℝ) ≤ (B.hi2 : ℝ) := by exact_mod_cast hthi
  have caH : ((aHi B w : ℚ) : ℝ) = (B.hi1 : ℝ) * (w.rhi : ℝ) := by
    simp only [aHi, Rat.cast_mul]
  have cmL : ((mLo B w : ℚ) : ℝ) = (B.lo1 : ℝ) * (1 + (w.rlo : ℝ)) / 2 := by
    simp only [mLo, Rat.cast_mul, Rat.cast_div, Rat.cast_add, Rat.cast_one, Rat.cast_ofNat]
  have cmH : ((mHi B w : ℚ) : ℝ) = (B.hi1 : ℝ) * (1 + (w.rhi : ℝ)) / 2 := by
    simp only [mHi, Rat.cast_mul, Rat.cast_div, Rat.cast_add, Rat.cast_one, Rat.cast_ofNat]
  have haHiR : ((aHi B w : ℚ) : ℝ) ≤ 1 / 2 := by
    have h := qcast_le haHi
    push_cast at h
    linarith
  have ha_le : μ.a ≤ ((aHi B w : ℚ) : ℝ) := by
    rw [caH]
    have := mul_le_mul_of_nonneg_left g4 hrhi0.le
    nlinarith
  -- entropy upper bounds at `a⁺` and `b⁺`
  obtain ⟨-, HaHi⟩ := H_bounds hptA
  obtain ⟨-, HbHi⟩ := H_bounds hptB
  have hHa : H μ.a ≤ H ((aHi B w : ℚ) : ℝ) :=
    H_strictMonoOn.monotoneOn ⟨ha.1.le, by linarith⟩ ⟨by linarith, haHiR⟩ ha_le
  have hHb : H μ.b ≤ H (B.hi1 : ℝ) :=
    H_strictMonoOn.monotoneOn ⟨hb.1.le, by linarith⟩ ⟨by linarith, hbhiR⟩ g4
  -- mean-entropy upper bound `E ≤ Ehi`
  have hEcapR : (B.hi2 : ℝ) * (((Hhi (aHi B w) : ℚ) : ℝ) + ((Hhi B.hi1 : ℚ) : ℝ)) / 2 ≤
      (w.Ehi : ℝ) := by
    have h := qcast_le hEcap
    push_cast at h
    linarith
  have hCle : capMean μ ≤ (((Hhi (aHi B w) : ℚ) : ℝ) + ((Hhi B.hi1 : ℚ) : ℝ)) / 2 := by
    unfold capMean
    linarith
  have hE_le : μ.meanEntropy ≤ (w.Ehi : ℝ) := by
    have := mul_le_mul_of_nonneg_left hCle hthiR
    nlinarith
  -- midpoint bounds `m⁻ ≤ m ≤ m⁺`
  have hm_def : μ.midpoint = (μ.a + μ.b) / 2 := rfl
  have hm_lo : ((mLo B w : ℚ) : ℝ) ≤ μ.midpoint := by
    rw [cmL, hm_def]
    have := mul_le_mul_of_nonneg_right g3 (by linarith : (0 : ℝ) ≤ 1 + (w.rlo : ℝ))
    nlinarith
  have hm_hi : μ.midpoint ≤ ((mHi B w : ℚ) : ℝ) := by
    rw [cmH, hm_def]
    have := mul_le_mul_of_nonneg_right g4 (by linarith : (0 : ℝ) ≤ 1 + (w.rhi : ℝ))
    nlinarith
  have hmHiR : ((mHi B w : ℚ) : ℝ) < 1 / 2 := by
    have h := qcast_lt hmHi
    push_cast at h
    linarith
  have hm_pos : 0 < μ.midpoint := by rw [hm_def]; linarith [ha.1, hb.1]
  have hHm : H μ.midpoint ≤ ((Hhi (mHi B w) : ℚ) : ℝ) := by
    obtain ⟨-, h⟩ := H_bounds hptM
    exact (H_strictMonoOn.monotoneOn ⟨hm_pos.le, by linarith⟩ ⟨by linarith, hmHiR.le⟩
      hm_hi).trans h
  -- feasibility of the mean entropy: `0 < E ≤ C ≤ H m`
  have hE_pos : 0 < μ.meanEntropy := by
    have h1 := μ.e_pos
    have h2 := μ.f_pos
    unfold InteriorLaw.meanEntropy
    linarith
  have hE_cap : μ.meanEntropy ≤ H μ.midpoint := by
    have h1 := μ.e_le_cap
    have h2 := μ.f_le_cap
    have h3 := μ.entropyDrop_nonneg
    unfold InteriorLaw.entropyDrop at h3
    unfold InteriorLaw.meanEntropy
    linarith
  -- (i) phi lower bound (corpus `PsiParentPhiFloor.phi_lower`)
  have hV := ptOk_pos hptV
  have hvpos : (0 : ℝ) < ((w.Ehi / 2 : ℚ) : ℝ) := by exact_mod_cast hV.1
  have hvcast : ((w.Ehi / 2 : ℚ) : ℝ) = (w.Ehi : ℝ) / 2 := by
    simp only [Rat.cast_div, Rat.cast_ofNat]
  have hEhi_pos : (0 : ℝ) < (w.Ehi : ℝ) := by rw [hvcast] at hvpos; linarith
  have hE2mR : (w.Ehi : ℝ) < 2 * ((mLo B w : ℚ) : ℝ) := by
    have h := qcast_lt hE2m
    push_cast at h
    linarith
  have hq0 : 0 < 1 - 2 * μ.midpoint := by linarith
  have hEq : μ.meanEntropy < 1 - (1 - 2 * μ.midpoint) := by linarith
  have hphi := PsiParentPhiFloor.phi_lower hq0 hE_pos hEq
  rw [show (1 - (1 - 2 * μ.midpoint)) / 2 = μ.midpoint by ring] at hphi
  have hcoef : 2 * ((mLo B w : ℚ) : ℝ) - (w.Ehi : ℝ) ≤
      1 - (1 - 2 * μ.midpoint) - μ.meanEntropy := by linarith
  have hlogmono : Real.log ((1 - ((w.Ehi / 2 : ℚ) : ℝ)) / ((w.Ehi / 2 : ℚ) : ℝ)) ≤
      Real.log ((2 - μ.meanEntropy) / μ.meanEntropy) := by
    apply Real.log_le_log
    · apply div_pos _ hvpos
      rw [hvcast]
      linarith
    · rw [div_le_div_iff₀ hvpos hE_pos, hvcast]
      nlinarith
  obtain ⟨hlamV', -⟩ := lam_bounds hptV
  have hL := log_two_mem
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlamV0 : (0 : ℝ) ≤ ((lamLo (w.Ehi / 2) : ℚ) : ℝ) := by exact_mod_cast hlamV
  have hJlo : ((lamLo (w.Ehi / 2) : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) ≤
      Real.log ((2 - μ.meanEntropy) / μ.meanEntropy) / Real.log 2 := by
    calc ((lamLo (w.Ehi / 2) : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ)
        ≤ ((lamLo (w.Ehi / 2) : ℚ) : ℝ) / Real.log 2 :=
          div_le_div_of_nonneg_left hlamV0 hlog2 hL.2
      _ ≤ Real.log ((2 - μ.meanEntropy) / μ.meanEntropy) / Real.log 2 :=
          div_le_div_of_nonneg_right (hlamV'.trans hlogmono) hlog2.le
  have hJlo0 : 0 ≤ ((lamLo (w.Ehi / 2) : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) :=
    div_nonneg hlamV0 (hlog2.le.trans hL.2)
  have ePhi : ((phiLo B w : ℚ) : ℝ) = (2 * ((mLo B w : ℚ) : ℝ) - (w.Ehi : ℝ)) *
      (((lamLo (w.Ehi / 2) : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ)) := by
    simp only [phiLo, Rat.cast_mul, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat]
  have hphiLo : ((phiLo B w : ℚ) : ℝ) ≤ phi μ.midpoint μ.meanEntropy := by
    rw [ePhi]
    calc (2 * ((mLo B w : ℚ) : ℝ) - (w.Ehi : ℝ)) *
          (((lamLo (w.Ehi / 2) : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ))
        ≤ (1 - (1 - 2 * μ.midpoint) - μ.meanEntropy) *
          (((lamLo (w.Ehi / 2) : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hcoef hJlo0
      _ ≤ (1 - (1 - 2 * μ.midpoint) - μ.meanEntropy) *
          (Real.log ((2 - μ.meanEntropy) / μ.meanEntropy) / Real.log 2) :=
          mul_le_mul_of_nonneg_left hJlo (by linarith)
      _ ≤ phi μ.midpoint μ.meanEntropy := hphi
  -- (ii) psi upper bound (corpus `LowEntropyLeaf.eta_le_of_witness`)
  have hU := ptOk_pos hptU
  have hu0 : (0 : ℝ) < (w.u : ℝ) := by exact_mod_cast hU.1
  have hu2R : (w.u : ℝ) ≤ 1 / 2 := by
    have h := qcast_le hu2
    push_cast at h
    linarith
  have hHuR : ((Hhi w.u : ℚ) : ℝ) ≤ 1 - ((Hhi (mHi B w) : ℚ) : ℝ) := by
    have h := qcast_le hHu
    push_cast at h
    linarith
  obtain ⟨-, HuHi⟩ := H_bounds hptU
  obtain ⟨-, hlamU'⟩ := lam_bounds hptU
  have hlamU0 : (0 : ℝ) ≤ ((lamHi w.u : ℚ) : ℝ) := by exact_mod_cast hlamU
  have hJu : J (w.u : ℝ) ≤ ((lamHi w.u : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) := by
    unfold J
    calc Real.log ((1 - (w.u : ℝ)) / (w.u : ℝ)) / Real.log 2
        ≤ ((lamHi w.u : ℚ) : ℝ) / Real.log 2 := div_le_div_of_nonneg_right hlamU' hlog2.le
      _ ≤ ((lamHi w.u : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) :=
          div_le_div_of_nonneg_left hlamU0 LqLo_pos hL.1
  have hX0 : 0 ≤ ((lamHi w.u : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) := div_nonneg hlamU0 LqLo_pos.le
  have hh0 : 0 < μ.meanEntropy + 1 - H μ.midpoint := by linarith [H_le_one μ.midpoint]
  have hh1 : μ.meanEntropy + 1 - H μ.midpoint ≤ 1 := by linarith
  have hHu_le : H (w.u : ℝ) ≤ μ.meanEntropy + 1 - H μ.midpoint := by linarith
  have hpsi := LowEntropyLeaf.eta_le_of_witness _ _ _ hh0 hh1 hu0 hu2R hHu_le hJu hX0
  have ePsi : ((psiHi w : ℚ) : ℝ) = (1 - 2 * (w.u : ℝ)) *
      (((lamHi w.u : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ)) := by
    simp only [psiHi, Rat.cast_mul, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  have hpsiHi : psi μ.midpoint μ.meanEntropy ≤ ((psiHi w : ℚ) : ℝ) := by
    rw [ePsi]
    exact hpsi
  -- final comparison, evaluated by the checker
  have hfinR : ((psiHi w : ℚ) : ℝ) ≤ ((phiLo B w : ℚ) : ℝ) := qcast_le hfin
  linarith

/-- Per-leaf acceptance: the witness is checked on the exact box of the archived path. -/
def checkLeaf (p : List ℕ) (w : Witness) : Bool := check (pathBox p) w

theorem checkLeaf_sound {p : List ℕ} {w : Witness} (h : checkLeaf p w = true) :
    ParentDominance (pathBox p) :=
  fun _ μ hB => check_sound h μ hB

theorem checkLeaf_owner {p : List ℕ} {w : Witness} (h : checkLeaf p w = true) :
    PsiOwnerOn (pathBox p) :=
  (checkLeaf_sound h).psiOwnerOn

/-- Batched acceptance of a list of archived leaves. -/
def checkAll (L : List (List ℕ × Witness)) : Bool := L.all fun x => checkLeaf x.1 x.2

theorem checkAll_sound {L : List (List ℕ × Witness)} (h : checkAll L = true) :
    ∀ x ∈ L, ParentDominance (pathBox x.1) := by
  intro x hx
  rw [checkAll, List.all_eq_true] at h
  exact checkLeaf_sound (h x hx)

end CKLaneM06

end


