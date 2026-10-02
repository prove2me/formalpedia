-- Prove2me | Definitions.Def_CK_CKLaneN1c_Normalized
-- name    : CK_CKLaneN1c_Normalized
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:51:54.395863+00:00
-- url     : https://prove2.me/theorems/e95924e6-b36c-42d5-8f8e-8412916d80f9
-- title:
--   Courtade–Kumar proof module `CKLaneN1c.Normalized` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1c.Normalized` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1c.Normalized` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1c.Normalized (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1c/Normalized.lean)

import Definitions.Def_CK_CKLaneN1c_NormAnalytic
import Definitions.Def_CK_CKLaneN1c_Endpoint

-- ===== source module CKLaneN1c.Normalized =====
section

/-!
# Lane N1c-c: Boolean kernel for the transition `normalized_phi_children` owner

Archive: `CK_OPPOSITE_EXTENSION.zip`, `transition/TRANSITION.py`, `bound`, owner
`normalized_phi_children`; `transition/PROOF.md` §3, box inequality (10):

  `E₋/L + β/(2L) · ℓ₀(C₊/E₋) − W(x₋) − 169 E₊/(144 c_*) ≥ 0`,

`C₊ = C(q₊)`, `q₊ = min(2/5, E₊y₊)`, `β = (1-2v₊)/(L(1-v₊)) · (1 + 1/log((1-v₋)/v₋))`,
`v₊ ≥ H⁻¹(E₊ + C₊)`, `v₋ ≤ H⁻¹(E₋)`, `ℓ₀(u) = log(1+u)/u`, `W(x) = f'(x)/(2x)` at a lower contact bracket
`v_l ≤ contact(x₋, 1)`, `c_* = 9 d₋/(20L) + max(0, 1/(2L) − (13/6) min(4/5, (x₊+y₊)E₊))/2`,
`d₋ = max(1/50, E₋x₋)`.  All quantities exact ℚ with lane E `CKLaneE.FP` enclosures.

Soundness (`checkN_sound`): premises `checkN B v_p v_m v_l = true`, membership of the law in the exact
leaf image `InExy B`, the rows' canonical/central hypotheses and strict psi-activity.  Entropy split
arbitrary; no stored margins; no real-variable hypotheses.  Chain (PROOF.md §3):
`gap ≤ η(E + C(q)) − childAverage` (retained child φ, `canonical_hybrid_gap_le_childAverage`),
child tangent lines with `γ` (6), the endpoint gain `cost ≥ F(d,E) + (9d/(20L)) 𝒥(τ)`
(`Gain.law_endpoint_gain_four`), `|A| ≤ 13q/(3E)` (`child_slope_bounds`), split loss (7), radial loss (8),
parent gain (9).
-/

set_option autoImplicit false

namespace CKLaneN1c

open GeneralCK CKLaneE.FP CKLaneN1 CKLaneG1 PsiChildEntropyCoupling PsiSignedSplit
  PsiExtendedEntropyCurvature

/-! ## The kernel -/

/-- `m₋ = (1 − q₊)/2`, `q₊ = min(2/5, E₊ y₊)`. -/
def nM (B : B3) : ℚ := (1 - min (2 / 5) (B.a1 * B.c1)) / 2
/-- `C₊ = 1 − H⁻(m₋) ≥ C(q)`. -/
def nCp (B : B3) : ℚ := 1 - Hlo (nM B)
/-- `u = C₊/E₋ ≥ C(q)/E`. -/
def nU (B : B3) : ℚ := nCp B / B.a0
/-- `h₊ = E₊ + C₊`. -/
def nHp (B : B3) : ℚ := B.a1 + nCp B
/-- `1/(1+u)`, whose log certifies `log(1+u)` from below. -/
def nZ (B : B3) : ℚ := 1 / (1 + nU B)
/-- The archived slope constant `β` (with `log 2` bounded above). -/
def nBeta (vp vm : ℚ) : ℚ := (1 - 2 * vp) / (LqHi * (1 - vp)) * (1 + 1 / lamHi vm)
/-- Parent term `E₋/L + β/(2L) ℓ₀(u)` (lower bound). -/
def nPar (B : B3) (vp vm : ℚ) : ℚ :=
  B.a0 / LqHi + nBeta vp vm / (2 * LqHi) * (-(lHi (nZ B)) / nU B)
/-- Lower bound of `kap v = −log(v(1−v))/2`. -/
def nKl (vl : ℚ) : ℚ := -(lHi vl + l1Hi vl) / 2
/-- Upper bound of `radialSlope v_l`. -/
def nRs (vl : ℚ) : ℚ := JhiQ vl + (1 - 2 * vl) * HnumHi vl / (2 * LqLo * vl * (1 - vl) * nKl vl)
/-- Upper bound of `W(x₋) = f'(x₋)/(2x₋)`. -/
def nW (B : B3) (vl : ℚ) : ℚ := nRs vl / (2 * B.b0)
/-- `s₊ = min(4/5, (x₊+y₊)E₊) ≥ d + q`. -/
def nSmax (B : B3) : ℚ := min (4 / 5) ((B.b1 + B.c1) * B.a1)
/-- `γ = max(0, 1/(2L) − (13/6) s₊)` (with `log 2` bounded above). -/
def nGam (B : B3) : ℚ := max 0 (1 / (2 * LqHi) - 13 / 6 * nSmax B)
/-- `c_* = 9 d₋/(20L) + γ/2`. -/
def nCs (B : B3) : ℚ := 9 * max (1 / 50) (B.a0 * B.b0) / (20 * LqHi) + nGam B / 2

/-- Kernel acceptance test of the transition `normalized_phi_children` owner (PROOF.md (10)). -/
def checkN (B : B3) (vp vm vl : ℚ) : Bool :=
  decide (0 < B.a0 ∧ B.a0 ≤ B.a1 ∧ 0 < B.b0 ∧ B.b0 ≤ B.b1 ∧ 0 ≤ B.c0 ∧ B.c0 ≤ B.c1) &&
  ptOk (nM B) && decide (nM B ≤ 1 / 2 ∧ 0 < nCp B) &&
  ptOk vp && decide (vp < 1 / 2 ∧ nHp B ≤ Hlo vp ∧ nHp B < 1) &&
  ptOk vm && decide (vm < 1 / 2 ∧ Hhi vm ≤ B.a0 ∧ 0 < lamHi vm) &&
  ptOk (nZ B) && decide (0 ≤ -(lHi (nZ B))) &&
  ptOk vl && decide (vl < 1 / 2 ∧ B.b0 * Hhi vl ≤ 1 - 2 * vl ∧ 0 < nKl vl ∧ 0 ≤ HnumHi vl) &&
  decide (0 < nCs B ∧ 0 ≤ nPar B vp vm - nW B vl - 169 * B.a1 / (144 * nCs B))

/-! ## Real core: the retained-child margin from the box constants -/

/-- PROOF.md §3 assembled: with the parent bound (9), the radial bound (8) and a barrier coefficient
`c ≥ c_* > 0`, the retained-child comparison is at most the endpoint lower bound. -/
theorem retained_margin_box {d q E t C γ par W cs a1 : ℝ}
    (hq : 0 ≤ q) (hqd : q ≤ d) (hdq : d + q ≤ 4 / 5) (hE : 0 < E) (hEi : E ≤ 11 / 200)
    (hEa1 : E ≤ a1) (ht : |t| < 1) (hγ : γ = 0 ∨ γ ≤ compensation (d + q))
    (hpar : q ^ 2 / E * par ≤ eta E - eta (E + C))
    (hrad : radialLoss d q E ≤ q ^ 2 / E * W)
    (hcs : 0 < cs) (hcsc : cs ≤ 9 * d / (20 * Real.log 2) + γ / 2)
    (hval : 0 ≤ par - W - 169 * a1 / (144 * cs)) :
    eta (E + C) - childAverage d q E t ≤ F d E + 9 * d / (20 * Real.log 2) * barrier t := by
  have hchild := NA.childAverage_lower hq hqd hdq hE hEi ht hγ
  obtain ⟨hA0, hA⟩ := PsiLowEntropyRedesign.child_slope_bounds hE (by linarith) hq hqd
  have hc : 0 < 9 * d / (20 * Real.log 2) + γ / 2 := lt_of_lt_of_le hcs hcsc
  have hsplit := NA.split_loss hc hE hA0 hA ht
  have hphi : (radialPhi (d + q) E + radialPhi (d - q) E) / 2 = eta E - F d E - radialLoss d q E := by
    unfold radialPhi radialLoss
    ring
  have hqE : 0 ≤ q ^ 2 / E := by positivity
  have hloss : 169 * q ^ 2 / (144 * (9 * d / (20 * Real.log 2) + γ / 2)) ≤
      q ^ 2 / E * (169 * a1 / (144 * cs)) := by
    have h1 : 169 * q ^ 2 / (144 * (9 * d / (20 * Real.log 2) + γ / 2)) ≤
        169 * q ^ 2 / (144 * cs) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have h2 : 169 * q ^ 2 / (144 * cs) = q ^ 2 / E * (169 * E / (144 * cs)) := by
      field_simp
    have h3 : 169 * E / (144 * cs) ≤ 169 * a1 / (144 * cs) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h4 := mul_le_mul_of_nonneg_left h3 hqE
    linarith
  have hfin := mul_nonneg hqE hval
  have hfin' : q ^ 2 / E * (169 * a1 / (144 * cs)) ≤ q ^ 2 / E * par - q ^ 2 / E * W := by
    have e : q ^ 2 / E * (par - W - 169 * a1 / (144 * cs)) =
        q ^ 2 / E * par - q ^ 2 / E * W - q ^ 2 / E * (169 * a1 / (144 * cs)) := by ring
    linarith
  have hcb : (9 * d / (20 * Real.log 2) + γ / 2) * barrier t =
      9 * d / (20 * Real.log 2) * barrier t + γ * barrier t / 2 := by ring
  linarith

/-! ## Soundness -/

set_option maxHeartbeats 4000000 in
/-- Soundness of the `normalized_phi_children` leaf check (in-row form). -/
theorem checkN_sound {B : B3} {vp vm vl : ℚ} (h : checkN B vp vm vl = true)
    {k : ℕ} (μ : InteriorLaw (Fin k)) (hsum : μ.a + μ.b ≤ 1) (ha : 1 / 10 ≤ μ.a)
    (hb : 1 / 2 ≤ μ.b) (hd : 1 / 50 ≤ μ.b - μ.a) (hE11 : μ.meanEntropy ≤ 11 / 200)
    (h4 : 4 * μ.meanEntropy ≤ μ.b - μ.a)
    (hin : InExy B μ.a μ.b μ.meanEntropy) (hact : PsiActive μ) : μ.gap ≤ μ.cost := by
  simp only [checkN, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hbox, hptM⟩, hMc⟩, hptp⟩, hvpc⟩, hptm⟩, hvmc⟩, hptz⟩, hluc⟩, hptl⟩, hvlc⟩,
    hfin⟩ := h
  obtain ⟨ha0, -, hb0, -, hc0, -⟩ := hbox
  obtain ⟨hMh, hCp0⟩ := hMc
  obtain ⟨hvph, hvpH, hHp1⟩ := hvpc
  obtain ⟨hvmh, hvmH, hlhi0⟩ := hvmc
  obtain ⟨hvlh, hvlH, hkl0, hhn0⟩ := hvlc
  obtain ⟨hcs0, hval⟩ := hfin
  obtain ⟨hE0, hE1, hx0, hx1, hy0, hy1⟩ := hin
  have haI := μ.a_interior
  have hbI := μ.b_interior
  have hEpos : 0 < μ.meanEntropy := CKLaneD.law_meanEntropy_pos μ
  have hL := log_two_pos
  obtain ⟨hLlo, hLhi⟩ := log_two_mem
  have hLqHi := LqHi_pos
  have hLqLo := LqLo_pos
  -- casts of box data
  have ha0R : (0 : ℝ) < (B.a0 : ℝ) := by exact_mod_cast ha0
  have hb0R : (0 : ℝ) < (B.b0 : ℝ) := by exact_mod_cast hb0
  have hc0R : (0 : ℝ) ≤ (B.c0 : ℝ) := by exact_mod_cast hc0
  -- basic law quantities
  have hdpos : 0 < μ.b - μ.a := by linarith
  have hq0 : 0 ≤ 1 - μ.a - μ.b := by linarith
  have hqd : 1 - μ.a - μ.b ≤ μ.b - μ.a := by linarith
  have hdq : (μ.b - μ.a) + (1 - μ.a - μ.b) ≤ 4 / 5 := by linarith
  have hq25 : 1 - μ.a - μ.b ≤ 2 / 5 := by linarith
  -- coordinates
  have hxE : (μ.b - μ.a) / μ.meanEntropy * μ.meanEntropy = μ.b - μ.a := by field_simp
  have hyE : (1 - μ.a - μ.b) / μ.meanEntropy * μ.meanEntropy = 1 - μ.a - μ.b := by field_simp
  have hxnn : 0 ≤ (μ.b - μ.a) / μ.meanEntropy := hb0R.le.trans hx0
  have hynn : 0 ≤ (1 - μ.a - μ.b) / μ.meanEntropy := hc0R.trans hy0
  have hd_hi : μ.b - μ.a ≤ (B.b1 : ℝ) * (B.a1 : ℝ) := by
    rw [← hxE]; exact mul_le_mul hx1 hE1 hEpos.le (hxnn.trans hx1)
  have hq_hi : 1 - μ.a - μ.b ≤ (B.c1 : ℝ) * (B.a1 : ℝ) := by
    rw [← hyE]; exact mul_le_mul hy1 hE1 hEpos.le (hynn.trans hy1)
  have hd_lo : (B.b0 : ℝ) * (B.a0 : ℝ) ≤ μ.b - μ.a := by
    rw [← hxE]; exact mul_le_mul hx0 hE0 ha0R.le hxnn
  -- C(q) and its upper enclosure
  have hMeq : ((nM B : ℚ) : ℝ) = (1 - min (2 / 5 : ℝ) ((B.a1 : ℝ) * (B.c1 : ℝ))) / 2 := by
    simp only [nM]; push_cast; ring
  have hqmin : 1 - μ.a - μ.b ≤ min (2 / 5 : ℝ) ((B.a1 : ℝ) * (B.c1 : ℝ)) :=
    le_min hq25 (by rw [mul_comm]; exact hq_hi)
  have hM0 : (0 : ℝ) < ((nM B : ℚ) : ℝ) := by exact_mod_cast (ptOk_pos hptM).1
  have hMle : ((nM B : ℚ) : ℝ) ≤ (1 - (1 - μ.a - μ.b)) / 2 := by rw [hMeq]; linarith
  have hHM : ((Hlo (nM B) : ℚ) : ℝ) ≤ H ((1 - (1 - μ.a - μ.b)) / 2) :=
    (H_bounds hptM).1.trans (CKLaneD.H_mono_left hM0.le hMle (by linarith))
  have hCle : 1 - H ((1 - (1 - μ.a - μ.b)) / 2) ≤ ((nCp B : ℚ) : ℝ) := by
    simp only [nCp]; push_cast; linarith
  have hC0 : 0 ≤ 1 - H ((1 - (1 - μ.a - μ.b)) / 2) := by
    linarith [H_le_one ((1 - (1 - μ.a - μ.b)) / 2)]
  have hHpR : ((nHp B : ℚ) : ℝ) = (B.a1 : ℝ) + ((nCp B : ℚ) : ℝ) := by
    simp only [nHp]; push_cast; ring
  have hEC : μ.meanEntropy + (1 - H ((1 - (1 - μ.a - μ.b)) / 2)) ≤ ((nHp B : ℚ) : ℝ) := by
    rw [hHpR]; linarith
  have hHp1R : ((nHp B : ℚ) : ℝ) < 1 := by
    have h' := (Rat.cast_lt (K := ℝ)).mpr hHp1
    push_cast at h' ⊢
    linarith
  -- `v_p`
  have hvp0 : (0 : ℝ) < (vp : ℝ) := by exact_mod_cast (ptOk_pos hptp).1
  have hvphR : (vp : ℝ) < 1 / 2 := by
    have h' := (Rat.cast_lt (K := ℝ)).mpr hvph
    push_cast at h'
    linarith
  have hvpHR : ((nHp B : ℚ) : ℝ) ≤ ((Hlo vp : ℚ) : ℝ) := by exact_mod_cast hvpH
  have hHvp : μ.meanEntropy + (1 - H ((1 - (1 - μ.a - μ.b)) / 2)) ≤ H (vp : ℝ) :=
    hEC.trans (hvpHR.trans (H_bounds hptp).1)
  -- `v_m`
  have hvm0 : (0 : ℝ) < (vm : ℝ) := by exact_mod_cast (ptOk_pos hptm).1
  have hvmhR : (vm : ℝ) < 1 / 2 := by
    have h' := (Rat.cast_lt (K := ℝ)).mpr hvmh
    push_cast at h'
    linarith
  have hvmHR : ((Hhi vm : ℚ) : ℝ) ≤ (B.a0 : ℝ) := by exact_mod_cast hvmH
  have hHvm : H (vm : ℝ) ≤ μ.meanEntropy := (H_bounds hptm).2.trans (hvmHR.trans hE0)
  have hlhi : Real.log ((1 - (vm : ℝ)) / (vm : ℝ)) ≤ ((lamHi vm : ℚ) : ℝ) := (lam_bounds hptm).2
  -- `u`, `ℓ₀`
  have hU : ((nU B : ℚ) : ℝ) = ((nCp B : ℚ) : ℝ) / (B.a0 : ℝ) := by
    simp only [nU]; push_cast; ring
  have hCp0R : (0 : ℝ) < ((nCp B : ℚ) : ℝ) := by exact_mod_cast hCp0
  have hu0 : (0 : ℝ) < ((nU B : ℚ) : ℝ) := by rw [hU]; positivity
  have hu : (1 - H ((1 - (1 - μ.a - μ.b)) / 2)) / μ.meanEntropy ≤ ((nU B : ℚ) : ℝ) := by
    rw [hU]
    calc (1 - H ((1 - (1 - μ.a - μ.b)) / 2)) / μ.meanEntropy
        ≤ ((nCp B : ℚ) : ℝ) / μ.meanEntropy := div_le_div_of_nonneg_right hCle hEpos.le
      _ ≤ ((nCp B : ℚ) : ℝ) / (B.a0 : ℝ) := div_le_div_of_nonneg_left hCp0R.le ha0R hE0
  have hZ : ((nZ B : ℚ) : ℝ) = 1 / (1 + ((nU B : ℚ) : ℝ)) := by
    simp only [nZ]; push_cast; ring
  have hlu : ((-(lHi (nZ B)) : ℚ) : ℝ) ≤ Real.log (1 + ((nU B : ℚ) : ℝ)) := by
    have h' := (ptOk_sound hptz).2.1
    rw [hZ, one_div, Real.log_inv] at h'
    push_cast
    linarith
  have hlu0 : (0 : ℝ) ≤ ((-(lHi (nZ B)) : ℚ) : ℝ) := by exact_mod_cast hluc
  -- parent gain (9)
  have hCq := NA.C_ge_half_sq hq0 (by linarith : 1 - μ.a - μ.b ≤ 1)
  have hpar0 := NA.parent_gain_box hEpos hC0 hCq (by linarith : μ.meanEntropy +
      (1 - H ((1 - (1 - μ.a - μ.b)) / 2)) < 1) hvp0.le hvphR hHvp hvm0 hvmhR.le hHvm hlhi hLhi
    hu0 hu hlu hlu0
  have hparQ : ((nPar B vp vm : ℚ) : ℝ) = (B.a0 : ℝ) / (LqHi : ℝ) +
      (1 - 2 * (vp : ℝ)) / ((LqHi : ℝ) * (1 - (vp : ℝ))) * (1 + 1 / ((lamHi vm : ℚ) : ℝ)) /
        (2 * (LqHi : ℝ)) * (((-(lHi (nZ B)) : ℚ) : ℝ) / ((nU B : ℚ) : ℝ)) := by
    simp only [nPar, nBeta]; push_cast; ring
  have hpar : (1 - μ.a - μ.b) ^ 2 / μ.meanEntropy * ((nPar B vp vm : ℚ) : ℝ) ≤
      eta μ.meanEntropy - eta (μ.meanEntropy + (1 - H ((1 - (1 - μ.a - μ.b)) / 2))) := by
    refine le_trans ?_ hpar0
    rw [hparQ]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := div_le_div_of_nonneg_right hE0 hLqHi.le
    linarith
  -- radial loss (8)
  have hrad0 := NA.radialLoss_le hdpos hEpos hq0 hqd
  have hvl0 : (0 : ℝ) < (vl : ℝ) := by exact_mod_cast (ptOk_pos hptl).1
  have hvlhR : (vl : ℝ) < 1 / 2 := by
    have h' := (Rat.cast_lt (K := ℝ)).mpr hvlh
    push_cast at h'
    linarith
  have hvlHR : (B.b0 : ℝ) * ((Hhi vl : ℚ) : ℝ) ≤ 1 - 2 * (vl : ℝ) := by exact_mod_cast hvlH
  have hvlcR : (B.b0 : ℝ) * H (vl : ℝ) ≤ 1 - 2 * (vl : ℝ) :=
    (mul_le_mul_of_nonneg_left (H_bounds hptl).2 hb0R.le).trans hvlHR
  have hslope := NA.radial_ratio_le_slope hb0R hx0 hvl0 hvlhR hvlcR
  obtain ⟨hl1, hl2, hl3, hl4⟩ := ptOk_sound hptl
  have hvl1 : (0 : ℝ) < 1 - (vl : ℝ) := by linarith
  have hhnle : Certificates.Mixed.hn (vl : ℝ) ≤ ((HnumHi vl : ℚ) : ℝ) := by
    unfold Certificates.Mixed.hn
    simp only [HnumHi]
    push_cast
    have a1 := mul_le_mul_of_nonneg_left hl1 hvl0.le
    have a2 := mul_le_mul_of_nonneg_left hl3 hvl1.le
    linarith
  have hklR : (0 : ℝ) < ((nKl vl : ℚ) : ℝ) := by exact_mod_cast hkl0
  have hklle : ((nKl vl : ℚ) : ℝ) ≤ Certificates.Mixed.kap (vl : ℝ) := by
    unfold Certificates.Mixed.kap
    rw [Real.log_mul hvl0.ne' hvl1.ne']
    simp only [nKl]
    push_cast
    linarith
  have hrs := NA.radialSlope_le hvl0 hvlhR (J_bounds hptl).2 hhnle hklR hklle hLqLo hLlo
  have hRsQ : ((nRs vl : ℚ) : ℝ) = ((JhiQ vl : ℚ) : ℝ) + (1 - 2 * (vl : ℝ)) * ((HnumHi vl : ℚ) : ℝ) /
      (2 * (LqLo : ℝ) * (vl : ℝ) * (1 - (vl : ℝ)) * ((nKl vl : ℚ) : ℝ)) := by
    simp only [nRs]; push_cast; ring
  have hWQ : ((nW B vl : ℚ) : ℝ) = ((nRs vl : ℚ) : ℝ) / (2 * (B.b0 : ℝ)) := by
    simp only [nW]; push_cast; ring
  have hW : deriv (fun r => F r 1) ((μ.b - μ.a) / μ.meanEntropy) /
      (2 * ((μ.b - μ.a) / μ.meanEntropy)) ≤ ((nW B vl : ℚ) : ℝ) := by
    refine hslope.trans ?_
    rw [hWQ, hRsQ]
    exact div_le_div_of_nonneg_right hrs (by positivity)
  have hrad : radialLoss (μ.b - μ.a) (1 - μ.a - μ.b) μ.meanEntropy ≤
      (1 - μ.a - μ.b) ^ 2 / μ.meanEntropy * ((nW B vl : ℚ) : ℝ) :=
    hrad0.trans (mul_le_mul_of_nonneg_left hW (by positivity))
  -- the compensation `γ`
  have hSmaxQ : ((nSmax B : ℚ) : ℝ) =
      min (4 / 5 : ℝ) (((B.b1 : ℝ) + (B.c1 : ℝ)) * (B.a1 : ℝ)) := by
    simp only [nSmax]; push_cast; ring
  have hsmax : (μ.b - μ.a) + (1 - μ.a - μ.b) ≤ ((nSmax B : ℚ) : ℝ) := by
    rw [hSmaxQ]
    apply le_min hdq
    nlinarith
  have hGamQ : ((nGam B : ℚ) : ℝ) =
      max (0 : ℝ) (1 / (2 * (LqHi : ℝ)) - 13 / 6 * ((nSmax B : ℚ) : ℝ)) := by
    simp only [nGam]; push_cast; ring
  have hγ : ((nGam B : ℚ) : ℝ) = 0 ∨
      ((nGam B : ℚ) : ℝ) ≤ compensation ((μ.b - μ.a) + (1 - μ.a - μ.b)) := by
    rw [hGamQ]
    rcases le_total (1 / (2 * (LqHi : ℝ)) - 13 / 6 * ((nSmax B : ℚ) : ℝ)) 0 with hn | hp
    · left; exact max_eq_left hn
    · right
      rw [max_eq_right hp]
      unfold compensation
      have h1 : 1 / (2 * (LqHi : ℝ)) ≤ 1 / Real.log 2 := by
        apply one_div_le_one_div_of_le hL
        linarith
      linarith
  -- `c_* ≤ c`
  have hCsQ : ((nCs B : ℚ) : ℝ) = 9 * max (1 / 50 : ℝ) ((B.a0 : ℝ) * (B.b0 : ℝ)) /
      (20 * (LqHi : ℝ)) + ((nGam B : ℚ) : ℝ) / 2 := by
    simp only [nCs]; push_cast; ring
  have hcs0R : (0 : ℝ) < ((nCs B : ℚ) : ℝ) := by exact_mod_cast hcs0
  have hcsc : ((nCs B : ℚ) : ℝ) ≤ 9 * (μ.b - μ.a) / (20 * Real.log 2) + ((nGam B : ℚ) : ℝ) / 2 := by
    rw [hCsQ]
    have hdm : max (1 / 50 : ℝ) ((B.a0 : ℝ) * (B.b0 : ℝ)) ≤ μ.b - μ.a :=
      max_le hd (by linarith)
    have hdm0 : (0 : ℝ) ≤ max (1 / 50 : ℝ) ((B.a0 : ℝ) * (B.b0 : ℝ)) :=
      le_trans (by norm_num) (le_max_left _ _)
    have h1 : 9 * max (1 / 50 : ℝ) ((B.a0 : ℝ) * (B.b0 : ℝ)) / (20 * (LqHi : ℝ)) ≤
        9 * (μ.b - μ.a) / (20 * (LqHi : ℝ)) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h2 : 9 * (μ.b - μ.a) / (20 * (LqHi : ℝ)) ≤ 9 * (μ.b - μ.a) / (20 * Real.log 2) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
    linarith
  have hvalR : 0 ≤ ((nPar B vp vm : ℚ) : ℝ) - ((nW B vl : ℚ) : ℝ) -
      169 * (B.a1 : ℝ) / (144 * ((nCs B : ℚ) : ℝ)) := by
    have h' := (Rat.cast_le (K := ℝ)).mpr hval
    push_cast at h'
    linarith
  -- the entropy split and the retained-child gap bound
  obtain ⟨ht, hce, hcf⟩ := PsiRetainedChildBridge.positive_entropy_split μ.e_pos μ.f_pos
  have hcore := retained_margin_box (t := (μ.e - μ.f) / (μ.e + μ.f)) hq0 hqd hdq hEpos hE11 hE1 ht
    hγ hpar hrad hcs0R hcsc hvalR
  have hmean : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  have hc := PsiRetainedChildBridge.canonical_hybrid_gap_le_childAverage
    (d := μ.b - μ.a) (q := 1 - μ.a - μ.b) (E := μ.meanEntropy)
    (t := (μ.e - μ.f) / (μ.e + μ.f)) hq0 hqd (by rw [hmean]; exact hact.le)
  have hca : (1 - (μ.b - μ.a) - (1 - μ.a - μ.b)) / 2 = μ.a := by ring
  have hcb : (1 + (μ.b - μ.a) - (1 - μ.a - μ.b)) / 2 = μ.b := by ring
  change μ.meanEntropy * (1 + (μ.e - μ.f) / (μ.e + μ.f)) = μ.e at hce
  change μ.meanEntropy * (1 - (μ.e - μ.f) / (μ.e + μ.f)) = μ.f at hcf
  rw [hca, hcb, hce, hcf] at hc
  change μ.gap ≤ _ at hc
  have hcost := Gain.law_endpoint_gain_four μ h4
  linarith

end CKLaneN1c

end


