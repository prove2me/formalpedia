-- Prove2me | Definitions.Def_CK_CKLaneN1b_Analytic
-- name    : CK_CKLaneN1b_Analytic
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:49:16.590369+00:00
-- url     : https://prove2.me/theorems/0e8a0793-c4b3-49d7-868d-b7b7a236c15a
-- title:
--   Courtade–Kumar proof module `CKLaneN1b.Analytic` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1b.Analytic` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1b.Analytic` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1b.Analytic (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1b/Analytic.lean)

import Definitions.Def_CK_CKLaneD_Checker
import Definitions.Def_CK_CKLaneE_FastPoint
import Definitions.Def_CK_CKLaneE_SlopeBounds
import Definitions.Def_CK_CKLaneM09_CapCore
import Definitions.Def_CK_GeneralCK_ScalarGap
import Definitions.Def_CK_GeneralCK_EntropyComparison

-- ===== source module CKLaneN1b.Analytic =====
section

/-!
# Lane N1b: analytic core for the opposite moderate-entropy cover

All statements are unconditional real-analysis facts derived from corpus theorems:

* `H_le_tangent`: tangent lines of the concave binary entropy.
* `P_tangent_lower`: tangent lines (right slope `P1`) of the convex profile `P`.
* `anchor_le_P1`: exact profile slope at an anchor `1 - H w`, monotone above it.
* `P_incr_mono`: increments of the convex `P` grow with the base point.
* `gap_nonneg_of_ends`: concavity of the scalar gap in the entropy deficit
  (`GeneralCK.Scalar.gap_concaveOn`): two endpoints control an interval.
* `contact_plane_cost`: the manuscript's global supporting plane at an arbitrary contact
  `(x, y)` with the explicit coefficients `CKLaneM09.capA/capB`, averaged over a law.
* `plane_gap_bound`: any plane `λ d - A e - B f ≤ cost` with `A, B ≥ 0` controls the psi
  candidate through the split-free scalar gap (entropy split eliminated by `min A B`).
* `jensenGap_le_corner`: the Jensen gap of `H` is maximal at the outer corner of a mean box.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneN1b

open GeneralCK GeneralCK.Scalar GeneralCK.PsiEndpointPlane Set

/-! ## Tangent lines -/

/-- Tangent line of the concave binary entropy. -/
theorem H_le_tangent {x y : ℝ} (hx : 0 < x) (hx1 : x < 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    H y ≤ H x + J x * (y - x) := by
  have hd := Comparison.hasDerivAt_H hx hx1
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hs := CKLaneD.H_concaveOn.slope_le_of_hasDerivAt ⟨hx.le, hx1.le⟩ ⟨hy, hy1⟩ hxy hd
    rw [slope_def_field] at hs
    have h := (div_le_iff₀ (sub_pos.mpr hxy)).mp hs
    linarith
  · simp
  · have hs := CKLaneD.H_concaveOn.le_slope_of_hasDerivAt ⟨hy, hy1⟩ ⟨hx.le, hx1.le⟩ hyx hd
    rw [slope_def_field] at hs
    have h := (le_div_iff₀ (sub_pos.mpr hyx)).mp hs
    linarith

/-- Tangent line of the convex profile `P` at a left point, with the right slope `P1`. -/
theorem P_tangent_lower {sL s : ℝ} (h0 : 0 ≤ sL) (hs : sL ≤ s) (h1 : s < 1) :
    P sL + P1 sL * (s - sL) ≤ P s := by
  rcases eq_or_lt_of_le hs with heq | hlt
  · rw [heq]; simp
  rcases eq_or_lt_of_le h0 with h00 | hpos
  · rw [← h00, P1_zero, P_zero]
    have := four_mul_le_P (by linarith : (0 : ℝ) ≤ s) h1
    linarith
  · have hd := CKLaneE.hasDerivAt_P_P1 hpos (by linarith)
    have hsl := P_convexOn.le_slope_of_hasDerivAt ⟨h0, by linarith⟩ ⟨by linarith, h1⟩ hlt hd
    rw [slope_def_field] at hsl
    have h := (le_div_iff₀ (sub_pos.mpr hlt)).mp hsl
    linarith

/-- Lower bound for the profile slope: the exact value at the anchor `1 - H w`, monotone
above it. -/
theorem anchor_le_P1 {w y : ℝ} (hw : 0 < w) (hw' : w < 1 / 2) (hy : 1 - H w ≤ y) (hy1 : y < 1) :
    2 + (1 - 2 * w) / (w * (1 - w) * Real.log ((1 - w) / w)) ≤ P1 y := by
  have hH0 : 0 < H w := H_pos hw (by linarith)
  have hH1 : H w < 1 := CKLaneE.H_lt_one_of_lt_half hw.le hw'
  have hy0 : 0 < 1 - H w := by linarith
  have hy01 : 1 - H w < 1 := by linarith
  have hmono := CKLaneE.P1_monotoneOn ⟨hy0.le, hy01⟩ ⟨hy0.le.trans hy, hy1⟩ hy
  rw [P1_eq_deriv hy0, deriv_P hy0 hy01] at hmono
  have hinv : entropyInverse (1 - (1 - H w)) = w := by
    rw [sub_sub_cancel]
    exact entropyInverse_H_lower hw.le hw'.le
  rw [hinv] at hmono
  have hJ : Real.log 2 * w * (1 - w) * J w = w * (1 - w) * Real.log ((1 - w) / w) := by
    unfold J
    field_simp [log_two_pos.ne']
  rw [hJ] at hmono
  exact hmono

/-! ## The convex profile: monotone increments -/

theorem P_incr_mono {Δ Δ' S : ℝ} (h0 : 0 ≤ Δ) (hΔ : Δ ≤ Δ') (hS : 0 ≤ S) (h1 : Δ' + S < 1) :
    P (Δ + S) - P Δ ≤ P (Δ' + S) - P Δ' := by
  rcases eq_or_lt_of_le hS with hS0 | hSpos
  · rw [← hS0]; simp
  rcases eq_or_lt_of_le hΔ with hΔe | hΔlt
  · rw [hΔe]
  have hmem : ∀ t, 0 ≤ t → t < 1 → t ∈ Ico (0 : ℝ) 1 := fun t ht ht' => ⟨ht, ht'⟩
  have m1 := hmem Δ h0 (by linarith)
  have m2 := hmem (Δ + S) (by linarith) (by linarith)
  have m3 := hmem Δ' (by linarith) (by linarith)
  have m4 := hmem (Δ' + S) (by linarith) h1
  -- slope (Δ, Δ+S) ≤ slope (Δ, Δ'+S) ≤ slope (Δ', Δ'+S)
  have s1 := P_convexOn.secant_mono m1 m2 m4 (by linarith) (by linarith) (by linarith)
  have s2 := P_convexOn.secant_mono m4 m1 m3 (by linarith) (by linarith) hΔlt.le
  have e1 : (Δ + S) - Δ = S := by ring
  have e2 : (Δ' + S) - Δ' = S := by ring
  rw [e1] at s1
  have hA : (P (Δ' + S) - P Δ) / (Δ' + S - Δ) = (P Δ - P (Δ' + S)) / (Δ - (Δ' + S)) := by
    rw [← neg_div_neg_eq]; ring_nf
  have hB : (P (Δ' + S) - P Δ') / S = (P Δ' - P (Δ' + S)) / (Δ' - (Δ' + S)) := by
    rw [← neg_div_neg_eq]; ring_nf
  have key : (P (Δ + S) - P Δ) / S ≤ (P (Δ' + S) - P Δ') / S := by
    rw [hB]; rw [hA] at s1; exact s1.trans s2
  exact (div_le_div_iff_of_pos_right hSpos).mp key

/-! ## Concavity of the scalar gap in the entropy deficit -/

theorem gap_nonneg_of_ends {j α Δ s0 s1 s : ℝ} (hΔ : 0 ≤ Δ) (hs0 : 0 ≤ s0) (hs01 : s0 ≤ s1)
    (hcap : Δ + s1 < 1) (hs : s0 ≤ s) (hs' : s ≤ s1)
    (h0 : 0 ≤ gap j α Δ s0) (h1 : 0 ≤ gap j α Δ s1) : 0 ≤ gap j α Δ s := by
  have hc := gap_concaveOn j α hΔ (hs0.trans hs01) hcap
  have hm := hc.min_le_of_mem_Icc ⟨hs0, hs01⟩ ⟨hs0.trans hs01, le_rfl⟩ ⟨hs, hs'⟩
  exact (le_min h0 h1).trans hm

/-! ## Global contact planes -/

/-- The manuscript's global supporting plane at an arbitrary ordered contact `(x, y)` with the
explicit coefficients of the two contact equations, averaged over a finite interior law. -/
theorem contact_plane_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) {x y : ℝ}
    (hx : 0 < x) (hxy : x < y) (hy : y < 1) (hdet : CKLaneM09.capDet x y ≠ 0)
    (hA : 0 < CKLaneM09.capA x y) (hB : 0 < CKLaneM09.capB x y) :
    (interiorCost x y + CKLaneM09.capA x y * H x + CKLaneM09.capB x y * H y) / (y - x) *
        (μ.b - μ.a) - CKLaneM09.capA x y * μ.e - CKLaneM09.capB x y * μ.f ≤ μ.cost := by
  obtain ⟨h1, h0⟩ := CKLaneM09.cap_contact hx hxy hy hdet
  have hplane := supporting_plane_of_contact hA hB ⟨hx, hxy, hy⟩ h1 h0
  have havg := averaged_supporting_plane μ hplane
  set A := CKLaneM09.capA x y with hAdef
  set B := CKLaneM09.capB x y with hBdef
  have hq : quotient A B x y =
      Real.log 2 * ((interiorCost x y + A * H x + B * H y) / (y - x)) := by
    unfold quotient naturalCost
    rw [binEntropy_eq_log_two_mul_H, binEntropy_eq_log_two_mul_H]
    ring
  rw [hq] at havg
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have key : Real.log 2 * ((interiorCost x y + A * H x + B * H y) / (y - x) * (μ.b - μ.a) -
      A * μ.e - B * μ.f) ≤ Real.log 2 * μ.cost := by
    have e1 : Real.log 2 * ((interiorCost x y + A * H x + B * H y) / (y - x) * (μ.b - μ.a) -
        A * μ.e - B * μ.f) =
        Real.log 2 * ((interiorCost x y + A * H x + B * H y) / (y - x)) * (μ.b - μ.a) -
          (A * (Real.log 2 * μ.e) + B * (Real.log 2 * μ.f)) := by ring
    rw [e1]
    linarith
  exact le_of_mul_le_mul_left key hl2

/-- A plane `λ d - A e - B f ≤ cost` controls the psi candidate through the split-free scalar
gap; the entropy split is eliminated with the smaller coefficient. -/
theorem plane_gap_bound {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) {lam A B : ℝ}
    (hplane : lam * (μ.b - μ.a) - A * μ.e - B * μ.f ≤ μ.cost)
    (hgap : 0 ≤ gap (lam * (μ.b - μ.a) - A * H μ.a - B * H μ.b) (2 * min A B)
      (H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2) ((H μ.a + H μ.b) / 2 - μ.meanEntropy)) :
    candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.cost := by
  have hjen := CKLaneD.law_gap_le_P μ
  have he := μ.e_le_cap
  have hf := μ.f_le_cap
  have hE : μ.meanEntropy = (μ.e + μ.f) / 2 := rfl
  have hI : H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 + ((H μ.a + H μ.b) / 2 - μ.meanEntropy) =
      H ((μ.a + μ.b) / 2) - μ.meanEntropy := by ring
  unfold gap at hgap
  rw [hI] at hgap
  have hmA : min A B ≤ A := min_le_left _ _
  have hmB : min A B ≤ B := min_le_right _ _
  have t1 : min A B * (H μ.a - μ.e) ≤ A * (H μ.a - μ.e) :=
    mul_le_mul_of_nonneg_right hmA (by linarith)
  have t2 : min A B * (H μ.b - μ.f) ≤ B * (H μ.b - μ.f) :=
    mul_le_mul_of_nonneg_right hmB (by linarith)
  have hs2 : 2 * min A B * ((H μ.a + H μ.b) / 2 - μ.meanEntropy) =
      min A B * (H μ.a - μ.e) + min A B * (H μ.b - μ.f) := by rw [hE]; ring
  have hcost : lam * (μ.b - μ.a) - A * H μ.a - B * H μ.b +
      2 * min A B * ((H μ.a + H μ.b) / 2 - μ.meanEntropy) ≤ μ.cost := by
    rw [hs2]; linarith
  linarith

/-! ## The Jensen gap of `H` on a mean box -/

theorem J_antitoneOn {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v < 1) : J v ≤ J u := by
  unfold J
  rw [Real.log_div (by linarith) (by linarith), Real.log_div (by linarith) hu.ne']
  have h1 : Real.log (1 - v) ≤ Real.log (1 - u) := Real.log_le_log (by linarith) (by linarith)
  have h2 : Real.log u ≤ Real.log v := Real.log_le_log hu huv
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  apply div_le_div_of_nonneg_right _ hl2.le
  linarith

/-- Derivative of the Jensen gap in the left mean. -/
theorem hasDerivAt_jensenGap_left {b t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hm0 : 0 < (t + b) / 2)
    (hm1 : (t + b) / 2 < 1) :
    HasDerivAt (fun s : ℝ => H ((s + b) / 2) - (H s + H b) / 2)
      (J ((t + b) / 2) / 2 - J t / 2) t := by
  have hH := Comparison.hasDerivAt_H hm0 hm1
  have hc : HasDerivAt (fun s : ℝ => (s + b) / 2) (1 / 2) t := by
    have := ((hasDerivAt_id t).add_const b).div_const 2
    simpa using this
  have hcomp := hH.comp t hc
  have hHt := Comparison.hasDerivAt_H ht0 ht1
  have hall := hcomp.sub ((hHt.add_const (H b)).div_const 2)
  exact hall.congr_deriv (by ring)

/-- Derivative of the Jensen gap in the right mean. -/
theorem hasDerivAt_jensenGap_right {a t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hm0 : 0 < (a + t) / 2)
    (hm1 : (a + t) / 2 < 1) :
    HasDerivAt (fun s : ℝ => H ((a + s) / 2) - (H a + H s) / 2)
      (J ((a + t) / 2) / 2 - J t / 2) t := by
  have hH := Comparison.hasDerivAt_H hm0 hm1
  have hc : HasDerivAt (fun s : ℝ => (a + s) / 2) (1 / 2) t := by
    have := ((hasDerivAt_id t).const_add a).div_const 2
    simpa using this
  have hcomp := hH.comp t hc
  have hHt := Comparison.hasDerivAt_H ht0 ht1
  have hall := hcomp.sub ((hHt.const_add (H a)).div_const 2)
  exact hall.congr_deriv (by ring)

theorem jensenGap_anti_left {a0 a b : ℝ} (ha0 : 0 < a0) (h1 : a0 ≤ a) (h2 : a ≤ b) (hb : b < 1) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤ H ((a0 + b) / 2) - (H a0 + H b) / 2 := by
  have hD : ∀ t ∈ Icc a0 b, HasDerivAt (fun s : ℝ => H ((s + b) / 2) - (H s + H b) / 2)
      (J ((t + b) / 2) / 2 - J t / 2) t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha0 ht.1
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hb
    exact hasDerivAt_jensenGap_left ht0 ht1 (by linarith [ht.2]) (by linarith [ht.2])
  have hanti : AntitoneOn (fun s : ℝ => H ((s + b) / 2) - (H s + H b) / 2) (Icc a0 b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a0 b)
      (fun t ht => (hD t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hD t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    have ht0 : 0 < t := lt_trans ha0 ht.1
    have hJ := J_antitoneOn ht0 (by linarith [ht.2] : t ≤ (t + b) / 2) (by linarith [ht.2])
    linarith
  exact hanti ⟨le_rfl, h1.trans h2⟩ ⟨h1, h2⟩ h1

theorem jensenGap_mono_right {a b b1 : ℝ} (ha : 0 < a) (h2 : a ≤ b) (h3 : b ≤ b1) (hb1 : b1 < 1) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤ H ((a + b1) / 2) - (H a + H b1) / 2 := by
  have hD : ∀ t ∈ Icc a b1, HasDerivAt (fun s : ℝ => H ((a + s) / 2) - (H a + H s) / 2)
      (J ((a + t) / 2) / 2 - J t / 2) t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hb1
    exact hasDerivAt_jensenGap_right ht0 ht1 (by linarith [ht.1]) (by linarith [ht.2])
  have hmono : MonotoneOn (fun s : ℝ => H ((a + s) / 2) - (H a + H s) / 2) (Icc a b1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b1)
      (fun t ht => (hD t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hD t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    have hm0 : 0 < (a + t) / 2 := by linarith [ht.1]
    have hJ := J_antitoneOn hm0 (by linarith [ht.1] : (a + t) / 2 ≤ t) (by linarith [ht.2])
    linarith
  exact hmono ⟨h2, h3⟩ ⟨h2.trans h3, le_rfl⟩ h3

/-- The Jensen gap `H(m) - (H a + H b)/2` is at most its value at the outer corner. -/
theorem jensenGap_le_corner {a0 a b b1 : ℝ} (ha0 : 0 < a0) (h1 : a0 ≤ a) (h2 : a ≤ b)
    (h3 : b ≤ b1) (hb1 : b1 < 1) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤ H ((a0 + b1) / 2) - (H a0 + H b1) / 2 :=
  (jensenGap_anti_left ha0 h1 h2 (lt_of_le_of_lt h3 hb1)).trans
    (jensenGap_mono_right ha0 (h1.trans h2) h3 hb1)

/-- The Jensen gap of `H` is nonnegative (concavity). -/
theorem jensenGap_nonneg {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ H ((a + b) / 2) - (H a + H b) / 2 := by
  have h := CKLaneD.H_concaveOn.2 ⟨ha, ha1⟩ ⟨hb, hb1⟩ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h
  have e : 1 / 2 * a + 1 / 2 * b = (a + b) / 2 := by ring
  rw [e] at h
  linarith

end CKLaneN1b

end


