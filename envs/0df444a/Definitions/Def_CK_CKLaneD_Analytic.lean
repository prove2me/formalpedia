-- Prove2me | Definitions.Def_CK_CKLaneD_Analytic
-- name    : CK_CKLaneD_Analytic
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:00:54.422715+00:00
-- url     : https://prove2.me/theorems/2703daad-ee1e-4af3-a3bd-328373550618
-- title:
--   Courtade–Kumar proof module `CKLaneD.Analytic` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneD.Analytic` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneD.Analytic` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneD.Analytic (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneD/Analytic.lean)

import Definitions.Def_CK_CKLaneD_PointBounds
import Definitions.Def_CK_GeneralCK_BellmanAssembly
import Definitions.Def_CK_GeneralCK_PsiEndpointPlaneSymmetric
import Definitions.Def_CK_GeneralCK_ProfileLowerBounds

-- ===== source module CKLaneD.Analytic =====
section

/-!
# Lane D: analytic lemmas for the endpoint relaxation checker

* Jensen split bound in explicit form,
* explicit symmetric supporting plane at a contact `v` (closed-form coefficient),
* concavity / monotonicity bounds for `H`,
* bracket bounds and convex chord for the scalar profile `P`.
-/

namespace CKLaneD

open GeneralCK GeneralCK.PsiEndpointPlane Set

/-! ## Jensen split bound -/

theorem law_gap_le_P {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) :
    candidateGap psi μ.a μ.b μ.e μ.f ≤
      Scalar.P (H ((μ.a + μ.b) / 2) - μ.meanEntropy) -
        Scalar.P ((H μ.a + H μ.b) / 2 - μ.meanEntropy) := by
  have h := μ.psi_gap_le_splitBound
  unfold InteriorLaw.splitBound at h
  have h1 : μ.entropyDrop + μ.meanDeficit = H ((μ.a + μ.b) / 2) - μ.meanEntropy := by
    unfold InteriorLaw.entropyDrop InteriorLaw.meanDeficit InteriorLaw.meanEntropy
      InteriorLaw.midpoint
    ring
  have h2 : μ.meanDeficit = (H μ.a + H μ.b) / 2 - μ.meanEntropy := by
    unfold InteriorLaw.meanDeficit InteriorLaw.meanEntropy
    ring
  rw [h1, h2] at h
  exact h

theorem law_meanEntropy_pos {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) :
    0 < μ.meanEntropy := by
  unfold InteriorLaw.meanEntropy
  linarith [μ.e_pos, μ.f_pos]

theorem law_deficit_mem {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) :
    0 ≤ (H μ.a + H μ.b) / 2 - μ.meanEntropy ∧ (H μ.a + H μ.b) / 2 - μ.meanEntropy < 1 := by
  have h := μ.meanDeficit_mem
  have h2 : μ.meanDeficit = (H μ.a + H μ.b) / 2 - μ.meanEntropy := by
    unfold InteriorLaw.meanDeficit InteriorLaw.meanEntropy
    ring
  rw [h2] at h
  exact ⟨h.1, h.2⟩

/-! ## Explicit symmetric supporting plane -/

/-- Closed-form symmetric plane coefficient at contact `v`. -/
noncomputable def planeK (v : ℝ) : ℝ :=
  (1 - 2 * v) ^ 2 / (2 * v * (1 - v) * (-Real.log (v * (1 - v))))

theorem planeK_pos {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) : 0 < planeK v := by
  have h1 : 0 < v * (1 - v) := mul_pos hv (by linarith)
  have h2 : v * (1 - v) < 1 := by nlinarith
  have hl : Real.log (v * (1 - v)) < 0 := Real.log_neg h1 h2
  unfold planeK
  apply div_pos
  · have : 0 < 1 - 2 * v := by linarith
    positivity
  · have : 0 < 1 - v := by linarith
    have : 0 < -Real.log (v * (1 - v)) := by linarith
    positivity

theorem plane_cost_lower {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) {v : ℝ}
    (hv : 0 < v) (hv' : v < 1 / 2) :
    (J v + 2 * planeK v * H v / (1 - 2 * v)) * (μ.b - μ.a) - 2 * planeK v * μ.meanEntropy ≤
      μ.cost := by
  have hK := planeK_pos hv hv'
  have hv1 : 0 < 1 - v := by linarith
  have hr : 0 < 1 - 2 * v := by linarith
  have hlogm : Real.log (v * (1 - v)) = Real.log v + Real.log (1 - v) :=
    Real.log_mul hv.ne' hv1.ne'
  have h1v : (0 : ℝ) < v * (1 - v) := mul_pos hv hv1
  have h2v : v * (1 - v) < 1 := by nlinarith
  have hl : Real.log (v * (1 - v)) < 0 := Real.log_neg h1v h2v
  have hlne : Real.log v + Real.log (1 - v) ≠ 0 := by rw [← hlogm]; exact hl.ne
  have hxy : (v, 1 - v) ∈ triangle := ⟨hv, by linarith, by linarith⟩
  have hc1 : contactLevel1 (planeK v) (planeK v) v (1 - v) = 0 := by
    unfold contactLevel1 planeK
    rw [hlogm]
    field_simp
    ring
  have hc0 : contactLevel0 (planeK v) (planeK v) v (1 - v) = 0 := by
    unfold contactLevel0 planeK
    rw [hlogm, show (1 : ℝ) - (1 - v) = v by ring]
    field_simp
    ring
  have hplane := supporting_plane_of_contact hK hK hxy hc1 hc0
  have havg := averaged_supporting_plane μ hplane
  have hq : quotient (planeK v) (planeK v) v (1 - v) =
      Real.log 2 * (J v + 2 * planeK v * H v / (1 - 2 * v)) := by
    unfold quotient naturalCost interiorCost
    rw [binEntropy_eq_log_two_mul_H, binEntropy_eq_log_two_mul_H, H_complement, J_complement]
    have hne1 : (1 : ℝ) - v - v ≠ 0 := (by linarith : (0 : ℝ) < 1 - v - v).ne'
    have hne2 : (1 : ℝ) - 2 * v ≠ 0 := hr.ne'
    have hne3 : (1 : ℝ) - v * 2 ≠ 0 := by intro h; apply hne2; linarith
    rw [div_eq_iff hne1]
    field_simp
    ring
  rw [hq] at havg
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hE : μ.meanEntropy = (μ.e + μ.f) / 2 := rfl
  rw [hE]
  have key : Real.log 2 * ((J v + 2 * planeK v * H v / (1 - 2 * v)) * (μ.b - μ.a) -
      2 * planeK v * ((μ.e + μ.f) / 2)) ≤ Real.log 2 * μ.cost := by
    nlinarith [havg]
  exact le_of_mul_le_mul_left key hl2

/-! ## Binary entropy: monotonicity and concavity bounds -/

theorem H_mono_left {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1 / 2) : H x ≤ H y :=
  H_strictMonoOn.monotoneOn ⟨hx, hxy.trans hy⟩ ⟨hx.trans hxy, hy⟩ hxy

theorem H_anti_right {x y : ℝ} (hx : 1 / 2 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) : H y ≤ H x := by
  rw [← H_complement x, ← H_complement y]
  exact H_mono_left (by linarith) (by linarith) (by linarith)

theorem H_concaveOn : ConcaveOn ℝ (Icc 0 1) H := by
  have h := Real.strictConcave_binEntropy.concaveOn
  have hl2 : (0 : ℝ) ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr (Real.log_pos (by norm_num)).le
  have h2 := h.smul hl2
  refine ⟨h2.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have := h2.2 hx hy ha hb hab
  simp only [smul_eq_mul] at this
  simp only [H, smul_eq_mul, div_eq_inv_mul]
  linarith

/-- Chord lower bound of the concave `H`, with rational lower bounds at the endpoints. -/
theorem H_chord_lower {lo hi x HL0 HL1 : ℝ} (hlo : 0 ≤ lo) (hlx : lo ≤ x) (hxh : x ≤ hi)
    (hhi : hi ≤ 1) (h0 : HL0 ≤ H lo) (h1 : HL1 ≤ H hi) :
    HL0 + (HL1 - HL0) / (hi - lo) * (x - lo) ≤ H x := by
  rcases eq_or_lt_of_le (hlx.trans hxh) with heq | hlt
  · have hx : x = lo := le_antisymm (heq ▸ hxh) hlx
    subst hx
    simp
    exact h0
  · have hd : 0 < hi - lo := by linarith
    set t := (x - lo) / (hi - lo) with ht
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hd.le
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hd]; linarith
    have hmem0 : lo ∈ Icc (0 : ℝ) 1 := ⟨hlo, by linarith⟩
    have hmem1 : hi ∈ Icc (0 : ℝ) 1 := ⟨by linarith, hhi⟩
    have hconc := H_concaveOn.2 hmem0 hmem1 (by linarith : (0 : ℝ) ≤ 1 - t) ht0 (by ring)
    simp only [smul_eq_mul] at hconc
    have hxe : (1 - t) * lo + t * hi = x := by
      rw [ht]; field_simp; ring
    rw [hxe] at hconc
    have hkey : HL0 + (HL1 - HL0) / (hi - lo) * (x - lo) = (1 - t) * HL0 + t * HL1 := by
      rw [ht]; field_simp; ring
    rw [hkey]
    have e1 : (1 - t) * HL0 ≤ (1 - t) * H lo := mul_le_mul_of_nonneg_left h0 (by linarith)
    have e2 : t * HL1 ≤ t * H hi := mul_le_mul_of_nonneg_left h1 ht0
    linarith

/-- Left-chord slope upper bound of the concave `H` to the right of `lo`. -/
theorem H_leftslope_upper {lo h x HU0 HLh : ℝ} (hh : 0 < h) (hlh : 0 ≤ lo - h)
    (hlx : lo ≤ x) (hx1 : x ≤ 1) (hU : H lo ≤ HU0) (hL : HLh ≤ H (lo - h)) :
    H x ≤ HU0 + (HU0 - HLh) / h * (x - lo) := by
  have hslope : (H lo - H (lo - h)) / h ≤ (HU0 - HLh) / h :=
    div_le_div_of_nonneg_right (by linarith) hh.le
  rcases eq_or_lt_of_le hlx with heq | hlt
  · subst heq; simp; exact hU
  · have hs := H_concaveOn.slope_anti_adjacent (x := lo - h) (y := lo) (z := x)
      ⟨hlh, by linarith⟩ ⟨by linarith, hx1⟩ (by linarith) hlt
    have hd : 0 < x - lo := by linarith
    rw [show lo - (lo - h) = h by ring] at hs
    have h3 : (H x - H lo) / (x - lo) ≤ (HU0 - HLh) / h := hs.trans hslope
    rw [div_le_iff₀ hd] at h3
    nlinarith [mul_le_mul_of_nonneg_right hslope hd.le]

/-! ## The scalar profile `P` -/

theorem P_le_bracket {p xa : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) (hxa : 0 < xa) (hxa' : xa ≤ 1 / 2)
    (hH : H xa ≤ 1 - p) : Scalar.P p ≤ (1 - 2 * xa) * J xa := by
  have h0 : 0 ≤ 1 - p := by linarith
  have h1 : 1 - p ≤ 1 := by linarith
  have hpos : 0 < 1 - p := by linarith
  unfold Scalar.P
  rw [eta_eq_profile h0 h1]
  obtain ⟨hx0, hx1, hHx⟩ := entropyInverse_spec h0 h1
  have hxpos := entropyInverse_pos hpos h1
  set x := entropyInverse (1 - p)
  have hxax : xa ≤ x := by
    by_contra hn
    have hlt : x < xa := lt_of_not_ge hn
    have := H_strictMonoOn ⟨hx0, hx1⟩ ⟨hxa.le, hxa'⟩ hlt
    linarith
  have hJ := J_antitone hxa hx1 hxax
  have hJ0 := J_nonneg hxpos hx1
  exact mul_le_mul (by linarith) hJ hJ0 (by linarith)

theorem P_ge_bracket {p xc : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) (hxc : 0 < xc) (hxc' : xc ≤ 1 / 2)
    (hH : 1 - p ≤ H xc) : (1 - 2 * xc) * J xc ≤ Scalar.P p := by
  have h0 : 0 ≤ 1 - p := by linarith
  have h1 : 1 - p ≤ 1 := by linarith
  have hpos : 0 < 1 - p := by linarith
  unfold Scalar.P
  rw [eta_eq_profile h0 h1]
  obtain ⟨hx0, hx1, hHx⟩ := entropyInverse_spec h0 h1
  have hxpos := entropyInverse_pos hpos h1
  set x := entropyInverse (1 - p)
  have hxxc : x ≤ xc := by
    by_contra hn
    have hlt : xc < x := lt_of_not_ge hn
    have := H_strictMonoOn ⟨hxc.le, hxc'⟩ ⟨hx0, hx1⟩ hlt
    linarith
  have hJ := J_antitone hxpos hxc' hxxc
  have hJ0 := J_nonneg hxc hxc'
  exact mul_le_mul (by linarith) hJ hJ0 (by linarith)

theorem P_chord {pLo pHi I : ℝ} (h0 : 0 ≤ pLo) (hlo : pLo ≤ I) (hhi : I ≤ pHi) (h1 : pHi < 1)
    (hlt : pLo < pHi) :
    Scalar.P I ≤ Scalar.P pLo + (Scalar.P pHi - Scalar.P pLo) / (pHi - pLo) * (I - pLo) := by
  have hd : 0 < pHi - pLo := by linarith
  set t := (I - pLo) / (pHi - pLo) with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hd.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hd]; linarith
  have hmem0 : pLo ∈ Ico (0 : ℝ) 1 := ⟨h0, by linarith⟩
  have hmem1 : pHi ∈ Ico (0 : ℝ) 1 := ⟨by linarith, h1⟩
  have hconv := Scalar.P_convexOn.2 hmem0 hmem1 (by linarith : (0 : ℝ) ≤ 1 - t) ht0 (by ring)
  simp only [smul_eq_mul] at hconv
  have hxe : (1 - t) * pLo + t * pHi = I := by
    rw [ht]; field_simp; ring
  rw [hxe] at hconv
  have hkey : Scalar.P pLo + (Scalar.P pHi - Scalar.P pLo) / (pHi - pLo) * (I - pLo) =
      (1 - t) * Scalar.P pLo + t * Scalar.P pHi := by
    rw [ht]; field_simp; ring
  rw [hkey]
  exact hconv

theorem P_nonneg {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) : 0 ≤ Scalar.P s := by
  have := Scalar.four_mul_le_P h0 h1
  linarith

end CKLaneD

end


