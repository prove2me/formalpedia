-- Prove2me | Definitions.Def_CK_CKLaneN4_EightCentral
-- name    : CK_CKLaneN4_EightCentral
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T01:39:20.190689+00:00
-- url     : https://prove2.me/theorems/c6f2eda8-839c-477a-b4f5-081ed362c6d6
-- title:
--   Courtade–Kumar proof module `CKLaneN4.EightCentral` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.EightCentral` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.EightCentral` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.EightCentral (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/EightCentral.lean)

import Definitions.Def_CK_CKLaneN4_EightCentralTree
import Definitions.Def_CK_CKLaneN4_RadialSharp
import Definitions.Def_CK_CKLaneN4_CentralSubrows
import Definitions.Def_CK_GeneralCK_PhiEntropyConvexity

-- ===== source module CKLaneN4.EightCentral =====
section

/-!
# Lane N4: the CENTRAL eight-ratio theorem, literal archive route (CK_OPPOSITE_EXTENSION
`analytic/EIGHT_RATIO_PROOF.md`)

Theorem: `a, b ∈ [1/10, 9/10]`, positive feasible entropies, `0 < E ≤ 11/200`, `q ≤ 8E`, `d ≥ 8E`
⇒ `ζ ≥ R_B`; in the psi-parent branch `B_end - R_B ≥ (2249/144000) q²/E` (`centralEight_margin`).

Proof exactly as archived:
* §1 endpoint (1): `B_end ≥ F(d,E) + (d/(2L))[-ln(1-τ²)]` (`PsiEndpointPlane.law_endpoint_logarithmic_lower`);
  supporting lines of the feasibly convex `Φ(z, ·)` at the common entropy `E`
  (`radialPhi_entropy_convexOn`; `E` is feasible at both children since `H(a), H(b) ≥ H(1/10) > E`);
  `0 ≤ Φ_h(d+q,E) - Φ_h(d-q,E) ≤ 13q/(3E)` (`child_slope_bounds`); with `-ln(1-τ²) ≥ τ²` the worst split
  loss is `169 L q²/(72 d) ≤ (1183/5760) q²/E` (`central_split_lower`, exact minimum of a quadratic);
* §2 radial loss `≤ (479/1000) q²/E` (`radial_average_loss_le_479`, f'(8)/16 < 479/1000);
* §3 parent correction (4) `≥ (7/10) q²/E` on `q + 8E ≤ 4/5` (`parent_gain_central`: archived 50-leaf
  `EIGHT_RATIO` cover + tail `E ≤ 10^-4`);
* §4 margin `7/10 - 479/1000 - 1183/5760 = 2249/144000`.

`sr_eightRatio_central : SR_EightRatio` is the second (literal-route) proof of the N1 sub-row.
-/

namespace CKLaneN4

open GeneralCK CKLaneD PsiChildEntropyCoupling PsiSignedSplit Set

/-- Central parent correction (4): `E[eta(E) - eta(E + C(q))]/q² ≥ 7/10` for `0 < E ≤ 11/200`,
`0 ≤ q ≤ 8E`, `q + 8E ≤ 4/5` (archived 50-leaf cover and the analytic tail `E ≤ 10^-4`). -/
theorem parent_gain_central {E q : ℝ} (hE : 0 < E) (hEi : E ≤ 11 / 200) (hq : 0 ≤ q)
    (hqE : q ≤ 8 * E) (h48 : q + 8 * E ≤ 4 / 5) :
    (7 / 10) * (q ^ 2 / E) ≤ eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  by_cases ht : E ≤ 1 / 10000
  · exact parent_gain_tail hE ht hq hqE
  · have h := EightCentralTree.sem_root
    simp only [SemEYc, EightCentralTree.root] at h
    exact h E q (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) hq h48

/-- Tangent line of a convex function at a point of differentiability. -/
theorem convex_tangent_lower {f : ℝ → ℝ} {S : Set ℝ} {x y : ℝ} (hconv : ConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hd : DifferentiableAt ℝ f x) :
    f x + deriv f x * (y - x) ≤ f y := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · have h := hconv.deriv_le_slope hx hy hxy hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h
    linarith
  · simp
  · have h := hconv.slope_le_deriv hy hx hxy hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h
    linarith

theorem radialPhi_differentiableAt' {z h : ℝ} (hz : 0 ≤ z) (hh : 0 < h) (hh1 : h < 1) :
    DifferentiableAt ℝ (radialPhi z) h := by
  rcases hz.eq_or_lt with he | hp
  · rw [← he, EntropyCurvature.radialPhi_zero]
    exact (hasDerivAt_eta hh hh1).differentiableAt
  · exact (EntropyCurvature.hasDerivAt_radialPhi_entropy hp hh hh1).differentiableAt

theorem barrier_ge_sq {t : ℝ} (ht : |t| < 1) : t ^ 2 ≤ barrier t := by
  unfold barrier
  have hti := abs_lt.mp ht
  have hp : 0 < 1 - t ^ 2 := by nlinarith
  have := Real.log_le_sub_one_of_pos hp
  linarith

/-- The central split bound (2): `(d/(2L)) t² + E t A/2 ≥ -(1183/5760) q²/E`. -/
theorem central_split_lower {d E A q t : ℝ} (hE : 0 < E) (hd : 8 * E ≤ d) (hA : 0 ≤ A)
    (hA' : A ≤ 13 * q / (3 * E)) (_hq : 0 ≤ q) :
    -((1183 / 5760) * (q ^ 2 / E)) ≤ d / (2 * Real.log 2) * t ^ 2 + E * t * A / 2 := by
  have hL : 0 < Real.log 2 := log_two_pos
  have hL7 : Real.log 2 ≤ 7 / 10 := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hd0 : 0 < d := by linarith
  have hα : 0 < d / (2 * Real.log 2) := by positivity
  have hβ0 : 0 ≤ E * A / 2 := by positivity
  have hEA : E * A ≤ 13 * q / 3 := by
    have h := (le_div_iff₀ (by positivity : 0 < 3 * E)).mp hA'
    nlinarith
  have hβle : E * A / 2 ≤ 13 * q / 6 := by linarith
  have hβ2 : (E * A / 2) ^ 2 ≤ (13 * q / 6) ^ 2 := pow_le_pow_left₀ hβ0 hβle 2
  have hsq : 0 ≤ d / (2 * Real.log 2) * (t + (E * A / 2) / (2 * (d / (2 * Real.log 2)))) ^ 2 :=
    mul_nonneg hα.le (sq_nonneg _)
  have hexp : d / (2 * Real.log 2) * (t + (E * A / 2) / (2 * (d / (2 * Real.log 2)))) ^ 2 =
      d / (2 * Real.log 2) * t ^ 2 + E * t * A / 2 +
        (E * A / 2) ^ 2 * (Real.log 2 / (2 * d)) := by
    field_simp
    ring
  have hLd : Real.log 2 / (2 * d) ≤ 7 / (160 * E) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hbound : (E * A / 2) ^ 2 * (Real.log 2 / (2 * d)) ≤ (1183 / 5760) * (q ^ 2 / E) := by
    have h1 := mul_le_mul hβ2 hLd (by positivity) (by positivity)
    have e2 : (13 * q / 6) ^ 2 * (7 / (160 * E)) = (1183 / 5760) * (q ^ 2 / E) := by
      field_simp
      ring
    linarith
  linarith

/-- The central eight-ratio theorem, psi-parent branch, at law level, with the archive's margin. -/
theorem centralEight_margin {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) (hab : μ.a ≤ μ.b)
    (hsum : μ.a + μ.b ≤ 1) (ha : 1 / 10 ≤ μ.a) (hb : 1 / 2 ≤ μ.b) (_hb9 : μ.b ≤ 9 / 10)
    (hEi : μ.meanEntropy ≤ 11 / 200) (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a)
    (hqE : 1 - μ.a - μ.b ≤ 8 * μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (2249 / 144000) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hEdef : μ.meanEntropy = (μ.e + μ.f) / 2 := rfl
  obtain ⟨ht, hce, hcf⟩ := PsiRetainedChildBridge.positive_entropy_split μ.e_pos μ.f_pos
  rw [← hEdef] at hce hcf
  -- hybrid gap through the retained phi children
  have hgap : μ.gap ≤ psi μ.midpoint μ.meanEntropy - (phi μ.a μ.e + phi μ.b μ.f) / 2 :=
    PsiRetainedChildBridge.hybrid_gap_le_retained_phi hactive
  have hq0 : 0 ≤ 1 - μ.a - μ.b := by linarith
  have hmid : μ.midpoint = (1 - (1 - μ.a - μ.b)) / 2 := by unfold InteriorLaw.midpoint; ring
  have hparent : psi μ.midpoint μ.meanEntropy =
      eta (μ.meanEntropy + (1 - H ((1 - (1 - μ.a - μ.b)) / 2))) := by
    rw [hmid]; unfold psi; congr 1; ring
  -- child radii: |1-2a| = d + q, |1-2b| = d - q
  have hra : |1 - 2 * μ.a| = (μ.b - μ.a) + (1 - μ.a - μ.b) := by
    rw [abs_of_nonneg (by linarith)]; ring
  have hrb : |1 - 2 * μ.b| = (μ.b - μ.a) - (1 - μ.a - μ.b) := by
    rw [abs_of_nonpos (by linarith)]; ring
  have hphia : phi μ.a μ.e = radialPhi ((μ.b - μ.a) + (1 - μ.a - μ.b)) μ.e := by
    unfold phi radialPhi; rw [hra]
  have hphib : phi μ.b μ.f = radialPhi ((μ.b - μ.a) - (1 - μ.a - μ.b)) μ.f := by
    unfold phi radialPhi; rw [hrb]
  -- feasibility of the common entropy
  have hH10 : (11 / 200 : ℝ) < H (1 / 10) := by
    have := H_gt_parabola (p := (1 / 10 : ℝ)) (by norm_num) (by norm_num)
    linarith
  have ha2 : μ.a ≤ 1 / 2 := by linarith
  have hHa : H (1 / 10) ≤ H μ.a := H_mono_left (by norm_num) ha ha2
  have hHb : H (1 / 10) ≤ H (1 - μ.b) := H_mono_left (by norm_num) (by linarith) (by linarith)
  have hza : (1 - ((μ.b - μ.a) + (1 - μ.a - μ.b))) / 2 = μ.a := by ring
  have hzb : (1 - ((μ.b - μ.a) - (1 - μ.a - μ.b))) / 2 = 1 - μ.b := by ring
  have hconvA := radialPhi_entropy_convexOn (z := (μ.b - μ.a) + (1 - μ.a - μ.b))
    (by linarith) (by linarith)
  have hconvB := radialPhi_entropy_convexOn (z := (μ.b - μ.a) - (1 - μ.a - μ.b))
    (by linarith) (by linarith)
  rw [hza] at hconvA
  rw [hzb] at hconvB
  have hEone : μ.meanEntropy < 1 := by linarith
  have hsa := convex_tangent_lower hconvA (x := μ.meanEntropy) (y := μ.e)
    ⟨hE, by linarith⟩ ⟨μ.e_pos, μ.e_le_cap⟩
    (radialPhi_differentiableAt' (by linarith) hE hEone)
  have hsb := convex_tangent_lower hconvB (x := μ.meanEntropy) (y := μ.f)
    ⟨hE, by linarith⟩ ⟨μ.f_pos, by rw [H_complement]; exact μ.f_le_cap⟩
    (radialPhi_differentiableAt' (by linarith) hE hEone)
  -- slope difference
  have hqd : 1 - μ.a - μ.b ≤ μ.b - μ.a := hqE.trans hd
  obtain ⟨hA, hA'⟩ := PsiLowEntropyRedesign.child_slope_bounds hE hEone hq0 hqd
  have hef : 0 < μ.e + μ.f := by linarith [μ.e_pos, μ.f_pos]
  have he' : μ.e - μ.meanEntropy = μ.meanEntropy * ((μ.e - μ.f) / (μ.e + μ.f)) := by
    rw [hEdef]; field_simp; ring
  have hf' : μ.f - μ.meanEntropy = -(μ.meanEntropy * ((μ.e - μ.f) / (μ.e + μ.f))) := by
    rw [hEdef]; field_simp; ring
  have hid : deriv (radialPhi ((μ.b - μ.a) + (1 - μ.a - μ.b))) μ.meanEntropy *
        (μ.e - μ.meanEntropy) +
      deriv (radialPhi ((μ.b - μ.a) - (1 - μ.a - μ.b))) μ.meanEntropy * (μ.f - μ.meanEntropy) =
      μ.meanEntropy * ((μ.e - μ.f) / (μ.e + μ.f)) *
        slopeDifference (μ.b - μ.a) (1 - μ.a - μ.b) μ.meanEntropy := by
    rw [he', hf']
    unfold slopeDifference
    ring
  -- radial, parent, endpoint, split
  have hrad := radial_average_loss_le_479 hE hd (1 - μ.a - μ.b)
  rw [abs_of_nonneg (show 0 ≤ (μ.b - μ.a) - (1 - μ.a - μ.b) by linarith),
    abs_of_nonneg (show 0 ≤ (μ.b - μ.a) + (1 - μ.a - μ.b) by linarith)] at hrad
  have hgain := parent_gain_central hE hEi hq0 hqE (by linarith)
  have hcost := PsiEndpointPlane.law_endpoint_logarithmic_lower μ hd
  have hbar : (μ.b - μ.a) / (2 * Real.log 2) * ((μ.e - μ.f) / (μ.e + μ.f)) ^ 2 ≤
      (μ.b - μ.a) / (2 * Real.log 2) * barrier ((μ.e - μ.f) / (μ.e + μ.f)) :=
    mul_le_mul_of_nonneg_left (barrier_ge_sq ht) (by have := log_two_pos; positivity)
  have hsplit := central_split_lower (t := (μ.e - μ.f) / (μ.e + μ.f)) hE hd hA hA' hq0
  have hRaE : radialPhi ((μ.b - μ.a) + (1 - μ.a - μ.b)) μ.meanEntropy =
      eta μ.meanEntropy - F ((μ.b - μ.a) + (1 - μ.a - μ.b)) μ.meanEntropy := rfl
  have hRbE : radialPhi ((μ.b - μ.a) - (1 - μ.a - μ.b)) μ.meanEntropy =
      eta μ.meanEntropy - F ((μ.b - μ.a) - (1 - μ.a - μ.b)) μ.meanEntropy := rfl
  rw [hphia, hphib, hparent] at hgap
  linarith [hgap, hsa, hsb, hid, hrad, hgain, hcost, hbar, hsplit, hRaE, hRbE]

/-- Second proof of the N1 sub-row `SR_EightRatio`, by the literal central route. -/
theorem sr_eightRatio_central : SR_EightRatio := by
  intro k μ hab hsum ha hb hb9 _hd50 hEi hd8 hq8 hact
  have h := centralEight_margin μ hab hsum ha hb hb9 hEi hd8 hq8 hact.le
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hm : 0 ≤ (2249 / 144000) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) := by positivity
  linarith

/-- Explicit restatement (for audit readability). -/
theorem sr_eightRatio_central_explicit :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
      1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 →
      1 / 50 ≤ μ.b - μ.a → μ.meanEntropy ≤ 11 / 200 →
      8 * μ.meanEntropy ≤ μ.b - μ.a → 1 - μ.a - μ.b ≤ 8 * μ.meanEntropy →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost :=
  sr_eightRatio_central

end CKLaneN4

end


