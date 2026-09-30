-- Prove2me | Definitions.Def_CK_GeneralCK_PsiBalancedMeans
-- name    : CK_GeneralCK_PsiBalancedMeans
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:58:20.361977+00:00
-- url     : https://prove2.me/theorems/e703a3c9-3549-4bd3-ba1e-b7b56f6af540
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiBalancedMeans` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiBalancedMeans` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiBalancedMeans` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiBalancedMeans (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiBalancedMeans.lean)

import Definitions.Def_CK_GeneralCK_PsiEndpointPlaneSymmetric
import Definitions.Def_CK_GeneralCK_EqualMean

-- ===== source module GeneralCK.PsiBalancedMeans =====
section

/-!
# Balanced parent means at every entropy

Complement symmetry makes the two child hybrid profiles identical functions
of entropy. Their proved entropy convexity removes the actual entropy split.
The global radial cost floor then proves the full hybrid inequality.
-/

namespace GeneralCK.PsiBalancedMeans
open Set

theorem ordered_gap_le_radial {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hab : μ.a < μ.b) (hbalance : μ.a + μ.b = 1) :
    μ.gap ≤ F (μ.b - μ.a) μ.meanEntropy := by
  have hb : μ.b = 1 - μ.a := by linarith
  have hcap : μ.f ≤ H μ.a := by
    simpa only [hb, H_complement] using μ.f_le_cap
  have hj := (B_entropy_convexOn μ.a_interior.1 μ.a_interior.2).2
    (show μ.e ∈ Ioc 0 (H μ.a) from ⟨μ.e_pos, μ.e_le_cap⟩)
    (show μ.f ∈ Ioc 0 (H μ.a) from ⟨μ.f_pos, hcap⟩)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hj
  have havg : (1 / 2 : ℝ) * μ.e + (1 / 2) * μ.f = μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    ring
  rw [havg] at hj
  have hchild : B μ.b μ.f = B μ.a μ.f := by rw [hb, B_complement]
  have hmid : (μ.a + μ.b) / 2 = (1 / 2 : ℝ) := by rw [hbalance]
  have hparent : B ((μ.a + μ.b) / 2) μ.meanEntropy = eta μ.meanEntropy := by
    rw [hmid]
    norm_num [B, phi, psi, F, H_half]
  have hrad : |1 - 2 * μ.a| = μ.b - μ.a := by
    rw [abs_of_nonneg (by linarith : 0 ≤ 1 - 2 * μ.a)]
    linarith
  have hphi : eta μ.meanEntropy - F (μ.b - μ.a) μ.meanEntropy ≤ B μ.a μ.meanEntropy := by
    simpa only [B, phi, hrad] using (le_max_left (phi μ.a μ.meanEntropy) (psi μ.a μ.meanEntropy))
  unfold InteriorLaw.gap
  change B ((μ.a + μ.b) / 2) μ.meanEntropy - (B μ.a μ.e + B μ.b μ.f) / 2 ≤ _
  rw [hparent, hchild]
  linarith only [hj, hphi]

/-- Every finite law with a balanced parent mean satisfies the full hybrid
Bellman inequality. There is no entropy cutoff or active-branch premise. -/
theorem law_gap_le_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hbalance : μ.a + μ.b = 1) : μ.gap ≤ μ.cost := by
  rcases lt_trichotomy μ.a μ.b with hab | heq | hba
  · exact (ordered_gap_le_radial μ hab hbalance).trans (PsiEndpointPlane.law_radial_lower μ hab)
  · exact μ.equal_mean_hybrid heq
  · have hs : μ.swap.a + μ.swap.b = 1 := by
      simp only [InteriorLaw.swap_a, InteriorLaw.swap_b]
      linarith
    have h := (ordered_gap_le_radial μ.swap hba hs).trans (PsiEndpointPlane.law_radial_lower μ.swap hba)
    simpa only [InteriorLaw.swap_gap, InteriorLaw.swap_cost] using h

theorem ordered_phi_gap_le_radial {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hab : μ.a < μ.b) (hbalance : μ.a + μ.b = 1) :
    candidateGap phi μ.a μ.b μ.e μ.f ≤ F (μ.b - μ.a) μ.meanEntropy := by
  have hb : μ.b = 1 - μ.a := by linarith
  have hcap : μ.f ≤ H μ.a := by
    simpa only [hb, H_complement] using μ.f_le_cap
  have hj := (phi_entropy_convexOn μ.a_interior.1 μ.a_interior.2).2
    (show μ.e ∈ Ioc 0 (H μ.a) from ⟨μ.e_pos, μ.e_le_cap⟩)
    (show μ.f ∈ Ioc 0 (H μ.a) from ⟨μ.f_pos, hcap⟩)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hj
  have havg : (1 / 2 : ℝ) * μ.e + (1 / 2) * μ.f = μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    ring
  rw [havg] at hj
  have hra : |1 - 2 * μ.a| = μ.b - μ.a := by
    rw [abs_of_nonneg (by linarith : 0 ≤ 1 - 2 * μ.a)]
    linarith
  have hrb : |1 - 2 * μ.b| = μ.b - μ.a := by
    rw [abs_of_nonpos (by linarith : 1 - 2 * μ.b ≤ 0)]
    linarith
  have hchild : phi μ.b μ.f = phi μ.a μ.f := by simp only [phi, hra, hrb]
  have hparent : phi ((μ.a + μ.b) / 2) μ.meanEntropy = eta μ.meanEntropy := by
    rw [hbalance]
    norm_num [phi, F]
  have href : phi μ.a μ.meanEntropy = eta μ.meanEntropy - F (μ.b - μ.a) μ.meanEntropy := by
    simp only [phi, hra]
  rw [href] at hj
  unfold candidateGap
  change phi ((μ.a + μ.b) / 2) μ.meanEntropy - (phi μ.a μ.e + phi μ.b μ.f) / 2 ≤ _
  rw [hparent, hchild]
  linarith only [hj]

/-- The phi candidate itself satisfies the balanced-mean Bellman inequality,
so this face can also be removed from the remaining phi-branch obligation. -/
theorem phi_gap_le_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hbalance : μ.a + μ.b = 1) : candidateGap phi μ.a μ.b μ.e μ.f ≤ μ.cost := by
  rcases lt_trichotomy μ.a μ.b with hab | heq | hba
  · exact (ordered_phi_gap_le_radial μ hab hbalance).trans (PsiEndpointPlane.law_radial_lower μ hab)
  · have hc : 0 ≤ μ.cost := by
      simpa [← heq, interiorCost] using LogSum.cost_lower_bound μ
    exact (μ.equal_mean_phi_gap_nonpos heq).trans hc
  · have hs : μ.swap.a + μ.swap.b = 1 := by
      simp only [InteriorLaw.swap_a, InteriorLaw.swap_b]
      linarith
    have h := (ordered_phi_gap_le_radial μ.swap hba hs).trans (PsiEndpointPlane.law_radial_lower μ.swap hba)
    simpa only [candidateGap, InteriorLaw.swap_a, InteriorLaw.swap_b,
      InteriorLaw.swap_e, InteriorLaw.swap_f, InteriorLaw.swap_cost, add_comm] using h

end GeneralCK.PsiBalancedMeans

#print axioms GeneralCK.PsiBalancedMeans.ordered_gap_le_radial
#print axioms GeneralCK.PsiBalancedMeans.law_gap_le_cost
#print axioms GeneralCK.PsiBalancedMeans.phi_gap_le_cost

end


