-- Prove2me | Definitions.Def_CK_GeneralCK_PsiSmallDistanceLowEntropy
-- name    : CK_GeneralCK_PsiSmallDistanceLowEntropy
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:59:08.445983+00:00
-- url     : https://prove2.me/theorems/bdf66182-4c86-46eb-8e3b-8c4a236ad6f1
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiSmallDistanceLowEntropy` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiSmallDistanceLowEntropy` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiSmallDistanceLowEntropy` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiSmallDistanceLowEntropy (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiSmallDistanceLowEntropy.lean)

import Definitions.Def_CK_GeneralCK_PsiSmallDistanceBounds

-- ===== source module GeneralCK.PsiSmallDistanceLowEntropy =====
section

namespace GeneralCK.PsiSmallDistance
open Set SmallMean

noncomputable def biasDeficit (r : ℝ) : ℝ := Cn r / Real.log 2

theorem biasDeficit_eq (r : ℝ) : biasDeficit r = 1 - H ((1 - r) / 2) := by
  unfold biasDeficit Cn
  field_simp

theorem biasDeficit_nonneg (r : ℝ) : 0 ≤ biasDeficit r := by
  rw [biasDeficit_eq]
  exact sub_nonneg.mpr (H_le_one _)

theorem biasDeficit_neg (r : ℝ) : biasDeficit (-r) = biasDeficit r := by
  rw [biasDeficit_eq, biasDeficit_eq,
    show (1 - -r) / 2 = 1 - (1 - r) / 2 by ring, H_complement]

theorem biasDeficit_le_sq {r : ℝ} (hr : |r| ≤ 1) : biasDeficit r ≤ r ^ 2 := by
  have hp := Cn_le_log_mul_sq (abs_nonneg r) hr
  have ha : biasDeficit |r| ≤ |r| ^ 2 := by
    exact (div_le_iff₀ log_two_pos).2 (by nlinarith only [hp])
  rw [sq_abs] at ha
  by_cases hz : 0 ≤ r
  · simpa only [abs_of_nonneg hz] using ha
  · simpa only [abs_of_neg (lt_of_not_ge hz), biasDeficit_neg] using ha

theorem corrected_deficit_concave :
    ConcaveOn ℝ (Icc (-1 / 100) (1 / 100))
      (fun r => biasDeficit r - (29 / 40) * r ^ 2) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (f' := fun r => A r / Real.log 2 - (29 / 20) * r)
    (f'' := fun r => 1 / (Real.log 2 * (1 - r ^ 2)) - 29 / 20)
  · exact (Cn_continuous.div_const (Real.log 2)).continuousOn.sub
      ((continuous_id.pow 2).const_mul (29 / 40)).continuousOn
  · intro r hr
    have hi := interior_subset hr
    have hd := ((hasDerivAt_Cn (by linarith [hi.1]) (by linarith [hi.2])).div_const
      (Real.log 2)).sub (((hasDerivAt_id r).pow 2).const_mul (29 / 40))
    convert! hd.hasDerivWithinAt using 1 <;> simp <;> ring
  · intro r hr
    have hi := interior_subset hr
    have hd := ((hasDerivAt_A (by linarith [hi.1]) (by linarith [hi.2])).div_const
      (Real.log 2)).sub ((hasDerivAt_id r).const_mul (29 / 20))
    convert! hd.hasDerivWithinAt using 1
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · intro r hr
    have hi := interior_subset hr
    have hs : r ^ 2 ≤ (1 / 10000 : ℝ) := by
      nlinarith [mul_nonneg (show 0 ≤ r + 1 / 100 by linarith [hi.1])
        (show 0 ≤ 1 / 100 - r by linarith [hi.2])]
    have hL : (69 / 100 : ℝ) ≤ Real.log 2 := by
      have hl := Certificates.PilotData.log_two.1
      norm_num at hl
      linarith
    have hden : 0 < Real.log 2 * (1 - r ^ 2) := mul_pos log_two_pos (by linarith)
    have hb := mul_le_mul hL (show (9999 / 10000 : ℝ) ≤ 1 - r ^ 2 by linarith)
      (by norm_num : (0 : ℝ) ≤ 9999 / 10000) log_two_pos.le
    have hf : 1 / (Real.log 2 * (1 - r ^ 2)) ≤ (29 / 20 : ℝ) := by
      apply (div_le_iff₀ hden).2
      nlinarith only [hb]
    linarith

theorem deficit_average_increment {q d : ℝ}
    (hm : q - d ∈ Icc (-1 / 100 : ℝ) (1 / 100))
    (hp : q + d ∈ Icc (-1 / 100 : ℝ) (1 / 100)) :
    (biasDeficit (q - d) + biasDeficit (q + d)) / 2 - biasDeficit q ≤
      (29 / 40) * d ^ 2 := by
  have hj := corrected_deficit_concave.2 hm hp
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hj
  rw [show (1 / 2 : ℝ) * (q - d) + (1 / 2) * (q + d) = q by ring] at hj
  nlinarith only [hj]

theorem eta_decrement_upper {E a b : ℝ} (hE : 0 < E)
    (hEa : E ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 100000) :
    eta a - eta b ≤ ((8 / 5) / E) * (b - a) := by
  have hm : MonotoneOn (fun h => eta h + ((8 / 5) / E) * h) (Icc E (1 / 100000)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (f' := fun h => deriv eta h + (8 / 5) / E)
    · intro h hh
      exact ((hasDerivAt_eta (by linarith [hh.1]) (by linarith [hh.2])).continuousAt.add
        (continuousAt_id.const_mul _)).continuousWithinAt
    · intro h hh
      have hi := interior_subset hh
      have hd := (hasDerivAt_eta (by linarith [hi.1]) (by linarith [hi.2])).add
        ((hasDerivAt_id h).const_mul ((8 / 5) / E))
      rw [← (hasDerivAt_eta (by linarith [hi.1]) (by linarith [hi.2])).deriv] at hd
      convert! hd.hasDerivWithinAt using 1
      simp
    · intro h hh
      have hi := interior_subset hh
      have hu := neg_deriv_eta_small_upper (by linarith [hi.1]) hi.2
      have hdiv := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 8 / 5) hE hi.1
      linarith
  have h := hm ⟨hEa, hab.trans hb⟩ ⟨hEa.trans hab, hb⟩ hab
  linarith

theorem splitBound_le_radial {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (hab : μ.a < μ.b) (hsum : μ.a + μ.b ≤ 1)
    (hq : 1 - μ.a - μ.b ≤ 8 * μ.meanEntropy)
    (hE : μ.meanEntropy ≤ 1 / 1000000)
    (hd : μ.b - μ.a ≤ 4 * μ.meanEntropy) :
    μ.splitBound ≤ F (μ.b - μ.a) μ.meanEntropy := by
  let q := 1 - μ.a - μ.b
  let d := μ.b - μ.a
  let E := μ.meanEntropy
  have hEpos : 0 < E := by
    dsimp [E, InteriorLaw.meanEntropy]
    linarith [μ.e_pos, μ.f_pos]
  have hdpos : 0 < d := sub_pos.mpr hab
  have hqpos : 0 ≤ q := by dsimp [q]; linarith
  have hqE : q ≤ 8 * E := hq
  have hdE : d ≤ 4 * E := hd
  have hEi : E ≤ 1 / 1000000 := hE
  have hcoords : q - d ∈ Icc (-1 / 10000 : ℝ) (1 / 10000) ∧
      q + d ∈ Icc (-1 / 10000 : ℝ) (1 / 10000) := by
    constructor <;> constructor <;> linarith
  have hbound : ∀ r ∈ Icc (-1 / 10000 : ℝ) (1 / 10000),
      biasDeficit r ≤ (1 / 100000000 : ℝ) := by
    intro r hr
    have hc := biasDeficit_le_sq (r := r) (abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩)
    have hs := mul_nonneg (show 0 ≤ r + 1 / 10000 by linarith [hr.1])
      (show 0 ≤ 1 / 10000 - r by linarith [hr.2])
    nlinarith only [hc, hs]
  have hCp := hbound (q + d) hcoords.2
  have hCm := hbound (q - d) hcoords.1
  have hmid : (1 - q) / 2 = μ.midpoint := by
    dsimp [q, InteriorLaw.midpoint]
    ring
  have hplus : (1 - (q + d)) / 2 = μ.a := by dsimp [q, d]; ring
  have hminus : (1 - (q - d)) / 2 = μ.b := by dsimp [q, d]; ring
  have hparent : 1 - μ.information = E + biasDeficit q := by
    rw [biasDeficit_eq, hmid]
    dsimp [E, InteriorLaw.information]
    ring
  have hchildren : 1 - μ.meanDeficit = E +
      (biasDeficit (q - d) + biasDeficit (q + d)) / 2 := by
    rw [biasDeficit_eq, biasDeficit_eq, hplus, hminus]
    dsimp [E, InteriorLaw.meanEntropy, InteriorLaw.meanDeficit]
    ring
  have harg : E ≤ 1 - μ.information := by
    rw [hparent]
    linarith [biasDeficit_nonneg q]
  have horder : 1 - μ.information ≤ 1 - μ.meanDeficit := by
    linarith [μ.information_eq, μ.entropyDrop_nonneg]
  have hupper : 1 - μ.meanDeficit ≤ (1 / 100000 : ℝ) := by
    rw [hchildren]
    linarith only [hCp, hCm, hEi]
  have hinc := deficit_average_increment
    (show q - d ∈ Icc (-1 / 100 : ℝ) (1 / 100) from
      ⟨by linarith [hcoords.1.1], by linarith [hcoords.1.2]⟩)
    (show q + d ∈ Icc (-1 / 100 : ℝ) (1 / 100) from
      ⟨by linarith [hcoords.2.1], by linarith [hcoords.2.2]⟩)
  have hdiff : (1 - μ.meanDeficit) - (1 - μ.information) ≤ (29 / 40) * d ^ 2 := by
    rw [hparent, hchildren]
    linarith only [hinc]
  have heta := eta_decrement_upper hEpos harg horder hupper
  have hmul := mul_le_mul_of_nonneg_left hdiff (by positivity : (0 : ℝ) ≤ (8 / 5) / E)
  have hsplit : μ.splitBound = eta (1 - μ.information) - eta (1 - μ.meanDeficit) := by
    unfold InteriorLaw.splitBound
    rw [← μ.information_eq]
    rfl
  have hs : μ.splitBound ≤ (29 / 25) * (d ^ 2 / E) := by
    rw [hsplit]
    calc
      _ ≤ ((8 / 5) / E) * ((1 - μ.meanDeficit) - (1 - μ.information)) := heta
      _ ≤ ((8 / 5) / E) * ((29 / 40) * d ^ 2) := hmul
      _ = _ := by ring
  exact hs.trans (F_lower_small_ratio hdpos hEpos hdE)

/-- The low-distance active-psi branch, for actual finite laws and arbitrary
entropy split. Both children are retained through their psi values. -/
theorem law_gap_le_cost {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (hab : μ.a < μ.b) (hsum : μ.a + μ.b ≤ 1)
    (hq : 1 - μ.a - μ.b ≤ 8 * μ.meanEntropy)
    (hE : μ.meanEntropy ≤ 1 / 1000000)
    (hd : μ.b - μ.a ≤ 4 * μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  exact μ.gap_le_of_splitBound hactive
    ((splitBound_le_radial μ hab hsum hq hE hd).trans (PsiEndpointPlane.law_radial_lower μ hab))

end GeneralCK.PsiSmallDistance

#print axioms GeneralCK.PsiSmallDistance.deficit_average_increment
#print axioms GeneralCK.PsiSmallDistance.eta_decrement_upper
#print axioms GeneralCK.PsiSmallDistance.law_gap_le_cost

end


