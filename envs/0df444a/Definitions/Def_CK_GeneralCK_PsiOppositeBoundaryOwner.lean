-- Prove2me | Definitions.Def_CK_GeneralCK_PsiOppositeBoundaryOwner
-- name    : CK_GeneralCK_PsiOppositeBoundaryOwner
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:59:41.133231+00:00
-- url     : https://prove2.me/theorems/44112a35-5849-48aa-9808-f04139fe5458
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiOppositeBoundaryOwner` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiOppositeBoundaryOwner` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiOppositeBoundaryOwner` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiOppositeBoundaryOwner (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiOppositeBoundaryOwner.lean)

import Definitions.Def_CK_GeneralCK_PsiBoundaryLeafReplay
import Definitions.Def_CK_GeneralCK_PsiBoundaryAnalyticBridge
import Definitions.Def_CK_GeneralCK_PsiEndpointBellman

-- ===== source module GeneralCK.PsiOppositeBoundaryOwner =====
section

/-!
# The complete extreme opposite-side boundary strip

The corner is handled by the new retained-child endpoint theorem. Outside the
corner, the original seventeen rational leaves are reused, with three stronger
plain-envelope checks. Those checks remove the old unproved factor-eight input
on the larger bias interval: every enhanced leaf now has upper endpoint at most
1/16, inside the analytically proved small-bias parent range.
-/

namespace GeneralCK.PsiOppositeBoundary
open BoundaryStrip

theorem capacity_quadratic_lower {q : ℝ} (hq : 0 ≤ q) (hqi : q ≤ 1) :
    5 * q ^ 2 / 7 ≤ Ccap q := by
  have hh := SmallMean.Cn_ge_half_sq hq hqi
  change q ^ 2 / 2 ≤ Real.log 2 * Ccap q at hh
  have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have hh := Certificates.PilotData.log_two.2
    norm_num at hh
    linarith
  have hm := mul_le_mul_of_nonneg_right hL (Ccap_nonneg (q := q))
  nlinarith only [hh, hm]

theorem leaf13_plain : stripPsi (1 / 16) false < stripCost (1 / 8) := by
  refine leaf_gap (v := (6000 : ℝ)⁻¹)
    (cL := 5 * (1 / 16 - Ac) ^ 2 / 7) (c2 := 13) (jU := 14 / 5)
    (by norm_num [Ac]) (by norm_num [Ac])
    (capacity_quadratic_lower (by norm_num [Ac]) (by norm_num [Ac]))
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num [Ac]) ?_ (by norm_num [Ac])
  · exact H_le_of_pow (b := 6000) (p := 13) (k := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Ac])
  · exact J_le_of_pow (b := 5999) (p := 13) (k := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · exact le_J_of_pow (b := 7) (c := 1) (p := 14) (k := 5)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leaf14_plain : stripPsi (1 / 8) false < stripCost (1 / 4) := by
  refine leaf_gap (v := (1200 : ℝ)⁻¹)
    (cL := 5 * (1 / 8 - Ac) ^ 2 / 7) (c2 := 11) (jU := 3 / 2)
    (by norm_num [Ac]) (by norm_num [Ac])
    (capacity_quadratic_lower (by norm_num [Ac]) (by norm_num [Ac]))
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num [Ac]) ?_ (by norm_num [Ac])
  · exact H_le_of_pow (b := 1200) (p := 11) (k := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Ac])
  · exact J_le_of_pow (b := 1199) (p := 11) (k := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · exact le_J_of_pow (b := 3) (c := 1) (p := 3) (k := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leaf15_plain : stripPsi (1 / 4) false < stripCost (2 / 5) := by
  refine leaf_gap (v := (256 : ℝ)⁻¹)
    (cL := 5 * (1 / 4 - Ac) ^ 2 / 7) (c2 := 8) (jU := 1 / 2)
    (by norm_num [Ac]) (by norm_num [Ac])
    (capacity_quadratic_lower (by norm_num [Ac]) (by norm_num [Ac]))
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num [Ac]) ?_ (by norm_num [Ac])
  · exact H_le_of_pow (b := 256) (p := 8) (k := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Ac])
  · exact J_le_of_pow (b := 255) (p := 8) (k := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · exact le_J_of_pow (b := 3) (c := 2) (p := 1) (k := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def enhanced (z : ℚ × ℚ × Bool) : Bool := decide (z.2.1 ≤ 1 / 16)

theorem revised_leaves_gap (z : ℚ × ℚ × Bool) (hz : z ∈ leaves) :
    stripPsi (z.1 : ℝ) (enhanced z) < stripCost (z.2.1 : ℝ) := by
  fin_cases hz <;> norm_num [enhanced]
  · exact leaf00
  · exact leaf01
  · exact leaf02
  · exact leaf03
  · exact leaf04
  · exact leaf05
  · exact leaf06
  · exact leaf07
  · exact leaf08
  · exact leaf09
  · exact leaf10
  · exact leaf11
  · exact leaf12
  · exact leaf13_plain
  · exact leaf14_plain
  · exact leaf15_plain
  · exact leaf16

theorem stripCost_le_actual {a b u : ℝ} (ha : 0 < a) (haA : a ≤ Ac)
    (hb : b < 1) (hxu : 1 - b ≤ u) (hu : u ≤ 1 / 2) :
    stripCost u ≤ interiorCost a b := by
  have hA0 : 0 < Ac := by norm_num [Ac]
  have hAhalf : Ac ≤ 1 / 2 := by norm_num [Ac]
  have hx0 : 0 < 1 - b := by linarith
  have hu0 : 0 < u := by linarith
  have hJA := J_antitone ha hAhalf haA
  have hJu := J_antitone hx0 hu hxu
  have hsum : 0 ≤ J Ac + J u := add_nonneg (J_nonneg hA0 hAhalf) (J_nonneg hu0 hu)
  have hdiff : 0 ≤ (1 - u - Ac) / 2 := by norm_num [Ac] at *; linarith
  have hh := mul_le_mul (show (1 - u - Ac) / 2 ≤ (b - a) / 2 by linarith)
    (show J Ac + J u ≤ J a + J (1 - b) by linarith) hsum
    (show 0 ≤ (b - a) / 2 by linarith [hdiff])
  rw [stripCost, interiorCost, show b = 1 - (1 - b) by ring,
    J_one_sub hx0 (by linarith : 1 - b < 1)]
  convert! hh using 1
  ring

theorem leaf_parent_envelope {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    {l u : ℝ} {enh : Bool} (haA : μ.a ≤ Ac)
    (hl : l ≤ 1 - μ.b) (hu : 1 - μ.b ≤ u) (huhalf : u ≤ 1 / 2)
    (hq0 : 0 < l - Ac) (hbranch : enh = true → u ≤ 1 / 16)
    (hactive : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy) :
    Scalar.P μ.information ≤ stripPsi l enh := by
  let q := 1 - μ.a - μ.b
  have ha := μ.a_interior.1
  have hqle : l - Ac ≤ q := by dsimp [q]; linarith
  have hqpos : 0 < q := hq0.trans_le hqle
  have hqhalf : q ≤ 1 / 2 := by dsimp [q]; linarith
  have hq0half : l - Ac ≤ 1 / 2 := hqle.trans hqhalf
  have hC := parentDeficit_mono hq0.le hqle (show q ≤ 1 by linarith)
  change Ccap (l - Ac) ≤ Ccap q at hC
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hmid : (1 - q) / 2 = μ.midpoint := by
    dsimp [q, InteriorLaw.midpoint]
    ring
  have hparent : 1 - μ.information = μ.meanEntropy + Ccap q := by
    rw [Ccap, hmid]
    unfold InteriorLaw.information
    ring
  have htarget : μ.meanEntropy + Ccap q ∈ Set.Ioc (0 : ℝ) 1 := by
    rw [← hparent]
    exact ⟨by linarith [μ.information_mem.2], by linarith [μ.information_mem.1]⟩
  have hCpos : 0 < Ccap (l - Ac) := by
    have hh := capacity_quadratic_lower hq0.le (show l - Ac ≤ 1 by linarith)
    have hs := sq_pos_of_pos hq0
    linarith
  unfold Scalar.P
  rw [hparent, stripPsi]
  refine eta_antitoneOn ?_ htarget ?_
  · constructor
    · cases enh <;> simp only [Bool.false_eq_true, reduceIte, add_zero]
      · exact hCpos
      · linarith
    · cases enh <;> simp only [Bool.false_eq_true, reduceIte, add_zero]
      · exact Ccap_le_one hq0.le hq0half
      · exact Ccap_add_eighth_le_one hq0.le hq0half
  · cases enh with
    | false => simp only [Bool.false_eq_true, reduceIte, add_zero]; linarith
    | true =>
      simp only [reduceIte]
      have hu16 := hbranch rfl
      have hqsmall : q ≤ 1 / 10 := by dsimp [q]; linarith
      have hact : phi ((1 - q) / 2) μ.meanEntropy < psi ((1 - q) / 2) μ.meanEntropy := by
        rwa [hmid]
      have hE8 : q / 8 < μ.meanEntropy := by
        have hh := PsiParentDominance.activePsi_entropy_gt_eighth hE
          (show 0 < 1 - 2 * ((1 - q) / 2) by linarith)
          (show 1 - 2 * ((1 - q) / 2) ≤ 1 / 10 by linarith) hact
        convert! hh using 1
        ring
      linarith

theorem leaf_bound {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (haA : μ.a ≤ Ac) (hactive : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy)
    {z : ℚ × ℚ × Bool} (hz : z ∈ leaves)
    (hl : (z.1 : ℝ) ≤ 1 - μ.b) (hu : 1 - μ.b ≤ (z.2.1 : ℝ)) :
    Scalar.P μ.information ≤ interiorCost μ.a μ.b := by
  have hvalid := leaf_branch_valid z hz
  have hq0 : 0 < (z.1 : ℝ) - Ac := by
    have hh : (Aq : ℝ) < (z.1 : ℝ) := by exact_mod_cast hvalid.1
    norm_num [Aq, Ac] at *
    linarith
  have huhalf : (z.2.1 : ℝ) ≤ 1 / 2 := by
    have hh : (z.2.1 : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by
      exact_mod_cast (leaf_endpoints_within hz).2
    norm_num at hh
    exact hh
  have hbranch : enhanced z = true → (z.2.1 : ℝ) ≤ 1 / 16 := by
    intro h
    have hh : z.2.1 ≤ 1 / 16 := of_decide_eq_true h
    have hh' : (z.2.1 : ℝ) ≤ ((1 / 16 : ℚ) : ℝ) := by exact_mod_cast hh
    norm_num at hh'
    exact hh'
  exact (leaf_parent_envelope μ haA hl hu huhalf hq0 hbranch hactive).trans
    ((revised_leaves_gap z hz).le.trans
      (stripCost_le_actual μ.a_interior.1 haA μ.b_interior.2 hu huhalf))

theorem law_gap_le_cost_outside_corner {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hside : 1 / 2 ≤ μ.b) (haA : μ.a ≤ Ac)
    (hcorner : 1 / 8192 < μ.a + 1 - μ.b)
    (hactive : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  have hlo : (((Kq - Aq : ℚ)) : ℝ) ≤ 1 - μ.b := by
    norm_num [Kq, Aq, Ac] at *
    linarith
  obtain ⟨z, hz, hl, hu⟩ := (mem_strip_iff (1 - μ.b)).mp ⟨hlo, by linarith⟩
  exact μ.gap_le_of_activePsi_of_P_information_le_interiorCost hactive
    (leaf_bound μ haA hactive hz hl hu)

end GeneralCK.PsiOppositeBoundary

namespace GeneralCK

/-- The entire original boundary owner now follows from the new analytic corner
and a revised finite strip certificate, with no remaining regional premise. -/
theorem oppositePsiBoundaryOwner : OppositePsiBoundaryOwner := by
  intro k μ hab hsum hmean hinfo hside haA hactive
  by_cases hc : μ.a + 1 - μ.b ≤ 1 / 8192
  · exact oppositePsiCornerOwner k μ hab hsum hmean hinfo hside hc hactive
  · exact PsiOppositeBoundary.law_gap_le_cost_outside_corner μ hside haA
      (lt_of_not_ge hc) hactive

end GeneralCK

#print axioms GeneralCK.PsiOppositeBoundary.capacity_quadratic_lower
#print axioms GeneralCK.PsiOppositeBoundary.leaf13_plain
#print axioms GeneralCK.PsiOppositeBoundary.leaf14_plain
#print axioms GeneralCK.PsiOppositeBoundary.leaf15_plain
#print axioms GeneralCK.PsiOppositeBoundary.revised_leaves_gap
#print axioms GeneralCK.PsiOppositeBoundary.stripCost_le_actual
#print axioms GeneralCK.PsiOppositeBoundary.leaf_parent_envelope
#print axioms GeneralCK.PsiOppositeBoundary.law_gap_le_cost_outside_corner
#print axioms GeneralCK.oppositePsiBoundaryOwner

end


