-- Prove2me | Definitions.Def_OAIQ093D012
-- name    : OAIQ093D012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:23:24.648353+00:00
-- url     : https://prove2.me/theorems/189fd854-3ab9-4e86-9ecb-9b37f1d49690
-- title:
--   Definitions bundle OAIQ093D012 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 2 definitions, 1 instance and 17 theorems. The definitions and types are `OAI.PolycyclicRecognition.booleanPartitionEvaluation`, `OAI.PolycyclicRecognition.polynomialModelCoordinate`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `BoundedDoubling`, `Packing`, `Poincare`, [`PolycyclicRecognition_Algebra_BooleanPartitionMaps`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/BooleanPartitionMaps.lean), [`PolycyclicRecognition_Algebra_MixedWordIdeal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/MixedWordIdeal.lean), [`PolycyclicRecognition_Algebra_PolynomialModelRepresentation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/PolynomialModelRepresentation.lean), [`PolycyclicRecognition_Analysis_WordBoxComparison`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Analysis/WordBoxComparison.lean), [`PolycyclicRecognition_Geometry_CartanBasisComparison`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanBasisComparison.lean), [`PolycyclicRecognition_Geometry_CartanGenerators`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanGenerators.lean), [`PolycyclicRecognition_Geometry_CartanWeightDilation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanWeightDilation.lean), [`PolycyclicRecognition_Geometry_WeightedBasisComparison`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/WeightedBasisComparison.lean), `Representation`.
--
--   **Imports.** It imports the published bundle `Def_PolycyclicRecognition`; the bundles `OAIQ093D006`, `OAIQ093D007`, `OAIQ093D008` and `OAIQ093D009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ093D016`, `OAIQ093D017` and `OAIQ093D018`; the proofs of `OAI.PolycyclicRecognition.CartanWordModel.eventually_root_neighbor_labels_eq` and `OAI.PolycyclicRecognition.CartanWordModel.exists_source_target_comparison_schemes`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D006
import Definitions.Def_OAIQ093D007
import Definitions.Def_OAIQ093D008
import Definitions.Def_OAIQ093D009

section
-- module Solutions.OAIQ093_PR.Packing
attribute [-instance] _root_.GeneratesNS.volume_finite_compact _root_.GeneratesNS.volume_mul_left_invariant _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Ball packing at a good scale

The packing sets `B`, `B_half`, `B_3` at a good scale, their finiteness and disjointness, and
the intersection-multiplicity bound `card_B_le_exp_wa`.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false

open scoped Finset
open scoped Pointwise

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped Topology

section V_Wrapper_Section

open V_Wrapper

variable [v_wrapper_inst: V_Wrapper]
include v_wrapper_inst

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

variable {b : Module.Basis ι ℝ V}

variable {b : Module.Basis ι ℝ V}

lemma pack_center_helper (data: GoodScalesData b) (x: G): #{ c ∈ (X_j_finite data).toFinset | x ∈ B_c_r c (3 * (R_1 data + 1)) } * #(S ^ ((R_1 data) / 2)) ≤ #(S ^ (4 * (R_1 data + 1))) := by
  rw [← closed_ball_eq_S_pow]
  rw [← smul_eq_mul]
  rw [← Finset.sum_const]

  rw [← closed_ball_eq_S_pow]
  grw [Finset.sum_le_sum (g := fun a => #(B_c_r a ↑((R_1 data : ℝ) / 2)))]
  .
    rw [← Finset.card_biUnion]
    .
      nth_rw 2 [← Finset.card_smul_finset (MulOpposite.op x)]
      apply Finset.card_le_card
      rw [← Finset.coe_subset]

      intro a ha
      simp at ha
      obtain ⟨p, ⟨p_mem, a_mem⟩⟩ := ha
      simp
      simp [B_c_r] at a_mem
      grw [dist_triangle _ p]
      grw [a_mem]
      have p_dist := p_mem.1
      simp [X_j] at p_dist
      apply Metric.maximalSeparatedSet_subset at p_dist
      simp at p_dist
      have x_mem := p_mem.2
      simp [B_c_r] at x_mem
      rw [dist_comm] at x_mem
      grw [x_mem]
      rw [mul_add]
      ring
      grind
    .
      rw [Finset.pairwiseDisjoint_iff]
      intro a ha b hb hab

      have from_b := B_half_disjoint data
      simp at ha hb
      simp [B_half] at from_b

      rw [Set.pairwiseDisjoint_iff] at from_b
      simp only [Set.mem_image, id_eq, forall_exists_index, and_imp] at from_b
      have inter_eq := from_b a ha.1 (i := (Metric.closedBall a ((↑(R_1 data) : ℝ) / 2) )) (?_) b hb.1 (j := (Metric.closedBall b (↑(R_1 data : ℝ) / 2) )) (?_) ?_
      .
        apply B_ball_injective_on data (R_1 data / 2) (by grind) (by simp [R_1]) at inter_eq
        .
          simp [inter_eq]
        . grind
        . grind
      . rfl
      . rfl
      .
        rw [← Finset.coe_nonempty] at hab
        simp [B_c_r] at hab
        simpa using hab
  .
    intro a ha
    simp at ha
    simp [B_c_r_eq_smul, B_r]
    rw [Nat.cast_div]
    . simp
    . simp [R_1]
    . simp

lemma log_pack_center_helper (data: GoodScalesData b) (x: G): #{ c ∈ (X_j_finite data).toFinset | x ∈ B_c_r c (3 * (R_1 data + 1)) } ≤ Real.exp (a data.d) := by
  by_cases inter_empty: { c ∈ (X_j_finite data).toFinset | x ∈ B_c_r c (3 * (R_1 data + 1)) } = ∅
  . simp [inter_empty]
    apply Real.exp_nonneg

  rw [← Real.log_le_iff_le_exp]
  have foo := pack_center_helper data x
  rw [← Nat.le_div_iff_mul_le] at foo
  grw [foo]
  .
    grw [Nat.cast_div_le]
    .
      rw [Real.log_div]
      .
        have bound := (GoodScales data).first_h_i
        grw [← bound]

        apply log_card_pow_sub_le (GoodScales data).i_1_ge (Nat.le_succ _)
        . simp [R_1]
        . rw [pow_succ]
          simp [R_1]
          ring
          rw [← le_tsub_iff_right]
          .
            rw [← Nat.mul_sub]
            norm_num
            grw [← Nat.one_le_pow]
            . simp
            . simp
          . simp
        . simp [R_1]
      . norm_cast
        rw [Finset.card_eq_zero]
        rw [← ne_eq, ← Finset.nonempty_iff_ne_empty]
        apply Finset.Nonempty.pow
        simp [S_nonempty]
      . norm_cast
        rw [Finset.card_eq_zero]
        rw [← ne_eq, ← Finset.nonempty_iff_ne_empty]
        apply Finset.Nonempty.pow
        simp [S_nonempty]
    . simp
      refine ⟨?_, ?_⟩
      . apply Finset.Nonempty.pow
        simp [S_nonempty]
      .
        apply Finset.card_pow_mono
        . simp [R_1]
        . grind
  .
    simp
    rw [Finset.nonempty_iff_ne_empty]
    simpa using inter_empty
  . simp
    apply Finset.Nonempty.pow
    simp [S_nonempty]
  . simp
    rw [Finset.nonempty_iff_ne_empty]
    simpa using inter_empty

end V_Wrapper_Section

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Poincare
attribute [-instance] _root_.GeneratesNS.volume_finite_compact _root_.GeneratesNS.volume_mul_left_invariant _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The Poincaré inequality

`poincare_inequality` and the packing-averaged form `lemma_3_25_poincare`.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false

open scoped Finset
open scoped Pointwise

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped Topology

section V_Wrapper_Section

open V_Wrapper

variable [v_wrapper_inst: V_Wrapper]
include v_wrapper_inst

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

variable {b : Module.Basis ι ℝ V}

lemma double_ball_sum (R: ℕ) (hR: 0 < R) (f: G → ℝ) (hf: ∀ g, 0 ≤ f g): ∑ x ∈ B_r (↑(R - 1)), ∑ y ∈ (Metric.closedBall x 1), f y ≤ 2 * #S * ∑ x ∈ B_r R, f x := by
  classical

  grw [Finset.sum_le_sum (g := fun x =>  ∑ y ∈ ((x) • S) ∪ ((MulOpposite.op x • S)), f y)]
  .
    have union_sub (x: G) := Finset.sum_union_inter (f := f) (s₁ := x • S) (s₂ := (MulOpposite.op x • S))
    simp_rw [← eq_sub_iff_add_eq] at union_sub
    have foo (x) := le_of_sub_eq _ _ _ (union_sub x) (by
      apply Finset.sum_nonneg
      simp [hf]
    )
    grw [Finset.sum_le_sum (h := fun x hx => foo x)]

    simp_rw [← Finset.image_smul]
    conv =>
      lhs
      arg 2
      intro x
      rw [Finset.sum_image (by simp)]
      rw [Finset.sum_image (by simp)]

    have card_le (i: G) : #({a ∈ B_r ↑(R - 1) ×ˢ S | a.1 • a.2 = i}) ≤ #S := by
      apply Finset.card_le_card_of_injOn (f := fun p => p.1⁻¹ * i)
      . intro a ha
        simp at ha
        simp
        simp [← ha.2]
        grind
      . intro a ha b hb hab
        simp at hab
        simp at ha
        simp at hb
        have ha_2 := ha.2
        have hb_2 := hb.2
        rw [Prod.ext_iff]
        rw [← ha_2] at hb_2
        simp [hab] at hb_2
        grind

    have card_le_rev (i: G) : #({a ∈ B_r ↑(R - 1) ×ˢ S | a.2 * a.1 = i}) ≤ #S := by
      apply Finset.card_le_card_of_injOn (f := fun p => i * p.1⁻¹)
      . intro a ha
        simp at ha
        simp
        simp [← ha.2]
        grind
      . intro a ha b hb hab
        simp at hab
        simp at ha
        simp at hb
        have ha_2 := ha.2
        have hb_2 := hb.2
        rw [Prod.ext_iff]
        rw [← ha_2] at hb_2
        simp [hab] at hb_2
        grind

    simp_rw [Finset.sum_add_distrib]
    rw [← Finset.sum_product']
    rw [← Finset.sum_product']
    simp_rw [Finset.sum_comp]
    grw [Finset.sum_le_sum_of_subset_of_nonneg (t := B_r R)]
    .
      grw [Finset.sum_le_sum (g := fun i => #S • f i)]
      .
        simp
        rw [← Finset.mul_sum]
        rw [add_comm]
        grw [Finset.sum_le_sum_of_subset_of_nonneg (t := B_r R)]
        .
          grw [Finset.sum_le_sum (g := fun i => #S • f i)]
          .
            simp
            rw [← Finset.mul_sum]
            rw [← mul_add]
            grind
          .
            intro i hi
            simp
            -- TODO - why doesn't grw work here
            apply mul_le_mul
            . simp
              apply card_le_rev
            . simp
            . apply hf
            . simp
        .
          rw [Finset.image_subset_iff]
          intro x hx
          simp at hx
          simp [B_r, dist, WordDist_one]
          grw [word_norm_mul_le]
          simp [B_r, dist, WordDist_one] at hx
          grw [hx.1]
          have norm_s := word_norm_le x.2 [⟨x.2, hx.2⟩] (by simp [ProdS])
          grw [norm_s]
          simp [hR]
          grind
        . intros
          apply mul_nonneg
          . simp
          . apply hf
      . intro i hi
        grw [card_le]
        apply hf

    . rw [Finset.image_subset_iff]
      intro x hx
      simp at hx
      simp [B_r, dist, WordDist_one]
      grw [word_norm_mul_le]
      simp [B_r, dist, WordDist_one] at hx
      grw [hx.1]
      have norm_s := word_norm_le x.2 [⟨x.2, hx.2⟩] (by simp [ProdS])
      grw [norm_s]
      simp [hR]
    . intros
      simp
      apply mul_nonneg
      . simp
      . apply hf
  . intro i hi
    grw [Finset.sum_le_sum_of_subset_of_nonneg]
    .
      simp
      apply ball_x_one_subset
    . intros
      apply hf

-- TODO - get rid of some lemmas, since mathlib already has Metric.smul_closedBall defined

-- Theorem 3.20
set_option maxHeartbeats 3500000 in
lemma poincare_inequality (R: ℕ) (f: G → ℝ): ∑ x ∈ (B_r (R - 1)), |f x - (f_avg (R - 1) f)|^2 ≤
    16 * R^2 * #S * (#(B_r (2 * R - 2))) / #(B_r (R - 1)) * ∑ x ∈ (B_r (3 * R)), deriv_sq_R f x := by

  by_cases R_nonpos: R = 0
  .
    simp [R_nonpos, f_avg, B_r]

  let δ_f (x: G) := ∑ x ∈ (finite_closed_ball x 1).toFinset, deriv_sq_R f x

  have f_sub_le (x: G): |f x - f_avg (R - 1) f| ≤ √((#((B_r (R - 1))) : ℝ)⁻¹ * (∑ y ∈ (B_r (R - 1)), (f x - f y)^2)) := by
    rw [f_avg]
    conv =>
      lhs
      arg 1
      arg 1
      equals (#((B_r (↑R - 1))) : ℝ)⁻¹ * ∑ y ∈ (B_r (↑R - 1)), f x =>
        simp
        rw [inv_mul_cancel_left₀]
        simp [B_r]
        exact Set.ncard_ne_zero_of_mem (a := 1) (by simp; grind) (finite_closed_ball 1 _)

    rw [B_r]
    rw [← mul_sub]
    rw [abs_mul]
    rw [← Finset.sum_sub_distrib]
    grw [Finset.abs_sum_le_sum_abs]
    conv =>
      lhs
      rhs
      arg 2
      intro i
      equals |f x - f i| * 1 => simp
    grw [Real.sum_mul_le_sqrt_mul_sqrt]
    simp [Real.sqrt_eq_rpow]
    rw [← Real.rpow_neg_one]
    rw [mul_comm]
    rw [mul_assoc]
    rw [← Real.rpow_add]
    .
      norm_num
      simp
      rw [Real.mul_rpow]
      .
        field_simp
        rw [← Real.rpow_mul]
        .
          simp
        . positivity
      . positivity
      . positivity

    . simp
      rw [Set.ncard_pos (finite_closed_ball 1 _)]
      exact ⟨1, by simp; grind⟩

  let γ (z: G) (i: ℕ) := ((word_norm_prod_self z).choose.take i).unattach.prod
  have gamma_zero (z: G): γ z 0 = 1 := by simp [γ]
  have gamma_norm (z: G): γ z (WordNorm z) = z := by
    simp [γ]
    obtain ⟨prod, len_eq⟩ := (word_norm_prod_self z).choose_spec
    simp [ProdS] at prod
    conv =>
      arg 1
      pattern (WordNorm z)
      rw [← len_eq]

    simp
    exact prod

  have gamma_i_norm_le (z: G) (i: ℕ): WordNorm (γ z i) ≤ i := by
    simp [γ]

    have i_le := word_norm_le ((word_norm_prod_self z).choose.take i).unattach.prod ((word_norm_prod_self z).choose.take i) (by simp [ProdS])
    grw [List.length_take_le] at i_le
    exact i_le

  have gamma_sum (z: G) (hz: z ∈ B_r (2*R - 2)): ∑ x ∈ B_r (R - 1), ∑ i ∈ Finset.range (WordNorm z), δ_f (x * (γ z i)) ≤ 2 * R * ∑ x ∈ B_r (3*R - 1), δ_f x := by

    rw [← Finset.sum_product']
    rw [Finset.sum_comp]
    simp
    grw [Finset.sum_le_sum (g := fun a => (((2 * R) : ℝ) * (δ_f a)))]
    .
      rw [← Finset.mul_sum]
      grw [Finset.sum_le_sum_of_subset_of_nonneg (t := B_r (3*R - 1))]
      .
        intro p hp
        simp at hp
        obtain ⟨a, b, ⟨a_mem, b_lt⟩, p_eq⟩ := hp
        rw [← p_eq]
        simp [B_r, dist, WordDist_one]
        grw [word_norm_mul_le]
        simp [B_r, dist, WordDist_one] at a_mem
        simp [B_r, dist, WordDist_one] at hz
        simp
        grw [a_mem]
        grw [gamma_i_norm_le]
        grw [b_lt]
        grw [hz]
        grind
      . intro p hp _
        simp [δ_f, deriv_sq_R]
        positivity
    .
      intro b hb
      simp at hb
      obtain ⟨x, n, ⟨x_mem, n_lt⟩, b_eq⟩ := hb
      grw [Finset.card_le_card (t := (Finset.range (2 * R)).image (fun n => (b * ((γ z n)⁻¹), n)))]
      .
        grw [Finset.card_image_le]
        . simp
        . simp [δ_f, deriv_sq_R]
          positivity
      .
        simp [δ_f, deriv_sq_R]
        positivity
      .
        intro p hp
        simp at hp
        simp
        use p.2
        refine ⟨?_, ?_⟩
        .

          by_contra!
          grw [hp.1.2] at this
          simp [B_r, dist, WordDist_one] at hz
          conv at hz =>
            rhs
            equals ↑(2*R - 2) =>
              rw [Nat.cast_sub]
              simp
              grind

          norm_cast at hz
          grind
        .
          ext
          . simp [← hp.2]
          . simp

  have diff_le_delta_sum (x y: G) (hx: x ∈ B_r (R - 1)) (hy: y ∈ B_r (R - 1)): |f y - f x| ≤ √((2 * R) * (∑ i ∈ Finset.range (WordNorm (x⁻¹ * y)), δ_f (x * γ (x⁻¹ * y) i))) := by

    have inv_prod_le: WordNorm (x⁻¹ * y) ≤ 2*R - 2 := by
      grw [word_norm_mul_le]
      rw [← word_norm_inv]
      simp [B_r, dist, WordDist_one] at hx hy
      conv at hx =>
        rhs
        equals ↑(R - 1) =>
          rw [Nat.cast_sub]
          simp
          grind
      conv at hy =>
        rhs
        equals ↑(R - 1) =>
          rw [Nat.cast_sub]
          simp
          grind
      norm_cast at hx hy
      grw [hx, hy]
      grind

    have root_le_R: √(WordNorm (x⁻¹ * y)) ≤ √(2*R) := by
      rw [Real.sqrt_le_sqrt_iff]
      . norm_cast
        grw [inv_prod_le]
        simp
      . simp

    conv =>
      lhs
      equals |(f (x * γ (x⁻¹ * y) (WordNorm (x⁻¹ * y)))) - f (x * γ (x⁻¹ * y) 0)| =>
        simp [gamma_zero, gamma_norm]

    rw [← Finset.sum_range_sub (n := WordNorm (x⁻¹ * y)) (f := fun i => f (x * γ (x⁻¹ * y) i))]
    grw [Finset.abs_sum_le_sum_abs]
    conv =>
      lhs
      arg 2
      intro i
      rw [← mul_one (a := |_|)]

    grw [Real.sum_mul_le_sqrt_mul_sqrt]
    simp
    grw [root_le_R]

    have sum_le_delta: ∑ x_1 ∈ Finset.range (WordNorm (x⁻¹ * y)), (f (x * γ (x⁻¹ * y) x_1) - f (x * γ (x⁻¹ * y) (x_1 + 1))) ^ 2 ≤ ∑ n ∈ Finset.range (WordNorm (x⁻¹ * y)), δ_f (x * (γ (x⁻¹ * y) n)) := by
      apply Finset.sum_le_sum
      intro n hn
      simp [δ_f, deriv_sq_R]
      rw [← Finset.add_sum_erase (a := (x * γ (x⁻¹ * y) n))]
      .
        apply le_add_of_le_of_nonneg
        .
          let s := (word_norm_prod_self (x⁻¹ * y)).choose[n]?.getD ⟨1, one_mem⟩
          rw [← Finset.add_sum_erase (a := s.val) (h := by simp)]
          apply le_add_of_le_of_nonneg
          .
            rw [sub_sq_comm]
            conv =>
              rhs
              lhs
              arg 1
              arg 1
              equals x * γ (x⁻¹ * y) (n + 1) =>

                rw [mul_assoc, mul_left_cancel_iff]
                simp [γ, s]
                -- TODO - we can probably use hn instead of this case split
                by_cases n_add_lt: (n) < (word_norm_prod_self (x⁻¹ * y)).choose.length
                .
                  simp [n_add_lt]
                  rw [List.take_add_one]
                  simp
                  rw [getElem?_pos]
                  . simp
                  . grind
                .
                  simp [n_add_lt]
                  rw [List.take_add_one]
                  simp
                  rw [getElem?_neg]
                  . simp
                  . grind
          . positivity
        . positivity
      . simp [dist, WordDist, word_norm_one]

    simp_rw [sub_sq_comm]
    grw [sum_le_delta]
    rw [mul_comm]
    simp

  conv at f_sub_le =>
    intro x
    rw [Real.le_sqrt (by
      simp
    ) (by
      positivity
    )]
  grw [Finset.sum_le_sum (h := fun x hx => f_sub_le x)]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product']
  rw [← Finset.mul_sum]
  rw [inv_mul_le_iff₀ (by norm_cast; simp; simp [B_r]; grind)]
  conv at diff_le_delta_sum =>
    intro x y hx hy
    rw [Real.le_sqrt (by simp) (by
      simp [δ_f, deriv_sq_R];
      positivity
    )]
  simp_rw [sq_abs] at diff_le_delta_sum
  grw [Finset.sum_le_sum (h := fun a ha => diff_le_delta_sum a.2 a.1 (by
    simp at ha
    simp [B_r]
    simp [B_r] at ha
    grind
  )
  (by
    grind
  ))]
  simp_rw [← Finset.mul_sum]
  rw [mul_comm]
  rw [← le_div_iff₀ (by simp; grind)]
  rw [Finset.sum_product]
  simp only []
  rw [Finset.sum_comm]
  -- TODO - use gcongr here
  grw [Finset.sum_le_sum (g := fun z => ∑ x ∈ B_r (2*R - 2), ∑ i ∈ Finset.range (WordNorm x), δ_f (z * γ x i))]
  .
    rw [Finset.sum_comm]
    grw [Finset.sum_le_sum (h := gamma_sum)]
    simp [δ_f]
    have b_card_ne : #(B_r (↑R - 1)) ≠ 0 := by
      simp [B_r]
      exact Set.ncard_ne_zero_of_mem (a := 1) (by simp; grind) (finite_closed_ball 1 _)
    have b_card_two_ne: #(B_r (2 * (↑R - 1))) ≠ 0 := by
      simp [B_r]
      exact Set.ncard_ne_zero_of_mem (a := 1) (by simp; grind) (finite_closed_ball 1 _)
    field_simp
    norm_num
    conv =>
      lhs
      rhs
      arg 1
      arg 1
      equals ↑(R*3 - 1) =>
        rw [Nat.cast_sub]
        simp
        grind
    grw [double_ball_sum]
    .
      norm_cast

      have four_le: (4: ℝ) ≤ 8 := by
        grind
      grw [four_le]
      simp [deriv_sq_R]
      ring
      simp
      simp [deriv_sq_R]
      positivity
    . simp
      grind
    . intro g
      simp [deriv_sq_R]
      positivity

  . intro a ha
    rw [Finset.sum_comp (g := fun y => a⁻¹ * y) (f := fun x => ∑ x_1 ∈ Finset.range (WordNorm (x)), δ_f (a * γ (x) x_1))]
    grw [Finset.sum_le_sum_of_subset_of_nonneg (t := B_r (2*R - 2))]
    .
      simp_rw [inv_mul_eq_iff_eq_mul]
      simp_rw [Finset.card_filter]
      simp
      apply Finset.sum_le_sum
      intro x hx
      split_ifs
      . simp
      . simp [δ_f, deriv_sq_R]
        positivity
    .
      rw [Finset.image_subset_iff]
      intro x hx
      simp [B_r, dist, WordDist_one]
      simp [B_r, dist, WordDist_one] at ha hx
      grw [word_norm_mul_le]
      rw [← word_norm_inv]
      simp
      grw [ha, hx]
      grind
    .
      intros
      simp [δ_f, deriv_sq_R]
      positivity

lemma sum_B_r_inv (r: ℝ) (g: G → ℝ): ∑ x ∈ B_r r, g x⁻¹ = ∑ x ∈ B_r r, g x := by
  apply Finset.sum_nbij' (i := fun x => x⁻¹) (j := fun x => x⁻¹) <;>
    simp +contextual [mem_B_r_inv]

lemma f_avg_inv (r: ℝ) (f: G → ℝ): f_avg r (fun y => f y⁻¹) = f_avg r f := by
  unfold f_avg
  rw [show (finite_closed_ball (1: G) r).toFinset = B_r r from rfl, sum_B_r_inv]

-- Theorem 3.20, restated for the *left* Cayley graph. Rather than mirroring the (long) proof of
-- `poincare_inequality`, we conjugate it by the inversion `x ↦ x⁻¹`: this is a bijection of every
-- `B_r r` (`mem_B_r_inv`) and carries `deriv_sq_R` to `deriv_sq` (`deriv_sq_R_inv_comp`).
lemma poincare_inequality_left (R: ℕ) (f: G → ℝ): ∑ x ∈ (B_r (R - 1)), |f x - (f_avg (R - 1) f)|^2 ≤
    16 * R^2 * #S * (#(B_r (2 * R - 2))) / #(B_r (R - 1)) * ∑ x ∈ (B_r (3 * R)), deriv_sq f x := by
  have poincare := poincare_inequality R (fun y => f y⁻¹)
  rw [f_avg_inv] at poincare
  rw [show (∑ x ∈ B_r ((R: ℝ) - 1), |f x⁻¹ - f_avg ((R: ℝ) - 1) f| ^ 2)
      = ∑ x ∈ B_r ((R: ℝ) - 1), |f x - f_avg ((R: ℝ) - 1) f| ^ 2 from
    sum_B_r_inv _ (fun x => |f x - f_avg ((R: ℝ) - 1) f| ^ 2)] at poincare
  rw [show (∑ x ∈ B_r (3 * (R: ℝ)), deriv_sq_R (fun y => f y⁻¹) x)
      = ∑ x ∈ B_r (3 * (R: ℝ)), deriv_sq f x from by
    rw [← sum_B_r_inv (3 * (R: ℝ)) (fun x => deriv_sq f x)]
    exact Finset.sum_congr rfl (fun x _ => deriv_sq_R_inv_comp f x)] at poincare
  exact poincare

lemma lemma_3_25_poincare (data: GoodScalesData b) (j: (X_j data)) (f: G → ℝ): ∑ x ∈ (B_c_r j (R_1 data )), |f x - (f_avg_c j (R_1 data ) f)|^2 ≤
    16 * (R_1 data + 1)^2 * #S * (Real.exp (a data.d)) * ∑ x ∈ (B_c_r j (3 * (R_1 data + 1))), deriv_sq f x := by

  have R_1_pos: 0 < R_1 data := by
    simp [R_1]

  -- `deriv_sq` is invariant under right translation, and `B_c_r j r` is the right translate
  -- `B_r r * j`, so the left-handed Poincaré inequality is the one that transfers here.
  have poincare := poincare_inequality_left (R_1 data + 1) (f ∘ (fun g => g * j.val))

  simp at poincare
  rw [← Finset.sum_image (f := fun x => ((f (x)) - f_avg (↑(R_1 data)) (f ∘ fun g ↦ g * j)) ^ 2) (by simp)] at poincare
  conv at poincare =>
    lhs
    arg 1
    equals B_c_r j ((R_1 data) ) =>
      rw [B_c_r_eq_smul]
      rw [← Finset.image_smul]
      simp

  conv at poincare =>
    lhs
    arg 2
    intro x
    arg 1
    rhs
    equals f_avg_c j ((R_1 data) ) f =>
      simp [f_avg_c, f_avg]
      rw [B_c_r_eq_smul]
      rw [← Finset.image_smul]
      rw [Finset.sum_image]
      .
        simp
        left
        simp [B_r]
      . simp

  simp_rw [sq_abs]
  grw [poincare]
  clear poincare

  have vol_frac_le: ↑(#(B_r (2 * (↑(R_1 data) + 1) - 2))) / ↑(#(B_r ↑(R_1 data))) ≤ Real.exp (a data.d) := by


    rw [← Real.log_le_iff_le_exp]
    . rw [Real.log_div]
      .


        rw [card_B_r_eq]
        conv =>
          lhs
          arg 1
          arg 1
          arg 1
          arg 1
          arg 1
          equals ↑(2 * ((R_1 data) + 1) - 2) =>
            simp
        rw [card_B_r_eq]
        grw [log_card_pow_sub_le (b := b) (k := (GoodScales data).i_1 + 1) (j := (GoodScales data).i_1)]
        .
          grw [(GoodScales data).first_h_i]
        .
          apply (GoodScales data).i_1_ge
        . simp
        . simp
          grind
        . simp
          have h_i_1 := (GoodScales data).i_1_ge
          simp [i₀, R'] at h_i_1
          simp [R_1]
          ring
          grind
        .
          simp [R_1]
      . simp only [B_r, Set.toFinite_toFinset, ne_eq, Nat.cast_eq_zero]
        apply Finset.card_ne_zero_of_mem (a := 1)
        simp [R_1]
      . simp only [B_r, Set.toFinite_toFinset, ne_eq, Nat.cast_eq_zero]
        apply Finset.card_ne_zero_of_mem (a := 1)
        simp [R_1]
    . apply mul_pos
      . simp only [B_r, Set.toFinite_toFinset]
        norm_cast
        rw [Finset.card_pos]
        use 1
        simp [R_1]
      .
        simp [-Set.toFinset_card]
        use 1
        simp [B_r, R_1]
  .
    rw [mul_div_assoc]
    norm_num
    grw [vol_frac_le]
    .

      conv =>
        lhs
        rhs
        equals  ∑ x ∈ B_c_r j (3 * ↑(R_1 data + 1)), deriv_sq f x =>

          rw [B_c_r_eq_smul]
          rw [← Finset.image_smul]
          rw [Finset.sum_image (by simp)]
          norm_cast
          apply congrArg
          ext x
          simp [deriv_sq]
          group
      simp
    . simp [deriv_sq]
      positivity

-- Estimating functions relative to cover

end V_Wrapper_Section

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.BoundedDoubling
attribute [-instance] _root_.GeneratesNS.volume_finite_compact _root_.GeneratesNS.volume_mul_left_invariant _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# A subspace with bounded doubling

`exists_bounded_doubling_subspace`, the main output of the `V_Wrapper` section.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false

open scoped Finset
open scoped Pointwise

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped Topology

section V_Wrapper_Section

open V_Wrapper

variable [v_wrapper_inst: V_Wrapper]
include v_wrapper_inst

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

variable {b : Module.Basis ι ℝ V}

set_option maxHeartbeats 2500000 in
lemma exists_bounded_doubling_subspace (data: GoodScalesData b): ∃ U: Submodule ℝ LipschitzH, U ≤ V ∧ dim V ≤ 2 * dim U ∧ ∀ f ∈ U, Q_R (16 * (R_2 data)) f f ≤ Real.exp (2 * (a data.d)) * Q_R ((R_2 data)) f f := by
  classical

  let R := 16 ^ ((GoodScales data).i_2)
  have h_R: R'_ V ≤ ↑R := R'_le_R_2 data

  have q_r_base_pos_def := (Q_R_matrix_pos_def_i₀ b (16 ^ ((GoodScales data).i_2)) (by
    simp [i₀]
    rw [pow_le_pow_iff_right₀]
    . have foo := (GoodScales data).i_2_ge
      simp [i₀] at foo
      exact foo
    . simp
  ))

  have det_succ_pos : 0 < (Q_R_matrix b (16 ^ ((GoodScales data).i_2 + 1))).det :=
    (Q_R_matrix_pos_def b (16 ^ ((GoodScales data).i_2 + 1))
      (le_trans h_R (by simp only [R]; push_cast; exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)))).det_pos

  -- Full (definite) inner product core, registered as a local instance so that
  -- `toNormedAddCommGroup` / `ofCore` pick it up by inference.
  letI Q_R_inner_core: InnerProductSpace.Core ℝ V := {
    inner := fun u v => Q_R R u.val v.val
    conj_inner_symm := by
      simp [Q_R]
      grind
    re_inner_nonneg := by
      simp [Q_R]
      intro a _
      apply Finset.sum_nonneg
      intro x _
      exact mul_self_nonneg _
    add_left := by
      simp
      intro a _ a1 _ a2 _
      simp [Q_R]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
    smul_left := by
      simp
      intro a _ a1 _ r
      simp [Q_R]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    definite := fun x hx => by
      by_contra hne
      exact absurd hx (ne_of_gt (Q_R_pos_on_R' x hne R h_R))
  }

  -- Install the definite Q_R-derived NORM (not just a seminorm) *before* `ofCore`, so the
  -- ambient LipschitzH norm on `↥V` is shadowed and `Q_R_inner` is over this `NormedAddCommGroup`.
  letI Q_R_norm : NormedAddCommGroup ↥V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  -- Also expose the seminorm projection as a *direct* local instance, so it shadows the
  -- ambient `V.seminormedAddCommGroup` (a bare `NormedAddCommGroup` letI does not).
  letI Q_R_seminorm : SeminormedAddCommGroup ↥V := Q_R_norm.toSeminormedAddCommGroup
  letI Q_R_inner : InnerProductSpace ℝ ↥V :=
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ ↥V)

  have norm_eq_q_r : ∀ x : ↥V, ‖x‖ = Real.sqrt (Q_R R x x) := fun _ => rfl
  have norm_sq_eq_q_r : ∀ x : ↥V, ‖x‖^2 = (Q_R R x x) := by
    intro x
    rw [norm_eq_q_r]
    rw [Real.sq_sqrt]
    simp [Q_R]
    simp_rw [← pow_two]
    positivity
  have inner_eq_q_r  : ∀ x y : ↥V, inner ℝ x y = Q_R R x y := fun _ _ => rfl

  obtain ⟨v_orthogonal_orig, v_orthogonal_orig_eval⟩ := LinearMap.BilinForm.exists_orthogonal_basis (Q_R_lin_symm V R)
  let v_orthonormal := v_orthogonal_orig.unitsSMul (fun a => Units.mk0 ‖v_orthogonal_orig a‖⁻¹ (by
    simp
    exact Module.Basis.ne_zero v_orthogonal_orig a
  ))

  let q_r_16_m := (Q_R_lin V (16 * R)).toMatrix₂ v_orthonormal v_orthonormal
  have q_r_16_m_hermitian: q_r_16_m.IsHermitian := Q_R_lin_hermetian v_orthonormal (16 * R)

  let q_r_16_eigen := q_r_16_m_hermitian.eigenvectorBasis.toBasis
  let eigen_basis_V :=  (WithLp.linearEquiv 2 ℝ (Fin (Module.finrank ℝ ↥V) → ℝ)).trans v_orthonormal.equivFun.symm
  let remapped_ortho := Module.Basis.map q_r_16_eigen eigen_basis_V

  let Q_R_ortho := (Q_R_lin V R).toMatrix₂ remapped_ortho remapped_ortho
  have Q_R_ortho_m_hermitian: Q_R_ortho.IsHermitian := Q_R_lin_hermetian remapped_ortho R

  have Q_R_pos: ∀ i, 0 ≤ Q_R ↑R ⇑(v_orthogonal_orig i).val ⇑(v_orthogonal_orig i).val :=
    fun i => Q_R_self_nonneg _ _
  have eval_nonzero: ∀ i, (Q_R_lin V ↑R) (v_orthogonal_orig i) (v_orthogonal_orig i) ≠ 0 := by
    intro i
    simp [Q_R_lin]
    apply ne_of_gt
    apply Q_R_pos_on_R'
    . exact Module.Basis.ne_zero v_orthogonal_orig i
    . exact h_R
  have v_orthonormal_isortho : (Q_R_lin V ↑R).IsOrthoᵢ remapped_ortho := by
    simp [remapped_ortho]
    rw [LinearMap.isOrthoᵢ_def]
    rw [LinearMap.isOrthoᵢ_def] at v_orthogonal_orig_eval
    intro x y hxy
    have x_mem := x.prop
    simp [-Subtype.coe_prop] at x_mem
    simp [eigen_basis_V, v_orthonormal]
    simp_rw [Module.Basis.unitsSMul_apply]
    simp_rw [Units.smul_def]
    simp_rw [map_smul]
    simp
    simp_rw [Finset.mul_sum]
    conv =>
      lhs
      arg 2
      intro i
      rw [Finset.sum_eq_single_of_mem i (by simp) (by
        intro j hj hij
        simp
        right
        right
        right
        right
        -- TODO - why doesn't an 'rw' with this work?
        apply v_orthogonal_orig_eval _ _ hij
      )]

    ring
    simp [norm_eq_q_r]
    conv =>
      lhs
      arg 2
      intro i
      rw [Real.sq_sqrt (by apply Q_R_pos)]
    field_simp
    conv =>
      lhs
      arg 2
      intro i
      rw [mul_div_assoc]
      rhs
      equals ((Q_R_lin V ↑R) (v_orthogonal_orig i)) (v_orthogonal_orig i) / ((Q_R_lin V ↑R) (v_orthogonal_orig i)) (v_orthogonal_orig i) =>
        rfl

    field_simp [eval_nonzero]
    have inner_zero :=  q_r_16_m_hermitian.eigenvectorBasis.inner_eq_zero hxy
    rw [EuclideanSpace.inner_eq_star_dotProduct] at inner_zero
    simp [dotProduct] at inner_zero
    exact inner_zero

  have q_r_lin_remapped_one: ∀ i, ((Q_R_lin V ↑R) (remapped_ortho i)) (remapped_ortho i) = 1 := by
    intro i
    simp [remapped_ortho]
    simp [eigen_basis_V,]
    ring
    field_simp
    simp only [eigen_basis_V, q_r_16_eigen]
    simp
    simp_rw [Finset.mul_sum]
    simp [v_orthonormal]
    rw [LinearMap.isOrthoᵢ_def] at v_orthogonal_orig_eval

    simp_rw [Module.Basis.unitsSMul_apply]
    simp_rw [Units.smul_def]
    simp_rw [map_smul]
    simp

    conv =>
      lhs
      arg 2
      intro i
      rw [Finset.sum_eq_single_of_mem i (by simp) (by
        intro j hj hij
        simp
        right
        right
        right
        right
        -- TODO - why doesn't an 'rw' with this work?
        apply v_orthogonal_orig_eval _ _ hij
      )]

    ring
    simp [norm_eq_q_r]
    conv =>
      lhs
      arg 2
      intro i
      rw [Real.sq_sqrt (by apply Q_R_pos)]
    field_simp
    conv =>
      lhs
      arg 2
      intro i
      rw [mul_div_assoc]
      rhs
      equals ((Q_R_lin V ↑R) (v_orthogonal_orig i)) (v_orthogonal_orig i) / ((Q_R_lin V ↑R) (v_orthogonal_orig i)) (v_orthogonal_orig i) =>
        rfl

    field_simp [eval_nonzero]
    have one_eq: (1: ℝ) = 1^2 := by
      simp
    rw [one_eq, ← OrthonormalBasis.norm_eq_one (q_r_16_m_hermitian.eigenvectorBasis) i]
    rw [EuclideanSpace.real_norm_sq_eq]

  let q_r_v_orthonormal := (Q_R_lin V (R)).toMatrix₂ v_orthonormal v_orthonormal

  have Q_R_v_orthonormal_eq_1: q_r_v_orthonormal = 1 := by
    ext i j
    simp [q_r_v_orthonormal, Matrix.one_apply]
    split_ifs
    .
      rename_i i_eq_j
      rw [i_eq_j]
      simp [v_orthonormal]
      simp [Module.Basis.unitsSMul_apply]
      rw [← mul_assoc, ← pow_two]
      simp
      rw [norm_sq_eq_q_r]
      simp [Q_R_lin]
      apply inv_mul_cancel₀
      apply ne_of_gt
      apply Q_R_pos_on_R'
      . apply Module.Basis.ne_zero
      . exact h_R

    .
      rw [LinearMap.isOrthoᵢ_def] at v_orthogonal_orig_eval
      simp [v_orthonormal]
      simp [Module.Basis.unitsSMul_apply]
      right
      right
      apply v_orthogonal_orig_eval
      grind

  -- TODO - an enormous amount of this should get deduplicated with v_orthonormal_isortho
  have Q_R_ortho_eq_1: Q_R_ortho = 1 := by
    ext i j
    simp [Q_R_ortho, Matrix.one_apply]
    split_ifs
    .
      rename_i i_eq_j
      rw [i_eq_j]
      apply q_r_lin_remapped_one
    .
      rw [LinearMap.isOrthoᵢ_def] at v_orthonormal_isortho
      apply v_orthonormal_isortho
      grind

  let Q_R_16_new_ortho := (Q_R_lin V (16 *R)).toMatrix₂ remapped_ortho remapped_ortho
  have Q_R_16_new_ortho_hermitian: Q_R_16_new_ortho.IsHermitian := Q_R_lin_hermetian remapped_ortho (16 *R)

  have det_Q_R_one: Q_R_ortho.det = 1 := by
    simp [Q_R_ortho_eq_1]

  have det_Q_R_16_ge: 1 ≤ Q_R_16_new_ortho.det := by
    rw [← det_Q_R_one]
    apply matrix_det_montone
    .
      simp [Q_R_ortho]
      apply Matrix.PosDef.of_dotProduct_mulVec_pos (?_)
      .
        intro x hx
        simp [Q_R_matrix]
        conv =>
          rhs
          lhs
          equals (star x) => simp
        rw [star_dotProduct_toMatrix₂_mulVec]
        apply Q_R_pos_on_R'
        . rw [LinearEquiv.map_ne_zero_iff]
          exact hx
        . exact h_R
      . apply Q_R_ortho_m_hermitian
    .
      simp [Q_R_16_new_ortho, Q_R_ortho]
      rw [← map_sub]
      rw [← LinearMap.isPosSemidef_iff_posSemidef_toMatrix]
      apply Q_R_lin_sub_pos_semi_def
      norm_cast
      grind

  have q_r_16_remapped_orthogonal : (Q_R_lin_plain V (16 * R)).IsOrthoᵢ remapped_ortho := by
    simp [remapped_ortho]
    rw [LinearMap.isOrthoᵢ_def]
    rw [LinearMap.isOrthoᵢ_def] at v_orthogonal_orig_eval
    intro x y hxy
    have x_mem := x.prop
    simp [-Subtype.coe_prop] at x_mem
    simp
    rw [apply_eq_dotProduct_toMatrix₂_mulVec (v_orthonormal) (v_orthonormal)]
    simp
    simp [eigen_basis_V]
    have repr_self: ∀ x, (∑ i, fun₀ | i => (q_r_16_eigen x).ofLp i) = (q_r_16_eigen x).ofLp := by
      intro z
      conv =>
        lhs
        arg 2
        intro i
        equals Pi.single i ((q_r_16_eigen z).ofLp i) =>
          simp
          ext a
          rw [Finsupp.single_apply]
          rw [Pi.single_apply]
          have foo := eq_comm (a := i) (b := a)
          simp_rw [foo]

      ext a
      simp

    simp [repr_self]
    unfold q_r_16_eigen
    unfold q_r_16_m
    conv =>
      lhs
      rhs
      lhs
      equals q_r_16_m => rfl

    have tobasis_lp: ∀ x, (q_r_16_m_hermitian.eigenvectorBasis.toBasis x).ofLp = (q_r_16_m_hermitian.eigenvectorBasis x).ofLp := by
      simp
    simp [tobasis_lp]
    rw [Matrix.IsHermitian.mulVec_eigenvectorBasis q_r_16_m_hermitian]
    simp
    right
    conv =>
      lhs
      rhs
      equals star ((q_r_16_m_hermitian.eigenvectorBasis y).ofLp) =>
        simp

    rw [← EuclideanSpace.inner_eq_star_dotProduct]
    apply OrthonormalBasis.inner_eq_zero
    exact hxy.symm

  have new_growth := data.h_growth
  have nonempty_fin: Nonempty (Fin (Module.finrank ℝ ↥V)) := by
    use 0
    apply Module.finrank_pos
  apply growth_bound_basis_change data.d b remapped_ortho at new_growth
  have a_gt := (GoodScales data).second_h_i
  simp [h, f] at a_gt
  rw [Real.log_mul] at a_gt
  .
    have log_pos_first: 0 ≤ Real.log ↑(#(S ^ 16 ^ ((GoodScales data).i_2 + 1))) := by
      apply Real.log_nonneg
      simp
      apply Finset.Nonempty.pow
      simp [S_nonempty]

    have log_second: Real.log ↑(#(S ^ 16 ^ (GoodScales data).i_2)) ≤ Real.log ↑(#(S ^ 16 ^ ((GoodScales data).i_2 + 1))) := by
      apply Real.log_le_log
      . simp
        apply Finset.Nonempty.pow
        simp [S_nonempty]
      . simp
        apply Finset.card_le_card
        apply Finset.pow_subset_pow_right
        . simp [one_mem]
        . grind

    --
    have inner_x_self (x: V) (k: ℝ) (hk: ∀ i ∈ (remapped_ortho.repr x).support, (Q_R_lin_plain V (16 * R) (remapped_ortho i) (remapped_ortho i)) ≤ k * (Q_R_lin_plain V (R) (remapped_ortho i) (remapped_ortho i))) : Q_R_lin_plain V (16 * R) x x ≤ k * Q_R_lin_plain V (R) x x := by
      rw [←  Module.Basis.sum_repr remapped_ortho (u := x)]
      have inner_sum_eq: ∀ i, ∑ i_1, inner ℝ ((remapped_ortho.repr x) i_1 • remapped_ortho i_1) ((remapped_ortho.repr x) i • remapped_ortho i) = inner ℝ ((remapped_ortho.repr x) i • remapped_ortho i) ((remapped_ortho.repr x) i • remapped_ortho i) := by
        intro i
        rw [Finset.sum_eq_single i]
        . intro k hk k_neq
          rw [inner_eq_q_r]
          simp [map_smul]
          rw [LinearMap.isOrthoᵢ_def] at v_orthonormal_isortho
          specialize v_orthonormal_isortho k i k_neq
          simp [Q_R_lin] at v_orthonormal_isortho
          simp [Q_R]
          simp [Q_R] at v_orthonormal_isortho
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]
          simp_rw [mul_comm ((remapped_ortho.repr x) i)]
          simp_rw [← mul_assoc]
          rw [← Finset.sum_mul]
          simp [v_orthonormal_isortho]
        .
          intro hi
          simp at hi

      have q_r_16_sum_eq: ∀ i, ∑ i_1, Q_R_lin_plain V (16 * R) ((remapped_ortho.repr x) i_1 • remapped_ortho i_1) ((remapped_ortho.repr x) i • remapped_ortho i) = Q_R_lin_plain V (16 * R) ((remapped_ortho.repr x) i • remapped_ortho i) ((remapped_ortho.repr x) i • remapped_ortho i) := by
        intro i
        rw [Finset.sum_eq_single i]
        . intro k hk k_neq
          simp [map_smul]
          rw [LinearMap.isOrthoᵢ_def] at q_r_16_remapped_orthogonal
          specialize q_r_16_remapped_orthogonal k i k_neq
          simp [Q_R_lin_plain] at q_r_16_remapped_orthogonal
          simp [Q_R_lin_plain, Q_R]
          simp [Q_R] at q_r_16_remapped_orthogonal
          right
          right
          simp [q_r_16_remapped_orthogonal]
        .
          intro hi
          simp at hi

      rw [map_sum]
      simp_rw [map_sum]
      simp [Finset.sum_apply]
      conv =>
        rhs
        rhs
        arg 2
        intro i
        rw [Finset.sum_eq_single i (by
          intro k hk k_neq
          simp [map_smul]
          rw [LinearMap.isOrthoᵢ_def] at v_orthonormal_isortho
          right
          specialize v_orthonormal_isortho k i k_neq
          simp [Q_R_lin] at v_orthonormal_isortho
          simp [Q_R_lin_plain, Q_R]
          simp [Q_R] at v_orthonormal_isortho
          simp [v_orthonormal_isortho]
        ) (by
          intro hi
          simp at hi
        )]
      conv =>
        rhs
        rw [←  Module.Basis.sum_repr remapped_ortho (u := x)]

      simp_rw [map_sum]
      simp
      simp_rw [Finset.mul_sum]
      conv =>
        lhs
        arg 2
        intro i
        rw [Finset.sum_eq_single i (by
          intro k hk k_neq
          simp [map_smul]
          rw [LinearMap.isOrthoᵢ_def] at q_r_16_remapped_orthogonal
          specialize q_r_16_remapped_orthogonal k i k_neq
          simp [Q_R_lin_plain] at q_r_16_remapped_orthogonal
          simp [Q_R_lin_plain, Q_R]
          simp [Q_R] at q_r_16_remapped_orthogonal
          right
          right
          simp [q_r_16_remapped_orthogonal]
        ) (by
          intro hi
          simp at hi
        )]

      apply Finset.sum_le_sum
      intro i hi
      by_cases i_mem_inter: i ∈ (remapped_ortho.repr x).support
      .
        conv =>
          lhs
          equals ((Q_R_lin_plain V (16 * ↑R)) (remapped_ortho i)) (remapped_ortho i)  * (remapped_ortho.repr x) i * (remapped_ortho.repr x) i =>
            ring

        conv =>
          rhs
          equals k * ((Q_R_lin_plain V ↑R) (remapped_ortho i)) (remapped_ortho i) * (remapped_ortho.repr x) i * (remapped_ortho.repr x) i =>
            ring

        rw [mul_assoc]
        nth_rw 2 [mul_assoc]
        specialize hk i i_mem_inter
        grw [hk]
        . ring
          simp
        . rw [← pow_two]
          positivity
      .
        simp at i_mem_inter
        simp [i_mem_inter]
    grw [← log_second] at a_gt
    rw [Real.log_mul] at a_gt
    .
      simp at a_gt
      rw [Real.log_rpow] at a_gt
      rw [Real.log_rpow] at a_gt
      rw [← mul_sub] at a_gt
      rw [← Real.log_div] at a_gt
      .

        simp [Q_R_matrix] at a_gt

        let large_basis: Finset _ := { i: Fin (Module.finrank ℝ ↥V) | (Real.exp (2 * (a data.d))) * Q_R_lin V (R) (remapped_ortho i) (remapped_ortho i) < Q_R_lin V (16 * R) (remapped_ortho i) (remapped_ortho i)}
        let small_basis: Finset _ := { i: Fin (Module.finrank ℝ ↥V) | ¬((Real.exp (2 * (a data.d))) * Q_R_lin V (R) (remapped_ortho i) (remapped_ortho i) < Q_R_lin V (16 * R) (remapped_ortho i) (remapped_ortho i))}
        let large_submodule := Submodule.span ℝ ((Finset.image remapped_ortho large_basis) : Set V)
        by_cases dim_small: 2 * dim large_submodule < dim V
        .
          let small_submodule := Submodule.span ℝ ((Finset.image remapped_ortho Finset.univ ) \ (Finset.image remapped_ortho large_basis) : Set V)
          use Submodule.map V.subtype small_submodule
          refine ⟨?_, ?_, ?_⟩
          . apply Submodule.map_subtype_le
          . simp [dim]
            simp [dim] at dim_small
            have large_small_compl: IsCompl large_submodule small_submodule := by
              simp [large_submodule, small_submodule]
              have diff_eq: Set.range ⇑remapped_ortho \ ⇑remapped_ortho '' ↑large_basis = Set.image remapped_ortho small_basis := by
                ext a
                simp [large_basis, small_basis]
                grind
              rw [diff_eq]
              apply LinearIndependent.isCompl_span_image
              . apply Module.Basis.linearIndependent
              . simp
              . apply IsCompl.of_eq
                . simp
                  ext a
                  simp [large_basis, small_basis]
                . simp
                  ext a
                  simp [large_basis, small_basis]
                  grind

            have dim_sum := Submodule.finrank_add_eq_of_isCompl large_small_compl
            rw [eq_comm, add_comm] at dim_sum

            apply Nat.sub_eq_of_eq_add at dim_sum
            rw [← dim_sum]
            rw [Nat.cast_sub (by apply Submodule.finrank_le)]
            rw [mul_sub]
            simp
            rw [le_sub_iff_add_le']
            grw [dim_small]
            ring
            simp
          .
            have all_le: ∀ f ∈ small_submodule, Q_R_lin V (16 * ↑(R_2 data)) f f ≤ Real.exp (2 * a data.d) * Q_R_lin V ↑(R_2 data) f f := by
              intro f hf
              apply inner_x_self
              intro i hi
              simp only [small_submodule, ← Finset.coe_sdiff] at hf
              rw [Submodule.mem_span_finset] at hf
              obtain ⟨g, g_supp, f_eq_g⟩ := hf
              rw [← f_eq_g] at hi
              rw [Finset.sum_sdiff_eq_sub] at hi
              .
                simp at hi
                rw [Finset.sum_image (by simp; apply Module.Basis.injective)] at hi
                rw [Finset.sum_image (by apply (Module.Basis.injective _).injOn)] at hi
                simp at hi
                have i_not_mem: ¬(i ∈ large_basis) := by
                  by_contra!
                  rw [Finset.sum_eq_single_of_mem i this] at hi
                  .
                    rw [Finset.sum_eq_single_of_mem i (by simp)] at hi
                    . simp at hi
                    . intro k hk i_neq
                      simp
                      right
                      simp [Finsupp.single_apply, i_neq]
                  . intro k hk i_neq
                    simp
                    right
                    simp [Finsupp.single_apply, i_neq]

                simp [large_basis] at i_not_mem
                simp [Q_R_lin_plain]
                simp [Q_R_lin] at i_not_mem
                simpa using i_not_mem

              . apply Finset.image_subset_image
                simp
            intro f hf
            simp at hf
            obtain ⟨f_mem_V, hf⟩ := hf
            specialize all_le ⟨_, f_mem_V⟩ hf
            apply all_le

        simp at dim_small
        have basis_change := Q_R_matrix_det_basis_change v_orthonormal b
        obtain ⟨K, k_pos, hK⟩ := basis_change
        simp [Q_R_matrix] at hK
        simp [hK] at a_gt
        field_simp at a_gt
        unfold Q_R_ortho at det_Q_R_one
        have foo := Q_R_v_orthonormal_eq_1
        unfold q_r_v_orthonormal at Q_R_v_orthonormal_eq_1
        simp [R] at Q_R_v_orthonormal_eq_1
        simp [Q_R_v_orthonormal_eq_1] at a_gt

        have q_r_16_eigen_ge_one: ∀ i, (1: ℝ) ≤ (Q_R_lin V (16 * ↑R)) (remapped_ortho i) (remapped_ortho i) := by
          intro i
          simp [Q_R_lin, Q_R]
          grw [← Finset.sum_le_sum_of_subset_of_nonneg (s := (finite_closed_ball 1 R).toFinset)]
          .
            have foo := q_r_lin_remapped_one
            simp [Q_R_lin, Q_R] at foo
            simp [finite_closed_ball]
            rw [foo]
          .
            simp
            apply Metric.closedBall_subset_closedBall
            norm_cast
            grind
          .
            intro i hi _
            rw [← pow_two]
            positivity

        have key_eq: ∀ i, (Q_R_lin V (16 * ↑R)) (remapped_ortho i) (remapped_ortho i) = q_r_16_m_hermitian.eigenvalues i := by
          intro i
          rw [Matrix.IsHermitian.eigenvalues_eq]
          have app_eq := dotProduct_toMatrix₂_mulVec v_orthonormal v_orthonormal (B := (Q_R_lin V (16 ^ ((GoodScales data).i_2 + 1))))
          conv at app_eq =>
            intro x y
            lhs
            lhs
            equals x =>
              ext j
              simp
          conv at app_eq =>
            intro x y
            lhs
            rhs
            rhs
            equals y =>
              ext j
              simp
          simp [star, R]
          conv =>
            rhs
            rhs
            arg 1
            simp [q_r_16_m]
          simp [R]
          simp_rw [← pow_succ']
          rw [app_eq]
          simp [remapped_ortho, eigen_basis_V, q_r_16_eigen]

        have q_r_16_eigen_ge: ∀ i ∈ large_basis, Real.exp (2 * a data.d) * ((Q_R_lin V ↑R) (remapped_ortho i)) (remapped_ortho i) ≤ q_r_16_m_hermitian.eigenvalues i := by
          intro i hi
          rw [← key_eq i]
          simp only [large_basis, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact le_of_lt hi

        conv at a_gt =>
          lhs
          pattern Matrix.det _
          equals q_r_16_m.det =>
            simp [q_r_16_m, R]
            rw [pow_succ']

        rw [Matrix.IsHermitian.det_eq_prod_eigenvalues q_r_16_m_hermitian] at a_gt
        .
          simp at a_gt
          rw [Real.log_prod] at a_gt
          .
            grw [← Finset.sum_le_sum_of_subset_of_nonneg (s := large_basis) (h := by simp)] at a_gt
            .
              grw [← Finset.card_nsmul_le_sum (n := 2 * (a data.d))] at a_gt
              .
                simp [dim, large_submodule] at dim_small
                rw [finrank_span_finset_eq_card] at dim_small
                . rw [Finset.card_image_iff.mpr] at dim_small
                  .
                    rw [← div_le_iff₀'] at dim_small
                    .
                      norm_cast at dim_small
                      conv at dim_small =>
                        lhs
                        equals ↑(Module.finrank ℝ V / 2) =>
                          rw [Nat.cast_div]
                          . grind
                          . apply Even.two_dvd
                            apply v_wrapper_inst.V_even
                          . simp

                      norm_cast at dim_small
                      grw [← dim_small] at a_gt
                      simp [dim] at a_gt
                      rw [Nat.cast_div] at a_gt
                      .
                        have rank_ne: (↑(Module.finrank ℝ ↥V) : ℝ) ≠ 0 := by
                          apply ne_of_gt
                          simp
                          apply Module.finrank_pos
                        field_simp at a_gt
                        grind
                      . apply Even.two_dvd
                        apply v_wrapper_inst.V_even
                      . simp
                      . simp [a]
                        positivity
                      . simp [dim]
                    . simp
                  . apply (Module.Basis.injective _).injOn
                .
                  rw [Finset.coe_image]
                  apply LinearIndepOn.id_image
                  apply Module.Basis.linearIndepOn
              . simp [dim]
              . intro i hi
                rw [Real.le_log_iff_exp_le]
                .

                  grw [← q_r_16_eigen_ge]
                  .
                    simp [q_r_lin_remapped_one]
                  . exact hi
                .
                  apply Matrix.PosDef.eigenvalues_pos
                  apply Matrix.PosDef.of_dotProduct_mulVec_pos (?_)
                  .
                    intro x hx
                    simp [Q_R_matrix]
                    conv =>
                      rhs
                      lhs
                      equals (star x) => simp
                    rw [star_dotProduct_toMatrix₂_mulVec]
                    apply Q_R_pos_on_R'
                    . rw [LinearEquiv.map_ne_zero_iff]
                      exact hx
                    . grw [h_R]
                      simp [R]
                  . exact q_r_16_m_hermitian
            . simp [dim]
            . intro i hi i_not_mem
              rw [← key_eq i]
              exact Real.log_nonneg (q_r_16_eigen_ge_one i)
          . intro i
            simp
            apply ne_of_gt
            apply Matrix.PosDef.eigenvalues_pos
            apply Matrix.PosDef.of_dotProduct_mulVec_pos (?_)
            . intro x hx
              simp [Q_R_matrix]
              conv =>
                rhs
                lhs
                equals (star x) => simp
              rw [star_dotProduct_toMatrix₂_mulVec]
              apply Q_R_pos_on_R'
              . rw [LinearEquiv.map_ne_zero_iff]
                exact hx
              . grw [h_R]
                simp [R]
            . exact q_r_16_m_hermitian

      . exact det_succ_pos.ne'
      . exact q_r_base_pos_def.det_pos.ne'
      . exact q_r_base_pos_def.det_pos
      . exact det_succ_pos
    . simp
      have foo := S_nonempty
      grind
    . exact (Real.rpow_pos_of_pos q_r_base_pos_def.det_pos _).ne'
  . simp
    have foo := S_nonempty
    grind
  . exact (Real.rpow_pos_of_pos det_succ_pos _).ne'

end V_Wrapper_Section

-- Theorem 3.23
-- Todo - is the better way to declare theorem_3_23 so that the constant is not allowed to depend on V?

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BooleanPartitionMaps
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Evaluation and split refinement maps for finite Boolean partitions -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
variable {X I : Type} (a : I → X → Bool)

def booleanPartitionEvaluation (s : Finset I) :
    booleanPartitionStage a s ⟶ booleanStepRepresentation a :=
  subsingletonGroupRepHom {
    toFun v := ⟨fun x => v (booleanPartitionPoint a s x), s, by
      intro x y hxy
      apply congrArg v
      apply Subtype.ext
      funext i
      exact hxy i i.property⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MixedWordIdeal
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mixed-word ideal used by the cone quotients -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- Bracketing a mixed word with an arbitrary word still gives a mixed word;
linearity extends this to the full generated algebra. -/
theorem mixedWordSpan_lie (X : I → L) (outside : I → Prop)
    (hgen : LieSubalgebra.lieSpan ℝ L (range X) = ⊤)
    (x y : L) (hy : y ∈ mixedWordSpan X outside) :
    ⁅x, y⁆ ∈ mixedWordSpan X outside := by
  have hx : x ∈ Submodule.span ℝ (range (evalBracketWord X)) := by
    rw [span_evalBracketWord, hgen]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, hv, rfl⟩ := hy
      exact eval_mixed_mem_span X outside (w := u * v) (Or.inr hv)
    | zero => simpa only [lie_zero] using (mixedWordSpan X outside).zero_mem
    | add y z _ _ hy hz =>
      simpa only [lie_add] using (mixedWordSpan X outside).add_mem hy hz
    | smul r y _ hy =>
      simpa only [lie_smul] using (mixedWordSpan X outside).smul_mem r hy
  | zero => simpa only [zero_lie] using (mixedWordSpan X outside).zero_mem
  | add x z _ _ hx hz =>
    simpa only [add_lie] using (mixedWordSpan X outside).add_mem hx hz
  | smul r x _ hx =>
    simpa only [smul_lie] using (mixedWordSpan X outside).smul_mem r hx

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialModelRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A faithful finite-dimensional representation in polynomial coordinates -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n : ℕ} (b : Module.Basis (Fin n) ℝ L)

def polynomialModelCoordinate (i : Fin n) (x : L) : ℝ := b.repr x i

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanGenerators
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The subalgebra generated by nonzero roots

The subalgebra generated by the nonzero root spaces is already an ideal.
Thus taking the ideal generated by them in the Cartan construction does not
enlarge the subgroup that must later be integrated.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
/-- The actual generated subalgebra equals the ideal used in the model. -/
theorem cartanRootSubalgebra_eq_ideal [FiniteDimensional ℝ L]
    {n : ℕ} (T : TriangularAdjoint L n) :
    (cartanRootSubalgebra H).toSubmodule = (cartanRootIdeal H).toSubmodule := by
  apply le_antisymm
  · change cartanRootSubalgebra H ≤ (cartanRootIdeal H).toLieSubalgebra
    apply LieSubalgebra.lieSpan_le.mpr
    exact LieSubmodule.subset_lieSpan
  · let I : LieIdeal ℝ L :=
      { (cartanRootSubalgebra H).toSubmodule with
        lie_mem := by intro x y hy; exact cartanRootSubalgebra_ideal H T x y hy }
    change cartanRootIdeal H ≤ I
    apply LieSubmodule.lieSpan_le.mpr
    exact LieSubalgebra.subset_lieSpan

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_WordBoxComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparing boxes with varying maximizing word bases

Only the target basis needs to maximize its costs. A small change in the
costs of the finite word list introduces exactly its exponential error.
-/

noncomputable section
namespace PolycyclicRecognition

open Module Filter
open scoped Topology

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

omit [FiniteDimensional ℝ L] in
/-- A uniform basis-change bound for all cost functions. -/
theorem exists_word_box_comparison_constant
    (X : I → L) (S : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (cost newCost : S → ℝ)
      (β γ : WordBasisSelections X S),
      IsMaximizingColumnBasis (wordListCoordinates X S b₀) cost β.val →
      ∀ {r ε : ℝ}, 0 ≤ r → (∀ w, newCost w ≤ cost w + ε) → ∀ v : L,
        ‖(exponentialRescaleBasis (WordBasisSelections.basis X S β)
          (fun j => cost (β.val j)) r).equivFun v‖ ≤
        D * Real.exp (ε * r) *
          ‖(exponentialRescaleBasis (WordBasisSelections.basis X S γ)
            (fun j => newCost (γ.val j)) r).equivFun v‖ := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_normalized_coordinate_bound (wordListCoordinates X S b₀)
  refine ⟨(finrank ℝ L : ℝ) * C, mul_nonneg (Nat.cast_nonneg _) hC, ?_⟩
  intro cost newCost β γ hβ r ε hr hcost v
  let b := exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun j => cost (β.val j)) r
  let b' := exponentialRescaleBasis (WordBasisSelections.basis X S γ)
    (fun j => newCost (γ.val j)) r
  have hword (w : S) : ‖b.equivFun (Real.exp (r * cost w) • evalBracketWord X w)‖ ≤ C := by
    apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro j
    change |b.repr (Real.exp (r * cost w) • evalBracketWord X w) j| ≤ C
    rw [repr_exponentialRescaleBasis_smul]
    have hh := hb cost β.val hβ w j r hr
    rw [columnCoordinates_eq_wordBasis_repr X S b₀ β w] at hh
    exact hh
  have hnew (w : S) :
      ‖b.equivFun (Real.exp (r * newCost w) • evalBracketWord X w)‖ ≤
        Real.exp (ε * r) * C := by
    have he : Real.exp (r * newCost w) • evalBracketWord X w =
        Real.exp (r * (newCost w - cost w)) •
          (Real.exp (r * cost w) • evalBracketWord X w) := by
      rw [smul_smul, ← Real.exp_add]
      congr 2
      ring
    rw [he, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul _ (hword w) (norm_nonneg _) (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (hcost w) hr]
  have hbase (j : Fin (finrank ℝ L)) : ‖b.equivFun (b' j)‖ ≤ Real.exp (ε * r) * C := by
    have he : b' j = Real.exp (r * newCost (γ.val j)) • evalBracketWord X (γ.val j) := by
      have hj := WordBasisSelections.eval_words X S γ j
      change evalBracketWord X (γ.val j) = _ at hj
      rw [hj]
      simp only [b', exponentialRescaleBasis, Basis.unitsSMul_apply,
        Units.smul_def, Units.val_mk0]
    rw [he]
    exact hnew (γ.val j)
  change ‖b.equivFun v‖ ≤ _ * ‖b'.equivFun v‖
  conv_lhs => rw [← b'.sum_repr v]
  rw [map_sum]
  calc
    _ ≤ ∑ j, ‖b.equivFun (b'.repr v j • b' j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin (finrank ℝ L), ‖b'.equivFun v‖ * (Real.exp (ε * r) * C) := by
      apply Finset.sum_le_sum
      intro j _
      rw [map_smul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (norm_le_pi_norm (b'.equivFun v) j) (hbase j)
        (norm_nonneg _) (norm_nonneg _)
    _ = ((finrank ℝ L : ℝ) * C) * Real.exp (ε * r) * ‖b'.equivFun v‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanWeightDilation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact dilations of generalized Cartan weight spaces

Scalar multiplication by `exp (χ h)` on every generalized root space defines
an actual Lie automorphism. The nilpotent parts of the Cartan action do not
enter this construction. These are the exact weight dilations used in the
box-translation argument.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule
open scoped DirectSum

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

include T

set_option maxHeartbeats 1000000 in
/-- Exact dilations preserve the nilpotent ideal generated by nonzero roots. -/
theorem cartanWeightDilation_mem_ideal (h : H) {x : L} (hx : x ∈ cartanRootIdeal H) :
    cartanWeightDilation T H h x ∈ cartanRootIdeal H := by
  have heq := cartanRootSubalgebra_eq_ideal H T
  have hx' : x ∈ cartanRootSubalgebra H := by
    change x ∈ (cartanRootSubalgebra H).toSubmodule
    rw [heq]
    exact hx
  suffices cartanWeightDilation T H h x ∈ cartanRootSubalgebra H by
    change cartanWeightDilation T H h x ∈ (cartanRootIdeal H).toSubmodule
    rwa [← heq]
  clear hx
  change x ∈ LieSubalgebra.lieSpan ℝ L
    {v | ∃ χ : Weight ℝ H L, χ.IsNonZero ∧ v ∈ rootSpace H χ} at hx'
  induction hx' using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
    obtain ⟨χ, hχ, hx⟩ := hx
    rw [cartanWeightDilation_apply, cartanWeightScale_apply_root T H h χ hx]
    exact (cartanRootSubalgebra H).smul_mem _ (LieSubalgebra.subset_lieSpan ⟨χ, hχ, hx⟩)
  | zero => simp only [map_zero]; exact (cartanRootSubalgebra H).zero_mem
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (cartanRootSubalgebra H).add_mem hx hy
  | smul a x _ hx =>
    rw [map_smul]
    exact (cartanRootSubalgebra H).smul_mem a hx
  | lie x y _ _ hx hy =>
    rw [LieEquiv.map_lie]
    exact (cartanRootSubalgebra H).lie_mem hx hy

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightedBasisComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparing any selected word box with a maximizing word box -/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped BigOperators

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

omit [FiniteDimensional ℝ L] in
/-- A fixed constant controls every selected word basis in every maximizing
basis, at all nonnegative scales. Thus a varying basis in a sampling row
can be replaced by the fixed maximizing basis without an exponential loss. -/
theorem exists_uniform_rescaled_basis_comparison
    (X : I → L) (S : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (cost : S → ℝ) (β γ : WordBasisSelections X S),
      IsMaximizingColumnBasis (wordListCoordinates X S b₀) cost β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ x : L,
        ‖(exponentialRescaleBasis (WordBasisSelections.basis X S β)
          (fun j => cost (β.val j)) r).equivFun x‖ ≤
        C * ‖(exponentialRescaleBasis (WordBasisSelections.basis X S γ)
          (fun j => cost (γ.val j)) r).equivFun x‖ := by
  obtain ⟨D, hD, hcompare⟩ := exists_word_box_comparison_constant X S b₀
  refine ⟨1 + D, by linarith, ?_⟩
  intro cost β γ hβ r hr x
  have h := hcompare cost cost β γ hβ hr (ε := 0) (by intro w; simp) x
  simp only [zero_mul, Real.exp_zero, mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBasisComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform comparison with a maximizing Cartan basis -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- Replacing a selected word basis by a maximizing one costs a fixed
multiplicative factor in the radius, uniformly in the template and scale. -/
theorem exists_groupBox_basis_comparison
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (E : Set W) (β γ : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ (r : ℝ), 0 ≤ r → ∀ {N : Type*} (exp : cartanRootIdeal H → N) (R : ℝ),
        M.groupBox T hunimod eW exp E γ r R ⊆
          M.groupBox T hunimod eW exp E β r (C * R) := by
  obtain ⟨C, hC, hcompare⟩ := exists_uniform_rescaled_basis_comparison M.letter M.wordList b₀
  refine ⟨C, hC, ?_⟩
  intro E β γ hβ r hr N exp R g hg
  obtain ⟨v, hv, hnorm⟩ := hg
  refine ⟨v, hv, ?_⟩
  exact (hcompare (M.boxCost T hunimod eW E) β γ hβ r hr v).trans
    (mul_le_mul_of_nonneg_left hnorm (zero_le_one.trans hC))

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Representation
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The representation of `G` on `W`

The space `W = LipschitzH ⧸ ConstF`, the representation `GRep` / `GRepW` of `G` on it, and the
fact that it preserves the quotient norm.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
-- TODO - vscode stops reporting underlines if there are too many total underlines / gutter messages
-- I've disabled some failing lints for now so that error underlines still sho up
set_option linter.style.commandStart false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped RealInnerProductSpace

-- `LipschitzH_seminorm` and `LipschitzH_normed` are public instances in
-- `Gromov.LipschitzNorm`, so they are already available here.

-- The lift of LipschitzSemiNorm to W, using a proof that LipschitzSemiNorm doesn't depend on the choice representative
-- (adding a constant to a Lipschitz function doesn't change its Lipschitz constant)


lemma lipschitz_norm_const (z: ℝ): LipschitzSemiNorm (ConstLipschitzH z) = 0 := by
  unfold LipschitzSemiNorm
  have zero_mem: 0 ∈ { k: NNReal | LipschitzWith k (ConstLipschitzH z).toFun } := by
    simp [ConstLipschitzH]
  have my_le := csInf_le (by simp) zero_mem
  exact nonpos_iff_eq_zero.mp my_le


lemma constf_eq_null: (ConstF : Set (LipschitzH)) = nullAddSubgroup (LipschitzH) := by
  unfold ConstF
  unfold nullAddSubgroup
  ext f
  simp
  refine ⟨?_, ?_⟩
  .
    intro hf
    obtain ⟨z, hz⟩ := hf
    rw [← hz]
    simp [norm]
    apply lipschitz_norm_const
  .
    intro hf
    simp [norm, LipschitzSemiNorm] at hf
    have lipschitz_zero := lipschitz_attains_norm f (f.lipschitz)
    simp [LipschitzSemiNorm] at lipschitz_zero
    rw [hf] at lipschitz_zero
    simp [LipschitzWith] at lipschitz_zero
    use (f.toFun 1)
    simp [ConstLipschitzH]
    ext a
    simp
    apply lipschitz_zero

@[expose]
instance const_isClosed: IsClosed (ConstF : Set (LipschitzH)) := by
  rw [constf_eq_null]
  exact isClosed_nullAddSubgroup


set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 9000000


set_option synthInstance.maxHeartbeats 500000


end GeneratesNS
end


