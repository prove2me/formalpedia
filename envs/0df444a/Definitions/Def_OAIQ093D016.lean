-- Prove2me | Definitions.Def_OAIQ093D016
-- name    : OAIQ093D016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:33:41.953789+00:00
-- url     : https://prove2.me/theorems/c5848ac2-a2ae-45b8-b419-a76e10724291
-- title:
--   Definitions bundle OAIQ093D016 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 42 declarations of OpenAI's Lean: 24 definitions, 1 inductive type or structure, 4 instances and 13 theorems. The definitions and types are `GeneratesNS.GRepW`, `GeneratesNS.G_SPolyData`, `GeneratesNS.S_n_ker_phi`, `GeneratesNS.e_i_with_gamma`, `GeneratesNS.isembedding_units_val`, `GeneratesNS.ker_S`, `GeneratesNS.ker_generates`, `GeneratesNS.map_equiv_S_data`, `GeneratesNS.map_range_S_data`, `GeneratesNS.rho_g`, `OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.fixedBasis`, `OAI.PolycyclicRecognition.CartanWordModel.BoxProbeChains.dilate`, `OAI.PolycyclicRecognition.CartanWordModel.BoxProbeChains.inSamplingBox`, `OAI.PolycyclicRecognition.CartanWordModel.ConeIdealBases`, `OAI.PolycyclicRecognition.CartanWordModel.IsMaximizingConeIdealBasis`, `OAI.PolycyclicRecognition.CartanWordModel.PolarConeModelInputs`, `OAI.PolycyclicRecognition.CartanWordModel.coneIdealBox`, `OAI.PolycyclicRecognition.CartanWordModel.coneIdealBoxBasis`, `OAI.PolycyclicRecognition.CartanWordModel.coneIdealWordBound`, `OAI.PolycyclicRecognition.CartanWordModel.coneIdealWordList`, `OAI.PolycyclicRecognition.CartanWordModel.coneMixedVector`, `OAI.PolycyclicRecognition.CartanWordModel.coneProjection`, `OAI.PolycyclicRecognition.CartanWordModel.coneWordIdeal`, `OAI.PolycyclicRecognition.cartanIdealWeightDilation`, `OAI.PolycyclicRecognition.mixedWordIdeal`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `GrowthZero`, `Lemma326`, `PolycyclicRecognition_Algebra_ComplexFactorParameters`, `PolycyclicRecognition_Algebra_ConeIdealGroup`, `PolycyclicRecognition_Algebra_MixedWordBasis`, `PolycyclicRecognition_Algebra_MixedWordIdeal`, `PolycyclicRecognition_Analysis_ConeIdealBoxCalculus`, `PolycyclicRecognition_Analysis_MixedWordBoxModel`, `PolycyclicRecognition_Geometry_CartanAllowedProbeChains`, `PolycyclicRecognition_Geometry_CartanBoxDilation`, `PolycyclicRecognition_Geometry_CartanConeGroup`, `PolycyclicRecognition_Geometry_CartanConeIdeal`, `PolycyclicRecognition_Geometry_CartanDilatedProbeChains`, `PolycyclicRecognition_Geometry_CartanNeighborRowBasis`, `PolycyclicRecognition_Geometry_CartanPolarConeModels`, `PolycyclicRecognition_Geometry_CartanProbeChainDilation`, `PolycyclicRecognition_Geometry_CartanWeightDilation`, `Representation`, `Theorem323`, `Theorem38`, `ThreeTwoGenerates`.
--
--   **Imports.** It imports the published bundle `Def_PolycyclicRecognition`; the bundles `OAIQ093D012`, `OAIQ093D013` and `OAIQ093D026` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ093D019` and `OAIQ093D020`; the statements `GeneratesNS.e_i_and_gamma_generates_G`, `GeneratesNS.rho_g_case_finite`, `GeneratesNS.three_two_kernel_poly_growth`, `OAI_PolycyclicRecognition_CartanWordModel_exists_published_adjacent_scale_labels`, `OAI.PolycyclicRecognition.CartanWordModel.exists_published_sublinear_height`, `OAI_PolycyclicRecognition_CartanWordModel_exists_sequence_path_quotient_restriction`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_identical_neighbor_profiles`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_affine_mean_approximation`, `OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_published_allowed_chain_concentration`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_basepoint_comparison`, `OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_published_bounded_height`, `OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_published_chain_concentration`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_profile_estimates`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_raw_chain_concentration`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_suffix_concentration`, `OAI_PolycyclicRecognition_CartanWordModel_uniform_affine_bound_of_published_inputs_and_sublinear`, `OAI.PolycyclicRecognition.CartanWordModel.uniform_normalized_affine_bound_of_published_inputs_and_sublinear` and `OAI.PolycyclicRecognition.exists_uniform_sampled_contact_bridge`; the proofs of `GeneratesNS.e_i_and_gamma_generates_G`, `GeneratesNS.exists_theorem_3_1_input`, `GeneratesNS.growth_const_pos`, `GeneratesNS.growth_exponent_pos`, `GeneratesNS.rho_g_case_finite`, `GeneratesNS.theorem_3_1`, `GeneratesNS.three_two_S_n_generates`, `GeneratesNS.three_two_ker_fg`, `GeneratesNS.three_two_kernel_poly_growth`, `OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.exists_fixed_basis_radius`, `OAI_PolycyclicRecognition_CartanWordModel_exists_basepoint_geometry_of_factor_bounds`, `OAI_PolycyclicRecognition_CartanWordModel_exists_metric_basepoint_comparison`, `OAI_PolycyclicRecognition_CartanWordModel_exists_published_adjacent_scale_labels`, `OAI.PolycyclicRecognition.CartanWordModel.exists_published_sublinear_height`, `OAI_PolycyclicRecognition_CartanWordModel_exists_sequence_path_quotient_restriction`, `OAI_PolycyclicRecognition_CartanWordModel_exists_small_metric_cartan_factor_bound`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_affine_mean_approximation`, `OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_published_allowed_chain_concentration`, `OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_published_bounded_height`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_profile_estimates`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_raw_chain_concentration`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_suffix_concentration`, `OAI_PolycyclicRecognition_cartan_cocycle_compact_words` and `OAI.PolycyclicRecognition.group_recognition`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D012
import Definitions.Def_OAIQ093D013
import Definitions.Def_OAIQ093D026

section
-- module Solutions.OAIQ093_PR.Lemma326
attribute [-instance] _root_.GeneratesNS.const_isClosed _root_.GeneratesNS.volume_finite_compact _root_.GeneratesNS.volume_mul_left_invariant _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Lemma 3.26 and basis changes

`lemma_3_26_a` together with the behaviour of `Q_R_matrix` and `growth_bound` under a change of
basis.
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
lemma lemma_3_26_a (data: GoodScalesData b) (u: V): Q_R (R_2 data) u u ≤ 2 * (#(S^(R_1 data ))) * ‖(phi data u)‖^2 + C * (Real.exp ((2 * a data.d))) * (R_1 data + 1)^2 * (∑ x ∈ B_r (8 * R_2 data), deriv_sq u x)  := by

  rw [Q_R]
  let b_union := ⋃₀ (B data)
  grw [Finset.sum_le_sum_of_subset_of_nonneg (t := (B_finsets data).biUnion id)]
  .
    grw [Finset.sum_biUnion_le (fun x => mul_self_nonneg ((↑u : LipschitzH) x))]
    .
      have u_bound (x: G) (j: B_finsets data): (u.val x)^2 ≤ 2 * ((u.val x - (phi data u).ofLp j)^2 + ((phi data u).ofLp j)^2) := by
        calc
          _ = |u.val x - ((phi data u).ofLp j) + (phi data u).ofLp j|^2 := by
            simp
          _ ≤ (|u.val x - (phi data u).ofLp j| + |(phi data u).ofLp j|)^2 := by
            grw [abs_add_le]
          _ = _ := by
            rw [add_sq]
          _ ≤ _ := by
            grw [two_mul_le_add_sq]
            simp [sq_abs]
            grind

      rw [← Finset.sum_finset_coe]
      simp_rw [← pow_two]
      simp
      grw [Finset.sum_le_sum (g := fun (j: B_finsets data) => ∑ x ∈ j, 2 * ((u.val x - (phi data u).ofLp j)^2 + ((phi data u).ofLp j)^2))]
      .

        simp_rw [← Finset.mul_sum]
        simp_rw [Finset.sum_add_distrib]
        simp
        have card_j_eq (j: B_finsets data): #j.val = #(S^(R_1 data)) := by
          have hj := j.prop
          simp only [B_finsets] at hj
          simp [-SetLike.coe_mem] at hj
          obtain ⟨x, hx, x_eq⟩ := hj
          rw [← x_eq]
          have foo := B_c_r_eq_smul x (R_1 data )
          simp [B_c_r] at foo
          rw [foo]
          simp

          rw [card_B_r_eq]

        simp [card_j_eq]
        simp_rw [← Finset.mul_sum]
        conv =>
          lhs
          rhs
          rhs
          rhs
          rw [← Finset.univ_eq_attach]
          rw [← EuclideanSpace.real_norm_sq_eq]

        have phi_eq (j : B_finsets data) :
            ((phi data) u).ofLp j = (#(j : Finset G) : ℝ)⁻¹ * ∑ x ∈ (j : Finset G), (u : G → ℝ) x :=
          rfl
        simp_rw [phi_eq]
        have attach_eq := Finset.sum_attach (B_finsets data)
          (fun j => ∑ x ∈ j, ((u : G → ℝ) x - (#j : ℝ)⁻¹ * ∑ y ∈ j, (u : G → ℝ) y) ^ 2)
        beta_reduce at attach_eq
        simp only [show (↑u : LipschitzH).toFun = ⇑(↑u : LipschitzH) from rfl, attach_eq]
        simp only [B_finsets]
        rw [Finset.sum_image]
        .
          rw [mul_add]

          rw [add_comm]
          apply add_le_add
          .
            ring
            simp

          .

            conv =>
              lhs
              rhs
              arg 2
              intro x
              equals ∑ x_1 ∈ B_c_r x (R_1 data ), (u.val.toFun x_1 - (f_avg_c x (R_1 data ) u.val.toFun)) ^ 2 =>
                apply Finset.sum_congr
                . simp [B_c_r]
                . intro y hy
                  simp [f_avg_c, B_c_r, -Set.toFinset_card]
                  conv =>
                    lhs
                    lhs
                    pattern #(Metric.closedBall x (↑(R_1 data) )).toFinset
                    equals #(B_c_r x (R_1 data)) =>
                      simp [B_c_r]
                  rw [B_c_r_eq_smul]
                  simp [B_r]

            conv =>
              lhs
              rhs
              arg 2
              intro x
              arg 2
              intro y
              rw [← sq_abs]
            rw [← Finset.sum_finset_coe]
            simp only [SetLike.coe_sort_coe, Finset.univ_eq_attach]
            grw [Finset.sum_le_sum (h := fun (a : {x // x ∈ (X_j_finite data).toFinset}) _ =>
              lemma_3_25_poincare data ⟨a.val, (X_j_finite data).mem_toFinset.mp a.prop⟩
                (f := u.val.toFun))]

            simp_rw [← Finset.mul_sum]
            have sum_swap: ∑ i ∈ (X_j_finite data).toFinset, ∑ x ∈ B_c_r (i) (3 * (↑(R_1 data) + 1)), deriv_sq (u.val).toFun x = ∑ x ∈ B_r (8 * (R_2 data)), #{ i ∈ (X_j_finite data).toFinset | x ∈ B_c_r (↑i) (3 * (↑(R_1 data) + 1))} * deriv_sq (u.val).toFun x := by
              simp_rw [Finset.card_filter]
              simp_rw [Nat.cast_sum]
              simp_rw [Finset.sum_mul]
              rw [Finset.sum_comm]
              apply Finset.sum_congr
              . simp
              . intro i hi
                have set_eq: B_r (8 * ↑(R_2 data)) ∩ B_c_r i (3 * (↑(R_1 data) + 1)) = B_c_r i (3 * (↑(R_1 data) + 1)) := by
                  simp
                  intro x hx
                  simp [B_c_r] at hx
                  simp [X_j] at hi
                  apply Metric.maximalSeparatedSet_subset at hi
                  simp [B_r]
                  simp at hi
                  grw [dist_triangle _ i]
                  grw [hx, hi]
                  simp [R_1, R_2]

                  rw [two_mul]
                  have i_1_le:  (GoodScales data).i_1 ≤  (GoodScales data).i_2 := by
                    have foo :=  (GoodScales data).i_diff_mem
                    simp at foo
                    grind
                  grw [i_1_le]
                  ring
                  .
                    rw [← le_sub_iff_add_le]
                    ring
                    have i_2_pos := (GoodScales data).i_2_pos
                    have le_one: 1 ≤  (GoodScales data).i_2 := by grind
                    grw [← le_one]
                    .
                      norm_num
                    . simp
                  . simp
                  . simp
                simp
                rw [set_eq]

            rw [Finset.sum_attach (f := fun (i: G) => ∑ x ∈ B_c_r (i) (3 * (↑(R_1 data) + 1)), deriv_sq (u.val).toFun x)]
            rw [sum_swap]

            have card_inter_le (x: G): #({i ∈ (X_j_finite data).toFinset | x ∈ B_c_r i (3 * (↑(R_1 data + 1)) )}) ≤ Real.exp (a data.d) := by
              have foo := log_pack_center_helper data x
              rw [Nat.cast_add]
              simpa using foo

            simp [C]
            simp_rw [← mul_assoc]
            norm_num
            rw [two_mul, Real.exp_add]
            conv =>
              rhs
              equals (32 * ↑(#S) * (Real.exp (a data.d) * (↑(R_1 data) + 1) ^ 2)) * ((Real.exp (a data.d)) * ∑ x ∈ B_r (8 * ↑(R_2 data)), deriv_sq (⇑u.val) x) =>
                ring
            apply mul_le_mul
            . ring
              simp
            .
              grw [Finset.sum_le_sum (g := fun x => Real.exp (a data.d) *  (deriv_sq (u.val).toFun x))]
              .

                rw [← Finset.mul_sum]
                apply le_refl
              . intro i hi
                norm_cast
                norm_cast at card_inter_le
                grw [card_inter_le]
                simp [deriv_sq, ← pow_two]
                positivity

            . simp [deriv_sq, ← pow_two]
              apply Finset.sum_nonneg
              intro i hi
              norm_cast
              positivity
            . positivity

        .
          simp
          have foo := B_ball_injective_on data (R_1 data ) (by simp [R_1]) (by simp)
          intro a ha b hb hab
          specialize foo ha hb (by
            simp
            simp at hab
            exact hab
          )
          exact foo

      . intro j hj
        apply Finset.sum_le_sum
        intro x hx
        apply u_bound

  .
    have cover := B_covers_R2 data
    simp
    intro a ha
    specialize cover ha
    simp [B_finsets]
    simp [B] at cover

    exact cover
  . intros
    rw [← pow_two]
    positivity

end V_Wrapper_Section

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Theorem323
attribute [-instance] _root_.GeneratesNS.const_isClosed _root_.GeneratesNS.volume_finite_compact _root_.GeneratesNS.volume_mul_left_invariant _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Theorem 3.23

`theorem_3_23` and the resulting finite-dimensionality of the space of Lipschitz harmonic
functions.

Root of the Theorem 3.23 hierarchy: importing it pulls in the cutoff inequality, the quadratic
form, the packing argument and the Poincaré inequality.
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

set_option maxHeartbeats 2500000 in
lemma theorem_3_23 (d: ℕ) (hd: 0 < d): ∃ C: ℕ, ∀ v_data: V_Wrapper, growth_bound (V_basis v_data.V) d → (Module.finrank ℝ v_data.V) < C := by
  let w := ⌈Real.logb 16 ((16^4) * #(S) * Real.exp (4 * a (d)))⌉₊
  let C: ℕ := 1 + (⌈2 * Real.exp (w * (a d))⌉₊)
  use C
  intro v_data h_growth

  let data: GoodScalesData (V_basis v_data.V) := {
    w := ⌈Real.logb 16 ((16^4) * #(S) * Real.exp (4 * a (d)))⌉₊
    d := d
    hw := by
      simp
      apply Real.logb_pos
      . simp
      . apply one_lt_mul
        .
          have card_s: 1 ≤ #(S) := by
            simp
            apply S_nonempty
          grw [← card_s]
          simp
          norm_num
        .
          norm_num
          simp [a]
          positivity
    hd := hd
    w_gt := by
      rw [Nat.lt_ceil]
      simp
      rw [Real.lt_logb_iff_rpow_lt]
      .
        have mul_pos: 1 < ↑(#S) * Real.exp (4 * a d) := by
          apply one_lt_mul
          . simp
            apply S_nonempty
          . simp [a]
            positivity
        linarith
      . simp
      . have S_ne: #(S) ≠ 0 := by
          have foo :=  S_card_ne_zero_re
          simpa using foo
        positivity
    h_growth := h_growth
  }

  obtain ⟨U, U_sub_v, hU_dim, bounded_double⟩ := exists_bounded_doubling_subspace data

  let phi_u := (phi data).domRestrict (U.submoduleOf v_data.V)
  have phi_u_inj: Function.Injective phi_u := by
    -- Pinning the module types keeps this rewrite out of the instance diamond on
    -- `↥(U.submoduleOf _)` (`Submodule…addCommMonoid` vs `AddCommGroup.toAddCommMonoid`),
    -- which otherwise only reconciles at a raised `maxSynthPendingDepth`.
    rw [← LinearMap.ker_eq_bot (M := ↥(U.submoduleOf v_data.V))
          (M₂ := EuclideanSpace ℝ ↥(B_finsets data))]
    rw [LinearMap.ker_eq_bot' (M := ↥(U.submoduleOf v_data.V))
          (M₂ := EuclideanSpace ℝ ↥(B_finsets data))]
    intro u hu

    have u_le := lemma_3_26_a data u
    simp [phi_u] at hu
    simp [hu] at u_le

    have u_bound := harmonic_r2_inequality u (by
      have u_prop := u.val.val.harmonic
      simp [Harmonic] at u_prop
      simp [Laplace_b]
      ext a
      simp
      nth_rw 1 [u_prop]
      simp [f_conv_mu]
    ) (4 * R_2 data) (by simp [R_2])
    simp [B_r] at u_le
    conv at u_bound =>
      lhs
      arg 1
      equals (Metric.closedBall 1 (8 * (R_2 data))).toFinset =>
        simp
        ring_nf

    grw [u_bound] at u_le
    .
      have u_double := bounded_double u (by
        exact u.prop
      )
      conv at u_double =>
        lhs
        simp [Q_R]

      simp_rw [← pow_two] at u_double
      grw [Finset.sum_le_sum_of_subset_of_nonneg (t := (finite_closed_ball 1 (16 * (R_2 data))).toFinset)] at u_le
      .
        simp [finite_closed_ball] at u_le
        grw [u_double] at u_le
        .
          by_cases u_zero: u = 0
          . exact u_zero
          .
            have r_pos := R'_pos v_data.V
            have r_ratio_le: (R_1 data + 1) / (4 * R_2 data) ≤ 4 * ((16: ℝ) ^ (-(data.w : ℝ))) := by
              simp [R_1, R_2]
              field_simp
              have i_diff := (GoodScales data).i_diff_mem
              simp at i_diff
              have one_le: (1: ℝ) ≤ 2*(16^((GoodScales data).i_1)) := by
                norm_num
                apply one_le_mul_of_one_le_of_one_le
                . simp
                . rw [one_le_pow_iff_of_nonneg]
                  . simp
                  . simp
                  . simp
                    have h_i := (GoodScales data).i_1_pos
                    grind
              grw [one_le]
              rw [← mul_add]
              rw [← two_mul]
              ring
              rw [← pow_add]
              apply mul_le_mul
              .
                rw [pow_le_pow_iff_right₀]
                . grind
                . simp
              . norm_num
              . simp
              . simp

            conv at u_le =>
              rhs
              equals GeneratesNS.C * Real.exp (2 * a data.d) * (((↑(R_1 data) + 1) / ((↑(4 * R_2 data : ℝ))))^2 * ↑(#S) * (Real.exp (2 * a data.d) * Q_R ↑(R_2 data) ⇑u.val.val ⇑u.val.val)) =>
                ring

            grw [r_ratio_le] at u_le
            ring_nf at u_le
            .
              have le_half: Q_R ↑(R_2 data) ⇑u.val.val ⇑u.val.val ≤ (2: ℝ)⁻¹ * Q_R ↑(R_2 data) ⇑u.val.val ⇑u.val.val := by
                have qr_nonneg : 0 ≤ Q_R ↑(R_2 data) ⇑u.val.val ⇑u.val.val :=
                  Q_R_self_nonneg _ _
                have ha : (0:ℝ) ≤ a data.d := by simp only [a] <;> positivity
                have hE1 : (1:ℝ) ≤ Real.exp (a data.d) := Real.one_le_exp ha
                have hE4 : (1:ℝ) ≤ Real.exp (a data.d) ^ 4 := one_le_pow₀ hE1
                have hEpos : (0:ℝ) < Real.exp (a data.d) := Real.exp_pos _
                have he4 : Real.exp (4 * a data.d) = Real.exp (a data.d) ^ 4 := by
                  rw [← Real.exp_nat_mul]; norm_num
                have he2 : Real.exp (a data.d * 2) = Real.exp (a data.d) ^ 2 := by
                  rw [show a data.d * 2 = 2 * a data.d from by ring, ← Real.exp_nat_mul]; norm_num
                have he2sq : Real.exp (a data.d * 2) ^ 2 = Real.exp (a data.d) ^ 4 := by
                  rw [he2]; ring
                have hS0 : (0:ℝ) < ↑(#S) := by exact_mod_cast Finset.card_pos.mpr S_nonempty
                have hXpos : (0:ℝ) < 16 ^ 4 * ↑(#S) * Real.exp (a data.d) ^ 4 := by positivity
                have h16w : (16:ℝ) ^ 4 * ↑(#S) * Real.exp (a data.d) ^ 4 ≤ (16:ℝ) ^ (↑data.w : ℝ) := by
                  rw [← he4]
                  have hlog : (16:ℝ) ^ Real.logb 16 (16 ^ 4 * ↑(#S) * Real.exp (4 * a data.d))
                      = 16 ^ 4 * ↑(#S) * Real.exp (4 * a data.d) :=
                    Real.rpow_logb (by norm_num) (by norm_num) (by rw [he4]; exact hXpos)
                  have hle : Real.logb 16 (16 ^ 4 * ↑(#S) * Real.exp (4 * a data.d)) ≤ (↑data.w : ℝ) := by
                    have hdef : data.w = ⌈Real.logb 16 (16 ^ 4 * ↑(#S) * Real.exp (4 * a data.d))⌉₊ := rfl
                    rw [hdef]; exact_mod_cast Nat.le_ceil _
                  calc 16 ^ 4 * ↑(#S) * Real.exp (4 * a data.d)
                      = (16:ℝ) ^ Real.logb 16 (16 ^ 4 * ↑(#S) * Real.exp (4 * a data.d)) := hlog.symm
                    _ ≤ (16:ℝ) ^ (↑data.w : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
                have ht0 : (0:ℝ) ≤ (16:ℝ) ^ (-↑data.w : ℝ) := Real.rpow_nonneg (by norm_num) _
                have htX : (16:ℝ) ^ (-↑data.w : ℝ) * (16 ^ 4 * ↑(#S) * Real.exp (a data.d) ^ 4) ≤ 1 := by
                  calc (16:ℝ) ^ (-↑data.w : ℝ) * (16 ^ 4 * ↑(#S) * Real.exp (a data.d) ^ 4)
                      ≤ (16:ℝ) ^ (-↑data.w : ℝ) * (16:ℝ) ^ (↑data.w : ℝ) :=
                        mul_le_mul_of_nonneg_left h16w ht0
                    _ = 1 := by rw [← Real.rpow_add (by norm_num)]; simp
                have hsq : ((16:ℝ) ^ (-↑data.w : ℝ) * (16 ^ 4 * ↑(#S) * Real.exp (a data.d) ^ 4)) ^ 2 ≤ 1 := by
                  nlinarith [htX, mul_nonneg ht0 (le_of_lt hXpos)]
                have hM8 : (0:ℝ) ≤ ((16:ℝ) ^ (-↑data.w : ℝ)) ^ 2 * (↑(#S)) ^ 2 * Real.exp (a data.d) ^ 4 * 16 ^ 8 := by
                  positivity
                have hP : ((16:ℝ) ^ (-↑data.w : ℝ)) ^ 2 * (↑(#S)) ^ 2 * Real.exp (a data.d) ^ 4 * 16 ^ 8 ≤ 1 := by
                  nlinarith [hsq, hE4, hM8]
                have key : GeneratesNS.C * Real.exp (a data.d * 2) ^ 2 * (16 ^ (-↑data.w : ℝ)) ^ 2 * ↑(#S)
                    * 16 ≤ 2⁻¹ := by
                  rw [he2sq]; simp only [GeneratesNS.C]
                  nlinarith [hP, hM8]
                calc Q_R ↑(R_2 data) ⇑u.val.val ⇑u.val.val
                    ≤ (GeneratesNS.C * Real.exp (a data.d * 2) ^ 2 * (16 ^ (-↑data.w : ℝ)) ^ 2 * ↑(#S)
                        * 16) * Q_R ↑(R_2 data) ⇑u.val.val ⇑u.val.val := by nlinarith [u_le]
                  _ ≤ 2⁻¹ * Q_R ↑(R_2 data) ⇑u.val.val ⇑u.val.val := by nlinarith [key, qr_nonneg]

              have Q_r_zero: Q_R ↑(R_2 data) ⇑u.val.val ⇑u.val.val = 0 := by
                by_contra!
                rw [mul_comm] at le_half
                have foo := one_le_of_le_mul_left₀ (by
                  have nonneg: 0 ≤ Q_R ↑(R_2 data) ⇑u.val.val ⇑u.val.val :=
                    Q_R_self_nonneg _ _
                  grind
                ) le_half
                norm_num at foo

              rw [← Submodule.coe_eq_zero]
              by_contra hne
              exact absurd Q_r_zero (ne_of_gt (Q_R_pos_on_R' (↑u) hne _ (R'_le_R_2 data)))
            . apply mul_nonneg (by positivity)
              exact Q_R_self_nonneg _ _
            . simp [GeneratesNS.C]
              positivity

        . simp [GeneratesNS.C]
          positivity
      .
        simp [GeneratesNS.C]
        positivity
      . intro a ha
        simp
        simp at ha
        grind
      . intro i hi _
        positivity
    .
      simp [GeneratesNS.C]
      positivity

  apply LinearMap.finrank_le_finrank_of_injective at phi_u_inj
  simp at phi_u_inj
  simp [dim] at hU_dim
  norm_cast at hU_dim
  grw [hU_dim]

  conv at phi_u_inj =>
    lhs
    equals Module.finrank ℝ U =>
      exact (Submodule.submoduleOfEquivOfLe U_sub_v).finrank_eq

  grw [phi_u_inj]
  have card_eq: #(B_finite data).toFinset = #(B_finsets data) := by
    have hR1 : (0:ℝ) ≤ ↑(R_1 data) := Nat.cast_nonneg _
    have hcoe := (X_j_finite data).coe_toFinset
    have hinj1 : Set.InjOn (fun a => Metric.closedBall a (↑(R_1 data):ℝ)) (X_j data) :=
      B_ball_injective_on data (↑(R_1 data)) hR1 le_rfl
    have hinj2 : Set.InjOn (fun a => (finite_closed_ball a (R_1 data)).toFinset) (X_j data) := by
      intro a ha b hb hab
      exact hinj1 ha hb (Set.Finite.toFinset_inj.mp hab)
    have hB : (B_finite data).toFinset
        = Finset.image (fun a => Metric.closedBall a (↑(R_1 data):ℝ)) (X_j_finite data).toFinset := by
      ext s
      simp only [Set.Finite.mem_toFinset, B, Set.mem_image, Finset.mem_image, Finset.mem_coe]
    rw [hB, B_finsets, Finset.card_image_of_injOn (hinj1.mono hcoe.le),
      Finset.card_image_of_injOn (hinj2.mono hcoe.le)]
  rw [← card_eq]
  rify
  grw [card_B_le_exp_wa]
  simp [C]
  conv =>
    lhs
    equals 0 + 2 * Real.exp (↑data.w * a data.d) =>
      simp
  apply add_le_add
  . simp
  . apply Nat.le_ceil

open scoped Topology

-- TODO - do we really need the double by_contra here?
-- Theorem 3.19
set_option maxHeartbeats 2500000 in
@[expose]
instance Lipschitz_finite_dimensional: FiniteDimensional ℝ LipschitzH := by
  classical
  by_contra!
  have B := Module.Basis.ofVectorSpace ℝ LipschitzH

  have B_infinite: Infinite ((Module.Basis.ofVectorSpaceIndex ℝ LipschitzH)) := by
    by_contra fin_basis
    simp at fin_basis
    have finite_module := Module.Finite.of_basis B
    have finite_dim: FiniteDimensional ℝ LipschitzH := by
      infer_instance
    contradiction

  obtain ⟨d, hd⟩ := hGS.g_growth
  obtain ⟨C, V_bound⟩ := theorem_3_23 ((d + 3) + (d + 3)) (by simp)

  obtain ⟨fin_basis_idx, card_fin_basis_idx⟩ := B_infinite.exists_subset_card_eq _ (2 + C * 2)
  let fin_basis := Finset.image (B) fin_basis_idx
  let large_v: V_Wrapper := {
    V := Submodule.span ℝ fin_basis
    V_finite := by infer_instance
    V_even := by
      rw [finrank_span_finset_eq_card]
      .
        simp [fin_basis]
        rw [Finset.card_image_of_injective]
        . grind
        .

          exact Module.Basis.injective B
      .
        simp [fin_basis]
        apply LinearIndepOn.id_image
        exact Module.Basis.linearIndepOn B ↑fin_basis_idx
    V_nontrivial := by
      rw [nontrivial_iff]
      have one_lt: 1 < #fin_basis_idx := by
        grind
      rw [Finset.one_lt_card_iff] at one_lt
      obtain ⟨a, b, ha, hb, a_neq⟩ := one_lt
      use ⟨B a, by simp [fin_basis, ha]⟩
      use ⟨B b, by simp [fin_basis, hb]⟩
      simp
      apply (Module.Basis.injective _).ne
      exact a_neq
  }
  -- `large_v.V` does not reduce on its own inside `rw`, so name the (definitional) equation.
  have large_v_V: large_v.V = Submodule.span ℝ fin_basis := rfl
  specialize V_bound large_v ?_
  .
    simp [growth_bound, my_expr]

    norm_cast
    conv =>
      arg 1
      intro a
      rw [mul_comm]
      rw [mul_div_assoc]
      rw [Nat.pow_add]
    push_cast
    conv =>
      arg 1
      intro a
      rw [div_mul_eq_div_mul_one_div]
      rw [mul_comm _ (1 / _)]
      rw [← mul_assoc]

    conv =>
      pattern (𝓝[>] 0)
      equals (𝓝[>] (0 * 0)) => simp

    apply Filter.TendstoNhdsWithinIoi.mul (by simp) (by simp)
    .
      unfold HasPolynomialGrowthD at hd
      obtain ⟨a, s_growth⟩ := hd
      simp
      let R'' := ⌈R'_ large_v.V⌉₊
      rw [← Filter.tendsto_add_atTop_iff_nat R'']
      --  Filter.tendsto_add_atTop_iff_nat
      apply squeeze_zero_nhdsGT (g := (fun (R: ℕ) => (det_bound_const (V_basis large_v.V) * (1 + (R + R'')) ^ 2 * ((a * (R + R'')^d : ℝ))) / ((R + R'') ^ (↑d + 3) : ℝ)))
      .
        rw [Filter.eventually_atTop]
        use 1
        intro R R_pos
        have det_pos := (Q_R_matrix_pos_def (V_basis large_v.V) (R + R'') (by
          -- TODO - why is this so messy?
          simp [R'']
          norm_cast
          have foo := Nat.le_ceil (a := R'_ large_v.V)
          rw [add_comm]
          simp
          grind
        )).det_pos
        norm_cast at det_pos
        positivity
      .
        apply Filter.Eventually.of_forall
        intro R
        have foo := det_bound (V_basis large_v.V) (R := R + R'') (by
          simp [R'']
          norm_cast
          have foo := Nat.le_ceil (a := R'_ (V := large_v.V))
          rw [add_comm]
          simp
          grind
        )
        simp
        rw [one_div] at foo
        push_cast at foo
        refine le_trans (mul_le_mul_of_nonneg_right foo (by positivity)) ?_
        by_cases const_zero: det_bound_const (V_basis large_v.V) = 0
        .
          simp [const_zero]

        field_simp
        rw [mul_div_assoc]
        rw [mul_div_assoc]
        rw [mul_assoc]
        rw [mul_le_mul_iff_right₀]
        .
          by_cases r_zero: (R + R'') = 0
          .
            norm_cast
            simp [r_zero]
          .
            grw [s_growth (R + R'') (by grind)]
            norm_cast
            simp
            rw [mul_div_assoc]
        .
          have nonneg := det_bound_const_nonneg (V_basis large_v.V)
          grind
      . -- was `poly_tendsto` (an `elab`, which the verifier refuses); the same goal by hand
        have hx : Filter.Tendsto (fun R : ℕ => ((R : ℝ) + R'')) Filter.atTop Filter.atTop :=
          Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
        have hpos : ∀ᶠ R : ℕ in Filter.atTop, (0 : ℝ) < (R : ℝ) + R'' :=
          hx.eventually (Filter.eventually_gt_atTop 0)
        have hlim : Filter.Tendsto (fun x : ℝ => x⁻¹ + 2 * (x⁻¹) ^ 2 + (x⁻¹) ^ 3)
            Filter.atTop (𝓝 0) := by
          have h := tendsto_inv_atTop_zero (𝕜 := ℝ)
          simpa using (h.add ((h.pow 2).const_mul 2)).add (h.pow 3)
        refine Filter.Tendsto.congr' ?_
          ((hlim.comp hx).const_mul (det_bound_const (V_basis V_Wrapper.V) * a) |>.trans (by simp))
        filter_upwards [hpos] with R hR
        have hR' : (R : ℝ) + R'' ≠ 0 := hR.ne'
        simp only [Function.comp_apply]
        field_simp
        ring_nf
    .
      unfold HasPolynomialGrowthD at hd
      obtain ⟨a, s_growth⟩ := hd
      apply squeeze_zero_nhdsGT (g := (fun (n: ℝ) => (a * n^d : ℝ) / (n ^ (↑d + 3))) ∘ (fun (n: ℕ) => (n: ℝ)))
      .
        rw [Filter.eventually_atTop]
        use 1
        intro n hn
        have card_nonzero: (0: ℝ) < #(S ^ n) := by
          simp
          apply Finset.Nonempty.pow
          apply S_nonempty

        norm_cast
        positivity
      .
        apply Filter.Eventually.of_forall
        intro n
        by_cases hn: n = 0
        .
          simp [hn]
        .
          grw [s_growth n (by grind)]
          norm_cast
          simp
      . -- was `poly_tendsto` (an `elab`, which the verifier refuses); the same goal by hand
        have hlim : Filter.Tendsto (fun n : ℕ => (a : ℝ) * (((n : ℝ)⁻¹) ^ 3)) Filter.atTop (𝓝 0) := by
          simpa using ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).pow 3).const_mul (a : ℝ)
        refine Filter.Tendsto.congr' ?_ hlim
        filter_upwards [Filter.eventually_ge_atTop 1] with n hn
        have hn' : (n : ℝ) ≠ 0 := by positivity
        simp only [Function.comp_apply]
        field_simp
        ring_nf
  .
    rw [large_v_V, finrank_span_finset_eq_card] at V_bound
    .
      simp [fin_basis] at V_bound
      rw [Finset.card_image_of_injective] at V_bound
      .
        simp [card_fin_basis_idx] at V_bound
        grind
      . exact Module.Basis.injective B
    .
      simp [fin_basis]
      apply LinearIndepOn.id_image
      exact Module.Basis.linearIndepOn B ↑fin_basis_idx

end GeneratesNS
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


set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 9000000

@[expose]
instance proper_linear_w: ProperSpace (((W →L[ℝ] W))) := FiniteDimensional.proper_rclike ℝ (((W →L[ℝ] W)))


-- Takes in an invertible linear map from W to W, and produces a *continuous* linear map from W to W
@[expose]
noncomputable def GRepW: (W →ₗ[ℝ] W)ˣ →* (W →L[ℝ] W)ˣ := {
  toFun := fun f => {
    val := LinearMap.toContinuousLinearMap f.val
    inv := LinearMap.toContinuousLinearMap f.inv
    val_inv := by
      have old_inv := f.val_inv
      ext a
      apply_fun (fun f => f a) at old_inv
      simp
      simp only [Units.inv_eq_val_inv, Module.End.one_apply] at old_inv
      apply old_inv
    inv_val := by
      have old_inv := f.inv_val
      ext a
      apply_fun (fun f => f a) at old_inv
      simp
      simp only [Units.inv_eq_val_inv, Module.End.one_apply] at old_inv
      apply old_inv
  }
  map_one' := by
    ext a
    simp
  map_mul' := by
    intro f g
    ext a
    simp
}


set_option synthInstance.maxHeartbeats 500000


@[expose]
noncomputable def rho_g := (GRepW_base).range


@[expose]
def isembedding_units_val := Units.isEmbedding_val_mk' (M := (W →L[ℝ] W)) (f := ContinuousLinearMap.inverse) (by
  intro x hx
  have foo := ContDiffAt.continuousAt (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse (e := x) (n := 0) (by
    simp at hx
    obtain ⟨u, hu⟩ := hx
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := u.inv)
    .
      simp
      have mul_inv := u.val_inv
      dsimp [HMul.hMul, Mul.mul] at mul_inv
      rw [hu] at mul_inv
      exact mul_inv
    . simp
      have inv_val := u.inv_val
      dsimp [HMul.hMul, Mul.mul] at inv_val
      rw [hu] at inv_val
      exact inv_val
  ))
  apply ContinuousAt.continuousWithinAt
  exact foo
  -- ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse
) (by
  intro u
  have mul_inv := u.val_inv
  dsimp [HMul.hMul, Mul.mul] at mul_inv
  apply ContinuousLinearMap.inverse_eq
  . exact u.val_inv
  . exact u.inv_val
)

@[expose]
instance T2_W: T2Space (W) := TopologicalSpace.t2Space_of_metrizableSpace

@[expose]
noncomputable def G_SPolyData {d: ℕ} (h_poly: HasPolynomialGrowthD hGS.S d): SPolyData (T := G) ⊤ := {
  S := Subgroup.topEquiv.symm.toMonoidHom '' hGS.S
  S_finite := by
    apply Set.Finite.image
    simp
  S_one := by
    simp
    apply hGS.one_mem
  S_inv := by
    rw [← Set.image_inv]
    nth_rw 1 [S_eq_Sinv]
    simp
  S_generates := by
    rw [← MonoidHom.map_closure]
    have foo := hGS.generates
    simp at foo
    simp [foo]

  S_poly_const := h_poly.choose
  S_poly_const_pos := by
    by_contra!
    have foo := h_poly.choose_spec
    simp [← this] at foo
    specialize foo 1 (by simp)
    simp at foo
    have S_nonempty := hGS.hS
    simp at S_nonempty
    grind
  S_poly_deg := d
  S_poly := by
    have foo := h_poly.choose_spec
    intro r hr
    rw [Set.Finite.toFinset_image]
    rw [← Finset.image_pow]
    grw [Finset.card_image_le]
    .
      specialize foo r hr
      simpa using foo
    . simp
}


-- Theorem 3.8 in Vikman

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Theorem38
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Theorem 3.8

`theorem_3_8` and its real form: a group of polynomial growth admits a nontrivial
finite-dimensional representation.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
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

set_option synthInstance.maxHeartbeats 500000

set_option maxHeartbeats 9000000

@[expose]
instance rho_g_FG: Group.FG (rho_g) := by
  unfold rho_g
  apply Group.fg_range

-- TODO - deduplicate with 'map_S_Data'
@[expose]
def map_range_S_data {G H: Type*} [Group G] [Group H] [DecidableEq G] [DecidableEq H] {f: G →* H} (S_data: SPolyData (T := G) ⊤): SPolyData f.range := {
  S := (f.rangeRestrict.comp (Subgroup.topEquiv.toMonoidHom)) '' S_data.S
  S_finite := by
    apply Set.Finite.image
    apply S_data.S_finite
  S_one := by
    simp only [Set.mem_image]
    use 1
    simp
    apply S_data.S_one
  S_inv := by
    rw [← Set.image_inv]
    rw [← S_data.S_inv]
  S_generates := by
    rw [← MonoidHom.map_closure]
    rw [S_data.S_generates]
    rw [Subgroup.map_top_of_surjective]
    simp
    apply MonoidHom.rangeRestrict_surjective
  S_poly_const := S_data.S_poly_const
  S_poly_const_pos := S_data.S_poly_const_pos
  S_poly_deg := S_data.S_poly_deg
  S_poly := by
    intro r hr
    rw [Set.Finite.toFinset_image]
    rw [← Finset.image_pow]
    grw [Finset.card_image_le]
    .
      apply S_data.S_poly r hr
    . exact S_data.S_finite
}

@[expose]
def map_equiv_S_data {A B: Type*} [Group A] [Group B] [DecidableEq A] [DecidableEq B] {G: Subgroup A} {H: Subgroup B} (f: G ≃* H) (S_data: SPolyData G): SPolyData H := {
  S := f.toMonoidHom '' S_data.S
  S_finite := by
    apply Set.Finite.image
    apply S_data.S_finite
  S_one := by
    simp only [Set.mem_image]
    use 1
    simp
    apply S_data.S_one
  S_inv := by
    rw [← Set.image_inv]
    rw [← S_data.S_inv]
  S_generates := by
    rw [← MonoidHom.map_closure]
    rw [S_data.S_generates]
    rw [Subgroup.map_top_of_surjective]
    simp
    exact MulEquiv.surjective f
  S_poly_const := S_data.S_poly_const
  S_poly_const_pos := S_data.S_poly_const_pos
  S_poly_deg := S_data.S_poly_deg
  S_poly := by
    intro r hr
    rw [Set.Finite.toFinset_image]
    rw [← Finset.image_pow]
    grw [Finset.card_image_le]
    .
      apply S_data.S_poly r hr
    . exact S_data.S_finite
}


end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.ThreeTwoGenerates
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The sets `S_n` generate the kernel

`e_i_and_gamma_generates_G`, `three_two_gamma_m_generates` and the finite generation of the
kernel of `φ`.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
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

set_option synthInstance.maxHeartbeats 500000

set_option maxHeartbeats 9000000

open MeasureTheory

open Additive

attribute [local implicit_reducible] Additive Multiplicative

@[expose]
def e_i_with_gamma (φ: (Additive G) →+ ℤ) (γ : G) (s: S): Additive G := (ofMul s.val) + ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))


-- The kernel of `φ` is generated by {γ_m_i}
set_option maxHeartbeats 1000000

lemma three_two_S_n_subset_ker {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (φ: (Additive G) →+ ℤ) (γ: G) (phi_gamma: φ γ = 1) (n: ℕ):
   ↑(three_two_S_n S φ γ n) ⊆ Additive.toMul '' φ.ker.carrier := by

  intro x hx
  simp [three_two_S_n, gamma_m_helper, e_i_regular_helper] at hx
  obtain ⟨m, m_in_range, s, s_mem_s, prod_eq_x⟩ := hx
  apply_fun ofMul at prod_eq_x
  rw [ofMul_mul] at prod_eq_x
  rw [ofMul_mul] at prod_eq_x
  apply_fun φ at prod_eq_x
  rw [AddMonoidHom.map_add] at prod_eq_x
  rw [AddMonoidHom.map_add] at prod_eq_x
  simp at prod_eq_x
  conv at prod_eq_x =>
    arg 1
    arg 2
    equals (ofMul s + -(φ (ofMul s) • ofMul γ)) => rfl

  simp at prod_eq_x
  conv at prod_eq_x =>
    pattern φ (ofMul γ)
    equals φ γ => rfl

  simp [phi_gamma] at prod_eq_x
  simp
  exact id (Eq.symm prod_eq_x)


-- Extract a generatating set for the kernel of φ
@[expose]
noncomputable def S_n_ker_phi  {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (φ: (Additive G) →+ ℤ) (γ: G) (hγ : φ γ = 1) (n: ℕ)  : Finset φ.ker := (three_two_S_n S φ γ n).attach.image (fun x => ⟨x.val, (by
obtain ⟨y, hy, hyx⟩ := (three_two_S_n_subset_ker S φ γ hγ n) x.property
rw [← hyx]
exact hy
)⟩) ∪ {0}

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.GrowthZero
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Polynomial growth of the kernel, and growth exponent zero

`three_two_kernel_poly_growth`, and that a group of growth exponent zero is finite.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
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

set_option synthInstance.maxHeartbeats 500000

set_option maxHeartbeats 1000000

open MeasureTheory

open Additive

attribute [local implicit_reducible] Additive Multiplicative

lemma one_mem_S  {G: Type*} [Group G] [DecidableEq G] {n: ℕ} (data: Theorem3_1_Input G) (hGS: GeneratesWithParam data.G') (γ: Additive data.G') (hγ: data.φ γ = 1): 0 ∈ S_n_ker_phi hGS.S data.φ γ hγ n := by
  simp [S_n_ker_phi]


-- The generating set of `ker φ` used below, shared between the `new_g_growth`
-- hypothesis and the `S` field so that `g_growth := new_g_growth` is definitionally
-- trivial (avoids an expensive `whnf` on the two separately-elaborated `Finset`s).
omit hGS in
@[expose]
noncomputable def ker_S {G: Type*} [Group G] [DecidableEq G] (data: Theorem3_1_Input G)
    (hGS: GeneratesWithParam data.G') (γ: data.G') (hγ: data.φ γ = 1) (n: ℕ) :
    Finset (Multiplicative data.φ.ker) :=
  (Finset.image Additive.toMul (S_n_ker_phi hGS.S data.φ γ hγ n)) ∪
    (Finset.image Additive.toMul ((S_n_ker_phi hGS.S data.φ γ hγ n)))⁻¹

-- TODO - figure out how to make this a 'let' without adding it to typeclass search
omit hGS in
@[expose]
noncomputable def ker_generates {n: ℕ} {G: Type*} [Group G] [DecidableEq G] (data: Theorem3_1_Input G) (hGS: GeneratesWithParam data.G') (γ: data.G') (hγ: data.φ γ = 1)
  (ker_infinite: Infinite (Multiplicative data.φ.ker))
  (ker_generates: AddSubgroup.closure (Additive.ofMul '' (three_two_S_n hGS.S data.φ γ (n))) = data.φ.ker)
  ( new_g_growth: HasPolynomialGrowth (ker_S data hGS γ hγ n))
  : Generates := {
  G := (Multiplicative data.φ.ker)
  g_group := by infer_instance
  g_eq := by infer_instance
  S := ker_S data hGS γ hγ n
  hS := by
    use 1
    simp only [ker_S]
    simp
    exact one_mem_S data hGS γ hγ
  generates := by
    simp only [ker_S]
    simp
    rw [Subgroup.closure_union]
    conv =>
      arg 1
      arg 1
      equals ⊤ =>

        let f := (AddSubgroup.subtype data.φ.ker).toMultiplicative
        ext a
        simp
        rw [AddSubgroup.ext_iff] at ker_generates
        specialize ker_generates a.val
        have foo := ker_generates.mpr a.prop
        conv at foo =>
          arg 2
          equals Additive.ofMul a.val => rfl

        apply (AddSubgroup.mem_toSubgroup' _ _).mpr at foo
        rw [AddSubgroup.toSubgroup'_closure] at foo
        simp at foo
        unfold S_n_ker_phi
        simp
        first
          | erw [Finset.coe_insert, Set.image_insert_eq, toMul_zero, Subgroup.closure_insert_one]
          | rw [Finset.coe_insert, Set.image_insert_eq, toMul_zero, Subgroup.closure_insert_one]
          | simp only [Finset.coe_insert, Set.image_insert_eq, toMul_zero, Subgroup.closure_insert_one]
        rw [← Subgroup.mem_map_iff_mem (f := f)]
        .
          simp only [f, Subgroup.subtype_apply]
          rw [MonoidHom.map_closure]
          simp
          conv =>
            arg 2
            equals a.val => rfl
          conv =>
            arg 1
            arg 1
            equals ((three_two_S_n hGS.S data.φ γ n : Finset ↥data.G') : Set ↥data.G') =>
              ext b
              constructor
              · intro hb
                obtain ⟨c, hc, rfl⟩ := hb
                obtain ⟨d, hd, rfl⟩ := hc
                obtain ⟨y, rfl⟩ := hd
                exact y.2
              · intro hb
                have hbk : b ∈ three_two_S_n hGS.S data.φ γ n := by simpa using hb
                exact ⟨_, ⟨_, ⟨⟨b, hbk⟩, rfl⟩, rfl⟩, rfl⟩
          exact foo
        . simp [f]
          intro x y hxy
          simpa using hxy
    simp
  one_mem := by
    apply Finset.mem_union_left
    rw [Finset.mem_image]
    use 0
    simp
    -- TODO - figure out wht 'apply one_mem_S' is slow
    exact one_mem_S data hGS γ hγ

  has_inv := by
    intro g hg
    simp only [ker_S] at hg ⊢
    simp at hg
    simp
    rw [or_comm]
    exact hg
  g_infinite := by
    exact ker_infinite
  g_growth := by convert new_g_growth using 2
}


end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ComplexFactorParameters
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear parameters for the two actual complex-weight factors -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

namespace ComplexTriangularAdjoint

theorem cartanComponent_weight (x : L) :
    T.weightMap (T.cartanComponent H x : L) = T.weightMap x :=
  T.cartanWeightSection_weight H _

end ComplexTriangularAdjoint
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

/-- The span of mixed words is an actual Lie ideal, rather than an assumed
quotient datum. -/
def mixedWordIdeal (X : I → L) (outside : I → Prop)
    (hgen : LieSubalgebra.lieSpan ℝ L (range X) = ⊤) : LieIdeal ℝ L :=
  { mixedWordSpan X outside with
    lie_mem := fun {x y} hy => mixedWordSpan_lie X outside hgen x y hy }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanConeIdeal
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mixed-word ideal contains every outside generalized weight space -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

set_option maxHeartbeats 1000000 in
/-- The ideal generated by the letters outside the allowed cone of weights. -/
def coneWordIdeal (C : Set (H →ₗ[ℝ] ℝ)) : LieIdeal ℝ (cartanRootIdeal H) :=
  mixedWordIdeal M.letter (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) M.generates

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanConeGroup
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual simply connected groups for the Cartan cone quotients -/

noncomputable section
namespace PolycyclicRecognition
namespace CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold ContDiff

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

set_option maxHeartbeats 1000000 in
/-- The canonical Lie algebra projection onto the mixed-word quotient. -/
def coneProjection (C : Set (H →ₗ[ℝ] ℝ)) :
    cartanRootIdeal H →ₗ⁅ℝ⁆ (cartanRootIdeal H) ⧸ M.coneWordIdeal C :=
  { (M.coneWordIdeal C).toSubmodule.mkQ with map_lie' := fun {_ _} => rfl }

set_option maxHeartbeats 1000000 in
theorem coneProjection_surjective (C : Set (H →ₗ[ℝ] ℝ)) :
    Function.Surjective (M.coneProjection C) :=
  (M.coneWordIdeal C).toSubmodule.mkQ_surjective

set_option maxHeartbeats 1000000 in
theorem coneQuotient_nilpotent (C : Set (H →ₗ[ℝ] ℝ)) :
    LieRing.IsNilpotent ((cartanRootIdeal H) ⧸ M.coneWordIdeal C) := by
  let : LieRing.IsNilpotent (cartanRootIdeal H) := LieModule.IsNilpotent.mk (cartanRootIdeal H) M.bound_zero
  exact (M.coneProjection_surjective C).lieAlgebra_isNilpotent

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConeIdealGroup
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual simply connected group of a cone ideal

The mixed ideal integrates to the kernel of the constructed quotient map.
This provides its intrinsic Haar measure and polynomial exponential
coordinates for the ideal boxes.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold ContDiff

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

theorem coneIdeal_nilpotent (C : Set (H →ₗ[ℝ] ℝ)) :
    LieRing.IsNilpotent (M.coneWordIdeal C) := by
  let : LieRing.IsNilpotent (cartanRootIdeal H) :=
    LieModule.IsNilpotent.mk (cartanRootIdeal H) M.bound_zero
  exact (show Function.Injective (M.coneWordIdeal C).incl from Subtype.val_injective).lieAlgebra_isNilpotent

/-- Lie correspondence realizes the mixed ideal as exactly the kernel of
the already constructed quotient, with a closed embedding into the
nilpotent factor and the correct intrinsic exponential. -/
theorem exists_cone_ideal_group
    (C : Set (H →ₗ[ℝ] ℝ))
    (N : NilpotentLieModel (cartanRootIdeal H))
    (ExpN : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier)
    (hExpN : IsGroupExponential ExpN)
    (haarN : NilpotentExponentialHaarInput N.modelSpace N.carrier)
    {Q : Type*} [Group Q] (π : N.carrier →* Q)
    (hker : (π.ker : Set N.carrier) =
      ExpN '' (N.equiv '' (M.coneWordIdeal C : Set (cartanRootIdeal H))))
    (existI : NilpotentLieExistenceInput (M.coneWordIdeal C))
    (haarI : ∀ I : NilpotentLieModel (M.coneWordIdeal C),
      NilpotentExponentialHaarInput I.modelSpace I.carrier)
    (integrate : ∀ I : NilpotentLieModel (M.coneWordIdeal C),
      NilpotentLieIntegrationInput (EN := I.modelSpace) (N := I.carrier)
        (EG := N.modelSpace) (G := N.carrier)) :
    ∃ (I : NilpotentLieModel (M.coneWordIdeal C))
      (ExpI : GroupLieAlgebra (𝓘(ℝ, I.modelSpace)) I.carrier → I.carrier),
      IsGroupExponential ExpI ∧
      ∃ ι : I.carrier →* N.carrier,
        Topology.IsClosedEmbedding ι ∧
        ContMDiff (𝓘(ℝ, I.modelSpace)) (𝓘(ℝ, N.modelSpace)) ∞ ι ∧
        (∀ x : M.coneWordIdeal C, ι (ExpI (I.equiv x)) = ExpN (N.equiv x)) ∧
        Set.range ι = (π.ker : Set N.carrier) := by
  obtain ⟨I⟩ := existI (M.coneIdeal_nilpotent C)
  obtain ⟨ExpI, hExpI, cI, hcI⟩ := I.exists_exponential_chart (M.coneIdeal_nilpotent C) (haarI I)
  have hnilN : LieRing.IsNilpotent (cartanRootIdeal H) :=
    LieModule.IsNilpotent.mk (cartanRootIdeal H) M.bound_zero
  obtain ⟨cN, hcN⟩ := (haarN.2 ExpN hExpN (N.tangent_nilpotent hnilN)).1
  let j := N.equiv.toLieHom.comp ((M.coneWordIdeal C).incl.comp I.equiv.symm.toLieHom)
  have hj : Function.Injective j :=
    N.equiv.injective.comp (Subtype.val_injective.comp I.equiv.symm.injective)
  obtain ⟨ι, hclosed, hsmooth, _hdiff, hι, hrange⟩ := exists_closed_integration
    (integrate I) (I.tangent_nilpotent (M.coneIdeal_nilpotent C)) j hj
    ExpI ExpN hExpI hExpN cI hcI cN hcN
  refine ⟨I, ExpI, hExpI, ι, hclosed, hsmooth, ?_, ?_⟩
  · intro x
    simpa [j] using hι (I.equiv x)
  · rw [hrange, hker]
    congr 1
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(I.equiv.symm x : cartanRootIdeal H), (I.equiv.symm x).property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨I.equiv ⟨x, hx⟩, ?_⟩
      simp [j]

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MixedWordBasis
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite mixed-word spanning pools for the cone ideals -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

def coneMixedVector (C : Set (H →ₗ[ℝ] ℝ)) (w : M.coneMixedWords C) : M.coneWordIdeal C :=
  ⟨evalBracketWord M.letter w.val, eval_mixed_mem_span M.letter _ w.property⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MixedWordBoxModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete nilpotent box model of a cone ideal

The finite mixed words generate the ideal even as a vector space. Using
them as an alphabet allows the existing box calculus to apply directly.
Flattening this alphabet retains the original word and its exact width.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule LieAlgebra
open scoped BigOperators

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

def coneIdealWordBound (C : Set (H →ₗ[ℝ] ℝ)) : ℕ := by
  let := M.coneIdeal_nilpotent C
  exact (LieModule.IsNilpotent.nilpotent ℝ (M.coneWordIdeal C)
    (M.coneWordIdeal C)).choose

abbrev coneIdealWordList (C : Set (H →ₗ[ℝ] ℝ)) :=
  boundedBracketWords (I := M.coneMixedWords C) (M.coneIdealWordBound C)

abbrev ConeIdealBases (C : Set (H →ₗ[ℝ] ℝ)) :=
  WordBasisSelections (M.coneMixedVector C) (M.coneIdealWordList C)

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConeIdealBoxCalculus
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product and Haar estimates for the actual cone ideal boxes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule MeasureTheory
open scoped Manifold BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

def coneIdealBoxBasis (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C) (r : ℝ) :
    Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C) :=
  exponentialRescaleBasis
    (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
    (fun j => M.coneIdealWordCost C s (β.val j)) r

def coneIdealBox {G : Type*} (Exp : M.coneWordIdeal C → G)
    (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C) (r R : ℝ) : Set G :=
  exponentialCoordinateBox Exp (M.coneIdealBoxBasis C s β r) R

def IsMaximizingConeIdealBasis
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C) : Prop :=
  IsMaximizingColumnBasis
    (wordListCoordinates (M.coneMixedVector C) (M.coneIdealWordList C) b₀)
    (fun w => M.coneIdealWordCost C s w) β.val

end PolycyclicRecognition.CartanWordModel

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
/-- Restriction to the actual nilpotent Cartan ideal. -/
def cartanIdealWeightDilation (h : H) : cartanRootIdeal H ≃ₗ⁅ℝ⁆ cartanRootIdeal H where
  toFun x := ⟨cartanWeightDilation T H h x, cartanWeightDilation_mem_ideal T H h x.property⟩
  invFun x := ⟨cartanWeightDilation T H (-h) x,
    cartanWeightDilation_mem_ideal T H (-h) x.property⟩
  left_inv x := by
    apply Subtype.ext
    change cartanWeightScale T H (-h) (cartanWeightScale T H h x) = _
    rw [← cartanWeightScale_add_apply, neg_add_cancel, cartanWeightScale_zero_apply]
  right_inv x := by
    apply Subtype.ext
    change cartanWeightScale T H h (cartanWeightScale T H (-h) x) = _
    rw [← cartanWeightScale_add_apply, add_neg_cancel, cartanWeightScale_zero_apply]
  map_add' x y := by apply Subtype.ext; exact map_add (cartanWeightDilation T H h) (x : L) (y : L)
  map_smul' a x := by apply Subtype.ext; exact map_smul (cartanWeightDilation T H h) a (x : L)
  map_lie' {x y} := by apply Subtype.ext; exact LieEquiv.map_lie (cartanWeightDilation T H h) x y

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoxDilation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact template shifts for actual Cartan boxes

The scalar action on generalized weight spaces is a genuine Lie automorphism.
It takes each scaled word basis to the basis for the translated template.
The finite Dynkin identity then integrates it to the needed group automorphism.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra
open scoped BigOperators Manifold

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
omit hunimod [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] eW in
/-- Every actual bracket word is scaled by the exponential of its total
weight, even when its total weight is zero. -/
theorem idealWeightDilation_word (h : H) (w : FreeMagma (Fin M.letterCount)) :
    cartanIdealWeightDilation T H h (evalBracketWord M.letter w) =
      Real.exp (bracketWordExponent (fun i => M.weight i h) w) • evalBracketWord M.letter w := by
  induction w using FreeMagma.rec with
  | of i =>
    rw [evalBracketWord_of, bracketWordExponent_of]
    apply Subtype.ext
    exact cartanWeightScale_apply_root T H h (M.weight i) (M.letter_root i)
  | mul u v hu hv =>
    change cartanIdealWeightDilation T H h (evalBracketWord M.letter (u * v)) =
      Real.exp (bracketWordExponent (fun i => M.weight i h) (u * v)) •
        evalBracketWord M.letter (u * v)
    rw [evalBracketWord_mul, LieEquiv.map_lie, hu, hv, bracketWordExponent_mul,
      Real.exp_add, smul_lie, lie_smul, smul_smul]

set_option maxHeartbeats 1000000 in
/-- The scaled basis itself shifts exactly, with no loss in its radius. -/
theorem idealWeightDilation_boxBasis {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (w : W) (β : M.Bases) (r : ℝ) :
    (M.boxBasis T hunimod eW E β r).map
      (cartanIdealWeightDilation T H (r • cartanHeightSection T H (eW.symm w))).toLinearEquiv =
        M.boxBasis T hunimod eW ((fun x => x + w) '' E) β r := by
  apply DFunLike.ext
  intro j
  simp only [Basis.map_apply, boxBasis, exponentialRescaleBasis, Basis.unitsSMul_apply,
    Units.smul_def, Units.val_mk0, map_smul]
  have hword := M.idealWeightDilation_word T (r • cartanHeightSection T H (eW.symm w)) (β.val j)
  have hb := WordBasisSelections.eval_words M.letter M.wordList β j
  change evalBracketWord M.letter (β.val j) = _ at hb
  rw [hb] at hword
  change Real.exp (r * M.boxCost T hunimod eW E (β.val j)) •
    cartanIdealWeightDilation T H (r • cartanHeightSection T H (eW.symm w))
      (WordBasisSelections.basis M.letter M.wordList β j) =
    Real.exp (r * M.boxCost T hunimod eW ((fun x => x + w) '' E) (β.val j)) •
      WordBasisSelections.basis M.letter M.wordList β j
  rw [hword, M.boxCost_translate T hunimod eW hE hne, smul_smul]
  have he : bracketWordExponent (fun i => M.weight i
      (r • cartanHeightSection T H (eW.symm w))) (β.val j) =
      r * bracketWordExponent (fun i => M.weight i
        (cartanHeightSection T H (eW.symm w))) (β.val j) := by
    simp only [bracketWordExponent, map_smul, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, ← Real.exp_add]
  congr 2
  ring

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanAllowedProbeChains
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Placing actual probe chains in the sampling coordinates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- Reexpress an actual probe chain in the enlarged sampling basis.
The word-basis comparison gives a constant radius for every prefix;
all endpoints, coefficients and generator edges are preserved. -/
def BoxProbeChains.inSamplingBox
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E C : Set W) (γ β : M.Bases) (t : Fin M.letterCount → ℝ)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW C) β.val)
    (ht : ∀ i, t i ≤ (M.supportIn T hunimod eW).weightSupport C i)
    (hw : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport C i)
    {δ : ℝ} (hδ : 0 ≤ δ) (scale : ℕ → ℝ) (hr : ∀ n, 0 ≤ scale n)
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (probe : ∀ n, Y n → F.N.carrier)
    (P : M.BoxProbeChains T F hunimod eW b₀ E γ t scale probe) :
    M.BoxProbeChains T F hunimod eW b₀ E β
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport C i) scale probe := by
  let hex := exists_word_box_comparison_constant M.letter M.wordList b₀
  let D := Classical.choose hex
  have hD := (Classical.choose_spec hex).1
  have hcompare := (Classical.choose_spec hex).2
  have hscaled : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun w => bracketWordExponent
        (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport C i) w) β.val := by
    refine ⟨hβ.1, ?_⟩
    intro β' hβ'
    simp only [columnBasisWeight, bracketWordExponent_const_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hβ.2 β' hβ') (by linarith)
  have hcost (w : M.wordList) : bracketWordExponent t w ≤
      bracketWordExponent
        (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport C i) w + 0 := by
    rw [add_zero]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hmul := mul_nonneg hδ (hw i)
    nlinarith [ht i]
  refine {
    length := P.length
    amplitude := P.amplitude
    prefixRadius := D * P.prefixRadius
    amplitude_ge_one := P.amplitude_ge_one
    prefixRadius_nonneg := mul_nonneg hD P.prefixRadius_nonneg
    mode := P.mode
    coefficient := P.coefficient
    vertex := P.vertex
    coefficient_measurable := P.coefficient_measurable
    vertex_measurable := P.vertex_measurable
    coefficient_bound := P.coefficient_bound
    vertex_zero := P.vertex_zero
    vertex_last := P.vertex_last
    vertex_step := P.vertex_step
    vertex_bound := ?_ }
  intro n y j
  have hb := hcompare
    (fun w => bracketWordExponent
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport C i) w)
    (fun w => bracketWordExponent t w) β γ hscaled (hr n) hcost (P.vertex n y j)
  simp only [zero_mul, Real.exp_zero, mul_one] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (P.vertex_bound n y j) hD)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanProbeChainDilation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact translation of the normalized probe generator chains -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The exact weight dilation preserves the coordinate bound when the
reference template is translated by the pivot height. -/
theorem probe_dilation_coordinate_norm {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (w : W) (β : M.Bases) (r : ℝ) (v : cartanRootIdeal H) :
    ‖(M.boxBasis T hunimod eW ((fun x => x + w) '' E) β r).equivFun
      (cartanIdealWeightDilation T H (r • cartanHeightSection T H (eW.symm w)) v)‖ =
      ‖(M.boxBasis T hunimod eW E β r).equivFun v‖ := by
  rw [← M.idealWeightDilation_boxBasis T hunimod eW hE hne w β r]
  change ‖(M.boxBasis T hunimod eW E β r).equivFun
    ((cartanIdealWeightDilation T H (r • cartanHeightSection T H (eW.symm w))).symm
      (cartanIdealWeightDilation T H (r • cartanHeightSection T H (eW.symm w)) v))‖ = _
  rw [LieEquiv.symm_apply_apply]

variable {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]

set_option maxHeartbeats 1000000 in
omit hunimod [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] eW in
/-- Dilation carries each actual generator edge to the same letter with
its explicitly rescaled coefficient. -/
theorem probe_dilation_generator_step
    (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
    (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExpN : IsGroupExponential ExpN)
    (hbij : Function.Bijective ExpN) (dynkin : NilpotentDynkinExpansionInput EN N)
    (h : H) (u v : cartanRootIdeal H) (i : Fin M.letterCount) (t : ℝ)
    (hedge : ExpN (eN v) = ExpN (eN u) * ExpN (eN (t • M.letter i))) :
    ExpN (eN (cartanIdealWeightDilation T H h v)) =
      ExpN (eN (cartanIdealWeightDilation T H h u)) *
        ExpN (eN ((t * Real.exp (M.weight i h)) • M.letter i)) := by
  let D := cartanIdealWeightDilation T H h
  let S := integrateNilpotentLieEquiv eN ExpN hbij dynkin hExpN M.bound_zero D
  have hS (x : cartanRootIdeal H) : S (ExpN (eN x)) = ExpN (eN (D x)) :=
    integrateNilpotentLieEquiv_apply_exp eN ExpN hbij dynkin hExpN M.bound_zero D x
  have hletter : D (t • M.letter i) = (t * Real.exp (M.weight i h)) • M.letter i := by
    rw [map_smul]
    have hi := M.idealWeightDilation_word T h (FreeMagma.of i)
    simp only [evalBracketWord_of, bracketWordExponent_of] at hi
    rw [hi, smul_smul]
  calc
    _ = S (ExpN (eN v)) := (hS v).symm
    _ = S (ExpN (eN u)) * S (ExpN (eN (t • M.letter i))) := by rw [hedge, map_mul]
    _ = _ := by rw [hS, hS, hletter]

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanDilatedProbeChains
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting actual probe chains to the contact pivot -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- Exact dilation transports all measurable prefixes, generator amplitudes
and endpoints. The chain length and prefix radius are unchanged. -/
def BoxProbeChains.dilate
    (hbij : Function.Bijective F.ExpN)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E B : Set W) (hE : IsCompact E) (hne : E.Nonempty)
    (hB : IsCompact B) (hBne : B.Nonempty) (w : W)
    (γ : M.Bases) (scale : ℕ → ℝ)
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (probe : ∀ n, Y n → F.N.carrier)
    (P : M.BoxProbeChains T F hunimod eW b₀ E γ
      ((M.supportIn T hunimod eW).weightSupport B) scale probe) :
    M.BoxProbeChains T F hunimod eW b₀ ((fun x => x + w) '' E) γ
      ((M.supportIn T hunimod eW).weightSupport ((fun x => x + w) '' B)) scale
      (fun n q => integrateNilpotentLieEquiv F.N.equiv F.ExpN hbij dynkinN F.isExpN
        M.bound_zero
        (cartanIdealWeightDilation T H (scale n • cartanHeightSection T H (eW.symm w)))
        (probe n q)) := by
  let h := fun n => scale n • cartanHeightSection T H (eW.symm w)
  let D := fun n => cartanIdealWeightDilation T H (h n)
  let S := fun n => integrateNilpotentLieEquiv F.N.equiv F.ExpN hbij dynkinN F.isExpN
    M.bound_zero (D n)
  have hS (n) (v : cartanRootIdeal H) :
      S n (F.ExpN (F.N.equiv v)) = F.ExpN (F.N.equiv (D n v)) :=
    integrateNilpotentLieEquiv_apply_exp F.N.equiv F.ExpN hbij dynkinN F.isExpN
      M.bound_zero (D n) v
  refine {
    length := P.length
    amplitude := P.amplitude
    prefixRadius := P.prefixRadius
    amplitude_ge_one := P.amplitude_ge_one
    prefixRadius_nonneg := P.prefixRadius_nonneg
    mode := P.mode
    coefficient := fun n q j => P.coefficient n q j *
      Real.exp (scale n * M.weight (P.mode n j) (cartanHeightSection T H (eW.symm w)))
    vertex := fun n q j => D n (P.vertex n q j)
    coefficient_measurable := fun n j => (P.coefficient_measurable n j).mul_const _
    vertex_measurable := ?_
    coefficient_bound := ?_
    vertex_zero := ?_
    vertex_last := ?_
    vertex_bound := ?_
    vertex_step := ?_ }
  · intro n j
    let A := b₀.equivFun.toLinearMap.comp ((D n).toLinearMap.comp b₀.equivFun.symm.toLinearMap)
    have hm := A.continuous_of_finiteDimensional.measurable.comp (P.vertex_measurable n j)
    have he : (fun q => A (b₀.equivFun (P.vertex n q j))) =
        (fun q => b₀.equivFun (D n (P.vertex n q j))) := by
      funext q
      change b₀.equivFun (D n (b₀.equivFun.symm (b₀.equivFun (P.vertex n q j)))) = _
      rw [LinearEquiv.symm_apply_apply]
    exact he ▸ hm
  · intro n q j
    exact M.probe_dilation_coefficient_bound T hunimod eW hE hne w (scale n)
      (P.coefficient n q j) P.amplitude (P.mode n j) (P.coefficient_bound n q j)
  · intro n q
    rw [P.vertex_zero, map_zero]
  · intro n q
    rw [← hS, P.vertex_last]
  · intro n q j
    change ‖(M.boxBasis T hunimod eW ((fun x => x + w) '' B) γ (scale n)).equivFun
      (D n (P.vertex n q j))‖ ≤ _
    rw [M.probe_dilation_coordinate_norm T hunimod eW hB hBne w γ (scale n)]
    exact P.vertex_bound n q j
  · intro n q j
    have hs := M.probe_dilation_generator_step T F.N.equiv F.ExpN F.isExpN hbij dynkinN
      (h n) (P.vertex n q j.castSucc) (P.vertex n q j.succ) (P.mode n j)
      (P.coefficient n q j) (P.vertex_step n q j)
    simpa only [h, map_smul, smul_eq_mul] using hs

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanNeighborRowBasis
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed maximizing bases for affine neighboring rows -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier]


variable [Fintype I] [DecidableEq I]


variable (π : G →* Multiplicative W)
  (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
  (cell : Set W) (βcell : M.Bases)
  (X : I → H) {d : ℕ} (βD : WordBasisSelections X (boundedBracketWords d))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (pivot : Fin M.letterCount → H) (shrink B δ : ℝ)
  (S : Set C((Fin (finrank ℝ H) → ℝ), W))
  [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
  {Λ : ℝ≥0}
  (D : AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
    haarN chartN hchartN pivot shrink B δ S (Λ := Λ))

set_option maxHeartbeats 1000000 in
/-- Replace the row's varying bases by the fixed maximizing cell basis.
The original samples, profiles, law and supported affine pair are preserved. -/
def AffineNeighborRow.fixedBasis
    (hcell : IsCompact cell) (hne : cell.Nonempty)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW cell) βcell.val)
    (hδ : 0 ≤ δ) (hs : ∀ n, 0 ≤ D.scale n) :
    AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
      haarN chartN hchartN pivot shrink B δ S (Λ := Λ) := by
  classical
  let bound := M.exists_groupBox_basis_comparison T hunimod eW b₀
  let C := Classical.choose bound
  have hC : 1 ≤ C := (Classical.choose_spec bound).1
  have hcompare := (Classical.choose_spec bound).2
  have hβ' := M.maximizing_box_basis_smul T hunimod eW b₀ hcell hne
    (show 0 ≤ 1 + δ by linarith) βcell hβ
  refine { D with
    radius := fun n => C * D.radius n
    radius_nonneg := fun n => mul_nonneg (zero_le_one.trans hC) (D.radius_nonneg n)
    radius_subexponential := ?_
    basis := fun _ => βcell
    base_mem := fun n => hcompare _ βcell (D.basis n) hβ' (D.scale n) (hs n)
      (F.ExpN ∘ F.N.equiv) (D.radius n) (D.base_mem n)
    step_mem := fun n => hcompare _ βcell (D.basis n) hβ' (D.scale n) (hs n)
      (F.ExpN ∘ F.N.equiv) (D.radius n) (D.step_mem n)
    time_bound := ?_ }
  · exact (sequence_subexponential_upper_const D.grows C).mul
      D.radius_subexponential (Eventually.of_forall fun _ => zero_le_one.trans hC)
  · intro n
    apply (D.time_bound n).trans
    exact mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_left (D.radius_nonneg n) hC) (Real.exp_pos _).le

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPolarConeModels
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Published inputs for the finite polar-cone models

This record only groups the already stated nilpotent existence, integration
and exponential Haar inputs. It contains no metric or profile conclusion.
It is instantiated separately for each ray or two-ray cone used below.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (C : Set (H →ₗ[ℝ] ℝ))

set_option maxHeartbeats 1000000 in
/-- The six published inputs actually used to realize a specified cone.
Lee's nilpotent existence/integration and Le Donne's exponential Haar
statements retain their original Lean propositions. -/
structure PolarConeModelInputs : Prop where
  existsQ : NilpotentLieExistenceInput ((cartanRootIdeal H) ⧸ M.coneWordIdeal C)
  haarQ : ∀ Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C),
    NilpotentExponentialHaarInput Q.modelSpace Q.carrier
  integratesQ : ∀ Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C),
    NilpotentLieIntegrationInput (EN := F.N.modelSpace) (N := F.N.carrier)
      (EG := Q.modelSpace) (G := Q.carrier)
  existsI : NilpotentLieExistenceInput (M.coneWordIdeal C)
  haarI : ∀ I : NilpotentLieModel (M.coneWordIdeal C),
    NilpotentExponentialHaarInput I.modelSpace I.carrier
  integratesI : ∀ I : NilpotentLieModel (M.coneWordIdeal C),
    NilpotentLieIntegrationInput (EN := I.modelSpace) (N := I.carrier)
      (EG := F.N.modelSpace) (G := F.N.carrier)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end


