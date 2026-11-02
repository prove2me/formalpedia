-- Prove2me | Definitions.Def_OAIQ093D006
-- name    : OAIQ093D006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:05:10.963094+00:00
-- url     : https://prove2.me/theorems/9fb8809d-c090-4b9c-b287-33e21dba0ab1
-- title:
--   Definitions bundle OAIQ093D006 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 61 declarations of OpenAI's Lean: 7 definitions, 5 instances and 49 theorems. The definitions and types are `GeneratesNS.GL_W`, `GeneratesNS.GRep`, `GeneratesNS.GRepW_base`, `GeneratesNS.GRepW_non_invertible`, `GeneratesNS.G_n`, `GeneratesNS.W`, `GeneratesNS.Δ`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `CutoffInequality`, `Defs`, `Defs_LipschitzH`, `Defs_WordMetric`, `HarmonicR2`, `Harmonic_Convolution`, `Harmonic_LaplaceLinear`, `Harmonic_Proposition318`, `Harmonic_SelfAdjoint`, `Lemma326`, `LipschitzNorm`, `Packing`, `Poincare`, `PolycyclicRecognition_Algebra_HomogeneousWordCoefficients`, `PolycyclicRecognition_Algebra_RescaledGeneratorBounds`, `QuadraticForm`, `Representation`.
--
--   **Imports.** It imports the bundles `OAIQ093D000` and `OAIQ093D001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ093D012` and `OAIQ093D014`; the proofs of `GeneratesNS.word_norm_list_prod_le`, `GeneratesNS.word_norm_pow`, `OAI.PolycyclicRecognition.CartanWordModel.cartan_independent_raw_chain_concentration`, `OAI.PolycyclicRecognition.CartanWordModel.cartan_profile_segment_volume_sequence`, `OAI.PolycyclicRecognition.CartanWordModel.cartan_supported_profile_affine_sequence`, `OAI.PolycyclicRecognition.CartanWordModel.exists_compact_measurable_box_profiles`, `OAI.PolycyclicRecognition.CartanWordModel.exists_compact_template_profile_paths`, `OAI.PolycyclicRecognition.CartanWordModel.exists_concentrated_profile_frames`, `OAI.PolycyclicRecognition.CartanWordModel.exists_good_conjugated_word_paths`, `OAI.PolycyclicRecognition.cartan_cocycle_approximation`, `OAI.PolycyclicRecognition.cartan_cocycle_polynomial_boxes`, `OAI.PolycyclicRecognition.exists_bounded_box_profile_anchors` and `OAI.PolycyclicRecognition.exists_cartan_n_log_metric_bound`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ093D000
import Definitions.Def_OAIQ093D001

section
-- module Solutions.OAIQ093_PR.Defs_WordMetric
attribute [-instance] _root_.GeneratesNS.LipschitzH.add _root_.GeneratesNS.LipschitzH.addMonoid _root_.GeneratesNS.LipschitzH.instAddCommGroup _root_.GeneratesNS.LipschitzH.instAddCommMonoid _root_.GeneratesNS.LipschitzH.zero _root_.GeneratesNS.LipschitzH_seminorm _root_.GeneratesNS.WordDist.instBorelSpace _root_.GeneratesNS.WordDist.instBorelSpaceAddOpp _root_.GeneratesNS.WordDist.instMeasurableSpace _root_.GeneratesNS.WordDist.instMeasureableSpaceOpp _root_.GeneratesNS.WordDist.measureSpace _root_.GeneratesNS.countable_G _root_.GeneratesNS.countable_add_G _root_.GeneratesNS.discreteTopology _root_.GeneratesNS.fintype_closedBall _root_.GeneratesNS.instContinuousInvG _root_.GeneratesNS.instContinuousMulG _root_.GeneratesNS.instFunLikeLipschitzHGReal _root_.GeneratesNS.instIsTopologicalGroupG _root_.GeneratesNS.isometricGMul _root_.GeneratesNS.lipschitzHVectorSpace _root_.GeneratesNS.lipschitzSMul _root_.GeneratesNS.my_add_haar_right_invariant _root_.GeneratesNS.negLipschitzH _root_.GeneratesNS.subLipschithZ _root_.GeneratesNS.volume_mul_left_invariant _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
attribute [-simp] _root_.GeneratesNS.LipschitzH.add_apply _root_.GeneratesNS.LipschitzH.finset_sum_apply _root_.GeneratesNS.LipschitzH_apply _root_.GeneratesNS.ae_eq_everywhere _root_.GeneratesNS.lipschitz_add_tofun _root_.GeneratesNS.lipschitz_neg_tofun _root_.GeneratesNS.lipschitz_smul_tofun _root_.GeneratesNS.lipschitz_sub_tofun _root_.GeneratesNS.zero_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The `Generates` class and the word metric

The `Generates` class packaging a finitely generated group with a symmetric generating set, the
definition of polynomial growth, and the word norm / word metric on `G` with its `MetricSpace`
@[expose]
instance.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false
set_option linter.style.whitespace false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

@[expose]
instance G_FG: Group.FG G := {
  out := by
    unfold Subgroup.FG
    use S
    have foo := hGS.generates
    simp at foo
    exact foo
}


-- TODO - we might want to adjust our definition to avoid this annoying case
lemma word_norm_one: WordNorm 1 = 0 := by
  simp [WordNorm, ProdS]

lemma dist_word_mul {x y : G} (hy: y ∈ S): dist x (y * x) ≤ 1 := by
  simp [dist, WordDist, WordNorm]
  apply csInf_le
  . simp
  . simp
    use [⟨y, hy⟩]
    simp [ProdS]

lemma dist_word_mul_le {x y z : G} (hy: y ∈ S): dist x (y * z) ≤ 1 + dist x z := by
  conv =>
    lhs
    simp [dist, WordDist, WordNorm]

  grw [csInf_le (a := 1 + (WordDist x z))]
  . simp [dist]
  . simp
  . simp

    have dist_eq: dist x z = dist x z := rfl
    conv at dist_eq =>
      lhs
      simp [dist, WordDist, WordNorm]

    have inf_mem := csInf_mem (s := {n | ∃ l, l.length = n ∧ ProdS (z * x⁻¹) l}) ?_
    .
      simp at inf_mem
      obtain ⟨l, l_len, l_prod⟩ := inf_mem
      simp [ProdS] at l_prod
      use [⟨y, hy⟩] ++ l
      simp [l_len, WordDist, WordNorm]
      rw [add_comm]
      simp
      simp [ProdS]
      rw [l_prod]
      group
    .
      obtain ⟨l, l_prod⟩ := mem_S_prod_list (z * x⁻¹)
      use l.length
      simp
      use l


lemma dist_word_le_mul {x y z : G} (hy: y ∈ S): WordDist x z ≤ (WordDist x (y * z)) + 1 := by
  by_cases x_eq: x = y * z
  . simp [x_eq]
    rw [WordDist_self]
    simp
    simp [WordDist_comm]
    have mul_dist := dist_word_mul (x := z) (y := y) hy
    simp [dist] at mul_dist
    exact mul_dist


  conv =>
    lhs
    simp [dist, WordDist, WordNorm]


  grw [csInf_le (a := (WordDist x (y * z)) + 1)]
  .
    simp


  simp
  obtain ⟨l, l_prod, l_len⟩ := word_norm_prod (n := WordDist x (y * z)) (y * z * x⁻¹) (rfl)
  match l with
  | [] =>
    simp [ProdS] at l_prod
    simp at l_len
    simp [← l_len]
    simp [ProdS]
    rw [eq_comm] at l_prod
    rw [mul_inv_eq_one] at l_prod
    grind
  | h::tail =>
    use [ ⟨y⁻¹, by simp [hGS.has_inv, hy]⟩, ⟨h.val, by simp [hGS.has_inv]⟩,] ++ tail
    simp [ProdS]
    simp [← l_len]
    simp [ProdS] at l_prod
    simp [l_prod]
    group

lemma word_dist_mul_eq {x y z : G} (hy: y ∈ S): WordDist x z = (WordDist x (y * z)) + 1 ∨ WordDist x z + 1 = (WordDist x (y * z)) ∨ WordDist x z = (WordDist x (y * z)) := by
  have first := dist_word_le_mul (x := x) (y := y) (z := z) hy
  have second := dist_word_le_mul (x := x) (y := y⁻¹) (z := (y * z)) (by rw [S_eq_Sinv]; simp [hy])
  simp at second
  grind

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Defs_LipschitzH
attribute [-instance] _root_.GeneratesNS.LipschitzH_seminorm _root_.GeneratesNS.fintype_closedBall _root_.GeneratesNS.isometricGMul _root_.GeneratesNS.volume_mul_left_invariant _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Lipschitz harmonic functions

The type `LipschitzH` of Lipschitz harmonic functions on `G`, its additive and vector space
structure, and finiteness of balls.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false
set_option linter.style.whitespace false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

/-- Nothing here is ever evaluated, and there is no computable equality test on `LipschitzH`
anyway, so decide equality classically once and for all. Supplying a single concrete instance
for this one type — rather than `open Classical`, which also overrides the *computable*
instances on e.g. `G` and `Fin n` — means every `DecidableEq` on `LipschitzH`, on a subspace
`↥V`, or on a basis index `↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)` resolves to the same term,
so no diamonds arise. Same idiom as `GL_W_DecidableEq` in `Gromov.lean`. -/
noncomputable instance LipschitzH_DecidableEq: DecidableEq (LipschitzH) :=
  Classical.typeDecidableEq _

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Defs
attribute [-instance] _root_.GeneratesNS.LipschitzH_seminorm _root_.GeneratesNS.volume_mul_left_invariant _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The discrete Laplacian and the `G`-action

The Laplacian `Laplace_b` / `Laplace`, the constant functions `ConstF`, the quotient `W`, the
`G`-action `gAct`, and the closed-ball counting lemmas.

Root of the `Gromov.Defs` hierarchy: importing it pulls in the word metric, the measure
structure, `LipschitzH` and the convolution API.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false
set_option linter.style.whitespace false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped Convolution
open MeasureTheory

abbrev W := (LipschitzH) ⧸ ConstF

lemma closed_ball_eq_S_pow (R: ℕ): (finite_closed_ball 1 R).toFinset = S ^ R := by
  ext a
  refine ⟨?_, ?_⟩
  . intro ha
    simp [dist, WordDist_one] at ha
    rw [Finset.mem_pow]
    obtain ⟨l, l_prod, l_len⟩ := word_norm_prod_self a
    let padded := l ++ List.replicate (R - WordNorm a) ⟨1, one_mem⟩
    simp_rw [← Function.comp_def]
    simp_rw [← List.map_ofFn]
    conv =>
      arg 1
      intro f
      lhs
      arg 1
      equals (List.ofFn f).unattach =>
        rfl

    have padded_len: padded.length = R := by
      unfold padded
      simp [l_len]
      grind
    use fun n => padded.get ⟨n, by (
      grind
    )⟩
    rw [List.ofFn_congr padded_len.symm]
    simp
    unfold padded
    simp
    simp [ProdS] at l_prod
    rw [← l_prod]
  . intro hb
    rw [Finset.mem_pow] at hb
    simp [dist, WordDist_one]
    obtain ⟨f, hf⟩ := hb
    conv at hf =>
      lhs
      arg 1
      equals (List.ofFn f).unattach =>
        simp_rw [← Function.comp_def]
        simp_rw [← List.map_ofFn]
        rfl

    have r_eq: R = (List.ofFn f).length := by
      simp
    rw [r_eq]
    apply word_norm_le
    simp [ProdS, hf]

lemma card_closed_ball_eq (R: ℕ): #((finite_closed_ball 1 R).toFinset) = #(S ^ R) := by
  rw [closed_ball_eq_S_pow]


-- Proposition 1.5 helper (moved from Harmonic.lean)
lemma laplace_sum_swap_helper {f g: G → ℝ} (hgf: f.support.Finite ∨ g.support.Finite): ∑' (x: G), (f x) * (Laplace_b g) x = 2⁻¹ * ∑' (x: G), ((#(S) : ℝ)⁻¹) * ∑ s ∈ S, (((f x) - (f (s * x))) * ((g x) - (g (s * x)))) := by
  simp_rw [sub_mul]
  simp_rw [Finset.sum_sub_distrib]
  simp_rw [Laplace_b, f_conv_mu]
  simp
  simp_rw [← Finset.mul_sum]
  simp_rw [Finset.sum_sub_distrib]
  simp
  have foo := S_card_ne_zero_re
  conv =>
    rhs
    rhs
    arg 1
    intro x
    rw [mul_sub (#S : ℝ)⁻¹]
    lhs
    rw [← mul_assoc]
    rw [mul_sub]
    ring_nf
    rw [mul_inv_cancel₀ (by apply S_card_ne_zero_re)]


  simp
  rw [Summable.tsum_sub]

  conv =>
    rhs
    rhs
    rhs
    arg 1
    intro x
    rw [Finset.mul_sum]
  rename_bvar b → x
  rw [Summable.tsum_finsetSum]
  .
    conv =>
      rhs
      rhs
      rhs
      arg 2
      intro s
      rw [← Equiv.tsum_eq (Equiv.mulLeft s⁻¹)]
      simp


    rw [← Summable.tsum_finsetSum]
    .
      simp_rw [← mul_assoc]
      simp_rw [mul_sub ((#S : ℝ)⁻¹ * _)]
      simp_rw [Finset.sum_sub_distrib]
      simp
      simp_rw [← mul_assoc]
      rw [mul_inv_cancel₀ (by apply S_card_ne_zero_re)]
      simp
      rename_bvar b → x
      conv =>
        rhs
        rhs
        rhs
        arg 1
        intro x
        rw [← neg_sub]
        rw [← Finset.mul_sum]
        rw [Finset.sum_equiv (Equiv.inv _) (s := S) (t := S) (g := fun s => g (s * x)) (by
          intro s
          simp
          nth_rw 2 [S_eq_Sinv]
          simp
        ) (by
          intro s
          simp
        )]


      rw [tsum_neg]
      simp
      rename_bvar b → x
      rw [← mul_two]
      simp_rw [mul_comm _ (f _), mul_assoc]
      simp_rw [← mul_sub]
      ring
    .
      intro s hs
      apply Summable.mul_left
      apply summable_of_finite_support
      unfold Function.HasFiniteSupport
      simp
      clear foo
      wlog hg: g.support.Finite
      .
        apply Set.Finite.inter_of_left
        have hf := hgf
        simp [hg] at hf
        exact hf
      .
        apply Set.Finite.inter_of_right
        apply Set.Finite.subset ?_ (Function.support_sub _ _)
        simp
        refine ⟨?_, hg⟩
        rw [← Function.comp_def]
        rw [Function.support_comp_eq_preimage]
        apply Set.Finite.preimage'
        . apply hg
        . intro x hx
          simp
  .
  -- TODO - deduplicate this
      intro s hs
      apply Summable.mul_left
      apply summable_of_finite_support
      unfold Function.HasFiniteSupport
      simp
      wlog hg: g.support.Finite
      .
        apply Set.Finite.inter_of_left
        have hf := hgf
        simp [hg] at hf
        rw [← Function.comp_def]
        rw [Function.support_comp_eq_preimage]
        apply Set.Finite.preimage'
        . apply hf
        . intro x hx
          simp
      .
        apply Set.Finite.inter_of_right
        apply Set.Finite.subset ?_ (Function.support_sub _ _)
        simp
        refine ⟨hg, ?_⟩
        rw [← Function.comp_def]
        rw [Function.support_comp_eq_preimage]
        apply Set.Finite.preimage'
        . apply hg
        . intro x hx
          simp
  .
    apply Summable.sub
    apply summable_of_finite_support
    .
      unfold Function.HasFiniteSupport
      simp
      cases hgf
      . apply Set.Finite.inter_of_left
        grind
      . apply Set.Finite.inter_of_right
        grind
    .
      simp_rw [mul_assoc]
      apply Summable.mul_left
      simp_rw [Finset.mul_sum]
      apply summable_sum
      intro s hs
      apply summable_of_finite_support
      unfold Function.HasFiniteSupport
      simp
      cases hgf
      . rename_i hf
        apply Set.Finite.inter_of_left
        apply hf
      .
        rename_i hg
        apply Set.Finite.inter_of_right
        rw [← Function.comp_def]
        rw [Function.support_comp_eq_preimage]
        apply Set.Finite.preimage'
        . apply hg
        . intro x hx
          simp
  .
    apply Summable.mul_left
    apply summable_sum
    intro s hs
    simp_rw [mul_sub]
    apply Summable.sub
    .
      apply summable_of_finite_support
      unfold Function.HasFiniteSupport
      simp
      cases hgf
      . rename_i hf
        apply Set.Finite.inter_of_left
        rw [← Function.comp_def]
        rw [Function.support_comp_eq_preimage]
        apply Set.Finite.preimage'
        . apply hf
        . intro x hx
          simp
      . rename_i hg
        apply Set.Finite.inter_of_right
        apply hg
    .
      apply summable_of_finite_support
      unfold Function.HasFiniteSupport
      simp
      cases hgf
      . rename_i hf
        apply Set.Finite.inter_of_left
        rw [← Function.comp_def]
        rw [Function.support_comp_eq_preimage]
        apply Set.Finite.preimage'
        . apply hf
        . intro x hx
          simp
      . rename_i hg
        apply Set.Finite.inter_of_right
        rw [← Function.comp_def]
        rw [Function.support_comp_eq_preimage]
        apply Set.Finite.preimage'
        . apply hg
        . intro x hx
          simp


lemma laplace_prod_harmonic (f φ : G → ℝ)  (hf: Laplace_b  f = 0) (x: G): Laplace_b (f * φ) x = ((1 : ℝ) / (#(S) : ℝ)) * ∑ s ∈ S, f (s * x) * ((φ (x) - φ (s * x))) := by
  simp_rw [Laplace_b]
  simp_rw [f_conv_mu]
  simp
  simp_rw [Laplace_b] at hf
  conv =>
    rhs
    simp [mul_sub]
    simp [← Finset.sum_mul]

  simp_rw [f_conv_mu] at hf
  apply_fun (fun f => f x) at hf
  simp at hf
  rw [← mul_assoc]
  rw [sub_eq_zero] at hf
  rw [← hf]


end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.LipschitzNorm
attribute [-instance] _root_.GeneratesNS.volume_mul_left_invariant _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The Lipschitz seminorm on `LipschitzH`

This file collects the Lipschitz seminorm `LipschitzSemiNorm` on functions `G → ℝ`, the basic
lemmas about it, and the resulting `SeminormedAddCommGroup` / `NormedSpace` instances on
`LipschitzH`. These instances are public so that they are available to downstream files.

Note that we only implement `SeminormedAddCommGroup` for `LipschitzH`, so this is only really a
seminormed space. The quotient space `W := LipschitzH ⧸ ConstF` is an actual normed space.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false

namespace GeneratesNS
open Generates


variable [hGS: Generates]
include hGS

-- Note that we only implement SeminormedAddCommGroup for LipschitzH, so this is only
-- really a seminormed space. The quotient space W := LipschitzH ⧸ ConstF
-- is an actual normed space.
noncomputable instance LipschitzH_normed: NormedSpace ℝ (LipschitzH) where
  norm_smul_le := by
    intro c f
    simp [HSMul.hSMul, SMul.smul]
    simp [norm]
    conv =>
      lhs
      simp [LipschitzSemiNorm]
    norm_cast
    apply csInf_le (by
      simp [BddBelow]
      apply Set.nonempty_of_mem (x := 0)
      rw [mem_lowerBounds]
      simp
    )
    simp
    let K := LipschitzSemiNorm f
    have hK := lipschitz_attains_norm f (f.lipschitz)
    use ‖ (c * K) ‖₊
    simp
    have comp_mul_const := LipschitzWith.comp (Kf := ‖c‖₊) (Kg := K) (f := fun x => c • x) (g := f.toFun) (by apply lipschitzWith_smul) hK
    simp at comp_mul_const
    conv =>
      lhs
      arg 2
      simp [DFunLike.coe]
      equals (fun x ↦ c • x) ∘ f.toFun => rfl


    refine ⟨comp_mul_const, ?_⟩
    left
    simp [K]

lemma iterated_lipschitz_bound (f: LipschitzH): ∀ g: G, ‖f g‖ ≤ (LipschitzSemiNorm f + ‖f 1‖) * (1 + WordNorm g) := by
  intro g
  induction hg: WordNorm g using Nat.strong_induction_on generalizing g with
  | h n ih =>
    obtain ⟨l, l_prod, l_len⟩ := word_norm_prod _ _ hg
    simp [ProdS] at l_prod
    by_cases n_eq: n = 0
    .
      simp [n_eq]
      simp [n_eq] at l_len
      simp [l_len] at l_prod
      simp [← l_prod]
    .
      obtain ⟨head, tail, l_eq⟩ := List.exists_cons_of_length_pos (l := l) (by grind)
      have tail_norm := word_norm_le tail.unattach.prod tail (by simp [ProdS])
      specialize ih (WordNorm tail.unattach.prod) (by grind) tail.unattach.prod rfl
      rw [← l_prod, l_eq]
      simp
      have foo := lipschitz_attains_norm f.toFun f.lipschitz
      unfold LipschitzWith at foo
      have s_dist := foo (head * tail.unattach.prod) tail.unattach.prod
      rw [edist_dist] at s_dist
      conv at s_dist =>
        rhs
        equals ENNReal.ofReal (LipschitzSemiNorm f *  (dist (↑head * tail.unattach.prod) tail.unattach.prod)) =>
          rw [ENNReal.ofReal_mul, ENNReal.ofReal_coe_nnreal]
          rw [edist_dist]
          .
            rfl
          . simp
      rw [ENNReal.ofReal_le_ofReal_iff] at s_dist
      .
        apply norm_le_norm_add_const_of_dist_le at s_dist
        simp only [Real.norm_eq_abs] at s_dist
        grw [s_dist]
        simp [DFunLike.coe] at ih
        grw [ih]
        rw [dist_comm]
        grw [dist_word_mul_le]
        .
          simp [dist, WordDist, word_norm_one]
          grw [tail_norm]
          have tail_len_le: tail.length ≤ n - 1 := by
            grind
          grw [tail_len_le]
          norm_cast
          rw [Nat.add_sub_of_le (by grind)]
          simp [DFunLike.coe]
          ring
          norm_cast
          conv =>
            lhs
            lhs
            arg 1
            equals (LipschitzSemiNorm f.toFun) * (n + 1) =>
              ring
          nth_rw 2 [add_comm]
          simp
          norm_cast
          simp
          rw [mul_add]
          simp
        . simp
      . positivity
        
end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.CutoffInequality
attribute [-instance] _root_.GeneratesNS.volume_mul_left_invariant _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The cutoff inequality

`cutoff_inequality`, the discrete integration-by-parts estimate underlying Theorem 3.23.
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

set_option maxHeartbeats 9000000 in
lemma cutoff_inequality (f φ : G → ℝ) (hf: Laplace_b f = 0) (hφ: φ.support.Finite):
    ∑' (x: G), ∑ s ∈ S, ((f x * φ x) - (f (s * x) * φ (s * x)))^2 ≤  ∑' (x: G), ∑ s ∈ S, (f x)^2 * (φ (s * x) - φ x)^2  := by

  conv =>
    lhs
    arg 1
    intro x
    arg 2
    intro s
    rw [pow_two]
  apply le_of_mul_le_mul_left (a := 2⁻¹ * (↑(#S) : ℝ)⁻¹) (a0 := by simp [S_nonempty])
  rw [mul_assoc]
  rw [← tsum_mul_left]
  rw [← laplace_sum_swap_helper]
  .
    conv =>
      lhs
      arg 1
      intro x
      rw [← Pi.mul_def]
      rw [laplace_prod_harmonic (hf := hf)]
      rw [← mul_assoc]
      rw [mul_comm (f x * φ x)]
      rw [mul_assoc, mul_assoc]
      rw [Finset.mul_sum]

    rw [tsum_mul_left]
    simp_rw [Finset.mul_sum]
    simp_rw [mul_comm (f _)]
    rw [Summable.tsum_finsetSum]
    .
      conv =>
        lhs
        rhs
        arg 2
        intro s
        rw [← Equiv.tsum_eq (Equiv.mulLeft s⁻¹)]
        simp

      nth_rw 2 [S_eq_Sinv]
      simp

      have sum_swap: ∑ x ∈ S, ∑' (c : G), φ (x * c) * ((φ (x * c) - φ c) * f c) * f (x * c) = -∑ x ∈ S, ∑' (c : G), φ (c) * ((φ (x * c) - φ c) * f (x * c)) * f (c) := by
        conv =>
          lhs
          arg 2
          intro s
          rw [← Equiv.tsum_eq (Equiv.mulLeft s⁻¹)]
          simp
        nth_rw 2 [S_eq_Sinv]
        simp
        rw [← Finset.sum_neg_distrib]
        simp_rw [← tsum_neg]
        ring

      have double {a b: ℝ} (hab: a = b): a = (a + b) / 2 := by
        rw [hab]
        ring

      rw [double sum_swap]
      rw [← sub_eq_add_neg]
      conv =>
        lhs
        rhs
        lhs
        rhs
        arg 2
        intro s
        arg 1
        intro x
        equals (((φ (s * x) - φ x) * f (s * x)) * f x) * (φ x) =>
          ring

      conv =>
        lhs
        rhs
        lhs
        lhs
        arg 2
        intro s
        arg 1
        intro x
        equals (((φ (s * x) - φ x) * f (s * x)) * f (x)) * φ (s * x)  =>
          ring

      rw [← Finset.sum_sub_distrib]
      conv =>
        lhs
        rhs
        arg 1
        arg 2
        intro s
        rw [← Summable.tsum_sub (by
          apply summable_of_hasFiniteSupport
          unfold Function.HasFiniteSupport
          simp
          apply Set.Finite.inter_of_right
          rw [← Function.comp_def]
          rw [Function.support_comp_eq_preimage]
          apply Set.Finite.preimage'
          . apply hφ
          . intro x hx
            simp
        ) (by
          apply summable_of_hasFiniteSupport
          unfold Function.HasFiniteSupport
          simp
          apply Set.Finite.inter_of_right
          apply hφ
        )]
      simp_rw [← mul_sub]
      conv =>
        lhs
        rhs
        lhs
        arg 2
        intro s
        arg 1
        intro x
        equals (f (s * x)) * f x * ((φ (s * x) - φ x))^2 =>
          ring

      have f_prod (x s: G): f (s * x) * (f x) ≤ (f (s * x)^2 + (f x)^2) / 2 := by
        field_simp
        rw [mul_comm]
        rw [← mul_assoc]
        apply two_mul_le_add_sq

      rw [div_eq_inv_mul]
      rw [← mul_assoc]
      nth_rw 2 [mul_comm]
      rw [mul_le_mul_iff_of_pos_left]
      calc
        ∑ s ∈ S, ∑' (x : G), f (s * x) * f x * (φ (s * x) - φ x) ^ 2 ≤ ∑ s ∈ S, ∑' (x : G), (f (s * x)^2 +  (f x)^2) * 2⁻¹ * (φ (s * x) - φ x) ^ 2 := by

          apply Finset.sum_le_sum
          intro s hs
          apply Summable.tsum_le_tsum
          intro x
          grw [f_prod]
          field_simp
          . simp
          .
            apply summable_of_finite_support
            unfold Function.HasFiniteSupport
            simp
            apply Set.Finite.inter_of_right
            apply Set.Finite.subset ?_ (Function.support_sub _ _)
            simp
            refine ⟨?_, hφ⟩
            rw [← Function.comp_def]
            rw [Function.support_comp_eq_preimage]
            apply Set.Finite.preimage'
            . apply hφ
            . intro x hx
              simp
          .
            apply summable_of_finite_support
            unfold Function.HasFiniteSupport
            simp
            apply Set.Finite.inter_of_right
            apply Set.Finite.subset ?_ (Function.support_sub _ _)
            simp
            refine ⟨?_, hφ⟩
            rw [← Function.comp_def]
            rw [Function.support_comp_eq_preimage]
            apply Set.Finite.preimage'
            . apply hφ
            . intro x hx
              simp
        _ ≤ _ := by
          simp_rw [add_mul]
          conv =>
            lhs
            arg 2
            intro s
            rw [Summable.tsum_add (by
              apply summable_of_finite_support
              unfold Function.HasFiniteSupport
              simp
              apply Set.Finite.inter_of_right
              apply Set.Finite.subset ?_ (Function.support_sub _ _)
              simp
              refine ⟨?_, hφ⟩
              rw [← Function.comp_def]
              rw [Function.support_comp_eq_preimage]
              apply Set.Finite.preimage'
              . apply hφ
              . intro x hx
                simp
            ) (by
                apply summable_of_finite_support
                unfold Function.HasFiniteSupport
                simp
                apply Set.Finite.inter_of_right
                apply Set.Finite.subset ?_ (Function.support_sub _ _)
                simp
                refine ⟨?_, hφ⟩
                rw [← Function.comp_def]
                rw [Function.support_comp_eq_preimage]
                apply Set.Finite.preimage'
                . apply hφ
                . intro x hx
                  simp
            )]
          rw [Finset.sum_add_distrib]
          conv =>
            lhs
            lhs
            arg 2
            intro s
            rw [← Equiv.tsum_eq (Equiv.mulLeft s⁻¹)]
            simp
          nth_rw 1 [S_eq_Sinv]
          simp
          rename_bvar c → b
          simp_rw [sub_sq_comm]
          field_simp
          norm_num
          field_simp
          simp_rw [tsum_div_const]
          rw [← Finset.sum_div]
          field_simp
          rw [← Summable.tsum_finsetSum]
          intro s hs
          apply summable_of_finite_support
          unfold Function.HasFiniteSupport
          simp
          apply Set.Finite.inter_of_right
          apply Set.Finite.subset ?_ (Function.support_sub _ _)
          simp
          refine ⟨hφ, ?_⟩
          rw [← Function.comp_def]
          rw [Function.support_comp_eq_preimage]
          apply Set.Finite.preimage'
          . apply hφ
          . intro x hx
            simp
      . simp [S_nonempty]
    .
      intro s hs
      apply summable_of_finite_support
      unfold Function.HasFiniteSupport
      simp
      apply Set.Finite.inter_of_left
      apply Set.Finite.inter_of_left
      apply hφ
  . left
    simp
    apply Set.Finite.inter_of_right
    apply hφ

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.HarmonicR2
attribute [-instance] _root_.GeneratesNS.volume_mul_left_invariant _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The harmonic `R²` inequality

`harmonic_r2_inequality`, bounding a harmonic function on a ball of radius `R` by its values on
a ball of radius `2R`.
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

set_option maxHeartbeats 9000000 in
lemma harmonic_r2_inequality (f : G → ℝ) (hf : Laplace_b f = 0) (r: ℕ) (hr: r ≠ 0):
    ∑ x ∈ Metric.closedBall 1 (2 * r), deriv_sq f x ≤ ((1: ℝ) / r^2) * #(S) * ∑ x ∈ Metric.closedBall 1 (4 * r), f x ^ 2 := by
  -- `deriv_sq f x = ∑ s, (f (s*x) - f x)^2`; the proof below is written with the
  -- (equal) `(f x - f (s*x))^2` orientation, so rewrite to that first.
  have hrw : ∀ x : G, deriv_sq f x = ∑ s ∈ S, (f x - f (s * x)) ^ 2 := fun x => by
    simp only [deriv_sq]; exact Finset.sum_congr rfl fun s _ => by ring
  simp_rw [hrw]

  -- m * x + b
  -- m * (4*r) + b = 0
  -- b = -4 * r * m

  -- m * (2 *r) - * (4 * r * m) = 1
  -- 2rm - 4rm = 1
  -- m = -1/2
  let φ := fun (x: G) => if WordNorm x ≤ (2 * r) + 1 then 1 else if (WordNorm x ≤ 4 * r) then (-(WordNorm x)/(2 * (r: ℝ))) + 2 else 0
  have phi_support : φ.support ⊆ Metric.ball 1 (4 * r) := by
    intro s hs
    simp at hs
    rw [ite_eq_iff] at hs
    simp at hs
    by_cases s_gt: 2 * r + 1 < (WordNorm s)
    .
      specialize hs s_gt
      simp [dist]
      rw [WordDist_one]
      by_cases eq_four: WordNorm s = 4*r
      .
        simp [eq_four] at hs
        field_simp [hr] at hs
        norm_num at hs
      .
        norm_cast
        grind
    .
      simp at s_gt
      simp [dist, WordDist_one]
      norm_cast
      grind

  have foo := cutoff_inequality f φ hf ?_
  .
    rw [tsum_eq_sum (s := (finite_closed_ball 1 (4 * r)).toFinset)] at foo
    rw [tsum_eq_sum (s := (finite_closed_ball 1 (4 * r)).toFinset)] at foo
    .
      grw [← Finset.sum_le_sum_of_subset_of_nonneg (s := (finite_closed_ball 1 (2 * r)).toFinset)] at foo
      .
        rw [Finset.sum_congr (g := fun x => ∑ s ∈ S, (f x - f (s * x)) ^ 2) (s₂ := (finite_closed_ball 1 (2 * r)).toFinset)] at foo
        .
          simp at foo
          grw [foo]
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro x hx
          conv =>
            rhs
            rw [mul_assoc]
            rhs
            equals ∑ s ∈ S, (f x)^2 =>
              simp
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro s hs
          simp [φ]
          have norm_s_x := word_dist_mul_eq (x := 1) (y := s) (z := x) hs
          simp_rw [WordDist_comm] at norm_s_x
          simp_rw [WordDist_one] at norm_s_x
          rw [← or_assoc] at norm_s_x
          cases norm_s_x
          .
            rename_i norm_s_x_eq
            cases norm_s_x_eq
            .
              rename_i s_lt
              simp [dist] at hx
              norm_cast at hx
              rw [WordDist_one] at hx
              by_cases s_x_le: WordNorm (s * x) ≤ 2 *r + 1
              .
                simp [s_x_le]
                simp [s_lt]
                split_ifs
                . simp
                  positivity
                .
                  have s_x_eq: WordNorm (s * x) = 2 *r + 1 := by grind
                  simp [s_x_eq]
                  field_simp
                  apply mul_le_mul
                  . simp
                  .
                    norm_num
                    ring
                    norm_num
                  . positivity
                  . positivity
                .
                  grind
              .
                have sub_eq: (WordNorm x) - 1 = WordNorm (s * x) := by omega
                have s_x_le_four: WordNorm (s * x) ≤ 4 * r := by
                  simp [s_lt] at hx
                  grind
                simp [s_x_le, s_x_le_four]
                split_ifs
                .
                  grind
                .
                  simp [← sub_eq]
                  rw [← sub_div]
                  simp
                  field_simp
                  push_cast
                  conv =>
                    lhs
                    rhs
                    lhs
                    equals 1 =>
                      rw [sub_eq]
                      rw [s_lt]
                      push_cast
                      ring
                  simp
                  norm_num
                  -- TODO - surely this can be simplified
                  by_cases f_x_zero: (f x) ^2 = 0
                  . simp [f_x_zero]

                  rw [le_mul_iff_one_le_right]
                  . norm_num
                  . positivity
            .
              rename_i s_lt
              simp [dist] at hx
              norm_cast at hx
              rw [WordDist_one] at hx
              by_cases s_x_le: WordNorm (s * x) ≤ 2*r + 1
              .
                simp [s_x_le]
                split_ifs
                . simp
                  positivity
                .
                  have s_x_eq: WordNorm (s * x) = 2 *r := by grind
                  simp [s_x_eq]
                  rw [mul_comm]
                  apply mul_le_mul
                  .
                    norm_num
                    ring
                    norm_num
                    field_simp
                    rw [mul_sub]
                    rw [← pow_two]
                    rw [sub_mul]
                    conv =>
                      lhs
                      equals (2 * r) * (2 * r) - (WordNorm x) * 2 * r * 2 + (WordNorm x)^2 =>
                        ring
                    rename_i x_gt
                    simp at x_gt
                    omega
                  . simp
                  . positivity
                  . norm_num
              .
                by_cases norm_x_eq: WordNorm x = 4 * r
                .
                  have not_le: ¬(WordNorm (s * x) ≤ (2 *r) + 1) := by grind
                  have not_le_four: ¬(WordNorm (s * x) ≤ (4 *r)) := by grind
                  have x_le: (WordNorm (x) ≤ (4 *r)) := by grind
                  have not_x_le: ¬(WordNorm (x) ≤ (2 *r) + 1) := by grind
                  simp [not_le, not_le_four, x_le, not_x_le]
                  rw [mul_comm]
                  -- TODO - surely this can be simplified
                  by_cases f_x_zero: (f x) ^2 = 0
                  . simp [f_x_zero]
                  rw [mul_le_mul_iff_left₀]
                  .
                    field_simp
                    grw [x_le]
                    grind
                    simp
                    norm_num
                    simp [norm_x_eq]
                  . positivity

                have sub_eq: (WordNorm x) = WordNorm (s * x) - 1 := by omega
                have s_x_le_four: WordNorm (s * x) ≤ 4 * r := by
                  rw [← s_lt]
                  grind
                simp [s_x_le, s_x_le_four]
                split_ifs
                .
                  field_simp
                  -- TODO - surely this can be simplified
                  by_cases f_x_zero: (f x) ^2 = 0
                  . simp [f_x_zero]

                  rw [mul_le_mul_iff_right₀]
                  .
                    norm_num
                    field_simp
                    conv =>
                      lhs
                      lhs
                      ring
                    conv =>
                      rhs
                      equals (2^2) =>
                        norm_num

                    have norm_x_eq: WordNorm x = 2 *r + 1 := by grind
                    rw [← s_lt, norm_x_eq]
                    conv =>
                      lhs
                      lhs
                      simp
                      field_simp
                      ring
                    norm_num

                  . positivity
                .
                  simp [← sub_eq]
                  rw [← sub_div]
                  simp
                  field_simp
                  push_cast
                  conv =>
                    lhs
                    rhs
                    lhs
                    equals -1 =>
                      rw [sub_eq]
                      push_cast
                      rw [Nat.cast_sub (by grind)]
                      ring
                  simp
                  norm_num
                  -- TODO - surely this can be simplified
                  by_cases f_x_zero: (f x) ^2 = 0
                  . simp [f_x_zero]

                  rw [le_mul_iff_one_le_right]
                  . norm_num
                  . positivity

          .
            rename_i norm_eq
            simp [← norm_eq]
            positivity
        . rfl
        . intro x hx
          apply Finset.sum_congr
          . rfl
          . intro s hs
            simp [φ]
            simp [dist, WordDist_one] at hx
            norm_cast at hx
            have hx_le : WordNorm x ≤ 2 * r + 1 := by grind
            simp [hx_le]

            have hx_le_sub : WordNorm x ≤ 2 * r := by grind
            have foo := dist_word_le_mul (x := 1) (y := s⁻¹) (z := (s * x)) (by rw [S_eq_Sinv]; simp [hs])
            simp at foo
            simp [WordDist_comm, WordDist_one] at foo

            grw [hx_le_sub] at foo
            simp [foo]
      . simp
        intro a ha
        simp at ha
        simp
        grind
      .
        intro a ha ha2
        positivity
    .
      intro s hs
      simp at hs
      apply Finset.sum_eq_zero
      intro x hx
      have phi_s := Set.notMem_subset phi_support (a := s) ?_
      .
        simp at phi_s
        simp [phi_s]
        have phi_s_x := Set.notMem_subset phi_support (a := x * s)
        .
          simp at phi_s_x
          simp [dist] at hs
          rw [WordDist_comm] at hs
          grw [dist_word_le_mul (y := x)] at hs
          simp at hs
          simp [dist] at phi_s_x
          norm_cast at hs
          norm_cast at phi_s_x
          rw [Nat.lt_add_one_iff] at hs
          rw [WordDist_comm] at hs
          specialize phi_s_x hs
          simp [phi_s_x]
          exact hx
      . simp
        grind
    .
      -- TODO - deduplicate this
      intro s hs
      simp at hs
      apply Finset.sum_eq_zero
      intro x hx
      have phi_s := Set.notMem_subset phi_support (a := s) ?_
      .
        simp at phi_s
        simp [phi_s]
        have phi_s_x := Set.notMem_subset phi_support (a := x * s)
        .
          simp at phi_s_x
          simp [dist] at hs
          rw [WordDist_comm] at hs
          grw [dist_word_le_mul (y := x)] at hs
          simp at hs
          simp [dist] at phi_s_x
          norm_cast at hs
          norm_cast at phi_s_x
          rw [Nat.lt_add_one_iff] at hs
          rw [WordDist_comm] at hs
          specialize phi_s_x hs
          simp [phi_s_x]
          exact hx
      . simp
        grind

  .
    simp [φ]
    apply Set.Finite.subset (s := Metric.ball 1 (4 * r))
    .
      apply finite_ball
    . exact phi_support

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.QuadraticForm
attribute [-instance] _root_.GeneratesNS.volume_mul_left_invariant _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The quadratic form `Q_R` and its determinant bound

The quadratic form `Q_R` on `LipschitzH`, its matrix `Q_R_matrix`, positive-definiteness, and
the determinant bound `det_bound` for a fixed finite-dimensional subspace `V`.
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

lemma Q_R_self_nonneg (R : ℝ) (v : G → ℝ) : 0 ≤ Q_R R v v := by
  simp [Q_R, ← pow_two] <;> positivity

open scoped Topology

section V_variable

variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V]

@[expose]
instance nonempty_basis: Nonempty ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V) := Module.Basis.index_nonempty (Module.Basis.ofVectorSpace _ _)

-- TODO - generalize and upstream
omit hGS in
lemma euclidean_of_lp_le {ι : Type*} [Fintype ι] (x: EuclideanSpace ℝ ι) (i: ι):
    |x.ofLp i| ≤ ‖x‖ := by

  rw [EuclideanSpace.norm_eq]
  rw [Real.le_sqrt]
  .
    simp
    apply Finset.single_le_sum (a := i)
    . intro i _
      positivity
    . simp
  . simp
  . positivity

omit V_finite [Nontrivial ↥V] in
lemma le_max_lipschitz {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) (i) : v_lipschitz_constant b i ≤ max_lipschitz b :=
  (Finite.exists_max (v_lipschitz_constant b)).choose_spec i

omit V_finite [Nontrivial ↥V] in
lemma le_max_origin {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) (i) : v_origin_norm b i ≤ max_origin b :=
  (Finite.exists_max (v_origin_norm b)).choose_spec i

omit V_finite [Nontrivial ↥V] in
lemma max_lipschitz_nonneg {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) : 0 ≤ max_lipschitz b := by
  unfold max_lipschitz v_lipschitz_constant; positivity

omit V_finite [Nontrivial ↥V] in
lemma max_origin_nonneg {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) : 0 ≤ max_origin b := by
  unfold max_origin v_origin_norm; positivity

omit V_finite [Nontrivial ↥V] in
lemma det_bound_const_nonneg {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) : 0 ≤ det_bound_const b := by
  simp [det_bound_const]
  positivity

lemma det_bound {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) (R: ℕ) (hR: (R'_ V) ≤ R):
    ((Q_R_matrix b R).det ^ ((1: ℝ) / Module.finrank ℝ V))
      ≤ det_bound_const b * (1 + R) ^ 2 * #(S ^ R) := by
  classical
  let argmax_eigen := (Finite.exists_max (Q_R_lin_hermetian b R).eigenvalues).choose
  let m :=  (Q_R_lin_hermetian b R).eigenvalues (argmax_eigen)
  let m_vec := (Q_R_lin_hermetian b R).eigenvectorBasis argmax_eigen
  let m_vec_V := b.equivFun.symm (m_vec.ofLp)

  let v_lipschitz_constant := v_lipschitz_constant b
  let v_origin_norm := v_origin_norm b
  let max_lipschitz := max_lipschitz b
  let max_origin := max_origin b
  have h_max_lipschitz : ∀ i, v_lipschitz_constant i ≤ max_lipschitz := le_max_lipschitz b
  have h_max_origin : ∀ i, v_origin_norm i ≤ max_origin := le_max_origin b
  obtain hB := iterated_lipschitz_bound m_vec_V.val

  rw [show det_bound_const b * (1 + R) ^ 2
        = (((Module.finrank ℝ ↥V) * max_lipschitz
            + (Module.finrank ℝ ↥V) * max_origin) * (1 + R)) ^ 2 from by
      simp only [max_lipschitz, max_origin, det_bound_const]; ring]
  rw [(Q_R_lin_hermetian b R).det_eq_prod_eigenvalues]
  grw [Finset.prod_le_prod (g := fun _ => m)]
  .
    simp
    rw [← Module.finrank_eq_card_basis b]
    rw [←  Real.rpow_natCast]
    rw [← Real.rpow_mul]
    .
      have finrank_pos := Module.finrank_pos (R := ℝ) (M := V)
      field_simp [finrank_pos]
      simp
      unfold m
      rw [Matrix.IsHermitian.eigenvalues_eq]
      simp [Q_R_matrix]
      have foo := dotProduct_toMatrix₂_mulVec b b (Q_R_lin V R)
      conv at foo =>
        intro x y
        lhs
        lhs
        equals x =>
          ext a
          simp
      conv at foo =>
        intro x y
        lhs
        rhs
        rhs
        equals y =>
          ext a
          simp
      rw [foo]
      simp only [Q_R_lin, Q_R, LipschitzH_apply,  map_sum,
        map_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_sum, LinearMap.coe_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ge_iff_le]
      simp_rw [← pow_two]
      grw [Finset.sum_le_card_nsmul (n := (((((Module.finrank ℝ ↥V)) * max_lipschitz + ((Module.finrank ℝ ↥V) * max_origin)) * (1 + R)) ^ 2))]
      .
        rw [← card_closed_ball_eq]
        simp
        rw [mul_comm]
        field_simp
        simp
      .
        intro x hx
        specialize hB x
        simp
        simp at hB
        rw [← Real.sqrt_sq_eq_abs] at hB
        rw [Real.sqrt_le_iff] at hB
        have foo := hB.2
        .
          simp [dist, WordDist_one] at hx
          grw [hx] at foo
          conv =>
            lhs
            arg 1
            arg 1
            arg 2
            intro x
            arg 1
            arg 1
            arg 1
            equals (Q_R_lin_hermetian b ↑R).eigenvectorBasis =>
              rfl
          conv at foo =>
            lhs
            simp [m_vec_V, m_vec]
          grw [foo]
          rw [mul_pow, mul_pow]
          rw [mul_le_mul_iff_left₀]
          .
            rw [pow_le_pow_iff_left₀]
            . apply add_le_add
              .
                simp [max_lipschitz]
                have foo := (m_vec_V).val.lipschitz.choose_spec
                conv at foo =>
                  arg 2
                  simp [m_vec_V]

                conv =>
                  lhs
                  equals ‖m_vec_V.val‖₊ =>
                    rfl
                simp [m_vec_V]
                --grw [norm_sum_l]
                grw [norm_sum_le]
                grw [Finset.sum_le_card_nsmul (n := ↑max_lipschitz)]
                .
                  simp
                  rw [← Module.finrank_eq_card_basis b]
                .
                  intro i _
                  simp [norm_smul]
                  grw [euclidean_of_lp_le]
                  simp [m_vec]
                  apply h_max_lipschitz
              .
                simp [m_vec_V, m_vec]
                rw [← LipschitzH_apply]
                rw [LipschitzH.finset_sum_apply]
                grw [Finset.abs_sum_le_sum_abs]
                grw [Finset.sum_le_card_nsmul (n := max_origin)]
                . simp
                  rw [← Module.finrank_eq_card_basis b]
                .
                  intro i hi
                  simp
                  grw [euclidean_of_lp_le]
                  simp
                  apply h_max_origin
            . positivity
            . exact add_nonneg (mul_nonneg (by positivity) (max_lipschitz_nonneg b))
                (mul_nonneg (by positivity) (max_origin_nonneg b))
            . simp
          . positivity

    . unfold m
      apply Matrix.PosSemidef.eigenvalues_nonneg
      apply (Q_R_matrix_pos_def b R hR).posSemidef
  .
    apply Finset.prod_nonneg
    intro i _
    apply Matrix.PosSemidef.eigenvalues_nonneg
    apply (Q_R_matrix_pos_def b R hR).posSemidef
  .
    intro i _
    apply Matrix.PosSemidef.eigenvalues_nonneg
    apply (Q_R_matrix_pos_def b R hR).posSemidef
  . intro i _
    unfold m
    have foo := (Finite.exists_max (Q_R_lin_hermetian b R).eigenvalues).choose_spec
    apply foo i

end V_variable

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Packing
attribute [-instance] _root_.GeneratesNS.volume_mul_left_invariant _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
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

omit v_wrapper_inst in
lemma smul_origin_ball_subset (a: G) (r: ℝ): (MulOpposite.op a) • Metric.closedBall 1 r ⊆ Metric.closedBall a r := by
  intro x hx
  simp
  rw [Set.mem_smul_set] at hx
  obtain ⟨y, hy, x_eq⟩ := hx
  rw [← x_eq]
  simp [dist, WordDist]
  simp at hy
  simp [dist, WordDist] at hy
  exact hy

omit v_wrapper_inst in
lemma ball_subset_smul_origin (a: G) (r: ℝ): Metric.closedBall a r ⊆ (MulOpposite.op a) • Metric.closedBall 1 r := by
  intro x hx
  simp at hx
  simpa using hx

lemma ball_smul_eq_origin (a: G) (r: ℝ): Metric.closedBall a r = (MulOpposite.op a) • Metric.closedBall 1 r := by
  ext x
  have foo := smul_origin_ball_subset a r
  have bar := ball_subset_smul_origin a r
  grind

/-- Common step for Lemma 3.25 (a) and (b).

`h i = log (#(S ^ 16 ^ i) * det (Q_{16 ^ i}) ^ (dim V)⁻¹)` splits into a log-cardinality term
plus a determinant term. The determinant term is monotone in the scale (Proposition 3.22, via
`Q_R_lin_sub_pos_semi_def` and `matrix_det_montone`), so it is non-negative and can be dropped,
leaving a comparison of ball cardinalities that follows from `Finset.card_pow_mono`. -/
lemma log_card_pow_sub_le {j k m n : ℕ} (hj : i₀ ≤ j) (hjk : j ≤ k) (hm0 : m ≠ 0)
    (hm : m ≤ 16 ^ k) (hn : 16 ^ j ≤ n) :
    Real.log (#(S ^ m)) - Real.log (#(S ^ n)) ≤ h b k - h b j := by
  have card_pos : ∀ p : ℕ, (0:ℝ) < #(S ^ p) := by
    intro p
    simp
    apply Finset.Nonempty.pow
    exact S_nonempty
  have i₀_le_j : ((16:ℝ) ^ i₀) ≤ ((16 ^ j : ℕ) : ℝ) := by
    push_cast
    exact pow_le_pow_right₀ (by norm_num) hj
  have i₀_le_k : ((16:ℝ) ^ i₀) ≤ ((16 ^ k : ℕ) : ℝ) := by
    push_cast
    exact pow_le_pow_right₀ (by norm_num) (hj.trans hjk)
  have pd_j : (Q_R_matrix b ((16 ^ j : ℕ) : ℝ)).PosDef := Q_R_matrix_pos_def_i₀ b _ i₀_le_j
  -- Proposition 3.22: the determinant is monotone in the scale, so the determinant part of
  -- `h k - h j` is non-negative and may be discarded.
  have det_le : (Q_R_matrix b ((16 ^ j : ℕ) : ℝ)).det ≤ (Q_R_matrix b ((16 ^ k : ℕ) : ℝ)).det := by
    apply matrix_det_montone
    . exact pd_j
    . unfold Q_R_matrix
      rw [← map_sub]
      rw [← LinearMap.isPosSemidef_iff_posSemidef_toMatrix]
      apply Q_R_lin_sub_pos_semi_def
      push_cast
      exact pow_le_pow_right₀ (by norm_num) hjk
  have dim_nonneg : (0:ℝ) ≤ (dim V)⁻¹ := by
    simp [dim]
  have log_det_le :
      Real.log ((Q_R_matrix b ((16 ^ j : ℕ) : ℝ)).det ^ (dim V)⁻¹) ≤
        Real.log ((Q_R_matrix b ((16 ^ k : ℕ) : ℝ)).det ^ (dim V)⁻¹) :=
    Real.log_le_log (Real.rpow_pos_of_pos pd_j.det_pos _)
      (Real.rpow_le_rpow pd_j.det_pos.le det_le dim_nonneg)
  have card_le :
      Real.log ((#(S ^ m) : ℝ)) - Real.log ((#(S ^ n) : ℝ)) ≤
        Real.log ((#(S ^ 16 ^ k) : ℝ)) - Real.log ((#(S ^ 16 ^ j) : ℝ)) := by
    apply sub_le_sub
    . apply Real.log_le_log (card_pos m)
      norm_cast
      exact Finset.card_pow_mono hm0 hm
    . apply Real.log_le_log (card_pos (16 ^ j))
      norm_cast
      exact Finset.card_pow_mono (by positivity) hn
  simp only [h, f]
  rw [Real.log_mul, Real.log_mul]
  . linarith
  . exact ne_of_gt (card_pos (16 ^ j))
  . exact ne_of_gt (Real.rpow_pos_of_pos pd_j.det_pos _)
  . exact ne_of_gt (card_pos (16 ^ k))
  . exact ne_of_gt (Real.rpow_pos_of_pos
      (Q_R_matrix_pos_def_i₀ b _ i₀_le_k).det_pos _)

-- Lemma 3.25 (a)

-- Lemma 3.25 (b)
lemma card_B_le_exp_wa (data: GoodScalesData b): #(B_finite data).toFinset < Real.exp (data.w * (a data.d)) := by
  have B_union := Finset.card_biUnion (s := (B_half_finsets data)) (t := id) ?_
  .
    simp at B_union
    have sum_le := Finset.sum_eq_card_nsmul (f := fun (u: Finset G) => #u) (s := B_half_finsets data) (b := #(S ^ (R_1 data / 2))) ?_
    .
      rw [← Nat.card_eq_card_finite_toFinset]
      simp [B]
      grw [Set.ncard_image_le (hs := by apply X_j_finite)]
      conv at sum_le =>
        rhs
        lhs
        simp [B_half_finsets]
        rw [Finset.card_image_iff.mpr (by
          have foo := B_ball_injective_on data (R_1 data / 2) (by grind) (by simp [R_1])
          conv =>
            rhs
            equals (X_j data) =>
              simp

          intro a ha b hb hab
          specialize foo ha hb
          specialize foo (by simpa using hab)
          exact foo
        )]
      simp at sum_le
      rw [eq_comm] at sum_le
      apply le_of_eq at sum_le
      rw [← Nat.le_div_iff_mul_le (by simp; apply Finset.Nonempty.pow; simp [S_nonempty])] at sum_le
      conv at sum_le =>
        lhs
        equals (X_j data).ncard =>
          rw [Set.ncard_eq_toFinset_card (hs := by apply X_j_finite)]

      grw [sum_le]
      rw [← B_union]
      grw [Finset.card_le_card (t := (finite_closed_ball (1: G) ↑(2 * (R_2 data))).toFinset)]
      .
        grw [Nat.cast_div_le]
        rw [card_closed_ball_eq]
        .
          rw [← Real.log_lt_iff_lt_exp]
          .
            apply lt_of_le_of_lt ?_  ((GoodScales data).h_diff_lt_w)
            rw [Real.log_div (by simp; grind [S_nonempty]) (by simp; grind [S_nonempty])]
            apply log_card_pow_sub_le (GoodScales data).i_1_ge
            . -- `i_2 - i_1 > w ≥ 0` forces `i_1 < i_2`
              have hdiff := (GoodScales data).i_diff_mem
              simp [Set.mem_Ioo] at hdiff
              omega
            . simp [R_2]
            . rw [pow_succ]
              simp [R_2]
              omega
            . simp [R_1]
          .
            apply div_pos
            . simp
              apply Finset.Nonempty.pow
              simp [S_nonempty]
            . simp
              apply Finset.Nonempty.pow
              simp [S_nonempty]
      .
        intro a ha
        simp at ha
        obtain ⟨x, x_mem, hx⟩ := ha
        simp [B_half_finsets] at x_mem
        simp
        obtain ⟨c, hc, x_eq⟩ := x_mem
        grw [dist_triangle _ c]
        rw [← x_eq] at hx
        simp at hx
        grw [hx]
        simp [X_j] at hc
        grw [Metric.maximalSeparatedSet_subset] at hc
        simp at hc
        grw [hc]
        simp [R_1, R_2]
        have i_1_le:  (GoodScales data).i_1 ≤  (GoodScales data).i_2 := by
          have foo :=  (GoodScales data).i_diff_mem
          simp at foo
          grind
        grw [i_1_le]
        .
          grind
        . simp
    .
      intro b hb
      simp [B_half_finsets] at hb
      obtain ⟨c, c_mem, b_eq⟩ := hb
      rw [← b_eq]
      rw [← Set.toFinite_toFinset]
      rw [← Nat.card_eq_card_finite_toFinset]
      rw [ball_smul_eq_origin]

      -- TODO - make the various finite/fintype/card conversion less awful
      conv =>
        lhs
        equals (MulOpposite.op c • (Metric.closedBall (1: G) (↑(R_1 data) / 2))).ncard =>
          simp

      simp [-Metric.smul_closedBall]
      conv =>
        lhs
        equals #(finite_closed_ball 1 ↑((R_1 data) / 2)).toFinset =>
          simp
          rw [Set.ncard_eq_toFinset_card']
          simp [R_1]
      rw [card_closed_ball_eq]

  .
    -- TODO - there must be a less horrendous way of dealing with Finset here
    simp [B_half_finsets]
    have foo := B_half_disjoint data
    simp [B_half] at foo
    unfold Set.PairwiseDisjoint Set.Pairwise
    unfold Set.PairwiseDisjoint Set.Pairwise at foo
    simp
    simp at foo
    intro a ha b hb hab p hp_a hp_b
    simp at hp_a hp_b
    specialize foo a ha b hb hab hp_a hp_b
    simpa using foo

end V_Wrapper_Section

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Poincare
attribute [-instance] _root_.GeneratesNS.volume_mul_left_invariant _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
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

-- Reindexing `s ↦ s⁻¹` over the symmetric generating set `S` turns a right-gradient of
-- `f ∘ (·⁻¹)` into a left-gradient of `f` at the inverted point.
omit v_wrapper_inst in
lemma deriv_sq_R_inv_comp (f: G → ℝ) (x: G):
    deriv_sq_R (fun y => f y⁻¹) x = deriv_sq f x⁻¹ := by
  unfold deriv_sq_R deriv_sq
  apply Finset.sum_nbij' (i := fun s => s⁻¹) (j := fun s => s⁻¹) <;>
    simp +contextual [hGS.has_inv, mul_inv_rev]

omit v_wrapper_inst in
lemma le_of_sub_eq (a b c: ℝ) (ha: a = b - c) (hc: 0 ≤ c): a ≤ b := by
  grind

-- `B_r` is centred at `1`, so it is closed under inversion (`word_norm_inv`).
omit v_wrapper_inst in
lemma mem_B_r_inv (r: ℝ) (x: G): x⁻¹ ∈ B_r r ↔ x ∈ B_r r := by
  simp [B_r, dist, WordDist_one, ← word_norm_inv]

omit v_wrapper_inst in
lemma card_B_r_eq (R: ℕ): #(B_r R) = #(S ^ R) := by
  rw [← card_closed_ball_eq]
  simp [B_r]

end V_Wrapper_Section

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Lemma326
attribute [-instance] _root_.GeneratesNS.volume_mul_left_invariant _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
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

omit [Nonempty ι] in
/-- The determinant of `Q_R_matrix` at two bases of `V` differs by a positive constant that is
**uniform in the scale `R`**. Hence the determinant *ratio* between two scales — and so the
`h`-difference used to select good scales — is basis-independent. -/
lemma Q_R_matrix_det_basis_change {index : Type*} [Fintype index] [DecidableEq index]
    (b_1 : Module.Basis ι ℝ V) (b_2 : Module.Basis index ℝ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, (Q_R_matrix b_2 R).det = K * (Q_R_matrix b_1 R).det := by
  obtain ⟨K, hK, hB⟩ := LinearMap.toMatrix₂_det_basis_change b_1 b_2
  refine ⟨K, hK, fun R => ?_⟩
  have h2 : Q_R_matrix b_2 R = LinearMap.toMatrix₂ b_2 b_2 (Q_R_lin_plain V R) := by
    simp only [Q_R_matrix]; ext i j; simp [Q_R_lin, Q_R_lin_plain]
  have h1 : Q_R_matrix b_1 R = LinearMap.toMatrix₂ b_1 b_1 (Q_R_lin_plain V R) := by
    simp only [Q_R_matrix]; ext i j; simp [Q_R_lin, Q_R_lin_plain]
  rw [h2, h1, hB]

omit [Nonempty ι] in
lemma growth_bound_basis_change (d: ℕ) {index: Type*} [Fintype index] [DecidableEq index] (b_1: Module.Basis ι ℝ V) (b_2: Module.Basis index ℝ V) (h_growth: growth_bound b_1 d) : growth_bound b_2 d := by
  -- the two bases index the same space, so their index types are canonically equivalent
  let equiv : ι ≃ index := b_1.indexEquiv b_2
  unfold growth_bound my_expr Q_R_matrix
  unfold growth_bound my_expr Q_R_matrix at h_growth
  have conv_plain: ∀ R, (LinearMap.toMatrix₂ b_2 b_2) (Q_R_lin V ↑R) = (LinearMap.toMatrix₂ b_2 b_2) (Q_R_lin_plain V ↑R) := by
    intro R
    ext i j
    simp [Q_R_lin, Q_R_lin_plain]

  have conv_plain_b_1: ∀ R, (LinearMap.toMatrix₂ b_1 b_1) (Q_R_lin V ↑R) = (LinearMap.toMatrix₂ b_1 b_1) (Q_R_lin_plain V ↑R) := by
    intro R
    ext i j
    simp [Q_R_lin, Q_R_lin_plain]

  -- The two change-of-basis determinant factors are transposes of each other, hence equal,
  -- and their common value is nonzero since it is the determinant of an (invertible) basis-change
  -- matrix (`(b_1.reindex equiv).toMatrix b_2`).
  have heq_det : ((b_1.toMatrix ⇑b_2).transpose.submatrix id ⇑equiv.symm).det
               = ((b_1.toMatrix ⇑b_2).submatrix (⇑equiv.symm) id).det := by
    rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
  have hne_det : ((b_1.toMatrix ⇑b_2).submatrix (⇑equiv.symm) id).det ≠ 0 := by
    rw [← Module.Basis.toMatrix_reindex]
    have hmul : ((b_1.reindex equiv).toMatrix ⇑b_2).det
              * (b_2.toMatrix ⇑(b_1.reindex equiv)).det = 1 := by
      rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
    exact left_ne_zero_of_mul_eq_one hmul

  simp_rw [conv_plain]
  conv =>
    arg 1
    intro R
    rw [← Matrix.det_reindex_self equiv.symm]
    rw [← LinearMap.toMatrix₂_mul_basis_toMatrix (b₁ := b_1.reindex equiv) (b₂ := b_1.reindex equiv)]
    simp [-LinearMap.toMatrix₂_mul_basis_toMatrix]
    rw [mul_assoc]
    rw [mul_comm _ (((b_1.toMatrix ⇑b_2).submatrix (⇑equiv.symm) id).det)]
    rw [← mul_assoc]
    rw [Real.mul_rpow (by rw [heq_det]; exact mul_self_nonneg _) (by
      apply Matrix.PosSemidef.det_nonneg
      conv =>
        arg 1
        equals (LinearMap.toMatrix₂ (b_1.reindex equiv) (b_1.reindex equiv)) (Q_R_lin V ↑R) =>
          ext i j
          simp [Q_R_lin, Q_R_lin_plain]

      -- TODO - make this a standalone lemma
      rw [← LinearMap.isPosSemidef_iff_posSemidef_toMatrix]
      rw [LinearMap.isPosSemidef_def]
      refine ⟨?_, ?_⟩
      .
        apply Q_R_lin_symm
      .
        rw [LinearMap.isNonneg_def]
        intro x
        simp [Q_R_lin, Q_R]
        simp_rw [← pow_two]
        positivity

    )]
    rw [← mul_assoc]
    rw [mul_comm ((#(S ^ R)) : ℝ)]
    rw [mul_assoc]
    rw [mul_div_assoc]

  let K := (((b_1.toMatrix ⇑b_2).transpose.submatrix id ⇑equiv.symm).det *
          ((b_1.toMatrix ⇑b_2).submatrix (⇑equiv.symm) id).det) ^ (↑(Module.finrank ℝ ↥V) : ℝ)⁻¹
  conv =>
    rhs
    equals (nhdsWithin (K * 0) (Set.Ioi (K * 0))) =>
      simp

  apply Filter.TendstoNhdsWithinIoi.const_mul
  .
    apply Real.rpow_pos_of_pos
    rw [heq_det]
    exact mul_self_pos.mpr hne_det
  .
    simp_rw [LinearMap.toMatrix₂_reindex_det]
    simp_rw [conv_plain_b_1] at h_growth
    simp at h_growth
    apply h_growth

lemma R'_le_R_2 (data: GoodScalesData b) : R'_ V ≤ (↑(R_2 data) : ℝ) := by
  have foo := (GoodScales data).i_2_ge
  simp [i₀] at foo
  have pow_le := Nat.le_pow_clog (b := 16) (x := ⌈R'_ V⌉₊) (by simp)
  have r_ceil := Nat.le_ceil (R')
  unfold R' at r_ceil
  grw [r_ceil]
  grw [pow_le]
  simp [R_2]
  rw [pow_le_pow_iff_right₀]
  . exact foo
  . simp

end V_Wrapper_Section

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Harmonic_Convolution
attribute [-instance] _root_.GeneratesNS.volume_mul_left_invariant _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Convolution and the Laplacian

Basic compatibility of the discrete Laplacian with convolution: additivity, scalar
multiplication, and `laplace_conv_eq_laplace_right`.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
attribute [local implicit_reducible] Additive

namespace GeneratesNS
open Generates


variable [hGS: Generates]
include hGS


-- If a harmonic function has a maximum value, then it must be a constant function
-- We state 'f is harmonc' as 'Laplace_b f = 0', as this is the hypothesis we have where we need to call this lemma
-- This is true even if it's a local maximum (considered in terms of the  poitns reached by multiply by S), but
-- we don't need that result yet
lemma harmonic_maximum_implies_const (f: G → ℝ) (hf: Laplace_b  f = 0) (a: G) (h_max: ∀ g: G, f g ≤ f a): f = fun _ => f a := by
  have path_implies_max (l : List S): f (l.unattach.prod * a) = f a := by
    induction l with
    | nil =>
      simp
    | cons s l ih =>
      simp
      simp [Laplace_b, f_conv_mu] at hf
      have f_at_l := congrFun hf (l.unattach.prod * a)
      simp at f_at_l
      rw [sub_eq_zero] at f_at_l
      rw [ih] at f_at_l
      field_simp at f_at_l

      -- TODO - is there a 'Finset.expect' theorem we can use?
     -- TODO - upstream this to mathlib in some form
      have f_s_eq: ∀ s: S, f a = f (s * (l.unattach.prod * a)) := by
        by_contra!
        simp at this
        obtain ⟨s, s_mem_s, hs⟩ := this
        by_cases val_le_max: f (s * (l.unattach.prod * a)) ≤ f a
        .
          have val_lt_max: f (s * (l.unattach.prod * a)) < f a := by
            exact lt_of_le_of_ne (h_max (↑s * (l.unattach.prod * a))) (id (Ne.symm hs))

          have sum_strict_lt := Finset.sum_lt_sum (f := fun x => f (x * (l.unattach.prod * a))) (g := fun x => f a) (s := S) ?_ ?_
          .
            simp at sum_strict_lt
            rw [mul_comm] at sum_strict_lt
            rw [← div_lt_iff₀] at sum_strict_lt
            .
              apply ne_of_gt at sum_strict_lt
              contradiction
            . simpa using S_nonempty
          . intro s hs
            apply h_max
          . use s
        .
          have val_gt := h_max (s * (l.unattach.prod * a))
          simp at val_le_max
          linarith
      specialize f_s_eq s
      rw [f_s_eq]
      rw [mul_assoc]
  ext g

  obtain ⟨l, h_l_prod⟩ := mem_S_prod_list (g * a⁻¹)
  simp [ProdS] at h_l_prod
  specialize path_implies_max l
  rw [h_l_prod] at path_implies_max
  simpa using path_implies_max


open scoped Finset
open scoped Pointwise


open scoped Convolution
open MeasureTheory


end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Harmonic_LaplaceLinear
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The Laplacian as a linear map on `L²`

`Laplace_linear`, the normalised functions `F_n`, and the limit `F_n_conv_mu_lim`.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
attribute [local implicit_reducible] Additive

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V]

open scoped Finset
open scoped Pointwise
open scoped Convolution
open MeasureTheory


@[expose]
instance volume_finite_compact: IsFiniteMeasureOnCompacts (volume (α := G)) := by
  simp [volume]
  rw [my_haar_eq_count]
  exact {
    lt_top_of_isCompact := by
      intro k hk
      have finite := IsCompact.finite hk DiscreteTopology.isDiscrete
      exact Measure.count_apply_lt_top.mpr finite
  }


end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Harmonic_SelfAdjoint
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Self-adjointness and the spectrum of the Laplacian

`laplace_self_adjoint`, `laplace_positive_semidefinite`, and that `0` lies in the spectrum of
`Δ`.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
attribute [local implicit_reducible] Additive

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V]

open scoped Finset
open scoped Pointwise
open scoped Convolution
open MeasureTheory

lemma laplace_smul (k: ℝ) (f: (Lp ℝ 2 volume (α := G))): Laplace (k • f) = k • (Laplace f) := by
  simp [Laplace, conv_mu_lp2]
  simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_smul _ _)]
  simp_rw [conv_smul]
  rw [MeasureTheory.MemLp.toLp_const_smul]
  rw [smul_sub]


lemma norm_conv_mu_le  (f: (Lp ℝ 2 volume (α := G))): ‖conv_mu_lp2 f‖ ≤ ‖f‖ := by
  simp [conv_mu_lp2]
  simp [f_conv_mu]
  simp_rw [← smul_eq_mul]
  rw [← Pi.smul_def]
  rw [MeasureTheory.eLpNorm_const_smul]
  -- TODO - deduplicate this with 'laplace_bounded'
  conv =>
    lhs
    rhs
    rhs
    arg 1
    equals ∑ x ∈ S, fun g => f (x • g) =>
      funext g
      simp

  have card_s_ne: (#S : ℝ) ≠ 0 := by
    simp
    have foo := hS
    simp at foo
    exact Finset.nonempty_iff_ne_empty.mp foo

  grw [MeasureTheory.eLpNorm_sum_le]
  simp_rw [← Function.comp_def]
  conv =>
    lhs
    rhs
    rhs
    arg 2
    intro x
    rw [MeasureTheory.eLpNorm_comp_measurePreserving (ν := MeasureTheory.volume) (by
      apply MeasureTheory.AEStronglyMeasurable.of_discrete
    ) (by
    exact {
      measurable := by
        apply Measurable.of_discrete
      map_eq := by
        simp [MeasureTheory.volume]
    }
  )]
  . simp
    field_simp
    rfl
  .
    apply WithTop.mul_ne_top
    .
      rw [Real.enorm_of_nonneg (by simp)]
      apply ENNReal.ofReal_ne_top
    .
      apply ENNReal.sum_ne_top.mpr
      intro s hs
      rw [← Function.comp_def]
      conv =>
        rw [MeasureTheory.eLpNorm_comp_measurePreserving (ν := MeasureTheory.volume) (by
          apply MeasureTheory.AEStronglyMeasurable.of_discrete
        ) (by
        exact {
          measurable := by
            apply Measurable.of_discrete
          map_eq := by
            simp [MeasureTheory.volume]
        }
      )]
      rw [← lt_top_iff_ne_top]
      apply (MeasureTheory.Lp.memLp f).2
  . intro s hs
    apply AEStronglyMeasurable.of_discrete
  .
    simp

open scoped RealInnerProductSpace
lemma inner_laplace_zero (f: (Lp ℝ 2 volume (α := G))) (hf: ⟪Laplace f, f⟫ = 0): Laplace f = 0 := by
  have inner_le := real_inner_le_norm (conv_mu_lp2 f) f

  by_cases norm_f_zero: ‖f‖ = 0
  .
    simp at norm_f_zero
    simp [Laplace, conv_mu_lp2]
    simp [f_conv_mu]
    simp_rw [norm_f_zero]
    simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)]
    simp
    simp_rw [← Pi.zero_def]
    rw [MeasureTheory.MemLp.toLp_zero]

  simp [Laplace] at hf
  rw [inner_sub_left] at hf
  rw [real_inner_self_eq_norm_sq] at hf
  rw [sub_eq_zero] at hf
  rw [eq_comm] at hf
  rw [pow_two] at hf
  rw [hf] at inner_le
  nth_rw 2 [mul_comm] at inner_le
  rw [mul_le_mul_iff_of_pos_left] at inner_le
  have conv_le_f := norm_conv_mu_le f
  have f_norm_eq: ‖f‖ = ‖conv_mu_lp2 f‖ := by
    linarith

  have f_sub_norm := norm_sub_sq_real f (conv_mu_lp2 f)
  rw [real_inner_comm] at f_sub_norm
  rw [hf] at f_sub_norm
  rw [← f_norm_eq] at f_sub_norm
  rw [← pow_two] at f_sub_norm
  group at f_sub_norm
  rw [zpow_two] at f_sub_norm
  rw [mul_self_eq_zero] at f_sub_norm
  simp at f_sub_norm
  simpa [Laplace] using f_sub_norm
  simpa using norm_f_zero


lemma harmonic_abs_max_implies_const (f: G → ℝ) (hf: Laplace_b  f = 0) (a: G) (h_max: ∀ g: G, |f g| ≤ |f a|): f = fun _ => f a := by
  by_cases f_a_pos: 0 ≤ f a
  .
    have lt_f_a: ∀ g: G, f g ≤ f a := by
      intro g
      by_cases f_g_pos: 0 ≤ f g
      . specialize h_max g
        rw [abs_eq_self.mpr ?_] at h_max
        rw [abs_eq_self.mpr f_a_pos] at h_max
        . exact h_max
        . exact f_g_pos
      . linarith
    exact harmonic_maximum_implies_const f hf a lt_f_a
  .
    have f_neg_le: ∀ g, (-f) g ≤ (-f) a := by
      intro g
      simp at f_a_pos
      simp
      specialize h_max g
      rw [abs_of_neg f_a_pos] at h_max
      by_cases f_g_pos: 0 ≤ f g
      . rw [abs_of_nonneg f_g_pos] at h_max
        linarith
      . simp at f_g_pos
        rw [abs_of_neg f_g_pos] at h_max
        linarith
    have neg_const := harmonic_maximum_implies_const (-f) ?_ a f_neg_le
    .
      apply_fun (fun h => -h) at neg_const
      simp at neg_const
      rw [Pi.neg_def] at neg_const
      simpa using neg_const
    .
      simp_rw [Laplace_b]
      simp_rw [Laplace_b] at hf
      conv =>
        lhs
        rhs
        arg 1
        equals (-1 : ℝ) • f =>
          simp
      rw [conv_smul]
      simp
      rw [add_comm]
      rw [← sub_eq_add_neg]
      rw [sub_eq_zero]
      rw [sub_eq_zero] at hf
      exact hf.symm


set_option maxHeartbeats 500000 in
lemma laplace_zero_iff_zero (g: (Lp ℝ 2 volume (α := G))) (eq_zero: Laplace g = 0): g = 0 := by
  by_cases g_has_maximum: ∃ a: G, ∀ b: G, ‖g b‖ ≤ ‖g a‖
  .
    obtain ⟨a, ha⟩ := g_has_maximum
    have laplace_b_zero: Laplace_b  g = 0 := by
      simp [Laplace, conv_mu_lp2, f_conv_mu] at eq_zero
      simp_rw [Laplace_b, f_conv_mu]
      apply_fun (fun f => f.val.cast) at eq_zero
      rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)] at eq_zero
      rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at eq_zero
      rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)] at eq_zero
      field_simp at eq_zero
      field_simp
      exact eq_zero

    simp [Laplace_b] at laplace_b_zero
    simp [f_conv_mu] at laplace_b_zero
    rw [sub_eq_zero] at laplace_b_zero

    have g_const := harmonic_abs_max_implies_const g (by
      simp [Laplace_b]
      simp [f_conv_mu]
      nth_rw 1 [laplace_b_zero]
      simp
    ) a (by simpa using ha)
    have new_g_const_zero := MeasureTheory.memLp_const_iff_enorm (p := 2) (by simp) (by simp) (c := g a) (μ := volume (α := G)) (by simp)
    rw [← g_const] at new_g_const_zero
    simp [MeasureTheory.Lp.memLp] at new_g_const_zero
    simp [volume, my_haar_eq_count] at new_g_const_zero
    have g_infinity := hGS.g_infinite
    rw [← not_infinite_iff_finite] at new_g_const_zero
    simp [hGS.g_infinite] at new_g_const_zero


    have g_eq_zero: g.val.cast = 0 := by
      rw [g_const]
      rw [new_g_const_zero]
      ext a
      simp

    ext
    rw [ae_eq_everywhere]
    rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)]
    exact g_eq_zero
  . rename _ => g_no_maximum
    simp at g_no_maximum
    have integrable_g := MeasureTheory.MemLp.integrable_sq (MeasureTheory.Lp.memLp g)
    simp [Integrable, HasFiniteIntegral] at integrable_g
    obtain ⟨_, integral_lt⟩ := integrable_g
    rw [lintegral_g_eq_add] at integral_lt
    rw [lt_top_iff_ne_top] at integral_lt
    by_contra g_ne_zero
    simp at g_ne_zero
    have nonzero_val: ∃ a: G, g a ≠ 0 := by
      rw [MeasureTheory.Lp.ext_iff] at g_ne_zero
      rw [ae_eq_everywhere] at g_ne_zero
      rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)] at g_ne_zero
      exact Function.ne_iff.mp g_ne_zero

    obtain ⟨a, ha⟩ := nonzero_val
    have finite_gt := ENNReal.finite_const_le_of_tsum_ne_top integral_lt (ε := ‖|g a|‖ₑ ^ 2) (by
      simpa using ha
    )
    have maximal := Set.Finite.exists_maximalFor (f := fun h => |g h|) _ finite_gt (by
      apply Set.nonempty_of_mem (x := a)
      simp
    )
    obtain ⟨m, m_in_g, hm⟩ := maximal
    simp at m_in_g
    -- Obtain an element greater than the maximum
    obtain ⟨p, hp⟩ := g_no_maximum m
    have p_gt := hm (j := p) ?_ ?_
    .
      have not_g_le := not_lt_of_ge p_gt
      contradiction
    .
      simp
      grw [m_in_g]
      rw [← ENNReal.toReal_le_toReal]
      .
        simp
        rw [sq_le_sq]
        linarith
      . simp
      . simp
    linarith


-- Proposition 3.17.1: "∆ is bounded" from Vikman
-- The paper also proves that the Laplace operator is self-adjoint as part of this step,
-- but we split it out
lemma laplace_bounded (f: (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G)))): ‖(Laplace  f)‖ₑ ≤ 2 * ‖f‖ₑ := by
  unfold Laplace
  unfold conv_mu_lp2
  simp_rw [f_conv_mu]
  grw [enorm_sub_le]
  --grw [norm_sub_le]
  --grw [norm_add_le]
  --grw [MeasureTheory.eLpNorm_sub_le]
  simp_rw [← smul_eq_mul]
  simp_rw [← Pi.smul_def]
  rw [MeasureTheory.MemLp.toLp_const_smul]
  rw [enorm_smul]
  conv =>
    lhs
    rhs
    rhs
    arg 1
    arg 1
    equals ∑ x ∈ S, fun g => f (x • g) =>
      funext g
      simp

  rw [MeasureTheory.Lp.enorm_toLp]
  grw [MeasureTheory.eLpNorm_sum_le]
  simp_rw [← Function.comp_def]
  conv =>
    lhs
    rhs
    rhs
    arg 2
    intro x
    rw [MeasureTheory.eLpNorm_comp_measurePreserving (ν := MeasureTheory.volume) (by
      apply MeasureTheory.AEStronglyMeasurable.of_discrete
    ) (by
    exact {
      measurable := by
        apply Measurable.of_discrete
      map_eq := by
        simp [MeasureTheory.volume]
    }
  )]
  simp
  rw [Real.enorm_of_nonneg (by simp)]
  rw [← mul_assoc]
  rw [← ENNReal.ofReal_natCast]
  rw [← ENNReal.ofReal_mul]
  field_simp
  rw [div_self (by
    have foo := hS
    simp at foo
    simp
    exact Finset.nonempty_iff_ne_empty.mp foo
  )]
  simp
  rw [two_mul]
  . rw [← MeasureTheory.Lp.enorm_def]
  -- TODO - inline these in the right places
  . simp
  .
    intro i hs
    apply MeasureTheory.AEStronglyMeasurable.of_discrete
  . norm_num
  .
    apply MeasureTheory.memLp_finsetSum
    intro s hs
    rw [← Function.comp_def]
    apply MeasureTheory.MemLp.comp_of_map
    .
      simp [MeasureTheory.volume]
      apply MeasureTheory.Lp.memLp f
    . apply AEMeasurable.of_discrete


lemma laplace_bounded' (f: (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G)))): ‖(Laplace  f)‖ ≤ 2 * ‖f‖ := by
  have bounded := laplace_bounded f
  rw [← ofReal_norm_eq_enorm] at bounded
  rw [← ofReal_norm_eq_enorm] at bounded
  simp_rw [← ENNReal.ofReal_ofNat] at bounded
  rw [← ENNReal.ofReal_mul] at bounded
  .
    rw [ENNReal.ofReal_le_ofReal_iff] at bounded
    . exact bounded
    . simp
  . simp

lemma tolp_apply (f: G → ℝ) {p: ENNReal}  (hf: MeasureTheory.MemLp f p) (g: G): (MeasureTheory.MemLp.toLp f hf) g = f g := by
  have eq_fun := MeasureTheory.AEEqFun.coeFn_mk f (μ := MeasureTheory.volume (α := G)) (by apply MeasureTheory.AEStronglyMeasurable.of_discrete)
  rw [ae_eq_everywhere] at eq_fun
  nth_rw 2 [← eq_fun]
  rfl


open scoped RealInnerProductSpace
lemma laplace_self_adjoint (f h: (MeasureTheory.Lp ℝ 2 (μ := volume (α := G)))): ⟪f, (Laplace  h)⟫ = ⟪(Laplace  f), h⟫ := by

  simp [MeasureTheory.L2.inner_def]



  -- MeasureTheory.Lp.coeFn_smul

  conv =>
    lhs
    arg 2
    intro g
    rw [mul_comm]
    rw [Laplace]
    rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)]
    simp
    rw [mul_sub]
    rhs
    equals (f g • (conv_mu_lp2 h)) g =>
      rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_smul _ _)]
      simp

  conv =>
    lhs
    arg 2
    intro g
    rhs
    unfold conv_mu_lp2
    rw [← MeasureTheory.MemLp.toLp_const_smul]

  simp_rw [f_conv_mu]
  simp_rw [Pi.smul_def]
  simp
  simp_rw [← mul_assoc]
  simp_rw [mul_comm]
  simp_rw [mul_assoc]
  simp_rw [Finset.mul_sum]


  conv =>
    lhs
    arg 2
    intro g
    rhs
    arg 1
    rhs
    arg 1
    intro i


  simp_rw [tolp_apply]
  rw [integral_sub]
  rw [MeasureTheory.integral_finset_sum]
  conv =>
    lhs
    rhs
    arg 2
    intro s
    rw [← MeasureTheory.integral_mul_left_eq_self (g := s⁻¹)]
    simp
  rw [← MeasureTheory.integral_finset_sum]
  conv =>
    lhs
    rhs
    arg 2
    intro g
    rw [← Finset.mul_sum]
    rw [Finset.sum_bijective (s := S) (t := S) (e := fun s => s⁻¹) (g := fun i => (f (i * g) * (h g))) (by
      refine ⟨?_, ?_⟩
      . exact inv_injective
      . exact inv_surjective
    ) (by
      intro a
      refine ⟨?_, ?_⟩
      . apply hGS.has_inv a
      . simpa using (hGS.has_inv a⁻¹)
    ) (by
      simp
    )]

  simp_rw [Finset.mul_sum]
  rw [← integral_sub]
  simp_rw [← mul_assoc]
  simp_rw [← Finset.sum_mul]
  simp_rw [mul_comm]
  conv =>
    lhs
    arg 2
    intro a
    rw [mul_comm]
    rw [← mul_sub]


  conv =>
    rhs
    arg 2
    intro g
    rw [Laplace]
    rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)]
    unfold conv_mu_lp2
    simp [f_conv_mu]
    rw [tolp_apply]


  simp_rw [Finset.mul_sum]
  .
    have prod_lp1 := MeasureTheory.MemLp.smul (φ := f) (f := h) (p := 2) (q := 2) (r := 1) (μ := volume) (MeasureTheory.Lp.memLp h) (MeasureTheory.Lp.memLp f)
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1
  .
    apply MeasureTheory.integrable_finset_sum
    intro s hs
    apply MeasureTheory.Integrable.const_mul
    have mem_lp_f_comp: MemLp (f ∘ (fun x => s * x)) 2 := by
      apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
      . apply MeasureTheory.Lp.memLp f
      . exact measurePreserving_mul_left volume s

    have prod_lp1 := MeasureTheory.MemLp.smul (f := h) (p := 2) (q := 2) (r := 1) (μ := volume) (MeasureTheory.Lp.memLp h) mem_lp_f_comp
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1
  .
    intro s hs
    apply MeasureTheory.Integrable.const_mul
    have mem_lp_f_comp: MemLp (f ∘ (fun x => s⁻¹ * x)) 2 := by
      apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
      . apply MeasureTheory.Lp.memLp f
      . exact measurePreserving_mul_left volume s⁻¹
    have prod_lp1 := MeasureTheory.MemLp.smul (f := h) (p := 2) (q := 2) (r := 1) (μ := volume) (MeasureTheory.Lp.memLp h) mem_lp_f_comp
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1
  .
    intro s hs
    apply MeasureTheory.Integrable.const_mul

    have mem_lp_h_comp: MemLp (h ∘ (fun x => s * x)) 2 := by
      apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
      . apply MeasureTheory.Lp.memLp h
      . exact measurePreserving_mul_left volume s

    have prod_lp1 := MeasureTheory.MemLp.smul (p := 2) (q := 2) (r := 1) (μ := volume) mem_lp_h_comp (MeasureTheory.Lp.memLp f)
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1
  .
    have prod_lp1 := MeasureTheory.MemLp.smul (φ := f) (f := h) (p := 2) (q := 2) (r := 1) (μ := volume) (MeasureTheory.Lp.memLp h) (MeasureTheory.Lp.memLp f)
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1
  .
    apply MeasureTheory.integrable_finset_sum
    intro s hs
    apply MeasureTheory.Integrable.const_mul

    have mem_lp_h_comp: MemLp (h ∘ (fun x => s * x)) 2 := by
      apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
      . apply MeasureTheory.Lp.memLp h
      . exact measurePreserving_mul_left volume s

    have prod_lp1 := MeasureTheory.MemLp.smul (p := 2) (q := 2) (r := 1) (μ := volume) mem_lp_h_comp (MeasureTheory.Lp.memLp f)
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1


set_option maxHeartbeats 200000 in
lemma laplace_positive_semidefinite (f: (MeasureTheory.Lp ℝ 2 (μ := volume (α := G)))): 0 ≤ ⟪f, (Laplace  f)⟫ := by
  unfold Laplace
  rw [inner_sub_right]
  rw [real_inner_self_eq_norm_sq]
  rw [conv_mu_lp2]
  rw [MeasureTheory.L2.inner_def]
  simp_rw [tolp_apply]
  simp_rw [f_conv_mu]
  simp_rw [← smul_eq_mul]
  simp_rw [inner_smul_right]
  simp_rw [inner_sum]
  rw [integral_const_mul]
  rw [MeasureTheory.integral_finset_sum]

  -- I couldn't figure how to to handle 'toLp (∑ x ∈ S), so I ended up manipulating the integral to avoid dealing with it
  have comp_smul_left (i: G) := MeasureTheory.Lp.coeFn_compMeasurePreserving (g := f) (f := fun a => i * a) (μ := volume) (by
    exact measurePreserving_mul_left volume i
  )
  simp_rw [ae_eq_everywhere] at comp_smul_left
  have congr_comp (i: G) (x: G) := congrFun (comp_smul_left i) x
  simp only [Function.comp_apply] at congr_comp
  simp_rw [smul_eq_mul]
  simp_rw [← congr_comp]
  simp_rw [← MeasureTheory.L2.inner_def]

  let f_eq_coe: f = f := by rfl
  nth_rw 1 [← MeasureTheory.Lp.toLp_coeFn (f := f) (hf := Lp.memLp f)] at f_eq_coe


  conv =>
    rhs
    rhs
    rhs
    arg 2
    intro x
    rw [← f_eq_coe]
    rw [MeasureTheory.Lp.toLp_compMeasurePreserving]
    simp


  -- We've now packed everything back up in an inner product -
  -- we no longer need to deal with commuting toLp and Finset.sum


  let conv_f_delta_lp (i: G) :=  MemLp.toLp (Conv (f) (delta i⁻¹)) (μ := volume) (p := 2) (by
    simp_rw [f_conv_delta_helper]
    apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
    . apply MeasureTheory.Lp.memLp f
    . exact measurePreserving_mul_left volume _
  )


  have sum_le := Finset.sum_le_sum (g := fun i => ‖f‖ * ‖conv_f_delta_lp i‖) (f := fun i => ⟪f, conv_f_delta_lp i⟫) (s := S) (by
    intro s hs
    have foo := norm_inner_le_norm (x := f) (y := conv_f_delta_lp s) (𝕜 := ℝ)
    rw [Real.norm_eq_abs] at foo
    exact real_inner_le_norm f (conv_f_delta_lp s)
  )
  rw [← ge_iff_le]
  conv =>
    lhs
    rhs
    rhs
    arg 2
    intro x
    rhs
    equals conv_f_delta_lp x =>
      apply Lp.ext
      rw [ae_eq_everywhere]
      funext g
      rw [tolp_apply]
      simp [conv_f_delta_lp]
      rw [tolp_apply]
      rw [f_conv_delta]
      simp


  calc
    _ ≥ ‖f‖ ^ 2 - 1 / ↑(#S) * ∑ i ∈ S, ‖f‖ * ‖conv_f_delta_lp i‖ := by

      apply sub_le_sub_left
      simp
      gcongr
    _ ≥ 0 := by
      unfold conv_f_delta_lp
      simp_rw [f_conv_delta_helper]
      conv =>
        lhs
        rhs
        rhs
        arg 2
        intro x
        rhs
        equals ‖f‖ =>
          simp
          rw [← Function.comp_def]
          rw [MeasureTheory.eLpNorm_comp_measurePreserving (ν := volume)]
          . simp [norm]
          . apply MeasureTheory.AEStronglyMeasurable.of_discrete
          . exact measurePreserving_mul_left volume x
      simp
      have s_card_ne_zero: (#S : ℝ) ≠ 0 := by
        simp
        have foo := hS
        simp at foo
        exact Finset.nonempty_iff_ne_empty.mp foo

      rw [← mul_assoc]
      simp [s_card_ne_zero]
      rw [pow_two]
  .
    intro s hs
    simp

    have mem_lp_h_comp: MemLp (f ∘ (fun x => s * x)) 2 := by
      apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
      . apply MeasureTheory.Lp.memLp f
      . exact measurePreserving_mul_left volume s

    have prod_lp1 := MeasureTheory.MemLp.smul (p := 2) (q := 2) (r := 1) (μ := volume) (MeasureTheory.Lp.memLp f) mem_lp_h_comp
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1


@[expose]
noncomputable def Δ := Laplace_linear.mkContinuous _ (laplace_bounded')

lemma Δ_symmetric: Δ.IsSymmetric := by
  unfold LinearMap.IsSymmetric
  intro x hx
  unfold Δ
  -- TODO - why doesn't this fire automatically?
  simp [LinearMap.mkContinuous]
  simp [Laplace_linear]
  rw [laplace_self_adjoint]

lemma Δ_spectrum_subset: spectrum ℝ Δ ⊆ Set.Icc 0 2 := by
  intro a ha
  have restricts := ContinuousLinearMap.IsPositive.spectrumRestricts (f := Δ) (by
    rw [ContinuousLinearMap.isPositive_def]
    refine ⟨?_, ?_⟩
    .
      apply Δ_symmetric
    .
      intro x
      simp [ContinuousLinearMap.reApplyInnerSelf_apply]
      unfold Δ
      simp [LinearMap.mkContinuous]
      simp [Laplace_linear]
      rw [← laplace_self_adjoint]
      apply laplace_positive_semidefinite
  )
  simp
  have a_nonneg: 0 ≤ a := by
    have zero_eq: (0: ℝ) = (0: NNReal) := by
      simp
    rw [zero_eq]
    apply (SpectrumRestricts.nnreal_le_iff restricts).mp
    . simp
    . exact ha


  refine ⟨?_, ?_⟩
  .
    exact a_nonneg
  .
    have norm_le: ‖a‖ ≤ ‖(2: ℝ)‖ := by
      have foo := spectrum.norm_le_norm_mul_of_mem ha

      simp at foo
      simp [Δ] at foo
      grw [← (ContinuousLinearMap.opNorm_le_iff (M := ‖2‖) (f := Δ) ?_).mpr]
      .
        have h := spectrum.norm_le_norm_mul_of_mem ha
        rw [ContinuousLinearMap.one_def] at h
        grw [ContinuousLinearMap.norm_id_le] at h
        simpa using h
      . intro x
        simp [Δ, LinearMap.mkContinuous, Laplace_linear]
        have bound := laplace_bounded x
        simp [enorm] at bound
        norm_cast at bound
      . simp

    simp at norm_le
    rw [abs_of_nonneg] at norm_le
    . exact norm_le
    . exact a_nonneg


lemma laplace_spectrum_contains_zero (f_n_limit: f_n_conv_delta_tendsto): 0 ∈ spectrum ℝ Δ := by
  rw [spectrum.zero_mem_iff]
  by_contra this
  obtain ⟨f, hf⟩ := this

  have inv_bounded := ContinuousLinearMap.isBoundedLinearMap (𝕜 := ℝ) (f.inv)

  have nontrival_lp : Nontrivial ↥(Lp ℝ 2 (volume (α := G))) := by
    rw [nontrivial_iff]
    use 0
    use MemLp.toLp (Pi.single 1 1) (by
      apply Continuous.memLp_of_hasCompactSupport
      . apply continuous_of_discreteTopology
      . simp [HasCompactSupport, tsupport]
    )
    simp
    rw [MeasureTheory.Lp.ext_iff]
    rw [ae_eq_everywhere]
    rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)]
    conv =>
      arg 1
      lhs
      equals 0 =>
        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)]
    by_contra!
    apply_fun (fun f => f 1) at this
    simp at this

  have norm_mul_bound := ContinuousLinearEquiv.one_le_norm_mul_norm_symm (ContinuousLinearEquiv.ofUnit f)

  have inv_norm_ge (n: ℕ) : (1 : ENNReal) / (eLpNorm (Laplace_b (F_n n)) 2 (μ := volume (α := G))) ≤ ENNReal.ofReal ‖f.inv‖ := by

    calc
    _ = (eLpNorm (F_n n) 2 (μ := volume (α := G))) / ((eLpNorm (Laplace_b (F_n n)) 2 (μ := volume (α := G)))) := by
      rw [F_n_norm_eq_one]
    _ = (eLpNorm ((f.inv (f.val (F_n_lp2 n)))) 2) / ((eLpNorm (Laplace_b (F_n n)) 2 (μ := volume (α := G)))) := by
      simp [F_n_lp2]
      simp_rw [← mul_apply_eq_comp]
      simp
      rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)]
    _ ≤ ENNReal.ofReal ‖f.inv‖ := by
      have other := ContinuousLinearMap.ratio_le_opNorm (f := f.inv) (x := (((F_n_lp2 n) - conv_mu_lp2 (F_n_lp2 n))))
      conv at other =>
        lhs
        rw [Lp.norm_def]


      conv =>
        lhs
        arg 1
        arg 1
        rhs
        rhs
        rhs
        simp [hf, Δ, Laplace, Laplace_linear]
      simp [-AddSubgroupClass.coe_sub, -AddSubgroup.coe_sub, Laplace]
      apply_fun ENNReal.ofReal at other
      -- TODO - consider removing @[simp] from 'AddSubgroupClass.coe_sub'
      simp only [map_sub, ofReal_norm] at other
      simp only [← Units.inv_eq_val_inv]
      simp only [F_n_lp2, Laplace_b, ← hf, conv_mu_lp2]
      --simp_rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)]
      by_cases norm_f_eq_zero: ‖F_n_lp2 n - conv_mu_lp2 (F_n_lp2 n)‖ = 0
      . rw [norm_eq_zero] at norm_f_eq_zero
        have foo := laplace_zero_iff_zero (F_n_lp2 n) (by
          simp [Laplace]
          exact norm_f_eq_zero
        )
        simp [F_n_lp2] at foo
        apply_fun (fun f => (f: (G → ℝ))) at foo
        simp_rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)] at foo
        conv at foo =>
          rhs
          equals 0 =>
            rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)]
        simp [foo]
        unfold Conv
        simp
        have const_zero: (fun (x: G) => (0 : ℝ)) = 0 := by rfl
        conv =>
          pattern MemLp.toLp _ _
          equals 0 =>
            simp_rw [ae_eq_everywhere.mp (MeasureTheory.AEEqFun.coeFn_zero)]
            simp
            simp_rw [const_zero]
            simp
        simp
        simp_rw [ae_eq_everywhere.mp (MeasureTheory.AEEqFun.coeFn_zero)]
        simp
      rw [ENNReal.ofReal_div_of_pos] at other
      .
        simp only [ofReal_norm, Lp.enorm_def] at other
        rw [ae_eq_everywhere.mp (Lp.coeFn_sub _ _)] at other
        simp only [F_n_lp2, conv_mu_lp2] at other
        simp_rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)] at other
        rw [ENNReal.ofReal_toReal] at other
        .
          rw [ae_eq_everywhere.mp (Lp.coeFn_sub _ _)]
          rw [ae_eq_everywhere.mp (Lp.coeFn_sub _ _)] at other
          simp_rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)] at other
          simp at other
          simp
          simp_rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)]
          exact other
        .
          rw [← ae_eq_everywhere.mp (Lp.coeFn_sub _ _)]
          apply MeasureTheory.Lp.eLpNorm_ne_top
      . simpa using norm_f_eq_zero
      . exact ENNReal.ofReal_mono
  .
    rw [isBoundedLinearMap_iff] at inv_bounded
    obtain ⟨M, M_pos, le_M⟩ := inv_bounded.2

    have foo := F_n_conv_mu_lim f_n_limit
    rw [ENNReal.tendsto_atTop_zero] at foo
    obtain ⟨n, hn⟩ := foo  ((1: ENNReal) /(2 * ‖f.inv‖ₑ)) (by
      simp
      rw [ENNReal.mul_eq_top]
      simp
    )
    specialize hn n (by simp)

    rw [Lp.enorm_def] at hn
    specialize inv_norm_ge n
    simp [Laplace_b] at inv_norm_ge
    rw [ae_eq_everywhere.mp (Lp.coeFn_sub _ _)] at hn
    simp only [F_n_lp2, conv_mu_lp2] at hn
    simp_rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)] at hn
    grw [hn] at inv_norm_ge
    simp at inv_norm_ge

    have norm_nonzero :‖f.inv‖ ≠ 0 := by
      by_contra!
      simp at this

    simp [enorm] at inv_norm_ge
    norm_cast at inv_norm_ge
    rw [two_mul] at inv_norm_ge
    simp at inv_norm_ge

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Harmonic_Proposition318
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Proposition 3.18

`proposition_3_18` and the auxiliary functions `G_n` used to produce an almost-harmonic
sequence.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
attribute [local implicit_reducible] Additive

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V]

open scoped Finset
open scoped Pointwise
open scoped Convolution
open MeasureTheory

open scoped RealInnerProductSpace

set_option maxHeartbeats 600000 in
lemma laplace_g_n (n: ℕ) (hn: 0 < n) (hf: f_n_conv_delta_tendsto): ∃ g: (Lp ℝ 2 volume (α := G)), ‖Laplace g‖ ≤ (1 : ℝ) / n ∧ ⟪Laplace g, g⟫ = 1 := by

  let eps := ((1: ℝ) / n)^2
  -- selfAdjoint.mem_spectrum_eq_re

  let P: Polynomial ℝ := (Polynomial.X^2 - eps • Polynomial.X)

  let Δ := Laplace_linear.mkContinuous _ (laplace_bounded')

  have spec_inter: spectrum ℝ Δ ∩ Set.Ioo 0 eps ≠ ∅ := by
    by_contra!
    have zero_isolated: spectrum ℝ Δ ∩ (Set.Ico 0 eps) = {0} := by
      ext a
      simp
      refine ⟨?_, ?_⟩
      .
        intro ha
        obtain ⟨a_mem_spec, a_range⟩ := ha
        by_contra a_nonzero
        have a_mem: a ∈ Set.Ioo 0 eps := by
          grind

        have a_mem_empty: a ∈ (∅ : Set ℝ) := by
          rw [← this]
          grind

        simp at a_mem_empty
      .
        intro ha
        simp [ha]
        refine ⟨?_, by simp [eps, hn]⟩
        apply laplace_spectrum_contains_zero hf

    have zero_mem := laplace_spectrum_contains_zero hf
    rw [spectrum.mem_iff] at zero_mem
    simp at zero_mem

    let ramp: ℝ → ℝ := fun x => max 0 (min 1 (x / eps))

    have self_adjoint_cx_del: IsSelfAdjoint (Cx.mapCLM Δ) := by
      apply Cx.isSelfAdjoint_mapCLM
      apply Δ_symmetric.isSelfAdjoint


    let Q := cfc (1 - ramp) (Cx.mapCLM Δ)
    have laplace_q: (Cx.mapCLM Δ) * Q = cfc (0: ℝ → ℝ) (Cx.mapCLM Δ) := by
      unfold Q
      nth_rw 1 [← cfc_id (a := Cx.mapCLM Δ) ℝ]
      rw [← cfc_mul (hf := by exact continuousOn_id) (hg := by fun_prop)]
      apply cfc_congr
      intro x hx
      simp [ramp, max_def']
      norm_num
      split_ifs
      .
        rw [Cx.spectrum_mapCLM] at hx
        rename_i x_div
        apply Δ_spectrum_subset at hx
        simp [eps] at x_div
        have x_nonpos := nonpos_of_mul_nonpos_left x_div (by simp [hn])
        left
        simp at hx
        grind
      . simp [min_def']
        split_ifs
        .

          by_cases x_eq: x = eps
          . simp [x_eq, eps]
            field_simp
            simp
          .
            rename_i x_div_le
            rw [div_le_one₀ (by simp [eps] <;> positivity)] at x_div_le
            have x_lt: x < eps := by
              grind


            have x_mem_zero: x ∈ ({0} : Set ℝ) := by
              rw [← zero_isolated]
              simp
              refine ⟨?_, ?_⟩
              .
                rw [Cx.spectrum_mapCLM] at hx
                exact hx
              .
                rw [Cx.spectrum_mapCLM] at hx
                apply Δ_spectrum_subset at hx
                simp at hx
                grind

            simp at x_mem_zero
            simp [x_mem_zero]
        . simp


    simp at laplace_q
    have one_mem_q_spec: 1 ∈ spectrum ℝ Q := by
      rw [cfc_map_spectrum (hf := by fun_prop)]
      simp [ramp]
      use 0
      rw [Cx.spectrum_mapCLM]
      refine ⟨laplace_spectrum_contains_zero hf, ?_⟩
      right
      simp

    have nontrivial_cx: Nontrivial (Cx ↥(Lp ℝ 2 volume (α := G))  →L[ℂ] Cx ↥(Lp ℝ 2 volume (α := G))) := by

      use 1
      use 0
      simp
      rw [ContinuousLinearMap.ext_iff]
      simp
      let hf := (finsupp_lp_top (Pi.single 1 1) (by
        simp
      ) 2)
      rw [← my_haar_eq_count] at hf
      use (hf.toLp, 0)
      apply_fun (fun a => a.fst)
      simp
      rw [MeasureTheory.Lp.ext_iff]
      have haar_eq_volume: myHaar = volume := by
        simp [volume]
      simp_rw [haar_eq_volume]
      rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
      simp
      rw [funext_iff]
      simp
      use 1
      simp

    have Q_nonzero: Q ≠ 0 := by
      by_contra!
      simp [this] at one_mem_q_spec

    apply ContinuousLinearMap.exists_ne_zero at Q_nonzero
    obtain ⟨x, hx⟩ := Q_nonzero
    have laplace_q_x: (Cx.mapCLM Δ) (Q x) = 0 := by
      rw [← ContinuousLinearMap.mul_apply]
      simp [laplace_q]

    by_cases fst_nonzero: (Q x).fst ≠ 0
    .
      simp at laplace_q_x
      apply_fun (fun a => a.fst) at laplace_q_x
      simp at laplace_q_x
      simp [Δ, LinearMap.mkContinuous, Laplace_linear] at laplace_q_x
      apply laplace_zero_iff_zero at laplace_q_x
      contradiction
    .
      have snd_nonzero: (Q x).snd ≠ 0 := by
        by_contra!
        simp at fst_nonzero
        have Q_zero: (Q x) = 0 := by
          apply Cx.ext
          all_goals {
            simp
            grind
          }
        contradiction

      -- TODO - deduplicate this
      simp at laplace_q_x
      apply_fun (fun a => a.snd) at laplace_q_x
      simp at laplace_q_x
      simp [Δ, LinearMap.mkContinuous, Laplace_linear] at laplace_q_x
      apply laplace_zero_iff_zero at laplace_q_x
      contradiction


  rw [← Set.nonempty_iff_ne_empty] at spec_inter
  obtain ⟨a, ha⟩ := spec_inter


  have a_spec := Set.mem_of_mem_inter_left ha
  have a_lt := Set.mem_of_mem_inter_right ha


  have mem_spec: P.eval a ∈ spectrum ℝ (Polynomial.aeval Δ P) := by
    apply spectrum.subset_polynomial_aeval
    simp
    use a

  have p_a_neg: P.eval a < 0 := by
    simp [P]
    simp at ha
    nlinarith

  have eval_symm: (((Polynomial.aeval Δ) P)).IsSymmetric := by
    simp [P]
    apply LinearMap.IsSymmetric.sub
    . apply LinearMap.IsSymmetric.pow
      apply Δ_symmetric
    . apply LinearMap.IsSymmetric.smul
      . simp
      . apply Δ_symmetric


  have not_pos := ContinuousLinearMap.IsPositive.spectrumRestricts (f := (Polynomial.aeval Δ P)).mt ?_
  .
    simp [ContinuousLinearMap.IsPositive, eval_symm] at not_pos
    obtain ⟨x, hx, x_inner⟩ := not_pos
    simp [ContinuousLinearMap.reApplyInnerSelf, P] at x_inner
    have laplace_inner_nonzero: √⟪Laplace ⟨x, hx⟩, ⟨x, hx⟩⟫ ≠ 0 := by
      rw [Real.sqrt_ne_zero']
      by_contra!
      --
      have nonneg := laplace_positive_semidefinite ⟨x, hx⟩
      rw [laplace_self_adjoint] at nonneg
      have foo := inner_laplace_zero ⟨x, hx⟩ (by
        grind
      )
      simp [Δ, LinearMap.mkContinuous, Laplace_linear] at x_inner
      simp [foo] at x_inner
      apply laplace_zero_iff_zero at foo
      simp [foo] at x_inner


    use ((√⟪Laplace ⟨x, hx⟩, ⟨x, hx⟩⟫)⁻¹) • ⟨x, hx⟩
    rw [inner_sub_left] at x_inner
    refine ⟨?_, ?_⟩
    .
      rw [norm_eq_sqrt_real_inner]
      simp [Δ, LinearMap.mkContinuous, Laplace_linear] at x_inner
      rw [← laplace_self_adjoint] at x_inner
      simp [inner_smul_left] at x_inner
      simp
      rw [laplace_smul]
      rw [norm_smul]
      simp
      rw [← Real.lt_sqrt] at x_inner
      . grw [x_inner]
        rw [Real.sqrt_mul]
        ring
        rw [abs_of_nonneg]
        .
          field_simp
          simp [eps]
          grind
        . simp
        . simp [eps]
      . simp

    .
      rw [laplace_smul]
      rw [inner_smul_left, inner_smul_right]
      simp
      field_simp
      rw [Real.sq_sqrt]
      rw [← laplace_self_adjoint]
      apply laplace_positive_semidefinite
  . rw [SpectrumRestricts.nnreal_iff]
    simp
    use P.eval a


  -- -- simp [P] at a_spec
  -- -- rw [spectrum.mem_iff] at a_spec
  -- -- --rw [LinearMap.isUnit_iff_ker_eq_bot] at a_spec
  -- -- rw [ContinuousLinearMap.isUnit_iff_bijective] at a_spec


  -- This whole proof is completely wrong - it needs to use the spectral theorem


@[expose]
noncomputable def G_n (n: ℕ) (hn: 0 < n) (hf: f_n_conv_delta_tendsto) := Classical.choose (laplace_g_n n hn hf)


end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_HomogeneousWordCoefficients
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite right-nested coefficients of homogeneous primitive words -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {n d : ℕ}

theorem exists_wordOfFn_of_length (w : FreeMonoid (Fin n)) (h : w.length = d) :
    ∃ f : Fin d → Fin n, wordOfFn f = w := by
  change w.toList.length = d at h
  subst d
  exact ⟨w.toList.get, congrArg FreeMonoid.ofList (List.ofFn_get _)⟩

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RescaledGeneratorBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform bounds for normalized generator vectors

The same maximizing-basis exchange estimate which bounds structure constants
also bounds all exponentially rescaled generator vectors. Thus both parts of
the normalized Lie-law data lie in fixed bounded coordinate sets.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype I] [DecidableEq I]

/-- Coordinates of a scalar-rescaled vector in an exponentially rescaled basis. -/
theorem repr_exponentialRescaleBasis_smul {J : Type*} (b : Basis J ℝ L)
    (cost : J → ℝ) (r s : ℝ) (x : L) (j : J) :
    (exponentialRescaleBasis b cost r).repr (Real.exp (r * s) • x) j =
      b.repr x j * Real.exp (r * (s - cost j)) := by
  simp only [exponentialRescaleBasis, Basis.repr_unitsSMul, Units.smul_def,
    Units.val_mk0, Units.val_inv_eq_inv_val, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [← Real.exp_neg]
  have he : Real.exp (-(r * cost j)) * Real.exp (r * s) =
      Real.exp (r * (s - cost j)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = b.repr x j * (Real.exp (-(r * cost j)) * Real.exp (r * s)) := by ring
    _ = _ := by rw [he]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Representation
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat
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

-- The space 'GL(W)' of invertible continuous linear functions from W to W
abbrev GL_W := (W →L[ℝ] W)ˣ

-- The space 'GL(W)' of invertible continuous linear functions from W to W


@[expose]
def GRep: Representation ℝ G (LipschitzH)  := {
  toFun := fun g => {
    toFun := gAct g
    map_add' := by
      intro f h
      ext a
      simp [gAct]
    map_smul' := by
      intro c f
      ext a
      simp [gAct]
  }
  map_one' := by
    ext f a
    simp [gAct]
  map_mul' := by
    intro g h
    ext f a
    simp [gAct]
    simp [mul_assoc]
}



-- We start with a map from G into the space of (not necessarily invertible) linear maps from W to W
@[expose]
def GRepW_non_invertible: Representation ℝ G (W) := Representation.quotient (GRep) ConstF (by
  intro g
  intro f hf
  simp
  simp [ConstF]
  simp [ConstF] at hf
  obtain ⟨K, hK⟩ := hf
  use K
  ext a
  simp [GRep]
  rw [← hK]
  rw [gAct_const]
)

-- We then build a map from G into the group of invertible linear maps from W to W
@[expose]
noncomputable def GRepW_base := Representation.asGroupHom GRepW_non_invertible


set_option synthInstance.maxHeartbeats 500000


end GeneratesNS
end


