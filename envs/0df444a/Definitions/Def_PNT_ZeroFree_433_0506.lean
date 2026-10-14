-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0506
-- name    : PNT_ZeroFree_433_0506
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:48:56.496184+00:00
-- url     : https://prove2.me/theorems/a1292bf9-a265-4e04-b10b-045cc2d6e21f
-- title:
--   Zero-free region foundations: Detector.GramPeriodicPoisson [0506]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Detector.GramPeriodicPoisson
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/GramPeriodicPoisson.lean#L13-L1091

import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0016
import Definitions.Def_PNT_ZeroFree_433_0019
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0037
import Definitions.Def_PNT_ZeroFree_433_0037_2
import Definitions.Def_PNT_ZeroFree_433_0038_1
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0100
import Definitions.Def_PNT_ZeroFree_433_0101
import Definitions.Def_PNT_ZeroFree_433_0148_parallel2
import Definitions.Def_PNT_ZeroFree_433_0221_parallel2
import Definitions.Def_PNT_ZeroFree_433_0229_parallel2
import Definitions.Def_PNT_ZeroFree_433_0505
import Definitions.Def_PNT_ZeroFree_433_0506_parallel1
import Definitions.Def_PNT_ZeroFree_433_0506_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0506_parallel1_2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/GramPeriodicPoisson.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical FourierTransform SchwartzMap RealInnerProductSpace

namespace ProbeGramPeriodicPoisson


theorem planeMajorant_eisenstein_summable :
    Summable (fun m : ActualEisensteinCubic.O =>
      planeMajorant (ConcreteTraceCRT.eisEmbedding m)) := by
  have hs := CubicEisenstein.summable_embedding_rpow (-4) (by norm_num)
  rw [← Finset.summable_compl_iff (s := ({0} : Finset ActualEisensteinCubic.O))]
  apply Summable.of_nonneg_of_le (fun _ => by unfold planeMajorant; positivity) _
    (hs.subtype (fun m : ActualEisensteinCubic.O => m ∉ ({0} : Finset _)))
  intro m
  have hm : m.val ≠ 0 := by simpa using m.property
  have hn : 0 < ‖ConcreteTraceCRT.eisEmbedding m.val‖ := norm_pos_iff.mpr
    (ConcreteTraceCRT.eisEmbedding_ne_zero hm)
  change ((1+‖ConcreteTraceCRT.eisEmbedding m.val‖^2)^2)⁻¹ ≤
    ‖ConcreteTraceCRT.eisEmbedding m.val‖ ^ (-4:ℝ)
  rw [show (-4:ℝ) = -(4:ℝ) by rfl, Real.rpow_neg hn.le, Real.rpow_ofNat]
  apply inv_anti₀ (by positivity)
  nlinarith [sq_nonneg (‖ConcreteTraceCRT.eisEmbedding m.val‖^2)]

theorem joint_eisenstein_summable_norm (W : 𝓢(Joint, ℂ)) :
    Summable (fun m : ActualEisensteinCubic.O × ActualEisensteinCubic.O =>
      ‖W (embeddingPair m)‖) := by
  have hs := planeMajorant_eisenstein_summable.mul_of_nonneg
    planeMajorant_eisenstein_summable
    (fun _ => by unfold planeMajorant; positivity)
    (fun _ => by unfold planeMajorant; positivity)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (hs.mul_left (productDecayConstant W))
  intro m
  exact norm_le_product_majorant W _ _

theorem joint_weighted_summable {R : Type*} (q : ActualEisensteinCubic.O → R)
    (a : R × R → ℂ) (B : ℝ) (hB : ∀ r, ‖a r‖ ≤ B) (W : 𝓢(Joint, ℂ)) :
    Summable (fun m : ActualEisensteinCubic.O × ActualEisensteinCubic.O =>
      a (q m.1,q m.2) * W (embeddingPair m)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((joint_eisenstein_summable_norm W).mul_left B)
  intro m
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)

open scoped LineDeriv


open EisensteinSchwartzPoisson hiding O


private theorem joint_cartesian_eq_partial (W : 𝓢(Joint, ℂ)) :
    (∑' p : (ℤ × ℤ) × (ℤ × ℤ), W (point (cartesianPoint p.1) (cartesianPoint p.2))) =
      ∑' n : ℤ × ℤ, ∑' m : ℤ × ℤ,
        partialFourier W (cartesianPoint n) (cartesianPoint m) := by
  have hp := (joint_cartesian_summable_norm W).of_norm
  have hm := (partialFourier_cartesian_summable_norm W).of_norm
  calc
    _ = ∑' m : ℤ × ℤ, ∑' n : ℤ × ℤ,
        W (point (cartesianPoint m) (cartesianPoint n)) := hp.tsum_prod
    _ = ∑' m : ℤ × ℤ, ∑' n : ℤ × ℤ,
        partialFourier W (cartesianPoint n) (cartesianPoint m) := by
      apply tsum_congr
      intro m
      exact rightSlice_poisson W _
    _ = _ := hm.tsum_comm.symm

private theorem partial_cartesian_poisson (W : 𝓢(Joint, ℂ)) (n : ℤ × ℤ) :
    (∑' m : ℤ × ℤ, partialFourier W (cartesianPoint n) (cartesianPoint m)) =
      ∑' m : ℤ × ℤ, (𝓕 W) (point (cartesianPoint m) (cartesianPoint n)) := by
  calc
    _ = ∑' m : ℤ × ℤ, partialFourierSchwartz W (cartesianPoint n) (cartesianPoint m) :=
      tsum_congr fun m =>
        (partialFourierSchwartz_apply W (cartesianPoint n) (cartesianPoint m)).symm
    _ = ∑' m : ℤ × ℤ,
        (𝓕 (partialFourierSchwartz W (cartesianPoint n)) : 𝓢(ℂ, ℂ)) (cartesianPoint m) := by
      simpa only [cartesianPoint] using
        integer_pair_poisson (partialFourierSchwartz W (cartesianPoint n))
    _ = _ := tsum_congr fun m =>
      fourier_partialFourierSchwartz W (cartesianPoint m) (cartesianPoint n)

private theorem cartesian_swap_tsum (F : 𝓢(Joint, ℂ)) :
    (∑' n : ℤ × ℤ, ∑' m : ℤ × ℤ, F (point (cartesianPoint m) (cartesianPoint n))) =
      ∑' p : (ℤ × ℤ) × (ℤ × ℤ), F (point (cartesianPoint p.1) (cartesianPoint p.2)) := by
  have hF := (joint_cartesian_summable_norm F).of_norm
  exact hF.tsum_comm.trans hF.tsum_prod.symm

private theorem partial_cartesian_eq_fourier (W : 𝓢(Joint, ℂ)) :
    (∑' n : ℤ × ℤ, ∑' m : ℤ × ℤ,
      partialFourier W (cartesianPoint n) (cartesianPoint m)) =
      ∑' p : (ℤ × ℤ) × (ℤ × ℤ), (𝓕 W) (point (cartesianPoint p.1) (cartesianPoint p.2)) := by
  exact (tsum_congr (partial_cartesian_poisson W)).trans (cartesian_swap_tsum (𝓕 W))

theorem joint_cartesian_poisson (W : 𝓢(Joint, ℂ)) :
    (∑' p : (ℤ × ℤ) × (ℤ × ℤ), W (point (cartesianPoint p.1) (cartesianPoint p.2))) =
      ∑' p : (ℤ × ℤ) × (ℤ × ℤ), (𝓕 W) (point (cartesianPoint p.1) (cartesianPoint p.2)) := by
  exact (joint_cartesian_eq_partial W).trans (partial_cartesian_eq_fourier W)


theorem joint_affine_poisson (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) (b : Joint) :
    (∑' p : (ℤ × ℤ) × (ℤ × ℤ),
      W (A (point (cartesianPoint p.1) (cartesianPoint p.2))+b)) =
      jointInverseJacobian A • ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
        Real.fourierChar (inner ℝ b
          (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2)))) •
        (𝓕 W) (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2))) := by
  have h := joint_cartesian_poisson (jointAffine W A b)
  simp only [jointAffine_apply, joint_fourier_affine] at h
  rw [tsum_const_smul''] at h
  exact h


open ActualEisensteinCubic ConcreteTraceCRT

theorem actual_joint_coset_poisson (W : 𝓢(Joint, ℂ)) (b : O × O) (c : O) (hc : c ≠ 0) :
    (∑' m : O × O, W (embeddingPair (b.1+c*m.1,b.2+c*m.2))) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 •
        ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
          Real.fourierChar (inner ℝ (embeddingPair b)
            (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
            (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p) := by
  let A := eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc)
  have h := joint_affine_poisson W (blockMap A) (embeddingPair b)
  simp only [jointInverseJacobian_blockMap, jointDual_blockMap] at h
  rw [eisenstein_inverseJacobian] at h
  calc
    _ = ∑' p : (ℤ × ℤ) × (ℤ × ℤ), W (embeddingPair
        (b.1+c*latticeCoordEquiv.symm p.1,b.2+c*latticeCoordEquiv.symm p.2)) :=
      ((latticeCoordEquiv.symm.prodCongr latticeCoordEquiv.symm).tsum_eq _).symm
    _ = ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
        W (blockMap A (point (cartesianPoint p.1) (cartesianPoint p.2))+embeddingPair b) := by
      apply tsum_congr
      intro p
      congr 1
      change point (eisEmbedding (b.1+c*ActualEisensteinCoordinates.eval p.1.1 p.1.2))
        (eisEmbedding (b.2+c*ActualEisensteinCoordinates.eval p.2.1 p.2.2)) = _
      simp only [map_add, map_mul, blockMap_apply, point]
      rw [← eisensteinLatticeMap_point (eisEmbedding c) (eisEmbedding_ne_zero hc) p.1,
        ← eisensteinLatticeMap_point (eisEmbedding c) (eisEmbedding_ne_zero hc) p.2]
      change point (eisEmbedding b.1 + A (cartesianPoint p.1))
        (eisEmbedding b.2 + A (cartesianPoint p.2)) =
          point (A (cartesianPoint p.1)+eisEmbedding b.1)
            (A (cartesianPoint p.2)+eisEmbedding b.2)
      simp only [add_comm]
    _ = _ := h


theorem actual_joint_periodic_poisson (W : 𝓢(Joint, ℂ)) (c : O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) :
    letI : Finite (Residue c) := finite_quotient_span hc
    letI : Fintype (Residue c) := Fintype.ofFinite _
    (∑' m : O × O, a (quotientPair c m) * W (embeddingPair m)) =
      ∑ r : Residue c × Residue c, a r *
        ((2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 •
          ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
            Real.fourierChar (inner ℝ (embeddingPair (representativePair c r))
              (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
              (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) := by
  classical
  let : Finite (Residue c) := finite_quotient_span hc
  let : Fintype (Residue c) := Fintype.ofFinite _
  have ha (r : Residue c × Residue c) : ‖a r‖ ≤ ∑ t : Residue c × Residue c, ‖a t‖ :=
    Finset.single_le_sum (fun t _ => norm_nonneg (a t)) (Finset.mem_univ r)
  have hs := joint_weighted_summable (Ideal.Quotient.mk (Ideal.span {c})) a _ ha W
  rw [GaussianAbelPartition.tsum_periodic_weighted_partition (quotientPair c) a
    (fun m => W (embeddingPair m)) hs]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  exact (joint_fiber_tsum c hc r (fun m => W (embeddingPair m))).trans
    (actual_joint_coset_poisson W (representativePair c r) c hc)

theorem actual_joint_periodic_fourier (W : 𝓢(Joint, ℂ)) (c : O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) :
    (∑' m : O × O, a (quotientPair c m) * W (embeddingPair m)) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 •
        ∑' p : (ℤ × ℤ) × (ℤ × ℤ), residueFourier c hc a p *
          (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p) := by
  classical
  let : Finite (Residue c) := finite_quotient_span hc
  let : Fintype (Residue c) := Fintype.ofFinite _
  rw [actual_joint_periodic_poisson W c hc a]
  have hs (r : Residue c × Residue c) : Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      a r * (Real.fourierChar (inner ℝ (embeddingPair (representativePair c r))
        (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
        (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p))) := by
    apply Summable.mul_left
    apply Summable.of_norm
    simpa only [Circle.norm_smul] using
      jointFrequency_summable_norm W (eisEmbedding c) (eisEmbedding_ne_zero hc)
  simp_rw [mul_smul_comm, ← tsum_mul_left]
  rw [← Finset.smul_sum, ← Summable.tsum_finsetSum (fun r _ => hs r)]
  congr 1
  apply tsum_congr
  intro p
  simp only [residueFourier, tsum_fintype, Circle.smul_def, smul_eq_mul,
    Finset.sum_mul, mul_assoc]


theorem norm_periodic_zero_mean_le (W : 𝓢(Joint, ℂ)) (c : O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) (B : ℝ) (hB : ∀ r, ‖a r‖ ≤ B)
    (hmean : (∑' r, a r) = 0) :
    ‖∑' m : O × O, a (quotientPair c m) * W (embeddingPair m)‖ ≤
      (4/3:ℝ) * B *
        ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
          ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖ := by
  let F (p : (ℤ × ℤ) × (ℤ × ℤ)) := residueFourier c hc a p *
    (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)
  let q : ℝ := Ideal.absNorm (Ideal.span {c})
  have hF0 : F 0 = 0 := by simp [F, hmean]
  have hnorm (p : (ℤ × ℤ) × (ℤ × ℤ)) : ‖F p‖ ≤ q^2 * B *
      ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)‖ := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (residueFourier_norm_le c hc a B hB p) (norm_nonneg _)
  have hsF : Summable (fun p => ‖F p‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm
      ((jointFrequency_summable_norm W (eisEmbedding c) (eisEmbedding_ne_zero hc)).mul_left _)
  have heq : (∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, F p.val) = ∑' p, F p := by
    apply tsum_subtype_eq_of_support_subset
    intro p hp
    change F p ≠ 0 at hp
    exact fun h => hp (h ▸ hF0)
  have hb : ‖∑' p, F p‖ ≤ q^2 * B *
      ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
        ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖ := by
    rw [← heq]
    have hs1 : Summable (fun p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0} => ‖F p.val‖) :=
      hsF.subtype (fun p => p ≠ 0)
    have hm : Summable (fun p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0} =>
        ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖) :=
      (jointFrequency_summable_norm W (eisEmbedding c)
        (eisEmbedding_ne_zero hc)).subtype (fun p => p ≠ 0)
    have ht : (∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, ‖F p.val‖) ≤
        ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, q^2 * B *
          ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖ :=
      Summable.tsum_le_tsum (fun p => hnorm p.val) hs1 (hm.mul_left (q^2*B))
    exact (norm_tsum_le_tsum_norm hs1).trans (by simpa only [tsum_mul_left] using ht)
  rw [actual_joint_periodic_fourier W c hc a, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (2/(Real.sqrt 3*‖eisEmbedding c‖^2))^2 * (q^2 * B *
      ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
        ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, principal_joint_inverse_covolume c hc]


theorem principal_high_bound (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (c : O) (_hc : c ≠ 0)
        (a : Residue c × Residue c → ℂ) (B : ℝ), 0 ≤ B →
        (∀ r, ‖a r‖ ≤ B) → (∑' r, a r) = 0 →
        ∀ (N : ℝ), 0 < N → (Ideal.absNorm (Ideal.span {c}) : ℝ) ≤ N →
        ‖∑' m : O × O, a (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A := by
  obtain ⟨S,C,hC,hhigh⟩ := ProbeGramLatticeDecay.dual_fourier_lattice_bound A hA
  refine ⟨S,(4/3)*C,mul_pos (by norm_num) hC,?_⟩
  intro W c hc a B hB0 hB hmean N hN hscale
  let q : ℝ := Ideal.absNorm (Ideal.span {c})
  have hq : 0 < q := by
    dsimp only [q]
    rw [← eisEmbedding_norm_sq_eq_absNorm_span]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hc))
  have hL : 1 ≤ Real.sqrt (N/q) := by
    apply Real.le_sqrt_of_sq_le
    norm_num only [one_pow]
    exact (le_div_iff₀ hq).mpr (by simpa only [one_mul] using hscale)
  let u : ℂ := generatorRotation (eisEmbedding c)
  have hu : ‖u‖ = 1 := norm_generatorRotation _ (eisEmbedding_ne_zero hc)
  have ht4 : (Real.sqrt N)^4 = N^2 := by
    rw [show (4:ℕ) = 2*2 by norm_num, pow_mul, Real.sq_sqrt hN.le]
  have hf (p : (ℤ × ℤ) × (ℤ × ℤ)) :
      ‖(𝓕 (scaledSource W (Real.sqrt N) (Real.sqrt_pos.mpr hN)))
        (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)‖ =
      N^2 * ‖(𝓕 W) (ProbeGramLatticeDecay.scaledDualPoint (Real.sqrt (N/q)) u p)‖ := by
    rw [fourier_scaledSource, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _), ht4,
      scaled_jointFrequency_eq _ _ N hN]
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
  have h := norm_periodic_zero_mean_le
    (scaledSource W (Real.sqrt N) (Real.sqrt_pos.mpr hN)) c hc a B hB hmean
  simp_rw [scaledSource_physicalPoint W N hN, hf, tsum_mul_left] at h
  have hD := hhigh W (Real.sqrt (N/q)) hL u hu
  rw [sqrt_ratio_decay N q hN hq A] at hD
  calc
    _ ≤ (4/3:ℝ)*B*(N^2 *
        ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
          ‖(𝓕 W) (ProbeGramLatticeDecay.scaledDualPoint (Real.sqrt (N/q)) u p.val)‖) := h
    _ ≤ (4/3:ℝ)*B*(N^2 *
        (C * ProbeGramLatticeDecay.sourceControl S W * (q/N)^A)) := by
      gcongr
    _ = _ := by ring


theorem principal_periodic_bound (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (c : O), c ≠ 0 →
        ∀ (a : Residue c × Residue c → ℂ) (B : ℝ), 0 ≤ B →
        (∀ r, ‖a r‖ ≤ B) → (∑' r, a r) = 0 → ∀ (N : ℝ), 1 ≤ N →
        Summable (fun m : O × O =>
          a (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
        ‖∑' m : O × O, a (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            min 1 (((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A) := by
  obtain ⟨Sl,Cl,hCl,hl⟩ := ProbeGramLatticeDecay.physical_lattice_bound
  obtain ⟨Sh,Ch,hCh,hh⟩ := principal_high_bound A hA
  refine ⟨Sl∪Sh,Cl+Ch,add_pos hCl hCh,?_⟩
  intro W c hc a B hB0 hB hm N hN
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  refine ⟨physical_weighted_summable W N hNp _ B (fun m => hB _),?_⟩
  have hSl : Cl*ProbeGramLatticeDecay.sourceControl Sl W ≤
      (Cl+Ch)*ProbeGramLatticeDecay.sourceControl (Sl∪Sh) W :=
    mul_le_mul (le_add_of_nonneg_right hCh.le)
      (ProbeGramLatticeDecay.sourceControl_mono Finset.subset_union_left W)
      (ProbeGramLatticeDecay.sourceControl_nonneg _ _) (by positivity)
  have hSh : Ch*ProbeGramLatticeDecay.sourceControl Sh W ≤
      (Cl+Ch)*ProbeGramLatticeDecay.sourceControl (Sl∪Sh) W :=
    mul_le_mul (le_add_of_nonneg_left hCl.le)
      (ProbeGramLatticeDecay.sourceControl_mono Finset.subset_union_right W)
      (ProbeGramLatticeDecay.sourceControl_nonneg _ _) (by positivity)
  have hratio : 0 ≤ (Ideal.absNorm (Ideal.span {c}) : ℝ)/N := div_nonneg (by positivity) hNp.le
  by_cases hscale : (Ideal.absNorm (Ideal.span {c}) : ℝ) ≤ N
  · have hp : ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A ≤ 1 :=
      pow_le_one₀ hratio ((div_le_one hNp).mpr hscale)
    rw [min_eq_right hp]
    exact (hh W c hc a B hB0 hB hm N hNp hscale).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSh hB0) (sq_nonneg _))
        (pow_nonneg hratio _))
  · have hp : 1 ≤ ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A :=
      one_le_pow₀ ((le_div_iff₀ hNp).mpr (by linarith))
    rw [min_eq_left hp, mul_one]
    calc
      _ ≤ B * ∑' m : O × O, ‖W (ProbeGramLatticeDecay.physicalPoint N m)‖ :=
        norm_physical_weighted_le W N hNp _ B (fun m => hB _)
      _ ≤ B * (Cl*ProbeGramLatticeDecay.sourceControl Sl W*N^2) :=
        mul_le_mul_of_nonneg_left (hl W N hN) hB0
      _ = Cl*ProbeGramLatticeDecay.sourceControl Sl W*B*N^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSl hB0) (sq_nonneg _)


theorem ideal_periodic_bound (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (r : Ideal O), r ≠ 0 →
        ∀ (a : (O ⧸ r) × (O ⧸ r) → ℂ) (B : ℝ), 0 ≤ B →
        (∀ v, ‖a v‖ ≤ B) → (∑' v, a v) = 0 → ∀ (N : ℝ), 1 ≤ N →
        Summable (fun m : O × O =>
          a (idealQuotientPair r m) * W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
        ‖∑' m : O × O, a (idealQuotientPair r m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            min 1 (((Ideal.absNorm r : ℝ)/N)^A) := by
  obtain ⟨S,C,hC,h⟩ := principal_periodic_bound A hA
  refine ⟨S,C,hC,?_⟩
  intro W r hr
  obtain ⟨c,hc,heq⟩ : ∃ c : O, c ≠ 0 ∧ Ideal.span {c} = r :=
    ⟨ConcretePrimeRowBridge.idealGenerator r,
      ConcretePrimeRowBridge.idealGenerator_ne_zero r hr,
      ConcretePrimeRowBridge.span_idealGenerator r⟩
  subst r
  exact h W c hc

theorem principal_annular_periodic_bound (A : ℕ) (hA : 2 < A)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), ProbeGramAnnularLattice.AnnularSupport a b W →
      ∀ (c : O), c ≠ 0 → ∀ (d : Residue c × Residue c → ℂ) (B : ℝ), 0 ≤ B →
        (∀ r, ‖d r‖ ≤ B) → (∑' r, d r) = 0 → ∀ (N : ℝ), 0 < N →
        Summable (fun m : O × O =>
          d (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
        ‖∑' m : O × O, d (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            min 1 (((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A) := by
  obtain ⟨Sl,Cl,hCl,hl⟩ := ProbeGramAnnularLattice.annular_weighted_lattice_bound a b ha hab
  obtain ⟨Sh,Ch,hCh,hh⟩ := principal_high_bound A hA
  refine ⟨Sl∪Sh,Cl+Ch,add_pos hCl hCh,?_⟩
  intro W hW c hc d B hB0 hB hm N hN
  refine ⟨physical_weighted_summable W N hN _ B (fun m => hB _),?_⟩
  have hSl : Cl*ProbeGramLatticeDecay.sourceControl Sl W ≤
      (Cl+Ch)*ProbeGramLatticeDecay.sourceControl (Sl∪Sh) W :=
    mul_le_mul (le_add_of_nonneg_right hCh.le)
      (ProbeGramLatticeDecay.sourceControl_mono Finset.subset_union_left W)
      (ProbeGramLatticeDecay.sourceControl_nonneg _ _) (by positivity)
  have hSh : Ch*ProbeGramLatticeDecay.sourceControl Sh W ≤
      (Cl+Ch)*ProbeGramLatticeDecay.sourceControl (Sl∪Sh) W :=
    mul_le_mul (le_add_of_nonneg_left hCl.le)
      (ProbeGramLatticeDecay.sourceControl_mono Finset.subset_union_right W)
      (ProbeGramLatticeDecay.sourceControl_nonneg _ _) (by positivity)
  have hratio : 0 ≤ (Ideal.absNorm (Ideal.span {c}) : ℝ)/N := div_nonneg (by positivity) hN.le
  by_cases hscale : (Ideal.absNorm (Ideal.span {c}) : ℝ) ≤ N
  · have hp : ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A ≤ 1 :=
      pow_le_one₀ hratio ((div_le_one hN).mpr hscale)
    rw [min_eq_right hp]
    exact (hh W c hc d B hB0 hB hm N hN hscale).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSh hB0) (sq_nonneg _))
        (pow_nonneg hratio _))
  · have hp : 1 ≤ ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A :=
      one_le_pow₀ ((le_div_iff₀ hN).mpr (by linarith))
    rw [min_eq_left hp, mul_one]
    exact (hl W hW (fun m => d (quotientPair c m)) B hB0
      (fun m => hB _) N hN).2.trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSl hB0) (sq_nonneg _))

theorem ideal_annular_periodic_bound (A : ℕ) (hA : 2 < A)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), ProbeGramAnnularLattice.AnnularSupport a b W →
      ∀ (r : Ideal O), r ≠ 0 → ∀ (d : (O ⧸ r) × (O ⧸ r) → ℂ) (B : ℝ), 0 ≤ B →
        (∀ v, ‖d v‖ ≤ B) → (∑' v, d v) = 0 → ∀ (N : ℝ), 0 < N →
        Summable (fun m : O × O =>
          d (idealQuotientPair r m) * W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
        ‖∑' m : O × O, d (idealQuotientPair r m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            min 1 (((Ideal.absNorm r : ℝ)/N)^A) := by
  obtain ⟨S,C,hC,h⟩ := principal_annular_periodic_bound A hA a b ha hab
  refine ⟨S,C,hC,?_⟩
  intro W hW r hr
  obtain ⟨c,hc,heq⟩ : ∃ c : O, c ≠ 0 ∧ Ideal.span {c} = r :=
    ⟨ConcretePrimeRowBridge.idealGenerator r,
      ConcretePrimeRowBridge.idealGenerator_ne_zero r hr,
      ConcretePrimeRowBridge.span_idealGenerator r⟩
  subst r
  exact h W hW c hc

end ProbeGramPeriodicPoisson

end

end OAI

end


