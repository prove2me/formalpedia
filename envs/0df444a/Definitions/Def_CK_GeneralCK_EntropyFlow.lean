-- Prove2me | Definitions.Def_CK_GeneralCK_EntropyFlow
-- name    : CK_GeneralCK_EntropyFlow
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:25:30.521796+00:00
-- url     : https://prove2.me/theorems/ee8975c8-7d41-4009-854b-0115c79048c3
-- title:
--   Courtade–Kumar proof module `GeneralCK.EntropyFlow` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.EntropyFlow` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.EntropyFlow` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.EntropyFlow (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/EntropyFlow.lean)

import Definitions.Def_CK_GeneralCK_CubeAnalysis
import Definitions.Def_CK_GeneralCK_NoiseEvolution
import Definitions.Def_CK_GeneralCK_EntropyComparison
import Definitions.Def_CK_GeneralCK_EnergyIdentity
import Mathlib.Analysis.Convex.Jensen
import Definitions.Def_GeneralCK_entropy_flow

namespace GeneralCK.Flow
open scoped BigOperators
open CubeAnalysis
















theorem mean_add {n : ℕ} (v w : Cube n → ℝ) :
    mean (fun x => v x + w x) = mean v + mean w := by
  simp [mean, Finset.sum_add_distrib, mul_add]

theorem mean_const_mul {n : ℕ} (c : ℝ) (v : Cube n → ℝ) :
    mean (fun x => c * v x) = c * mean v := by
  simp only [mean, ← Finset.mul_sum]
  ring

theorem initialMean_eq {n : ℕ} (f : Cube n → Bool) (eps : ℝ) :
    initialMean f eps = eps + (1 - 2 * eps) * Information.meanIndicator f := by
  unfold initialMean regularized
  rw [mean_add, mean_const, mean_const_mul]
  rfl

theorem regularized_bounds {n : ℕ} (f : Cube n → Bool) {eps : ℝ}
    (he : eps ≤ 1 / 2) (x : Cube n) :
    eps ≤ regularized f eps x ∧ regularized f eps x ≤ 1 - eps := by
  cases h : f x <;> simp only [regularized, h, Bool.false_eq_true, ite_false, ite_true,
    mul_zero, mul_one, add_zero] <;> constructor <;> linarith

theorem flow_bounds {n : ℕ} (f : Cube n → Bool) {eps t : ℝ}
    (he : eps ≤ 1 / 2) (ht : 0 ≤ t) (x : Cube n) :
    eps ≤ flow f eps t x ∧ flow f eps t x ≤ 1 - eps := by
  exact Noise.applyNoise_bounds (Noise.crossover_nonneg ht)
    (le_trans (Noise.crossover_lt_half t).le (by norm_num))
    (regularized f eps) (regularized_bounds f he) x

theorem flow_interior {n : ℕ} (f : Cube n → Bool) {eps t : ℝ}
    (he : 0 < eps) (he' : eps < 1 / 2) (ht : 0 ≤ t) (x : Cube n) :
    0 < flow f eps t x ∧ flow f eps t x < 1 := by
  have h := flow_bounds f he'.le ht x
  constructor <;> linarith

theorem mean_flow {n : ℕ} (f : Cube n → Bool) (eps t : ℝ) :
    mean (flow f eps t) = initialMean f eps := by
  simp only [mean, flow, Noise.applyNoise_sum, initialMean]

theorem entropy_mean_le {n : ℕ} (v : Cube n → ℝ)
    (hv : ∀ x, 0 ≤ v x ∧ v x ≤ 1) : mean (H ∘ v) ≤ H (mean v) := by
  have hj := Real.strictConcave_binEntropy.concaveOn.le_map_sum
    (t := Finset.univ) (w := fun _ : Cube n => Information.cubeWeight n) (p := v)
    (fun _ _ => by unfold Information.cubeWeight; positivity)
    (Information.weight_sum n) (fun x _ => hv x)
  have h := div_le_div_of_nonneg_right hj GeneralCK.log_two_pos.le
  simpa only [smul_eq_mul, ← Finset.mul_sum, div_eq_mul_inv, ← Finset.sum_mul,
    mul_assoc, mean, H, Function.comp_apply, Information.cubeWeight] using h

theorem delta_range {n : ℕ} (f : Cube n → Bool) {eps t : ℝ}
    (he : 0 < eps) (he' : eps < 1 / 2) (ht : 0 ≤ t) : delta f eps t ∈ Set.Ioc 0 1 := by
  have hv := flow_interior f he he' ht
  have hp : 0 < gamma f eps t := by
    have h := mean_strictMono (fun x => H_pos (hv x).1 (hv x).2)
    simpa only [mean_const, gamma, Function.comp_def] using h
  have hcap := entropy_mean_le (flow f eps t) (fun x => ⟨(hv x).1.le, (hv x).2.le⟩)
  rw [mean_flow] at hcap
  have hm := H_le_one (initialMean f eps)
  change 0 < gamma f eps t + 1 - H (initialMean f eps) ∧
    gamma f eps t + 1 - H (initialMean f eps) ≤ 1
  dsimp only [gamma] at hp ⊢
  constructor <;> linarith

theorem flow_continuous {n : ℕ} (f : Cube n → Bool) (eps : ℝ) (x : Cube n) :
    Continuous (fun t => flow f eps t x) := by
  exact continuous_iff_continuousAt.mpr fun t =>
    (Noise.hasDerivAt_applyNoise (regularized f eps) x t).continuousAt

theorem delta_continuous {n : ℕ} (f : Cube n → Bool) (eps : ℝ) : Continuous (delta f eps) := by
  have hg : Continuous (gamma f eps) := by
    unfold gamma mean
    apply Continuous.const_mul
    apply continuous_finsetSum
    intro x _
    exact H_continuous.comp (flow_continuous f eps x)
  exact (hg.add_const 1).sub continuous_const

theorem hasDerivAt_gamma {n : ℕ} (f : Cube n → Bool) {eps t : ℝ}
    (he : 0 < eps) (he' : eps < 1 / 2) (ht : 0 ≤ t) :
    HasDerivAt (gamma f eps) (energy n (flow f eps t)) t := by
  have hv := flow_interior f he he' ht
  have h := (HasDerivAt.fun_sum (u := Finset.univ) (fun (x : Cube n) _ =>
    (Comparison.hasDerivAt_H (hv x).1 (hv x).2).comp t
      (Noise.hasDerivAt_applyNoise (regularized f eps) x t))).const_mul ((2 : ℝ)^(-(n : ℤ)))
  rw [Energy.energy_eq_generator]
  exact h

theorem hasDerivAt_delta {n : ℕ} (f : Cube n → Bool) {eps t : ℝ}
    (he : 0 < eps) (he' : eps < 1 / 2) (ht : 0 ≤ t) :
    HasDerivAt (delta f eps) (energy n (flow f eps t)) t :=
  ((hasDerivAt_gamma f he he' ht).add_const 1).sub_const _

theorem delta_production (hB : FiniteHybridBellman) {n : ℕ} (f : Cube n → Bool)
    {eps t : ℝ} (he : 0 < eps) (he' : eps < 1 / 2) (ht : 0 ≤ t) :
    eta (delta f eps t) ≤ energy n (flow f eps t) := by
  have h := static_induction hB n (flow f eps t) (flow_interior f he he' ht)
  have hpsi := le_max_right (phi (mean (flow f eps t)) (gamma f eps t))
    (psi (mean (flow f eps t)) (gamma f eps t))
  have hm := mean_flow f eps t
  simpa only [B, psi, hm, delta, gamma] using hpsi.trans h

theorem regularized_entropy {n : ℕ} (f : Cube n → Bool) (eps : ℝ) (x : Cube n) :
    H (regularized f eps x) = H eps := by
  cases h : f x
  · simp [regularized, h]
  · have he : regularized f eps x = 1 - eps := by simp [regularized, h]; ring
    rw [he, H_complement]

theorem gamma_zero {n : ℕ} (f : Cube n → Bool) (eps : ℝ) : gamma f eps 0 = H eps := by
  have h : H ∘ flow f eps 0 = fun _ : Cube n => H eps := by
    funext x
    simp only [Function.comp_apply, flow, Noise.crossover_zero, Noise.applyNoise_zero,
      regularized_entropy]
  unfold gamma
  rw [h, mean_const]

theorem delta_initial {n : ℕ} (f : Cube n → Bool) (eps : ℝ) : H eps ≤ delta f eps 0 := by
  have h := H_le_one (initialMean f eps)
  unfold delta
  rw [gamma_zero]
  linarith

theorem entropy_flow_bound (hB : FiniteHybridBellman) {n : ℕ} (f : Cube n → Bool)
    {eps T : ℝ} (he : 0 < eps) (he' : eps < 1 / 2) (hT : 0 ≤ T) :
    H (Comparison.noiseParameter eps T) ≤ delta f eps T := by
  apply Comparison.entropy_lower_bound he he' hT (delta_continuous f eps).continuousOn
    (delta' := fun t => energy n (flow f eps t))
  · intro t ht
    exact (hasDerivAt_delta f he he' ht.1).hasDerivWithinAt
  · intro t ht
    exact delta_range f he he' ht.1
  · intro t ht
    exact delta_production hB f he he' ht.1
  · exact delta_initial f eps

end GeneralCK.Flow


