-- Prove2me | Definitions.Def_OAIE3v2B206
-- name    : OAIE3v2B206
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:02:48.50998+00:00
-- url     : https://prove2.me/theorems/39a09ade-2044-4747-a8c7-cd22d2e4afe1
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 210 of 311
-- statement:
--   Definitions bundle 210 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B299`, `OAIE3v2B180`, `OAIE3v2B181`, `OAIE3v2B182`, `OAIE3v2B185`, `OAIE3v2B186`, `OAIE3v2B188` of this split.
--
--   Modules: `Estimates/AntisymmetricPairVerticalModel.lean`, `Estimates/DiagonalRowTransfer.lean`, `Estimates/DiagonalWrapComparison.lean`, `Estimates/MixedFrozenMiddleRows.lean`, `Estimates/MixedPairComparison.lean`, `Estimates/MixedPairFrozenEquivalence.lean`, `Estimates/MixedPermutationTensor.lean`, `Estimates/MixedRootCyclicComparison.lean`, `Estimates/MixedRootLosses.lean`, `Estimates/NativeCommonModelQuadruples.lean`, `Estimates/NativeMixedReflectionBridge.lean`, `Estimates/OriginalDiagonalComparison.lean`, `Estimates/OriginalMixedRootEquivalence.lean`, `Estimates/QuadraticAntisymmetricCorrelation.lean`, `Estimates/QuadraticBoundedFamily.lean`, `Estimates/QuadraticCyclicIntegration.lean`, `Estimates/QuadraticPairCorrelator.lean`, `Estimates/QuadraticPairStepDrop.lean`, `Estimates/QuarticRootExchange.lean`, `Estimates/TensorSquarePairComparison.lean`, `Estimates/UnitVerticalCyclicDifference.lean`, `Fourier/MixedOriginalPairFrequency.lean`, `Geometry/MixedCoordinateTransfer.lean`, `Geometry/MixedPairCoordinateTest.lean`, `Linear/AllocatedModularRankMixedUniform.lean`, `Linear/AntisymmetricPairProjections.lean`, `Nilpotent/QuadraticPrimitiveNiltest.lean`, `Polynomial/MixedPairPolynomial.lean`, `Sampling/ForecastPreparedScaleBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B299
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B181
import Definitions.Def_OAIE3v2B182
import Definitions.Def_OAIE3v2B185
import Definitions.Def_OAIE3v2B186
import Definitions.Def_OAIE3v2B188

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoordinateTransfer
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem antisymmetricKernel_norm {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
    (i j : Fin W.outputDim) (x y : ℤ) : ‖W.antisymmetricKernel i j x y‖ ≤ 1 := by
  rw [antisymmetricKernel, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval i _)).trans
    (W.norm_eval j _)

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TensorSquarePairComparison
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem half_dilation_integer_representative {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
    (x : Fin 2 → ℤ) (j : Fin W.outputDim) :
    (W.rationalDilation (1 / 2)).eval j (fun i => x i - ((x i : ZMod 2).val : ℤ)) =
      W.eval j (fun i => x i / 2) := by
  have hx : (fun i => x i - ((x i : ZMod 2).val : ℤ)) = (fun i => 2 * (x i / 2)) := by
    funext i
    rw [ZMod.val_intCast]
    omega
  rw [hx]
  exact W.rationalDilation_eval_rescaled (1 / 2) 2 (by norm_num) j _

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

theorem halfDilationExchangeCorrection_pointwise_error
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖(W.rationalDilation (1 / 2)).antisymmetricKernel a b (x 0) (x 1) -
        W.halfDilationExchangeCorrection G a b x‖ ≤
      ∑ ij : Fin W.outputDim × Fin W.outputDim,
        ‖W.antisymmetricKernel ij.1 ij.2 (x 0 / 2) (x 1 / 2) -
          G ij.1 ij.2 (fun k => x k / 2)‖ := by
  have hinput (z : Fin 2 → ℤ) : correlationInput (z 0) (z 1) = z := by
    funext k
    fin_cases k <;> rfl
  have hswap (z : Fin 2 → ℤ) : correlationInput (z 1) (z 0) = (fun k => z k.rev) := by
    funext k
    fin_cases k <;> rfl
  simp only [antisymmetricKernel, hinput x, hswap x,
    hinput (fun k => x k / 2), hswap (fun k => x k / 2), halfDilationExchangeCorrection]
  exact norm_unit_pair_replacement_error
    (fun i => W.eval i (fun k => x k / 2)) (fun j => W.eval j (fun k => x k.rev / 2))
    (W.unit_eval _) (W.unit_eval _) (fun i => W.norm_eval i _) (fun j => W.norm_eval j _)
    ((W.rationalDilation (1 / 2)).eval a x) ((W.rationalDilation (1 / 2)).eval b (fun k => x k.rev))
    ((W.rationalDilation (1 / 2)).norm_eval a _) ((W.rationalDilation (1 / 2)).norm_eval b _)
    (fun i j => G i j (fun k => x k / 2))

theorem halfDilationExchangeCorrection_mean_error {N : ℕ} [NeZero N]
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) {ε : ℝ}
    (herr : ∀ i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.antisymmetricKernel i j ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a b : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖(W.rationalDilation (1 / 2)).antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
        W.halfDilationExchangeCorrection G a b (fun k => ((x k).val : ℤ))‖) ≤
      4 * (W.outputDim : ℝ) ^ 2 * ε := by
  have hmean := Finset.expect_le_expect (s := Finset.univ)
    (fun (x : Fin 2 → ZMod N) _ => W.halfDilationExchangeCorrection_pointwise_error G a b (fun k => ((x k).val : ℤ)))
  rw [Finset.expect_sum_comm] at hmean
  have he (ij : Fin W.outputDim × Fin W.outputDim) :
      (𝔼 x : Fin 2 → ZMod N,
        ‖W.antisymmetricKernel ij.1 ij.2 (((x 0).val : ℤ) / 2) (((x 1).val : ℤ) / 2) -
          G ij.1 ij.2 (fun k => ((x k).val : ℤ) / 2)‖) ≤ 4 * ε := by
    have h := expect_pair_cyclicHalf_le (fun x : Fin 2 → ZMod N =>
      ‖W.antisymmetricKernel ij.1 ij.2 ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G ij.1 ij.2 (fun k => ((x k).val : ℤ))‖) (fun _ => norm_nonneg _)
    simp only [cyclicHalf_val, Int.natCast_ediv, Nat.cast_ofNat] at h
    exact h.trans (mul_le_mul_of_nonneg_left (herr ij.1 ij.2) (by norm_num))
  apply hmean.trans
  calc
    _ ≤ ∑ _ : Fin W.outputDim × Fin W.outputDim, 4 * ε :=
      Finset.sum_le_sum (fun ij _ => he ij)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul]
      ring

theorem halfDilationExchangeCorrection_norm {N : ℕ} [NeZero N]
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) {B : ℝ}
    (hG : ∀ i j (x : Fin 2 → ZMod N), ‖G i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (a b : Fin W.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.halfDilationExchangeCorrection G a b (fun k => ((x k).val : ℤ))‖ ≤
      (W.outputDim : ℝ) ^ 2 * B := by
  unfold halfDilationExchangeCorrection
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : Fin W.outputDim × Fin W.outputDim, B := by
      apply Finset.sum_le_sum
      intro ij _
      rw [norm_mul]
      have hc : ‖star ((W.rationalDilation (1 / 2)).eval a (fun k => ((x k).val : ℤ)) *
          star (W.eval ij.1 (fun k => ((x k).val : ℤ) / 2))) *
          ((W.rationalDilation (1 / 2)).eval b (fun k => ((x k.rev).val : ℤ)) *
          star (W.eval ij.2 (fun k => ((x k.rev).val : ℤ) / 2)))‖ ≤ 1 := by
        rw [norm_mul, norm_star]
        refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans ?_
        · rw [norm_mul, norm_star]
          exact (mul_le_of_le_one_left (norm_nonneg _)
            ((W.rationalDilation (1 / 2)).norm_eval a _)).trans (W.norm_eval _ _)
        · rw [norm_mul, norm_star]
          exact (mul_le_of_le_one_left (norm_nonneg _)
            ((W.rationalDilation (1 / 2)).norm_eval b _)).trans (W.norm_eval _ _)
      apply (mul_le_of_le_one_left (norm_nonneg _) hc).trans
      have h := hG ij.1 ij.2 (fun k => cyclicHalf (x k))
      simpa only [cyclicHalf_val, Int.natCast_ediv, Nat.cast_ofNat] using h
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul, pow_two]

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

theorem tensorSquare_antisymmetricKernel (a b : Fin (W.outputDim ^ 2)) (h n : ℤ) :
    (W.tensorPower 2).antisymmetricKernel a b h n =
      W.antisymmetricKernel ((tensorIndexEquiv W.outputDim 2).symm a 0)
        ((tensorIndexEquiv W.outputDim 2).symm b 0) h n *
      W.antisymmetricKernel ((tensorIndexEquiv W.outputDim 2).symm a 1)
        ((tensorIndexEquiv W.outputDim 2).symm b 1) h n := by
  simp only [antisymmetricKernel, tensorPower_eval, Fin.prod_univ_two, star_mul]
  ring

theorem tensorSquareExchangeCorrection_mean_error {N : ℕ} [NeZero N]
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) {B ε : ℝ}
    (hB : 0 ≤ B)
    (hcap : ∀ i j (x : Fin 2 → ZMod N), ‖G i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (herr : ∀ i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.antisymmetricKernel i j ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a b : Fin (W.outputDim ^ 2)) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖(W.tensorPower 2).antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
        W.tensorSquareExchangeCorrection G a b (fun k => ((x k).val : ℤ))‖) ≤ (1 + B) * ε := by
  let i := (tensorIndexEquiv W.outputDim 2).symm a
  let j := (tensorIndexEquiv W.outputDim 2).symm b
  let K (r : Fin 2) (x : Fin 2 → ZMod N) :=
    W.antisymmetricKernel (i r) (j r) ((x 0).val : ℤ) ((x 1).val : ℤ)
  let F (r : Fin 2) (x : Fin 2 → ZMod N) := G (i r) (j r) (fun k => ((x k).val : ℤ))
  have hpoint (x : Fin 2 → ZMod N) :
      ‖K 0 x * K 1 x - F 0 x * F 1 x‖ ≤
        ‖K 1 x - F 1 x‖ + B * ‖K 0 x - F 0 x‖ := by
    have heq : K 0 x * K 1 x - F 0 x * F 1 x =
        K 0 x * (K 1 x - F 1 x) + (K 0 x - F 0 x) * F 1 x := by ring
    rw [heq]
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_mul]
    apply add_le_add
    · exact mul_le_of_le_one_left (norm_nonneg _) (W.antisymmetricKernel_norm _ _ _ _)
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hcap _ _ x) (norm_nonneg (K 0 x - F 0 x))
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun x _ => hpoint x)
  rw [Finset.expect_add_distrib, ← Finset.mul_expect] at hm
  have h0 : (𝔼 x, ‖K 0 x - F 0 x‖) ≤ ε := herr _ _
  have h1 : (𝔼 x, ‖K 1 x - F 1 x‖) ≤ ε := herr _ _
  have hbnd := hm.trans (add_le_add h1 (mul_le_mul_of_nonneg_left h0 hB))
  have hfinal : (𝔼 x, ‖K 0 x * K 1 x - F 0 x * F 1 x‖) ≤ (1 + B) * ε :=
    hbnd.trans_eq (by ring)
  simpa only [K, F, i, j, tensorSquare_antisymmetricKernel, tensorSquareExchangeCorrection] using hfinal

theorem exists_tensorSquareExchangeCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p), 0 ≤ q →
      ∀ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (G i j))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((q + C) ^ C)
        (W.tensorSquareExchangeCorrection G a b)) := by
  obtain ⟨C, hC, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG a b
  exact hmul hq (Classical.choice (hG _ _)) (Classical.choice (hG _ _))

theorem explicit_half_root_exchange_mean_error {N : ℕ} [NeZero N]
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) {ε : ℝ}
    (hcap : ∀ i j (x : Fin 2 → ZMod N), ‖G i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.antisymmetricKernel i j ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a b : Fin (W.outputDim ^ 2)) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖((W.rationalDilation (1 / 2)).tensorPower 2).antisymmetricKernel a b
          ((x 0).val : ℤ) ((x 1).val : ℤ) -
        (W.rationalDilation (1 / 2)).tensorSquareExchangeCorrection
          (W.halfDilationExchangeCorrection G) a b (fun k => ((x k).val : ℤ))‖) ≤
      (1 + (W.outputDim : ℝ) ^ 2) * (4 * (W.outputDim : ℝ) ^ 2 * ε) := by
  apply tensorSquareExchangeCorrection_mean_error (W.rationalDilation (1 / 2))
    (W.halfDilationExchangeCorrection G) (by positivity)
  · intro i j x
    simpa only [mul_one] using W.halfDilationExchangeCorrection_norm G hcap i j x
  · exact W.halfDilationExchangeCorrection_mean_error G herr

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DiagonalWrapComparison
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

theorem quadraticDiagonalDerivative_norm (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.quadraticDiagonalDerivative a x‖ ≤ 1 := by
  simp only [quadraticDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

theorem wrappedDiagonalDerivative_norm (N : ℕ) (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.wrappedDiagonalDerivative N a x‖ ≤ 1 := by
  simp only [wrappedDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem diagonalWrapCoefficient_norm (N : ℕ) (j k : Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.diagonalWrapCoefficient N j k x‖ ≤ 1 := by
  simp only [diagonalWrapCoefficient, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem wrappedDiagonalDerivative_resolution (N : ℕ)
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.wrappedDiagonalDerivative N a x =
      ∑ k, W.diagonalWrapCoefficient N a.2 k x * W.quadraticDiagonalDerivative (a.1, k) x := by
  have h := complex_unit_vector_resolution
    (fun k => W.eval k (fun _ => x 1 + x 0)) (W.unit_eval _)
    (star (W.eval a.2 (fun _ => x 1 + x 0 - N)))
  calc
    _ = W.eval a.1 (fun _ => x 1) *
        ∑ k, (star (W.eval a.2 (fun _ => x 1 + x 0 - N)) *
          star (W.eval k (fun _ => x 1 + x 0))) * W.eval k (fun _ => x 1 + x 0) := by
      rw [← h]
      rfl
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [diagonalWrapCoefficient, quadraticDiagonalDerivative]
      ring

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalCyclicDifference
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

theorem diagonalSquareCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.quadraticDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
        W.diagonalSquareCorrection G a b (fun z => ((x z).val : ℤ))‖) ≤ W.outputDim * ε := by
  have hpoint (x : Fin 2 → ZMod N) :
      ‖W.quadraticDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
        W.diagonalSquareCorrection G a b (fun z => ((x z).val : ℤ))‖ ≤
      ∑ j, ‖W.antisymmetricKernel b.1 j ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G b.1 j (fun z => ((x z).val : ℤ))‖ := by
    let z := fun i => ((x i).val : ℤ)
    let c := (W.quadraticDiagonalDerivative a z * W.eval b.2.1 (correlationInput (z 0) (z 1))) *
      W.eval b.2.2 (fun _ => z 0)
    have hc : ‖c‖ ≤ 1 := by
      simp only [c, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        ((mul_le_of_le_one_left (norm_nonneg _) (W.quadraticDiagonalDerivative_norm a z)).trans
          (W.norm_eval _ _))).trans (W.norm_eval _ _)
    have htarget : W.quadraticDiagonalDerivative a z * star (W.quadraticSquareTriple b z) =
        c * W.eval b.1 (correlationInput (z 0) (z 1)) := by
      simp only [quadraticSquareTriple, star_star, c]
      ring
    have hsum : W.diagonalSquareCorrection G a b z =
        c * ∑ j, W.eval j (correlationInput (z 1) (z 0)) * star (G b.1 j z) := by
      unfold diagonalSquareCorrection
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [quadraticMixedTriple, star_star, c]
      ring
    change ‖W.quadraticDiagonalDerivative a z * star (W.quadraticSquareTriple b z) -
      W.diagonalSquareCorrection G a b z‖ ≤ _
    rw [htarget, hsum, ← mul_sub, norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) hc).trans
    exact norm_unit_vector_exchange_error
      (fun j => W.eval j (correlationInput (z 1) (z 0))) (W.unit_eval _) (fun j => W.norm_eval j _)
      (W.eval b.1 (correlationInput (z 0) (z 1))) (fun j => G b.1 j z)
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N,
        ∑ j, ‖W.antisymmetricKernel b.1 j ((x 0).val : ℤ) ((x 1).val : ℤ) -
          G b.1 j (fun z => ((x z).val : ℤ))‖ := Finset.expect_le_expect (fun x _ => hpoint x)
    _ = ∑ j, 𝔼 x : Fin 2 → ZMod N,
        ‖W.antisymmetricKernel b.1 j ((x 0).val : ℤ) ((x 1).val : ℤ) -
          G b.1 j (fun z => ((x z).val : ℤ))‖ := Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _j : Fin W.outputDim, ε := Finset.sum_le_sum (fun j _ => herr b.1 j)
    _ = _ := by simp

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

theorem quadraticSquareTriple_norm (b : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.quadraticSquareTriple b x‖ ≤ 1 := by
  simp only [quadraticSquareTriple, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans
      (W.norm_eval _ _))).trans (W.norm_eval _ _)

theorem wrappedDiagonalCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.quadraticDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
        F a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.wrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) *
          star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
        W.wrappedDiagonalCorrection N F a b (fun z => ((x z).val : ℤ))‖) ≤ W.outputDim * ε := by
  have hpoint (x : Fin 2 → ℤ) :
      ‖W.wrappedDiagonalDerivative N a x * star (W.quadraticSquareTriple b x) -
        W.wrappedDiagonalCorrection N F a b x‖ ≤
      ∑ k, ‖W.quadraticDiagonalDerivative (a.1, k) x * star (W.quadraticSquareTriple b x) -
        F (a.1, k) b x‖ := by
    have heq : W.wrappedDiagonalDerivative N a x * star (W.quadraticSquareTriple b x) -
        W.wrappedDiagonalCorrection N F a b x =
        ∑ k, W.diagonalWrapCoefficient N a.2 k x *
          (W.quadraticDiagonalDerivative (a.1, k) x * star (W.quadraticSquareTriple b x) -
            F (a.1, k) b x) := by
      rw [W.wrappedDiagonalDerivative_resolution, Finset.sum_mul]
      simp only [wrappedDiagonalCorrection, mul_sub, Finset.sum_sub_distrib, mul_assoc]
    rw [heq]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k _
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (W.diagonalWrapCoefficient_norm N a.2 k x)
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N,
        ∑ k, ‖W.quadraticDiagonalDerivative (a.1, k) (fun z => ((x z).val : ℤ)) *
            star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
          F (a.1, k) b (fun z => ((x z).val : ℤ))‖ :=
      Finset.expect_le_expect (fun x _ => hpoint _)
    _ = ∑ k, 𝔼 x : Fin 2 → ZMod N,
        ‖W.quadraticDiagonalDerivative (a.1, k) (fun z => ((x z).val : ℤ)) *
            star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
          F (a.1, k) b (fun z => ((x z).val : ℤ))‖ := Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _k : Fin W.outputDim, ε := Finset.sum_le_sum (fun k _ => herr (a.1, k) b)
    _ = _ := by simp

theorem cyclicDiagonalCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (δ : ℝ≥0) (hδ : 0 < δ)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.quadraticDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
        F a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.cyclicDiagonalDerivative a x * star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
        W.cyclicDiagonalCorrection N δ F a b (fun z => ((x z).val : ℤ))‖) ≤
      (W.outputDim + 1) * ε + 12 * (δ : ℝ) + 2 / N := by
  have hpoint (x : Fin 2 → ZMod N) := norm_smoothed_branch_error
    (cyclicCarry (x 0) (x 1)) (smoothCyclicCarry N δ (fun z => ((x z).val : ℤ)))
    (circleCarryCutoff_range δ _)
    (W.quadraticDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
      star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))))
    (W.wrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) *
      star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))))
    (F a b (fun z => ((x z).val : ℤ)))
    (W.wrappedDiagonalCorrection N F a b (fun z => ((x z).val : ℤ)))
    (by
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (W.quadraticDiagonalDerivative_norm a _)).trans (W.quadraticSquareTriple_norm b _))
    (by
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (W.wrappedDiagonalDerivative_norm N a _)).trans (W.quadraticSquareTriple_norm b _))
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun x _ => hpoint x)
  simp only [Complex.ofReal_sub, Complex.ofReal_one, ← mul_assoc, ← add_mul,
    ← W.cyclicDiagonalDerivative_branches] at hm
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect] at hm
  have hi := herr a b
  have hw := W.wrappedDiagonalCorrection_mean_error F herr a b
  have hc := smoothCyclicCarry_mean_error (N := N) δ hδ
  dsimp only [cyclicDiagonalCorrection]
  exact hm.trans ((add_le_add (add_le_add hi hw)
    (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2))).trans_eq (by ring))

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

theorem cyclicExchangeCorrection_mean_error {p ε : ℝ} {N : ℕ} [NeZero N]
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (δ : ℝ≥0) (hδ : 0 < δ)
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G a b (fun k => ((x k).val : ℤ))‖) ≤ ε) (a b) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.cyclicDiagonalDerivative a x * star (W.quadraticSquareTriple b (fun k => ((x k).val : ℤ))) -
        W.cyclicDiagonalCorrection N δ (W.diagonalSquareCorrection G) a b
          (fun k => ((x k).val : ℤ))‖) ≤
      (W.outputDim + 1) * (W.outputDim * ε) + 12 * (δ : ℝ) + 2 / N :=
  W.cyclicDiagonalCorrection_mean_error δ hδ (W.diagonalSquareCorrection G)
    (W.diagonalSquareCorrection_mean_error G herr) a b

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def rootCyclicCorrection (N : ℕ) (δ : ℝ≥0)
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) :=
  W.quadraticRoot.cyclicDiagonalCorrection N δ
    (W.quadraticRoot.diagonalSquareCorrection (W.rootExchangeCorrection G))

theorem rootCyclicCorrection_mean_error {N : ℕ} [NeZero N] (δ : ℝ≥0) (hδ : 0 < δ)
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) {ε : ℝ}
    (hcap : ∀ i j (x : Fin 2 → ZMod N), ‖G i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.antisymmetricKernel i j ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G i j (fun k => ((x k).val : ℤ))‖) ≤ ε) (a b) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.quadraticRoot.cyclicDiagonalDerivative a x *
          star (W.quadraticRoot.quadraticSquareTriple b (fun k => ((x k).val : ℤ))) -
        W.rootCyclicCorrection N δ G a b (fun k => ((x k).val : ℤ))‖) ≤
      (W.quadraticRoot.outputDim + 1) *
        (W.quadraticRoot.outputDim * ((1 + (W.outputDim : ℝ) ^ 2) * (4 * (W.outputDim : ℝ) ^ 2 * ε))) +
        12 * (δ : ℝ) + 2 / N := by
  exact W.quadraticRoot.cyclicExchangeCorrection_mean_error δ hδ (W.rootExchangeCorrection G)
    (W.explicit_half_root_exchange_mean_error G hcap herr) a b

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCommonModelQuadruples
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra
  NativeCyclicModel.topology NativeCyclicModel.topologicalAdd
  NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

def NativeModelDetector (degree N : ℕ) [NeZero N] (p : ℝ)
    (X : Seminorm ℂ (ZMod N → ℂ)) (K M beta tau : ℝ) : Prop :=
  ∀ psi : ZMod N → ℂ, (∀ x, ‖psi x‖ ≤ K / tau) → tau / M ^ 2 ≤ X psi →
    ∃ f ∈ nativeCyclicFunctions degree N p, beta ≤ ‖𝔼 x, psi x * star (f x)‖

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticBoundedFamily
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {ι σ : Type*} [Fintype ι] [Fintype σ] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ} {bound : σ → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (M : ∀ i, (D i).MultidegreeStructure bound)

noncomputable def productMultidegreeLayerBasis (a : ∀ j, Fin (bound j + 1)) :
    Basis (Σ i, Fin (finrank ℚ ((M i).filtration.layer (fun j => (a j).val)))) ℚ
      ((MultidegreeLieFiltration.pi (fun i => (M i).filtration)).layer (fun j => (a j).val)) :=
  (Pi.basis (fun i => (M i).basis a)).map
    (MultidegreeLieFiltration.piLayerEquiv (fun i => (M i).filtration) (fun j => (a j).val))

noncomputable def productMultidegreeLayerFinBasis (a : ∀ j, Fin (bound j + 1)) :
    Basis (Fin (finrank ℚ
      ((MultidegreeLieFiltration.pi (fun i => (M i).filtration)).layer (fun j => (a j).val)))) ℚ
      ((MultidegreeLieFiltration.pi (fun i => (M i).filtration)).layer (fun j => (a j).val)) :=
  (productMultidegreeLayerBasis D M a).reindex
    (Fintype.equivFinOfCardEq (finrank_eq_card_basis (productMultidegreeLayerBasis D M a)).symm)

noncomputable def piMultidegree : (pi D).MultidegreeStructure bound where
  filtration := MultidegreeLieFiltration.pi (fun i => (M i).filtration)
  ordinary := congrArg NilpotentLieFiltration.pi (funext (fun i => (M i).ordinary))
  basis := productMultidegreeLayerFinBasis D M

theorem productMultidegreeLayerBasis_logHeight {p : ℝ} (hp : 0 ≤ p)
    (hM : ∀ i, (M i).ComplexityLE p) (a : ∀ j, Fin (bound j + 1))
    (j : Σ i, Fin (finrank ℚ ((M i).filtration.layer (fun k => (a k).val))))
    (k : Σ i, Fin (d i)) :
    rationalLogHeight ((Pi.basis (fun i => (D i).basis)).repr
      ((productMultidegreeLayerBasis D M a j).val) k) ≤ p := by
  classical
  rcases j with ⟨j, m⟩
  rcases k with ⟨k, n⟩
  simp only [productMultidegreeLayerBasis, Basis.map_apply, Pi.basis_repr]
  change rationalLogHeight ((D k).basis.repr
    (((Pi.basis (fun i => (M i).basis a)) ⟨j, m⟩ k).val) n) ≤ p
  rw [Pi.basis_apply]
  by_cases hjk : j = k
  · subst k
    rw [Pi.single_eq_same]
    exact (hM j).2 a m n
  · rw [Pi.single_eq_of_ne (Ne.symm hjk)]
    simpa [rationalLogHeight] using hp

theorem piMultidegree_complexity {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hM : ∀ i, (M i).ComplexityLE p) :
    (piMultidegree D M).ComplexityLE ((p + 2) ^ 2) := by
  refine ⟨pi_geometry D hp hι (fun i => (hM i).1), ?_⟩
  intro a j k
  change Fin (finrank ℚ
    ((MultidegreeLieFiltration.pi (fun i => (M i).filtration)).layer (fun i => (a i).val))) at j
  change rationalLogHeight ((productFinBasis D).repr
    ((productMultidegreeLayerFinBasis D M a j).val) k) ≤ (p + 2) ^ 2
  rw [productFinBasis, Basis.repr_reindex_apply, productMultidegreeLayerFinBasis, Basis.reindex_apply]
  exact (productMultidegreeLayerBasis_logHeight D M hp hM a _ _).trans (by nlinarith [sq_nonneg p])

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators NNReal

theorem exists_bounded_multidegree_product_family
    {ι σ : Type*} [Fintype ι] [Fintype σ] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ} {bound : σ → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (M : ∀ i, (D i).MultidegreeStructure bound)
    (g : ∀ i, (M i).filtration.realification.PolynomialOrbit)
    {I : ι → Type*} (V : ∀ i, I i → (D i).Space → ℂ) {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hM : ∀ i, (M i).ComplexityLE p)
    (hV : ∀ i j x, ‖V i j x‖ ≤ 1)
    (hLip : ∀ i, letI := (D i).metricSpace;
      ∀ j, LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ (V i j)) :
    (piMultidegree D M).ComplexityLE (productNiltestBudget (p + 4)) ∧
    ∃ T : (∀ i, I i) → (pi D).Niltest (fun _ : σ => 1),
      (∀ j, (T j).orbit = (piMultidegree D M).orbitToOrdinary
        (MultidegreeLieFiltration.piRealOrbit (fun i => (M i).filtration) g)) ∧
      (∀ j, (T j).normBound = 1) ∧
      (∀ j, (T j).ComplexityLE (productNiltestBudget (p + 4))) ∧
      (∀ j x, (T j).observable x = ∏ i, V i (j i) (productProjection D i x)) ∧
      ∀ j x, (T j).eval x =
        ∏ i, V i (j i) (QuotientGroup.mk ((M i).filtration.realification.polynomialOrbitEval x (g i))) := by
  classical
  have hpq : p ≤ p + 4 := by linarith
  have hq : 0 ≤ p + 4 := by linarith
  let K (i : ι) (j : I i) : (D i).Niltest (fun _ : σ => 1) := {
    orbit := (M i).orbitToOrdinary (g i)
    observable := V i j
    normBound := 1
    lipBound := ⟨Real.exp p, Real.exp_nonneg _⟩
    norm_le := hV i j
    lipschitz := hLip i j
  }
  have hK (i : ι) (j : I i) : (K i j).ComplexityLE (p + 4) := by
    refine ⟨(hM i).1.mono (D i) hpq, ?_⟩
    change Real.log (2 + 1 + Real.exp p) ≤ p + 4
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    calc
      _ ≤ 4 * Real.exp p := by linarith [Real.one_le_exp hp]
      _ ≤ Real.exp 4 * Real.exp p := mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  let o := (piMultidegree D M).orbitToOrdinary
    (MultidegreeLieFiltration.piRealOrbit (fun i => (M i).filtration) g)
  let T (j : ∀ i, I i) := (unitBoundedPiNiltest D (fun i => K i (j i)) hq (hι.trans hpq)
    (fun i => hK i (j i)) (fun _ => le_rfl)).withOrbit o
  refine ⟨(piMultidegree_complexity D M hq (hι.trans hpq)
      (fun i => (hM i).mono (M i) hpq)).mono _ (productNiltestBudget_geometry hq),
    T, (fun _ => rfl), (fun _ => rfl),
    (fun j => unitBoundedPiNiltest_complexity D (fun i => K i (j i)) hq (hι.trans hpq)
      (fun i => hK i (j i)) (fun _ => le_rfl)),
    (fun _ _ => rfl), ?_⟩
  intro j x
  change (∏ i, V i (j i) (productProjection D i
    (QuotientGroup.mk ((pi D).filtration.realification.polynomialOrbitEval (fun _ : σ => 1) x o)))) = _
  apply Finset.prod_congr rfl
  intro i _
  rw [productProjection_mk]
  apply congrArg (fun z : (D i).RealGroup => V i (j i) (QuotientGroup.mk z))
  exact (congrArg (productProjectionHom D i)
    ((piMultidegree D M).orbitToOrdinary_eval
      (MultidegreeLieFiltration.piRealOrbit (fun i => (M i).filtration) g) x)).trans
        (MultidegreeLieFiltration.piRealOrbit_eval (fun i => (M i).filtration) g x i)

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators NNReal

def HasBoundedBinaryMultidegreeFamily
    {σ I J : Type*} {L₀ L₁ : Type u} [Fintype σ]
    [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing L₁] [LieAlgebra ℚ L₁]
    [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
    [TopologicalSpace (ℝ ⊗[ℚ] L₁)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁)] [T2Space (ℝ ⊗[ℚ] L₁)]
    {s d₀ d₁ : ℕ} {bound : σ → ℕ}
    (D₀ : RationalFilteredNilmanifold L₀ s d₀) (D₁ : RationalFilteredNilmanifold L₁ s d₁)
    (M₀ : D₀.MultidegreeStructure bound) (M₁ : D₁.MultidegreeStructure bound)
    (g₀ : M₀.filtration.realification.PolynomialOrbit) (g₁ : M₁.filtration.realification.PolynomialOrbit)
    (V₀ : I → D₀.Space → ℂ) (V₁ : J → D₁.Space → ℂ) (p : ℝ) : Prop :=
    let P := optionProduct D₀ (fun _ : Unit => D₁)
    ∃ M : P.MultidegreeStructure bound, M.ComplexityLE (productNiltestBudget (p + 4)) ∧
      ∃ g : M.filtration.realification.PolynomialOrbit,
        (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : Option Unit, optionLieSpace L₀ (fun _ : Unit => L₁) i))
         letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i : Option Unit, optionLieSpace L₀ (fun _ : Unit => L₁) i)) :=
            IsModuleTopology.topologicalAddGroup ℝ _
         letI := realification_moduleTopology_t2 P.basis
         ∃ T : I × J → P.Niltest (fun _ : σ => 1),
           (∀ ij, (T ij).orbit = M.orbitToOrdinary g) ∧
           (∀ ij, (T ij).normBound = 1) ∧
           (∀ ij, (T ij).ComplexityLE (productNiltestBudget (p + 4))) ∧
           ∀ ij x, (T ij).eval x =
             V₀ ij.1 (QuotientGroup.mk (M₀.filtration.realification.polynomialOrbitEval x g₀)) *
             V₁ ij.2 (QuotientGroup.mk (M₁.filtration.realification.polynomialOrbitEval x g₁)))

theorem exists_bounded_binary_multidegree_family
    {σ I J : Type*} {L₀ L₁ : Type u} [Fintype σ]
    [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing L₁] [LieAlgebra ℚ L₁]
    [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
    [TopologicalSpace (ℝ ⊗[ℚ] L₁)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁)] [T2Space (ℝ ⊗[ℚ] L₁)]
    {s d₀ d₁ : ℕ} {bound : σ → ℕ}
    (D₀ : RationalFilteredNilmanifold L₀ s d₀) (D₁ : RationalFilteredNilmanifold L₁ s d₁)
    (M₀ : D₀.MultidegreeStructure bound) (M₁ : D₁.MultidegreeStructure bound)
    (g₀ : M₀.filtration.realification.PolynomialOrbit) (g₁ : M₁.filtration.realification.PolynomialOrbit)
    (V₀ : I → D₀.Space → ℂ) (V₁ : J → D₁.Space → ℂ) {p : ℝ}
    (hp : 2 ≤ p) (hM₀ : M₀.ComplexityLE p) (hM₁ : M₁.ComplexityLE p)
    (hV₀ : ∀ i x, ‖V₀ i x‖ ≤ 1) (hV₁ : ∀ j x, ‖V₁ j x‖ ≤ 1)
    (hLip₀ : letI := D₀.metricSpace; ∀ i, LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ (V₀ i))
    (hLip₁ : letI := D₁.metricSpace; ∀ j, LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ (V₁ j)) :
    HasBoundedBinaryMultidegreeFamily D₀ D₁ M₀ M₁ g₀ g₁ V₀ V₁ p := by
  unfold HasBoundedBinaryMultidegreeFamily
  dsimp only
  let P := optionProduct D₀ (fun _ : Unit => D₁)
  let D := optionFactors D₀ (fun _ : Unit => D₁)
  let M : ∀ i : Option Unit, (D i).MultidegreeStructure bound
    | none => M₀
    | some _ => M₁
  let g : ∀ i : Option Unit, (M i).filtration.realification.PolynomialOrbit
    | none => g₀
    | some _ => g₁
  let : ∀ i : Option Unit, TopologicalSpace (ℝ ⊗[ℚ] optionLieSpace L₀ (fun _ : Unit => L₁) i) :=
    fun i => match i with
      | none => inferInstanceAs (TopologicalSpace (ℝ ⊗[ℚ] L₀))
      | some _ => inferInstanceAs (TopologicalSpace (ℝ ⊗[ℚ] L₁))
  let : ∀ i : Option Unit, IsTopologicalAddGroup (ℝ ⊗[ℚ] optionLieSpace L₀ (fun _ : Unit => L₁) i) :=
    fun i => match i with
      | none => inferInstanceAs (IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀))
      | some _ => inferInstanceAs (IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁))
  let : ∀ i : Option Unit, ContinuousSMul ℝ (ℝ ⊗[ℚ] optionLieSpace L₀ (fun _ : Unit => L₁) i) :=
    fun i => match i with
      | none => inferInstanceAs (ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀))
      | some _ => inferInstanceAs (ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁))
  let : ∀ i : Option Unit, T2Space (ℝ ⊗[ℚ] optionLieSpace L₀ (fun _ : Unit => L₁) i) :=
    fun i => match i with
      | none => inferInstanceAs (T2Space (ℝ ⊗[ℚ] L₀))
      | some _ => inferInstanceAs (T2Space (ℝ ⊗[ℚ] L₁))
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : Option Unit, optionLieSpace L₀ (fun _ : Unit => L₁) i))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i : Option Unit, optionLieSpace L₀ (fun _ : Unit => L₁) i)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 P.basis
  let V : ∀ i : Option Unit, (I × J) → (D i).Space → ℂ
    | none => fun ij => V₀ ij.1
    | some _ => fun ij => V₁ ij.2
  have hM : ∀ i, (M i).ComplexityLE p := fun i => by
    match i with
    | none => exact hM₀
    | some _ => exact hM₁
  have hV : ∀ i ij x, ‖V i ij x‖ ≤ 1 := fun i => by
    match i with
    | none => exact fun ij x => hV₀ ij.1 x
    | some _ => exact fun ij x => hV₁ ij.2 x
  have hLip : ∀ i, letI := (D i).metricSpace;
      ∀ ij, LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ (V i ij) := fun i => by
    match i with
    | none => exact fun ij => hLip₀ ij.1
    | some _ => exact fun ij => hLip₁ ij.2
  obtain ⟨hprod, T, hTo, hTn, hTc, _, hTe⟩ :=
    exists_bounded_multidegree_product_family D M g V (by linarith) (by simpa using hp) hM hV hLip
  refine ⟨piMultidegree D M, hprod, MultidegreeLieFiltration.piRealOrbit (fun i => (M i).filtration) g,
    (fun ij => T (fun _ => ij)), (fun ij => hTo (fun _ => ij)),
    (fun ij => hTn (fun _ => ij)), (fun ij => hTc (fun _ => ij)), ?_⟩
  intro ij x
  have he := hTe (fun _ => ij) x
  rw [Fintype.prod_option, Fintype.prod_unique] at he
  exact he

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeBoundedMultidegreeFamily.lie NativeBoundedMultidegreeFamily.algebra
  NativeBoundedMultidegreeFamily.topology NativeBoundedMultidegreeFamily.topologicalAdd
  NativeBoundedMultidegreeFamily.continuousSMul NativeBoundedMultidegreeFamily.hausdorff

namespace NativeMultidegreeNilcharacter

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

theorem exists_product_with_bounded_family
    {σ J : Type*} [Fintype σ] {bound : σ → ℕ} {p B : ℝ}
    (W : NativeMultidegreeNilcharacter bound p)
    {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d : ℕ} (D : RationalFilteredNilmanifold L s d)
    (M : D.MultidegreeStructure bound) (hstep : s = ∑ i, bound i)
    (g : M.filtration.realification.PolynomialOrbit)
    (G : J → D.Space → ℂ) (hB : 0 ≤ B) (hM : M.ComplexityLE B)
    (hG : ∀ j x, ‖G j x‖ ≤ 2)
    (hLip : letI := D.metricSpace; ∀ j, LipschitzWith ⟨Real.exp B, Real.exp_nonneg _⟩ (G j)) :
    ∃ F : NativeBoundedMultidegreeFamily bound (Fin W.outputDim × J)
        (productNiltestBudget (p + B + 2 + 4)),
      ∀ ij x, F.eval ij x = W.eval ij.1 x *
        G ij.2 (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)) / 2 := by
  subst hstep
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hpP : p ≤ p + B + 2 := by linarith
  have hBP : B ≤ p + B + 2 := by linarith
  let G' (j : J) (x : D.Space) := G j x / 2
  have hGn (j : J) (x : D.Space) : ‖G' j x‖ ≤ 1 := by
    dsimp only [G']
    rw [norm_div]
    norm_num only [Complex.norm_ofNat]
    linarith [hG j x]
  have hGL : letI := D.metricSpace;
      ∀ j, LipschitzWith ⟨Real.exp (p + B + 2), Real.exp_nonneg _⟩ (G' j) := by
    let := D.metricSpace
    intro j
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (G j x / 2) (G j y / 2) ≤ _
    rw [dist_eq_norm, ← sub_div, norm_div]
    norm_num only [Complex.norm_ofNat]
    have h := (hLip j).dist_le_mul x y
    rw [dist_eq_norm] at h
    exact (div_le_self (norm_nonneg _) (by norm_num : (1 : ℝ) ≤ 2)).trans
      (h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hBP) dist_nonneg))
  have hWL : letI := W.model.metricSpace;
      ∀ i, LipschitzWith ⟨Real.exp (p + B + 2), Real.exp_nonneg _⟩ (W.vertical.observable i) := by
    let := W.model.metricSpace
    intro i
    exact (W.vertical.lipschitz i).weaken
      (show W.vertical.lipBound ≤ ⟨Real.exp (p + B + 2), Real.exp_nonneg _⟩ from
        W.vertical.lip_bound.trans (Real.exp_le_exp.mpr hpP))
  obtain ⟨MP, hMP, gP, htests⟩ := exists_bounded_binary_multidegree_family
    W.model D W.multi M W.orbit g W.vertical.observable G' (by linarith : 2 ≤ p + B + 2)
    (W.complexity.mono W.multi hpP) (hM.mono M hBP) W.vertical.norm hGn hWL hGL
  let P := optionProduct W.model (fun _ : Unit => D)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : Option Unit, optionLieSpace W.L (fun _ : Unit => L) i))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i : Option Unit, optionLieSpace W.L (fun _ : Unit => L) i)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 P.basis
  obtain ⟨T, hTo, hTn, hTc, hTe⟩ := htests
  let F : NativeBoundedMultidegreeFamily bound (Fin W.outputDim × J)
      (productNiltestBudget (p + B + 2 + 4)) := {
    L := ∀ i : Option Unit, optionLieSpace W.L (fun _ : Unit => L) i
    dim := Fintype.card (Σ i : Option Unit, Fin (optionDimension W.dim (fun _ : Unit => d) i))
    model := P
    multi := MP
    complexity := hMP
    orbit := gP
    test := T
    test_orbit := hTo
    test_norm := hTn
    test_complexity := hTc
  }
  refine ⟨F, ?_⟩
  intro ij x
  change (T ij).eval x = _
  rw [hTe]
  change W.eval ij.1 x * (G ij.2 _ / 2) = _
  rw [mul_div_assoc]

end NativeMultidegreeNilcharacter

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticAntisymmetricCorrelation
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem NativeMultidegreeNilcharacter.reflected_pair_target_unit {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (z a b : ℤ) :
    (∑ k : (Fin W.outputDim × Fin W.outputDim) × (Fin W.outputDim × Fin W.outputDim),
      ‖W.eval k.1.1 (correlationInput a (z - a)) *
        star (W.eval k.2.1 (correlationInput b (z - b))) *
        star (W.eval k.1.2 (correlationInput a b)) *
        W.eval k.2.2 (correlationInput b a)‖ ^ 2) = 1 := by
  calc
    _ = ∑ k : (Fin W.outputDim × Fin W.outputDim) × (Fin W.outputDim × Fin W.outputDim),
        ‖(W.eval k.1.1 (correlationInput a (z - a)) *
          star (W.eval k.1.2 (correlationInput a b))) *
          star (W.eval k.2.1 (correlationInput b (z - b)) *
            star (W.eval k.2.2 (correlationInput b a)))‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _
      congr 2
      simp only [star_mul, star_star]
      ring
    _ = 1 := by
      simp only [norm_mul, norm_star, mul_pow, Fintype.sum_prod_type,
        ← Finset.mul_sum, W.unit_eval, mul_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticPairCorrelator
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

theorem pairComponent_eval (out : Fin W.outputDim) (a b : Fin 2) (n : Fin 2 → ℤ) :
    (W.pairComponent out a b).eval n = W.eval out (correlationInput (n a) (n b)) := by
  rw [pairComponent, Niltest.eval_linearPullbackHom, component_eval]
  apply congrArg (W.eval out)
  funext k
  fin_cases k <;> rfl

theorem pairComponent_vertical (out : Fin W.outputDim) (a b : Fin 2)
    (z : W.model.RealGroup)
    (hz : z ∈ W.model.filtration.realification.subgroup (∑ k, mixedCorrelationDegree 1 k))
    (x : W.model.Space) :
    (W.pairComponent out a b).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional W.vertical.frequency z.coord : ℝ) : CircleFourier.Circle) *
          (W.pairComponent out a b).observable x :=
  W.vertical.vertical out z (by rwa [W.multi.realSubgroup_top]) x

end NativeMultidegreeNilcharacter

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticPairStepDrop
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

theorem pairFrozenVector_unit (k : Fin 2)
    (a b : (pi V.antisymmetricPairModels).RealGroup) (x : Fin 2 → ℤ) :
    ∑ out, ‖R.pairFrozenVector k a b out x‖ ^ 2 = 1 :=
  W.vertical.unit _

def HasPairFrozenEquivalence (u b : ℝ) : Prop :=
  ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.exp u →
    ∀ a r : (pi V.antisymmetricPairModels).RealGroup,
      (∀ i, |((pi V.antisymmetricPairModels).basis.baseChange ℝ).repr a.coord i| ≤ Real.exp u) →
      ((pi V.antisymmetricPairModels).basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m →
      NativeIntegerVectorEquivalence 1 b (R.pairFrozenVector 0 a r) (R.pairFrozenVector 1 a r)

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AntisymmetricPairProjections
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def pairComponentPolynomial (out : Fin W.outputDim) (a b : Fin 2) :
    (W.model.filtration.realification.adaptedPolynomialFiltration (fun _ : Fin 2 => 1)).Group :=
  ⟨⟨(W.pairComponent out a b).orbit.log, (W.pairComponent out a b).orbit.property⟩⟩

end NativeMultidegreeNilcharacter

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AntisymmetricPairVerticalModel
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

theorem hasPairFrozenEquivalence_mono {u a b : ℝ}
    (h : R.HasPairFrozenEquivalence u a) (hab : a ≤ b) : R.HasPairFrozenEquivalence u b := by
  intro m hm hmb left right hleft hright
  exact (h m hm hmb left right hleft hright).mono hab

def HasPairFrozenReduction (b : ℝ) : Prop :=
  ∃ u : ℝ, 0 ≤ u ∧ u ≤ b ∧ R.HasOuterValueControl u ∧ R.HasPairFrozenEquivalence u b

theorem hasPairFrozenReduction_mono {a b : ℝ}
    (h : R.HasPairFrozenReduction a) (hab : a ≤ b) : R.HasPairFrozenReduction b := by
  obtain ⟨u, hu, hua, houter, hequiv⟩ := h
  exact ⟨u, hu, hua.trans hab, houter, R.hasPairFrozenEquivalence_mono hequiv hab⟩

end NativePolynomialOrbitFactors

end Erdos3

end

section

namespace Erdos3.NativePolynomialOrbitFactors

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

def HasPairLocalApproximation (b : ℝ) : Prop :=
  ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧
    ∀ y : Fin 2 → ℤ, (∀ i, |(y i : ℝ)| ≤ (N : ℝ)) →
      ∀ (k : Fin 2) (out : Fin W.outputDim) (x : Fin 2 → ℤ) (δ : ℝ), 0 ≤ δ →
        (∀ i, |(x i : ℝ)| ≤ (N : ℝ)) → (∀ i, (P : ℤ) ∣ x i - y i) →
        (∀ i, |(x i : ℝ) - (y i : ℝ)| ≤ (N : ℝ) * δ) →
        ‖W.eval out (correlationInput (x k) (x k.rev)) -
          R.pairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤ Real.exp b * δ

theorem hasPairLocalApproximation_mono {a b : ℝ}
    (h : R.HasPairLocalApproximation a) (hab : a ≤ b) : R.HasPairLocalApproximation b := by
  obtain ⟨P, hP, hPb, hlocal⟩ := h
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hab), ?_⟩
  intro y hy k out x δ hδ hx hres hnear
  exact (hlocal y hy k out x δ hδ hx hres hnear).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hab) hδ)

end Erdos3.NativePolynomialOrbitFactors

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

theorem pairAnchoredVector_norm (y : Fin 2 → ℤ) (k : Fin 2)
    (out : Fin W.outputDim) (x : Fin 2 → ℤ) : ‖R.pairAnchoredVector y k out x‖ ≤ 1 :=
  W.vertical.norm out _

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OriginalDiagonalComparison
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def originalDiagonalCorrection
    (F : (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
      (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
      (Fin 2 → ℤ) → ℂ)
    (a : Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim)
    (i : Fin W.outputDim) (c : Fin W.quadraticRoot.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∑ b : Fin 2 → Fin W.quadraticRoot.outputDim,
    (W.eval i x * star (tensorVector W.quadraticRoot.eval 2 b x)) * F a (b 0, b 1, c) x

theorem originalDiagonalCorrection_pointwise_error {N : ℕ} [NeZero N]
    (F : (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
      (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
      (Fin 2 → ℤ) → ℂ)
    (a : Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim)
    (i : Fin W.outputDim) (c : Fin W.quadraticRoot.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.quadraticRoot.cyclicDiagonalDerivative a x *
        (W.eval i (fun k => ((x k).val : ℤ)) * W.quadraticRoot.eval c (fun _ => ((x 0).val : ℤ))) -
      W.originalDiagonalCorrection F a i c (fun k => ((x k).val : ℤ))‖ ≤
      ∑ b : Fin 2 → Fin W.quadraticRoot.outputDim,
        ‖W.quadraticRoot.cyclicDiagonalDerivative a x *
            star (W.quadraticRoot.quadraticSquareTriple (b 0, b 1, c) (fun k => ((x k).val : ℤ))) -
          F a (b 0, b 1, c) (fun k => ((x k).val : ℤ))‖ := by
  let z : Fin 2 → ℤ := fun k => ((x k).val : ℤ)
  let R := W.quadraticRoot
  let D := R.cyclicDiagonalDerivative a x
  let T := tensorVector R.eval 2
  have hunit := tensorVector_unit R.eval R.unit_eval 2 z
  have hres := complex_unit_vector_resolution (fun b => T b z) hunit (W.eval i z)
  have hin : correlationInput (z 0) (z 1) = z := by funext k; fin_cases k <;> rfl
  have ht (b : Fin 2 → Fin R.outputDim) :
      star (R.quadraticSquareTriple (b 0, b 1, c) z) = T b z * R.eval c (fun _ => z 0) := by
    simp only [quadraticSquareTriple, star_star, hin, T, tensorVector, Fin.prod_univ_two]
  have heq : D * (W.eval i z * R.eval c (fun _ => z 0)) =
      ∑ b : Fin 2 → Fin R.outputDim,
        (W.eval i z * star (T b z)) * (D * star (R.quadraticSquareTriple (b 0, b 1, c) z)) := by
    calc
      _ = D * ((∑ b, (W.eval i z * star (T b z)) * T b z) * R.eval c (fun _ => z 0)) := by rw [← hres]
      _ = _ := by
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        rw [ht]
        ring
  change ‖D * (W.eval i z * R.eval c (fun _ => z 0)) - W.originalDiagonalCorrection F a i c z‖ ≤ _
  rw [heq, originalDiagonalCorrection, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b _
  rw [← mul_sub, norm_mul]
  have hc : ‖W.eval i z * star (T b z)‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval i z)).trans
    dsimp [T, tensorVector]
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun k _ => R.norm_eval (b k) z)
  exact mul_le_of_le_one_left (norm_nonneg _) hc

theorem originalDiagonalCorrection_mean_error {N : ℕ} [NeZero N]
    (F : (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
      (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
      (Fin 2 → ℤ) → ℂ) {ε : ℝ}
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.quadraticRoot.cyclicDiagonalDerivative a x *
          star (W.quadraticRoot.quadraticSquareTriple b (fun k => ((x k).val : ℤ))) -
        F a b (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim)
    (i : Fin W.outputDim) (c : Fin W.quadraticRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.quadraticRoot.cyclicDiagonalDerivative a x *
          (W.eval i (fun k => ((x k).val : ℤ)) * W.quadraticRoot.eval c (fun _ => ((x 0).val : ℤ))) -
        W.originalDiagonalCorrection F a i c (fun k => ((x k).val : ℤ))‖) ≤
      (W.quadraticRoot.outputDim : ℝ) ^ 2 * ε := by
  have hm := Finset.expect_le_expect (s := Finset.univ)
    (fun (x : Fin 2 → ZMod N) _ => W.originalDiagonalCorrection_pointwise_error F a i c x)
  rw [Finset.expect_sum_comm] at hm
  apply hm.trans
  calc
    _ ≤ ∑ _b : Fin 2 → Fin W.quadraticRoot.outputDim, ε :=
      Finset.sum_le_sum (fun b _ => herr a (b 0, b 1, c))
    _ = _ := by simp

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DiagonalRowTransfer
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff
  NativePairPartition.finite

theorem NativePairPartition.partition_sum_norm {p q r b ε : ℝ}
    {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
    {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
    {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
      Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
      (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
    {R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
      V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
      (fun _ : Fin 2 => (N : ℝ)) r}
    (P : NativePairPartition R b ε) (k : Fin 2) (out : Fin W.outputDim)
    (x : Fin 2 → ZMod N) :
    ‖∑ cell, ((∏ z, P.weight (cell z) (x z) : ℝ) : ℂ) *
      R.pairAnchoredVector (fun z => ((P.anchor cell z).val : ℤ)) k out
        (fun z => ((x z).val : ℤ))‖ ≤ 1 := by
  classical
  exact norm_positive_partition_sum_le_one
    (fun cell : Fin 2 → P.I => ∏ z, P.weight (cell z) (x z))
    (fun cell => R.pairAnchoredVector (fun z => ((P.anchor cell z).val : ℤ)) k out
      (fun z => ((x z).val : ℤ)))
    (fun cell => Finset.prod_nonneg (fun z _ => ((P.positive (cell z)).unit_interval (x z)).1))
    (sum_productPartitionWeight (fun (_ : Fin 2) a x => P.weight a x) (fun _ => P.total) x)
    (fun cell => R.pairAnchoredVector_norm _ _ _ _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

theorem cyclicDiagonalDerivative_unit {p : ℝ} {N : ℕ} [NeZero N]
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (x : Fin 2 → ZMod N) :
    ∑ a : Fin W.outputDim × Fin W.outputDim, ‖W.cyclicDiagonalDerivative a x‖ ^ 2 = 1 := by
  simp only [cyclicDiagonalDerivative, Fintype.sum_prod_type, norm_mul, norm_star,
    mul_pow, ← Finset.mul_sum, W.unit_eval, mul_one]

theorem cyclicDiagonalDerivative_norm {p : ℝ} {N : ℕ} [NeZero N]
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.cyclicDiagonalDerivative a x‖ ≤ 1 := by
  rw [cyclicDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem original_diagonal_row_correlation_bound {p ε : ℝ} {N : ℕ} [NeZero N]
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (i : Fin W.outputDim)
    (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (K : (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
      Fin W.quadraticRoot.outputDim → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a c, (𝔼 x : Fin 2 → ZMod N,
      ‖W.quadraticRoot.cyclicDiagonalDerivative a x *
        (W.eval i (fun k => ((x k).val : ℤ)) * W.quadraticRoot.eval c (fun _ => ((x 0).val : ℤ))) -
        K a c (fun k => ((x k).val : ℤ))‖) ≤ ε) :
    (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
        star (W.evalCyclic N i (correlationInput h n))‖) ≤
      (∑ ac : (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) × Fin W.quadraticRoot.outputDim,
        𝔼 h : ZMod N, ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
          W.quadraticRoot.cyclicDiagonalDerivative ac.1 ![h, n] *
            star (K ac.1 ac.2 ![(h.val : ℤ), (n.val : ℤ)])‖) +
        (W.quadraticRoot.outputDim : ℝ) ^ 3 * ε := by
  have hinput (h n : ZMod N) : (fun k => ((![h, n] k).val : ℤ)) = ![(h.val : ℤ), (n.val : ℤ)] := by
    funext k
    fin_cases k <;> rfl
  have heval (h n : ZMod N) : W.evalCyclic N i (correlationInput h n) = W.eval i ![(h.val : ℤ), (n.val : ℤ)] := by
    unfold evalCyclic
    congr 1
    funext k
    fin_cases k <;> rfl
  have hh := unit_row_correlation_bound (multiplicativeDerivative f)
    (fun h n => W.eval i ![(h.val : ℤ), (n.val : ℤ)])
    (fun a h n => W.quadraticRoot.cyclicDiagonalDerivative a ![h, n])
    (fun c h => W.quadraticRoot.eval c (fun _ => (h.val : ℤ)))
    (fun a c h n => K a c ![(h.val : ℤ), (n.val : ℤ)])
    (fun h => multiplicativeDerivative_norm_le_one f hf h)
    (fun h n => W.quadraticRoot.cyclicDiagonalDerivative_unit ![h, n])
    (fun h => W.quadraticRoot.unit_eval _) (fun a h n => W.quadraticRoot.cyclicDiagonalDerivative_norm a ![h, n])
    (fun c h => W.quadraticRoot.norm_eval _ _) (ε := ε) (by
      intro a c
      have he := herr a c
      rw [expect_fin_two] at he
      simpa only [hinput, Matrix.cons_val_zero, mul_assoc, mul_comm, mul_left_comm] using he)
  have hc : (Fintype.card ((Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) × Fin W.quadraticRoot.outputDim) : ℝ) =
      (W.quadraticRoot.outputDim : ℝ) ^ 3 := by simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]; ring
  simpa only [heval, hc] using hh

end NativeMultidegreeNilcharacter
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPermutationTensor
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem NativeMultidegreeNilcharacter.exists_mixed_missing_factors {s : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex s => 1) p)
    (a : MissingAssignment s → Fin W.outputDim) :
    ∃ A : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ,
      (∀ k x, ‖A k x‖ ≤ 1) ∧
      (∀ k x y, (∀ l, l ≠ k → x l = y l) → A k x = A k y) ∧
      ∀ x, (∏ k, A k x) = mixedMissingProduct W.eval a x := by
  classical
  apply exists_missing_coordinate_product_factors
    (fun v x => W.eval (a v) (mixedReplicatedInput (x 0) (fun j => x (v.val j).succ)))
    (fun _ _ => W.norm_eval _ _)
  intro v
  obtain ⟨j, hj⟩ := W.mixed_missing_assignment_independent v
  exact ⟨j.succ, hj (a v)⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem NativeMultidegreeNilcharacter.mixedPermutationProduct_tensorPower {s : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex s => 1) p)
    (a : Equiv.Perm (Fin s) → Fin W.outputDim) (x : Fin (s + 1) → ℤ) :
    mixedPermutationProduct W.eval a x =
      (W.tensorPower s.factorial).eval (mixedPermutationTensorIndex W.outputDim a)
        (mixedReplicatedInput (x 0) (fun j => x j.succ)) := by
  simp only [tensorPower_eval, mixedPermutationTensorIndex, Equiv.symm_apply_apply]
  exact ((mixedPermutationIndex s).symm.prod_comp
    (fun e => W.eval (a e) (mixedReplicatedInput (x 0) (fun j => x j.succ)))).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuarticRootExchange
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_native_cross_contraction :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J K L M : Type*}
      [Fintype J] [Fintype K] [Fintype L] [Fintype M] {s : ℕ} {p : ℝ}
      {a : J → (σ → ℤ) → ℂ} {u : K → (σ → ℤ) → ℂ}
      {b : L → (σ → ℤ) → ℂ} {v : M → (σ → ℤ) → ℂ}
      (G : K → M → (σ → ℤ) → ℂ),
      0 ≤ p → NativeIntegerVectorEquivalence s p a u → NativeIntegerVectorEquivalence s p b v →
      (∀ k m, Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s p (G k m))) →
      ∀ j l, Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C)
        (fun x => complexCrossContraction (a j x) (b l x)
          (fun k => u k x) (fun m => v m x) (fun k m => G k m x))) := by
  obtain ⟨A, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C A) ^ A + 2 * X)
  refine ⟨C, hC, ?_⟩
  intro σ J K L M _ _ _ _ s p a u b v G hp E F hG j l
  classical
  let t := p + (p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_right (by positivity)
  have hAt : (p + A) ^ A ≤ t := by dsimp [t]; linarith
  have hterm (km : K × M) : Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s
      ((t + A) ^ A) (fun x =>
        (a j x * star (u km.1 x)) * star (b l x * star (v km.2 x)) * G km.1 km.2 x)) := by
    obtain ⟨H⟩ := hmul hp (Classical.choice (E.expansion j km.1))
      (Classical.choice (F.expansion l km.2)).conjugate
    exact hmul ht (H.mono hAt) ((Classical.choice (hG km.1 km.2)).mono hpt)
  have hcard : (Fintype.card (K × M) : ℝ) ≤ Real.exp (2 * p) := by
    rw [Fintype.card_prod, Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p :=
        mul_le_mul E.right_dimension F.right_dimension (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, two_mul]
  have hc : (∑ _ : K × M, ‖(1 : ℂ)‖) ≤ Real.exp (2 * p) := by simpa using hcard
  have H := NativeIntegerExpansion.weightedSum (fun km => Classical.choice (hterm km))
    (fun _ => 1) (by positivity : 0 ≤ 2 * p) hcard hc
  have hcost : (t + A) ^ A + 2 * p ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by simpa only [one_mul, complexCrossContraction] using H.mono hcost⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

namespace NativeMultidegreeNilcharacter

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem division_dilation_integer_representative (d : ℕ) [NeZero d]
    {σ : Type*} [Fintype σ] {bound : σ → ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter bound p) (x : σ → ℤ) (j : Fin W.outputDim) :
    (W.rationalDilation ((d : ℚ)⁻¹)).eval j (fun i => x i - ((x i : ZMod d).val : ℤ)) =
      W.eval j (fun i => x i / (d : ℤ)) := by
  have hx : (fun i => x i - ((x i : ZMod d).val : ℤ)) =
      (fun i => (d : ℤ) * (x i / (d : ℤ))) := by
    funext i
    rw [ZMod.val_intCast, sub_eq_iff_eq_add]
    simpa only [add_comm] using (Int.emod_add_mul_ediv (x i) (d : ℤ)).symm
  rw [hx]
  apply W.rationalDilation_eval_rescaled
  rw [Int.cast_natCast]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne d))

end NativeMultidegreeNilcharacter
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMixedReflectionBridge
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem mixed_reflection_target_unit {n : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
    (c : ℤ) (x : Fin (n + 2) → ℤ) :
    ∑ a, ‖W.mixedReflectionTarget c a x‖ ^ 2 = 1 := by
  have heq (a : (Fin W.outputDim × Fin W.outputDim) × (Fin W.outputDim × Fin W.outputDim)) :
      W.mixedReflectionTarget c a x =
        (W.eval a.1.1 (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ)) *
          star (W.eval a.1.2 (mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ)))) *
        star (W.eval a.2.1 (mixedSlotInput (x 1) (c - x 1) (fun j => x j.succ.succ)) *
          star (W.eval a.2.2 (mixedSlotInput (x 1) (x 0) (fun j => x j.succ.succ)))) := by
    simp only [mixedReflectionTarget, star_mul, star_star]
    ring
  simp only [heq, norm_mul, norm_star, mul_pow, Fintype.sum_prod_type,
    ← Finset.mul_sum, W.unit_eval, mul_one]

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_reflection_weights {n : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
    (c : ℤ) (a : (Fin W.outputDim × Fin W.outputDim) × (Fin W.outputDim × Fin W.outputDim))
    (B : Fin (n + 2) → (Fin (n + 2) → ℤ) → ℂ)
    (hB : ∀ i x, ‖B i x‖ ≤ 1)
    (hBind : ∀ i x y, (∀ l, l ≠ i → x l = y l) → B i x = B i y) :
    ∃ C : Fin (n + 2) → (Fin (n + 2) → ℤ) → ℂ,
      (∀ i x, ‖C i x‖ ≤ 1) ∧
      (∀ i x y, (∀ l, l ≠ i → x l = y l) → C i x = C i y) ∧
      ∀ x, star (W.mixedReflectionTarget c a x) * (∏ i, B i x) =
        W.mixedAntisymmetric a.1.2 a.2.2 x * ∏ i, C i x := by
  classical
  let F (i : Fin 2) (x : Fin (n + 2) → ℤ) : ℂ :=
    Fin.cases
      (W.eval a.2.1 (mixedSlotInput (x 1) (c - x 1) (fun j => x j.succ.succ)))
      (fun _ => star (W.eval a.1.1 (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ)))) i
  have hF0 (x : Fin (n + 2) → ℤ) : F 0 x =
      W.eval a.2.1 (mixedSlotInput (x 1) (c - x 1) (fun j => x j.succ.succ)) := rfl
  have hF1 (x : Fin (n + 2) → ℤ) : F 1 x =
      star (W.eval a.1.1 (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ))) := rfl
  have hF : ∀ i x, ‖F i x‖ ≤ 1 := by
    intro i x
    fin_cases i
    · exact W.norm_eval _ _
    · change ‖F 1 x‖ ≤ 1
      simpa only [hF1, norm_star] using W.norm_eval a.1.1
        (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ))
  have hFind : ∀ i, ∃ k : Fin (n + 2), ∀ x y,
      (∀ l, l ≠ k → x l = y l) → F i x = F i y := by
    intro i
    fin_cases i
    · refine ⟨0, ?_⟩
      intro x y hxy
      have ht : (fun j : Fin n => x j.succ.succ) = fun j => y j.succ.succ :=
        funext (fun j => hxy j.succ.succ (Fin.succ_ne_zero j.succ))
      change W.eval a.2.1 (mixedSlotInput (x 1) (c - x 1) _) =
        W.eval a.2.1 (mixedSlotInput (y 1) (c - y 1) _)
      rw [hxy 1 (Fin.succ_ne_zero (0 : Fin (n + 1))), ht]
    · refine ⟨1, ?_⟩
      intro x y hxy
      have hne (j : Fin n) : j.succ.succ ≠ (1 : Fin (n + 2)) := by
        intro heq
        exact Fin.succ_ne_zero j (Fin.succ_injective (n + 1) heq)
      have ht : (fun j : Fin n => x j.succ.succ) = fun j => y j.succ.succ :=
        funext (fun j => hxy j.succ.succ (hne j))
      change star (W.eval a.1.1 (mixedSlotInput (x 0) (c - x 0) _)) =
        star (W.eval a.1.1 (mixedSlotInput (y 0) (c - y 0) _))
      rw [hxy 0 (Fin.succ_ne_zero (0 : Fin (n + 1))).symm, ht]
  obtain ⟨D, hD, hDind, hDprod⟩ := exists_missing_coordinate_product_factors F hF hFind
  refine ⟨(fun i x => B i x * D i x), ?_, ?_, ?_⟩
  · intro i x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hB i x)).trans (hD i x)
  · intro i x y hxy
    change B i x * D i x = B i y * D i y
    rw [hBind i x y hxy, hDind i x y hxy]
  · intro x
    rw [Finset.prod_mul_distrib, hDprod]
    simp only [Fin.prod_univ_two, hF0, hF1,
      mixedReflectionTarget, mixedAntisymmetric, star_mul, star_star]
    ring

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OriginalMixedRootEquivalence
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem mixedDiagonalDerivative_norm (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.mixedDiagonalDerivative a x‖ ≤ 1 := by
  rw [mixedDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem mixedNonconstantTensor_norm (a : MixedNonconstantCorner s → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.mixedNonconstantTensor a x‖ ≤ 1 := by
  rw [mixedNonconstantTensor, norm_star, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem mixedNonconstantTensor_unit (x : Fin 2 → ℤ) :
    ∑ a : MixedNonconstantCorner s → Fin W.outputDim, ‖W.mixedNonconstantTensor a x‖ ^ 2 = 1 := by
  simp only [mixedNonconstantTensor, norm_star, norm_prod, ← Finset.prod_pow]
  calc
    _ = ∏ v : MixedNonconstantCorner s, ∑ a : Fin W.outputDim,
        ‖W.eval a (mixedDiagonalCorner v.val x)‖ ^ 2 := (Fintype.prod_sum _).symm
    _ = 1 := by simp only [W.unit_eval, Finset.prod_const_one]

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {n : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)

theorem mixedPairComponent_eval (out : Fin W.outputDim) (v : Fin (n + 2) → Fin (n + 2))
    (x : Fin (n + 2) → ℤ) :
    (W.mixedPairComponent out v).eval x =
      W.eval out (mixedSlotInput (x (v 0)) (x (v 1)) (fun j => x (v j.succ.succ))) := by
  rw [mixedPairComponent, Niltest.eval_linearPullbackHom, component_eval]
  exact congrArg (W.eval out) (mixedInputCoordinate_eval n (fun j => x (v j)))

theorem mixedPairComponent_vertical (out : Fin W.outputDim) (v : Fin (n + 2) → Fin (n + 2))
    (z : W.model.RealGroup)
    (hz : z ∈ W.model.filtration.realification.subgroup (∑ _ : MixedReplicatedIndex (n + 1), 1))
    (x : W.model.Space) :
    (W.mixedPairComponent out v).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional W.vertical.frequency z.coord : ℝ) : CircleFourier.Circle) *
          (W.mixedPairComponent out v).observable x := by
  exact W.vertical.vertical out z (by rwa [W.multi.realSubgroup_top]) x

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem mixedCyclicDiagonalDerivative_norm {N : ℕ} [NeZero N]
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.mixedCyclicDiagonalDerivative a x‖ ≤ 1 := by
  rw [mixedCyclicDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem mixedCyclicDiagonalDerivative_unit {N : ℕ} [NeZero N]
    (x : Fin 2 → ZMod N) :
    ∑ a : Fin W.outputDim × Fin W.outputDim, ‖W.mixedCyclicDiagonalDerivative a x‖ ^ 2 = 1 := by
  simp only [mixedCyclicDiagonalDerivative, Fintype.sum_prod_type, norm_mul, norm_star,
    mul_pow, ← Finset.mul_sum, W.unit_eval, mul_one]

theorem mixedWrappedDiagonalDerivative_norm (N : ℕ) (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.mixedWrappedDiagonalDerivative N a x‖ ≤ 1 := by
  simp only [mixedWrappedDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem mixedDiagonalWrapCoefficient_norm (N : ℕ) (j k : Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.mixedDiagonalWrapCoefficient N j k x‖ ≤ 1 := by
  simp only [mixedDiagonalWrapCoefficient, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem mixedWrappedDiagonalDerivative_resolution (N : ℕ)
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.mixedWrappedDiagonalDerivative N a x =
      ∑ k, W.mixedDiagonalWrapCoefficient N a.2 k x * W.mixedDiagonalDerivative (a.1, k) x := by
  have h := complex_unit_vector_resolution
    (fun k => W.eval k (fun _ => x 1 + x 0)) (W.unit_eval _)
    (star (W.eval a.2 (fun _ => x 1 + x 0 - N)))
  calc
    _ = W.eval a.1 (fun _ => x 1) *
        ∑ k, (star (W.eval a.2 (fun _ => x 1 + x 0 - N)) *
          star (W.eval k (fun _ => x 1 + x 0))) * W.eval k (fun _ => x 1 + x 0) := by
      rw [← h]
      rfl
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [mixedDiagonalWrapCoefficient, mixedDiagonalDerivative]
      ring

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedRootLosses
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem divisionMixedExchangeCorrection_pointwise_error (d : ℕ)
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (π : Fin (s + 3) → Fin 2) (a b : Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖(W.rationalDilation ((d : ℚ)⁻¹)).eval a (mixedSampledInput π x) *
        star ((W.rationalDilation ((d : ℚ)⁻¹)).eval b (mixedSampledInput (mixedSwapSample π) x)) -
      W.divisionMixedExchangeCorrection d G π a b x‖ ≤
      ∑ ij : Fin W.outputDim × Fin W.outputDim,
        ‖W.eval ij.1 (mixedSampledInput π (fun k => x k / (d : ℤ))) *
            star (W.eval ij.2 (mixedSampledInput (mixedSwapSample π) (fun k => x k / (d : ℤ)))) -
          G π ij.1 ij.2 (fun k => x k / (d : ℤ))‖ := by
  exact norm_sub_complexCrossContraction_le_sum _ _ _ _ _
    ((W.rationalDilation ((d : ℚ)⁻¹)).norm_eval _ _) ((W.rationalDilation ((d : ℚ)⁻¹)).norm_eval _ _)
    (W.unit_eval _) (W.unit_eval _) (fun i => W.norm_eval i _) (fun j => W.norm_eval j _)

theorem divisionMixedExchangeCorrection_mean_error (d : ℕ) [NeZero d]
    {N : ℕ} [NeZero N] {ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (π : Fin (s + 3) → Fin 2) (a b : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖(W.rationalDilation ((d : ℚ)⁻¹)).eval a (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star ((W.rationalDilation ((d : ℚ)⁻¹)).eval b
            (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        W.divisionMixedExchangeCorrection d G π a b (fun k => ((x k).val : ℤ))‖) ≤
      (d : ℝ) ^ 2 * (W.outputDim : ℝ) ^ 2 * ε := by
  have hmean := Finset.expect_le_expect (s := Finset.univ)
    (fun (x : Fin 2 → ZMod N) _ => W.divisionMixedExchangeCorrection_pointwise_error d G π a b
      (fun k => ((x k).val : ℤ)))
  rw [Finset.expect_sum_comm] at hmean
  have he (ij : Fin W.outputDim × Fin W.outputDim) :
      (𝔼 x : Fin 2 → ZMod N,
        ‖W.eval ij.1 (mixedSampledInput π (fun k => ((x k).val : ℤ) / (d : ℤ))) *
            star (W.eval ij.2 (mixedSampledInput (mixedSwapSample π)
              (fun k => ((x k).val : ℤ) / (d : ℤ)))) -
          G π ij.1 ij.2 (fun k => ((x k).val : ℤ) / (d : ℤ))‖) ≤ (d : ℝ) ^ 2 * ε := by
    have h := expect_pair_cyclicDivision_le d (fun x : Fin 2 → ZMod N =>
      ‖W.eval ij.1 (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval ij.2 (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π ij.1 ij.2 (fun k => ((x k).val : ℤ))‖) (fun _ => norm_nonneg _)
    simp only [cyclicDivision_val, Int.natCast_ediv] at h
    exact h.trans (mul_le_mul_of_nonneg_left (herr π ij.1 ij.2) (sq_nonneg _))
  apply hmean.trans
  calc
    _ ≤ ∑ _ : Fin W.outputDim × Fin W.outputDim, (d : ℝ) ^ 2 * ε :=
      Finset.sum_le_sum (fun ij _ => he ij)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul]
      ring

theorem divisionMixedExchangeCorrection_norm (d : ℕ) [NeZero d]
    {N : ℕ} [NeZero N] {B : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (π : Fin (s + 3) → Fin 2) (a b : Fin W.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.divisionMixedExchangeCorrection d G π a b (fun k => ((x k).val : ℤ))‖ ≤
      (W.outputDim : ℝ) ^ 2 * B := by
  unfold divisionMixedExchangeCorrection complexCrossContraction
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : Fin W.outputDim × Fin W.outputDim, B := by
      apply Finset.sum_le_sum
      intro ij _
      rw [norm_mul]
      apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
      · have h := hG π ij.1 ij.2 (fun k => cyclicDivision d (x k))
        simpa only [cyclicDivision_val, Int.natCast_ediv] using h
      · rw [norm_mul, norm_star, norm_mul, norm_star, norm_mul, norm_star]
        exact (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          ((mul_le_of_le_one_left (norm_nonneg _)
            ((W.rationalDilation ((d : ℚ)⁻¹)).norm_eval _ _)).trans (W.norm_eval _ _))).trans
          ((mul_le_of_le_one_left (norm_nonneg _)
            ((W.rationalDilation ((d : ℚ)⁻¹)).norm_eval _ _)).trans (W.norm_eval _ _))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul, pow_two]

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem mixedTensorExchange_kernel (n : ℕ) (π : Fin (s + 3) → Fin 2)
    (a b : Fin (W.outputDim ^ n)) (x : Fin 2 → ℤ) :
    (W.tensorPower n).eval a (mixedSampledInput π x) *
        star ((W.tensorPower n).eval b (mixedSampledInput (mixedSwapSample π) x)) =
      ∏ k : Fin n, W.eval ((tensorIndexEquiv W.outputDim n).symm a k) (mixedSampledInput π x) *
        star (W.eval ((tensorIndexEquiv W.outputDim n).symm b k)
          (mixedSampledInput (mixedSwapSample π) x)) := by
  simp only [tensorPower_eval, star_prod, Finset.prod_mul_distrib]

theorem mixedTensorExchangeCorrection_mean_error (n : ℕ) {N : ℕ} [NeZero N] {B ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) (hB : 1 ≤ B)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (π : Fin (s + 3) → Fin 2) (a b : Fin (W.outputDim ^ n)) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖(W.tensorPower n).eval a (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star ((W.tensorPower n).eval b
            (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        W.mixedTensorExchangeCorrection n G π a b (fun k => ((x k).val : ℤ))‖) ≤ B ^ n * (n * ε) := by
  let i := (tensorIndexEquiv W.outputDim n).symm a
  let j := (tensorIndexEquiv W.outputDim n).symm b
  have h := mean_prod_error_le
    (fun k (x : Fin 2 → ZMod N) =>
      W.eval (i k) (mixedSampledInput π (fun l => ((x l).val : ℤ))) *
        star (W.eval (j k) (mixedSampledInput (mixedSwapSample π) (fun l => ((x l).val : ℤ)))))
    (fun k (x : Fin 2 → ZMod N) => G π (i k) (j k) (fun l => ((x l).val : ℤ))) hB
    (fun k x => (by
      rw [norm_mul, norm_star]
      exact ((mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans
        (W.norm_eval _ _)).trans hB))
    (fun _ x => hG _ _ _ x) (fun k => herr π (i k) (j k))
  simpa only [Fintype.card_fin, mixedTensorExchange_kernel, mixedTensorExchangeCorrection, i, j] using h

theorem dilationTensorMixedExchangeCorrection_mean_error (d n : ℕ) [NeZero d]
    {N : ℕ} [NeZero N] {ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (π : Fin (s + 3) → Fin 2) (a b : Fin (W.outputDim ^ n)) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖((W.rationalDilation ((d : ℚ)⁻¹)).tensorPower n).eval a
            (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (((W.rationalDilation ((d : ℚ)⁻¹)).tensorPower n).eval b
            (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        (W.rationalDilation ((d : ℚ)⁻¹)).mixedTensorExchangeCorrection n
          (W.divisionMixedExchangeCorrection d G) π a b (fun k => ((x k).val : ℤ))‖) ≤
      (W.outputDim : ℝ) ^ (2 * n) * (n * ((d : ℝ) ^ 2 * (W.outputDim : ℝ) ^ 2 * ε)) := by
  have hd : (1 : ℝ) ≤ W.outputDim := by exact_mod_cast W.output_pos
  have hB : 1 ≤ (W.outputDim : ℝ) ^ 2 := by nlinarith
  have hH (π : Fin (s + 3) → Fin 2) (i j : Fin W.outputDim) (x : Fin 2 → ZMod N) :
      ‖W.divisionMixedExchangeCorrection d G π i j (fun k => ((x k).val : ℤ))‖ ≤ (W.outputDim : ℝ) ^ 2 := by
    simpa only [mul_one] using W.divisionMixedExchangeCorrection_norm d G hG π i j x
  have h := (W.rationalDilation ((d : ℚ)⁻¹)).mixedTensorExchangeCorrection_mean_error n
    (W.divisionMixedExchangeCorrection d G) hB hH
    (W.divisionMixedExchangeCorrection_mean_error d G herr) π a b
  simpa only [← pow_mul] using h

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem mixedRootExchangeCorrection_norm {N : ℕ} [NeZero N]
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (π : Fin (s + 3) → Fin 2) (a b : Fin W.mixedIntegrationRoot.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.mixedRootExchangeCorrection G π a b (fun k => ((x k).val : ℤ))‖ ≤ (W.outputDim : ℝ) ^ (2 * ((s + 3) ^ (s + 2))) := by
  have hH (π : Fin (s + 3) → Fin 2) (i j : Fin W.outputDim) (x : Fin 2 → ZMod N) :
      ‖W.divisionMixedExchangeCorrection (s + 3) G π i j (fun k => ((x k).val : ℤ))‖ ≤ (W.outputDim : ℝ) ^ 2 := by
    simpa only [mul_one] using W.divisionMixedExchangeCorrection_norm (s + 3) G hG π i j x
  simpa only [mixedRootExchangeCorrection, ← pow_mul] using
    (W.rationalDilation (((s + 3 : ℕ) : ℚ)⁻¹)).mixedTensorExchangeCorrection_norm ((s + 3) ^ (s + 2))
      (W.divisionMixedExchangeCorrection (s + 3) G) hH π a b x

theorem mixedRootExchangeCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (π : Fin (s + 3) → Fin 2) (a b : Fin W.mixedIntegrationRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedIntegrationRoot.eval a (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.mixedIntegrationRoot.eval b
            (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        W.mixedRootExchangeCorrection G π a b (fun k => ((x k).val : ℤ))‖) ≤
      (W.outputDim : ℝ) ^ (2 * ((s + 3) ^ (s + 2))) *
        ((((s + 3) ^ (s + 2) : ℕ) : ℝ) *
          (((s + 3 : ℕ) : ℝ) ^ 2 * (W.outputDim : ℝ) ^ 2 * ε)) := by
  exact W.dilationTensorMixedExchangeCorrection_mean_error
    (s + 3) ((s + 3) ^ (s + 2)) G hG herr π a b

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

namespace NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem mixedRawCornerFactor_norm (a b : MixedNonconstantCorner s → Fin W.outputDim)
    (v : MixedNonconstantCorner s) (x : Fin 2 → ℤ) : ‖W.mixedRawCornerFactor a b v x‖ ≤ 1 := by
  rw [mixedRawCornerFactor, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem mixedCornerExchangeFactor_norm {N : ℕ} [NeZero N] {B : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hB : 1 ≤ B)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (a b : MixedNonconstantCorner s → Fin W.outputDim) (v : MixedNonconstantCorner s)
    (x : Fin 2 → ZMod N) :
    ‖W.mixedCornerExchangeFactor G a b v (fun k => ((x k).val : ℤ))‖ ≤
      (W.outputDim : ℝ) ^ 2 * B := by
  have hd : (1 : ℝ) ≤ W.outputDim := by exact_mod_cast W.output_pos
  have hd2 : (1 : ℝ) ≤ (W.outputDim : ℝ) ^ 2 := by nlinarith
  have hQ : 1 ≤ (W.outputDim : ℝ) ^ 2 * B :=
    hB.trans (le_mul_of_one_le_left (zero_le_one.trans hB) hd2)
  by_cases hv : v.val 0 = 1
  · rw [mixedCornerExchangeFactor, if_pos hv]
    exact (W.mixedRawCornerFactor_norm a b v _).trans hQ
  · rw [mixedCornerExchangeFactor, if_neg hv]
    have h := norm_complexCrossContraction_le_card
      (W.eval (a v) (mixedDiagonalCorner v.val (fun k => ((x k).val : ℤ))))
      (W.eval (b v) (mixedSampledInput (mixedCanonicalSample v.val) (fun k => ((x k).val : ℤ))))
      (fun i => W.eval i (mixedSampledInput (mixedPreExchangeSample v.val) (fun k => ((x k).val : ℤ))))
      (fun j => W.eval j (mixedSampledInput (mixedSwapSample (mixedPreExchangeSample v.val))
        (fun k => ((x k).val : ℤ))))
      (fun i j => G (mixedPreExchangeSample v.val) i j (fun k => ((x k).val : ℤ)))
      (W.norm_eval _ _) (W.norm_eval _ _) (fun _ => W.norm_eval _ _) (fun _ => W.norm_eval _ _)
      (fun i j => hG _ i j x)
    convert h using 1; first | rfl | simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two]

theorem mixedCornerExchangeFactor_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hε : 0 ≤ ε)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a b : MixedNonconstantCorner s → Fin W.outputDim) (v : MixedNonconstantCorner s) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedRawCornerFactor a b v (fun k => ((x k).val : ℤ)) -
        W.mixedCornerExchangeFactor G a b v (fun k => ((x k).val : ℤ))‖) ≤
      (W.outputDim : ℝ) ^ 2 * ε := by
  by_cases hv : v.val 0 = 1
  · simpa [mixedCornerExchangeFactor, hv] using mul_nonneg (sq_nonneg (W.outputDim : ℝ)) hε
  · simp only [mixedCornerExchangeFactor, if_neg hv, mixedRawCornerFactor]
    have h := mean_complexCrossContraction_error_le_card
      (fun x : Fin 2 → ZMod N => W.eval (a v) (mixedDiagonalCorner v.val (fun k => ((x k).val : ℤ))))
      (fun x => W.eval (b v) (mixedSampledInput (mixedCanonicalSample v.val) (fun k => ((x k).val : ℤ))))
      (fun i x => W.eval i (mixedSampledInput (mixedPreExchangeSample v.val) (fun k => ((x k).val : ℤ))))
      (fun j x => W.eval j (mixedSampledInput (mixedSwapSample (mixedPreExchangeSample v.val))
        (fun k => ((x k).val : ℤ))))
      (fun i j x => G (mixedPreExchangeSample v.val) i j (fun k => ((x k).val : ℤ)))
      (fun _ => W.norm_eval _ _) (fun _ => W.norm_eval _ _)
      (fun _ => W.unit_eval _) (fun _ => W.unit_eval _)
      (fun _ _ => W.norm_eval _ _) (fun _ _ => W.norm_eval _ _) (herr (mixedPreExchangeSample v.val))
    convert h using 1; first | rfl | simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two]

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem mixedCanonicalTensor_norm (a : MixedNonconstantCorner s → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.mixedCanonicalTensor a x‖ ≤ 1 := by
  rw [mixedCanonicalTensor, norm_star, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem mixedNonconstantTensor_cross_symmetric
    (a b : MixedNonconstantCorner s → Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.mixedNonconstantTensor a x * star (W.mixedCanonicalTensor b x) =
      star (∏ v, W.mixedRawCornerFactor a b v x) := by
  simp only [mixedNonconstantTensor, mixedCanonicalTensor, mixedRawCornerFactor,
    Finset.prod_mul_distrib, star_prod, star_mul, star_star]
  ring

theorem mixedCornerExchangeProduct_mean_error {N : ℕ} [NeZero N] {B ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hB : 1 ≤ B) (hε : 0 ≤ ε)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a b : MixedNonconstantCorner s → Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedNonconstantTensor a (fun k => ((x k).val : ℤ)) *
          star (W.mixedCanonicalTensor b (fun k => ((x k).val : ℤ))) -
        W.mixedCornerExchangeProduct G a b (fun k => ((x k).val : ℤ))‖) ≤
      ((W.outputDim : ℝ) ^ 2 * B) ^ (mixedCornerCount s) * ((mixedCornerCount s) * ((W.outputDim : ℝ) ^ 2 * ε)) := by
  have hd : (1 : ℝ) ≤ W.outputDim := by exact_mod_cast W.output_pos
  have hd2 : (1 : ℝ) ≤ (W.outputDim : ℝ) ^ 2 := by nlinarith
  have hQ : 1 ≤ (W.outputDim : ℝ) ^ 2 * B :=
    hB.trans (le_mul_of_one_le_left (zero_le_one.trans hB) hd2)
  have h := mean_prod_error_le
    (fun v (x : Fin 2 → ZMod N) => W.mixedRawCornerFactor a b v (fun k => ((x k).val : ℤ)))
    (fun v (x : Fin 2 → ZMod N) => W.mixedCornerExchangeFactor G a b v (fun k => ((x k).val : ℤ))) hQ
    (fun v x => (W.mixedRawCornerFactor_norm a b v _).trans hQ)
    (fun v x => W.mixedCornerExchangeFactor_norm G hB hG a b v x)
    (fun v => W.mixedCornerExchangeFactor_mean_error G hε herr a b v)
  simpa only [W.mixedNonconstantTensor_cross_symmetric, mixedCornerExchangeProduct,
    ← star_sub, norm_star, mixedNonconstantCorner_card_eq] using h

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_corner_exchange_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)
      (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ),
      0 ≤ q → 0 ≤ r →
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π i j))) →
      (∀ (e : Equiv.Perm (Fin (s + 2))) (π : Fin (s + 3) → Fin 2), NativeIntegerVectorEquivalence (s + 2) r
        (fun i (x : Fin 2 → ℤ) => W.eval i (mixedSampledInput π x))
        (fun i x => W.eval i (mixedSampledInput (mixedPermuteSample e π) x))) →
      ∀ a b v, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((q + r + C) ^ C)
        (W.mixedCornerExchangeFactor G a b v)) := by
  obtain ⟨A, _, hcontract⟩ := exists_native_cross_contraction
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p q r W G hq hr hG hperm a b v
  let t := q + r
  have ht : 0 ≤ t := add_nonneg hq hr
  have hqt : q ≤ t := by dsimp [t]; linarith
  have hrt : r ≤ t := by dsimp [t]; linarith
  have hsum : t + (t + A) ^ A ≤ (q + r + C) ^ C := by
    simpa [X, t, Polynomial.eval₂_pow] using hbudget (q + r) (add_nonneg hq hr)
  have htC : t ≤ (q + r + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hAC : (t + A) ^ A ≤ (q + r + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  by_cases hv : v.val 0 = 1
  · have hcanon := mixedCanonicalSample_of_first_one v.val hv
    obtain ⟨F⟩ := ((hperm (mixedTailSortPermutation v.val)
      (mixedCornerSample v.val)).mono hrt).expansion (a v) (b v)
    have heq : (fun x => W.eval (a v) (mixedSampledInput (mixedCornerSample v.val) x) *
        star (W.eval (b v) (mixedSampledInput
          (mixedPermuteSample (mixedTailSortPermutation v.val)
            (mixedCornerSample v.val)) x))) = W.mixedCornerExchangeFactor G a b v := by
      funext x
      simp only [mixedCornerExchangeFactor, if_pos hv, mixedRawCornerFactor,
        mixedCornerSample_input, hcanon]
    exact ⟨heq ▸ F.mono htC⟩
  · have hv0 := binary_eq_zero_of_ne_one (v.val 0) hv
    have hcanon := mixedCanonicalSample_of_first_zero v hv0
    have Eleft : NativeIntegerVectorEquivalence (s + 2) t
        (fun i (x : Fin 2 → ℤ) => W.eval i (mixedDiagonalCorner v.val x))
        (fun i x => W.eval i (mixedSampledInput (mixedPreExchangeSample v.val) x)) := by
      simpa only [mixedCornerSample_input, mixedPreExchangeSample] using
        (hperm (mixedHeadPermutation v.val) (mixedCornerSample v.val)).mono hrt
    have Eright : NativeIntegerVectorEquivalence (s + 2) t
        (fun i (x : Fin 2 → ℤ) => W.eval i (mixedSampledInput (mixedCanonicalSample v.val) x))
        (fun i x => W.eval i (mixedSampledInput (mixedSwapSample (mixedPreExchangeSample v.val)) x)) := by
      rw [hcanon]
      exact ((hperm (mixedPostExchangePermutation v.val)
        (mixedSwapSample (mixedPreExchangeSample v.val))).mono hrt).symm
    have H := hcontract (fun i j x => G (mixedPreExchangeSample v.val) i j x) ht Eleft Eright
      (fun i j => ⟨(Classical.choice (hG _ i j)).mono hqt⟩) (a v) (b v)
    have heq : (fun x => complexCrossContraction
        (W.eval (a v) (mixedDiagonalCorner v.val x))
        (W.eval (b v) (mixedSampledInput (mixedCanonicalSample v.val) x))
        (fun i => W.eval i (mixedSampledInput (mixedPreExchangeSample v.val) x))
        (fun j => W.eval j (mixedSampledInput (mixedSwapSample (mixedPreExchangeSample v.val)) x))
        (fun i j => G (mixedPreExchangeSample v.val) i j x)) = W.mixedCornerExchangeFactor G a b v := by
      funext x
      simp only [mixedCornerExchangeFactor, if_neg hv]
    exact ⟨heq ▸ (Classical.choice H).mono hAC⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem mixedPermutedDiagonalCorrection_mean_error {N : ℕ} [NeZero N] {B ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) (hB : 1 ≤ B)
    (hG : ∀ π a b (x : Fin 2 → ZMod N), ‖G π a b (fun z => ((x z).val : ℤ))‖ ≤ B)
    (hε : 0 ≤ ε)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim) (b : MixedNonconstantCorner s → Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
        W.mixedPermutedDiagonalCorrection G a b (fun z => ((x z).val : ℤ))‖) ≤
      (W.outputDim : ℝ) ^ (mixedCornerCount s) * (((W.outputDim : ℝ) ^ 2 * B) ^ (mixedCornerCount s) * ((mixedCornerCount s) * ((W.outputDim : ℝ) ^ 2 * ε))) := by
  have hid (x : Fin 2 → ℤ) :
      W.mixedDiagonalDerivative a x * star (W.mixedCanonicalTensor b x) =
        ∑ c : MixedNonconstantCorner s → Fin W.outputDim,
          (W.mixedDiagonalDerivative a x * star (W.mixedNonconstantTensor c x)) *
            (W.mixedNonconstantTensor c x * star (W.mixedCanonicalTensor b x)) := by
    calc
      _ = ∑ c, ((W.mixedDiagonalDerivative a x * star (W.mixedCanonicalTensor b x)) *
          star (W.mixedNonconstantTensor c x)) * W.mixedNonconstantTensor c x :=
        complex_unit_vector_resolution _ (W.mixedNonconstantTensor_unit x) _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro c _
        ring
  have hpoint (x : Fin 2 → ZMod N) :
      ‖W.mixedDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
        W.mixedPermutedDiagonalCorrection G a b (fun z => ((x z).val : ℤ))‖ ≤
      ∑ c : MixedNonconstantCorner s → Fin W.outputDim,
        ‖W.mixedNonconstantTensor c (fun z => ((x z).val : ℤ)) *
            star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
          W.mixedCornerExchangeProduct G c b (fun z => ((x z).val : ℤ))‖ := by
    rw [hid, mixedPermutedDiagonalCorrection, ← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro c _
    rw [← mul_sub, norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (W.mixedDiagonalDerivative_norm _ _)).trans (W.mixedNonconstantTensor_norm _ _)
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N, ∑ c : MixedNonconstantCorner s → Fin W.outputDim,
        ‖W.mixedNonconstantTensor c (fun z => ((x z).val : ℤ)) *
            star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
          W.mixedCornerExchangeProduct G c b (fun z => ((x z).val : ℤ))‖ :=
      Finset.expect_le_expect (fun x _ => hpoint x)
    _ = ∑ c : MixedNonconstantCorner s → Fin W.outputDim, 𝔼 x : Fin 2 → ZMod N,
        ‖W.mixedNonconstantTensor c (fun z => ((x z).val : ℤ)) *
            star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
          W.mixedCornerExchangeProduct G c b (fun z => ((x z).val : ℤ))‖ :=
      Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _ : MixedNonconstantCorner s → Fin W.outputDim,
        ((W.outputDim : ℝ) ^ 2 * B) ^ (mixedCornerCount s) * ((mixedCornerCount s) * ((W.outputDim : ℝ) ^ 2 * ε)) :=
      Finset.sum_le_sum (fun c _ => W.mixedCornerExchangeProduct_mean_error G hB hε hG herr c b)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        mixedNonconstantCorner_card_eq, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem mixedRootCornerCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hε : 0 ≤ ε)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim)
    (b : MixedNonconstantCorner s → Fin W.mixedIntegrationRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedIntegrationRoot.mixedDiagonalDerivative a (fun k => ((x k).val : ℤ)) *
          star (W.mixedIntegrationRoot.mixedCanonicalTensor b (fun k => ((x k).val : ℤ))) -
        W.mixedRootCornerCorrection G a b (fun k => ((x k).val : ℤ))‖) ≤
      (W.mixedIntegrationRoot.outputDim : ℝ) ^ mixedCornerCount s *
        (((W.mixedIntegrationRoot.outputDim : ℝ) ^ 2 *
            (W.outputDim : ℝ) ^ (2 * ((s + 3) ^ (s + 2)))) ^ mixedCornerCount s *
          ((mixedCornerCount s : ℝ) * ((W.mixedIntegrationRoot.outputDim : ℝ) ^ 2 *
            ((W.outputDim : ℝ) ^ (2 * ((s + 3) ^ (s + 2))) *
              ((((s + 3) ^ (s + 2) : ℕ) : ℝ) *
                (((s + 3 : ℕ) : ℝ) ^ 2 * (W.outputDim : ℝ) ^ 2 * ε)))))) := by
  have hd : (1 : ℝ) ≤ W.outputDim := by exact_mod_cast W.output_pos
  have hB : 1 ≤ (W.outputDim : ℝ) ^ (2 * ((s + 3) ^ (s + 2))) := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hd (2 * ((s + 3) ^ (s + 2)))
  exact W.mixedIntegrationRoot.mixedPermutedDiagonalCorrection_mean_error
    (W.mixedRootExchangeCorrection G) hB (W.mixedRootExchangeCorrection_norm G hG)
    (by positivity) (W.mixedRootExchangeCorrection_mean_error G hG herr) a b

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem mixedRootCornerCorrection_mean_error_power {N : ℕ} [NeZero N] {ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hε : 0 ≤ ε)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim)
    (b : MixedNonconstantCorner s → Fin W.mixedIntegrationRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedIntegrationRoot.mixedDiagonalDerivative a (fun k => ((x k).val : ℤ)) *
          star (W.mixedIntegrationRoot.mixedCanonicalTensor b (fun k => ((x k).val : ℤ))) -
        W.mixedRootCornerCorrection G a b (fun k => ((x k).val : ℤ))‖) ≤
      (mixedRootCornerCoefficient s : ℝ) * (W.outputDim : ℝ) ^ mixedRootCornerExponent s * ε := by
  have H := W.mixedRootCornerCorrection_mean_error G hε hG herr a b
  apply H.trans_eq
  rw [W.mixedIntegrationRoot_outputDim, Nat.cast_pow]
  exact root_corner_loss_identity (W.outputDim : ℝ) (mixedRootTensorExponent s) (mixedCornerCount s) (s + 3) ε

end NativeMultidegreeNilcharacter
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedFrozenMiddleRows
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem mixedFirstTensor_norm (a : Fin (s + 3) → Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖W.mixedFirstTensor a x‖ ≤ 1 := by
  rw [mixedFirstTensor, tensorVector, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem mixedFirstTensor_unit (x : Fin 2 → ℤ) :
    ∑ a : Fin (s + 3) → Fin W.outputDim, ‖W.mixedFirstTensor a x‖ ^ 2 = 1 :=
  tensorVector_unit W.eval W.unit_eval (s + 3) _

theorem mixedCanonicalTensor_weight_merge
    (a : (k : Fin (s + 3)) → MixedWeightCorner s (k.val + 1) → Fin W.outputDim)
    (x : Fin 2 → ℤ) :
    star (W.mixedCanonicalTensor (mixedWeightMerge a) x) = ∏ k, W.mixedWeightTensor k (a k) x := by
  rw [mixedCanonicalTensor, star_star]
  calc
    _ = ∏ z : MixedWeightBlock s,
        W.eval (mixedWeightMerge a (mixedWeightBlockEquiv s z))
          (mixedSampledInput (mixedCanonicalSample (mixedWeightBlockEquiv s z).val) x) :=
      ((mixedWeightBlockEquiv s).prod_comp _).symm
    _ = ∏ z : MixedWeightBlock s,
        W.eval (a z.1 z.2) (mixedSampledInput (mixedWeightSample s z.1) x) := by
      apply Finset.prod_congr rfl
      intro z _
      rw [mixedWeightMerge_block, mixedWeightBlock_canonical]
    _ = _ := by simp only [Fintype.prod_sigma, mixedWeightTensor]

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem mixedCanonicalTensor_grouped_merge (a : Fin (s + 3) → Fin W.outputDim)
    (b : MixedHigherCorner s → Fin W.outputDim) (x : Fin 2 → ℤ) :
    star (W.mixedCanonicalTensor (mixedGroupedWeightMerge a b) x) =
      W.mixedFirstTensor a x * W.mixedHigherTensor b x := by
  rw [mixedGroupedWeightMerge, W.mixedCanonicalTensor_weight_merge, Fin.prod_univ_succ]
  change W.mixedWeightTensor 0 (fun v => a ((mixedWeightOneEquiv s).symm v)) x *
    (∏ k : Fin (s + 2), W.mixedWeightTensor k.succ (fun v => b ⟨k, v⟩) x) = _
  rw [W.mixedWeightTensor_first]
  congr 1
  exact (Fintype.prod_sigma (fun z : MixedHigherCorner s =>
    W.eval (b z) (mixedSampledInput (mixedWeightSample s z.1.succ) x))).symm

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem mixedMiddleTensor_unit (x : Fin 2 → ℤ) :
    ∑ b : MixedMiddleCorner s → Fin W.outputDim, ‖W.mixedMiddleTensor b x‖ ^ 2 = 1 := by
  simp only [mixedMiddleTensor, norm_prod, ← Finset.prod_pow]
  calc
    _ = ∏ z : MixedMiddleCorner s, ∑ i : Fin W.outputDim,
        ‖W.eval i (mixedSampledInput (mixedWeightSample s z.1.castSucc.succ) x)‖ ^ 2 :=
      (Fintype.prod_sum _).symm
    _ = 1 := by simp only [W.unit_eval, Finset.prod_const_one]

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ}
  (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (s + 2)) p)
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem mixedOriginalWeightCorrection_pointwise_error
    (F : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
      (MixedNonconstantCorner s → Fin W.mixedIntegrationRoot.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim)
    (i : Fin M.outputDim) (b : MixedHigherCorner s → Fin W.mixedIntegrationRoot.outputDim)
    (x : Fin 2 → ℤ) (D : ℂ) :
    ‖D * (M.eval i x * W.mixedIntegrationRoot.mixedHigherTensor b x) -
      M.mixedOriginalWeightCorrection W F a i b x‖ ≤
      ∑ d : Fin (s + 3) → Fin W.mixedIntegrationRoot.outputDim,
        ‖D * star (W.mixedIntegrationRoot.mixedCanonicalTensor (mixedGroupedWeightMerge d b) x) -
          F a (mixedGroupedWeightMerge d b) x‖ := by
  let R := W.mixedIntegrationRoot
  have hres := complex_unit_vector_resolution (fun d => R.mixedFirstTensor d x)
    (R.mixedFirstTensor_unit x) (M.eval i x)
  have heq : D * (M.eval i x * R.mixedHigherTensor b x) =
      ∑ d : Fin (s + 3) → Fin R.outputDim,
        (M.eval i x * star (R.mixedFirstTensor d x)) *
          (D * star (R.mixedCanonicalTensor (mixedGroupedWeightMerge d b) x)) := by
    calc
      _ = D * ((∑ d, (M.eval i x * star (R.mixedFirstTensor d x)) * R.mixedFirstTensor d x) *
          R.mixedHigherTensor b x) := by rw [← hres]
      _ = _ := by
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        rw [R.mixedCanonicalTensor_grouped_merge]
        ring
  rw [heq, mixedOriginalWeightCorrection, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d _
  rw [← mul_sub, norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (M.norm_eval i x)).trans
    (R.mixedFirstTensor_norm d x)

theorem mixedOriginalWeightCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (F : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
      (MixedNonconstantCorner s → Fin W.mixedIntegrationRoot.outputDim) → (Fin 2 → ℤ) → ℂ)
    (D : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
      (Fin 2 → ZMod N) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖D a x * star (W.mixedIntegrationRoot.mixedCanonicalTensor b (fun k => ((x k).val : ℤ))) -
        F a b (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim)
    (i : Fin M.outputDim) (b : MixedHigherCorner s → Fin W.mixedIntegrationRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖D a x * (M.eval i (fun k => ((x k).val : ℤ)) *
          W.mixedIntegrationRoot.mixedHigherTensor b (fun k => ((x k).val : ℤ))) -
        M.mixedOriginalWeightCorrection W F a i b (fun k => ((x k).val : ℤ))‖) ≤
      (W.mixedIntegrationRoot.outputDim : ℝ) ^ (s + 3) * ε := by
  have hm := Finset.expect_le_expect (s := Finset.univ)
    (fun (x : Fin 2 → ZMod N) _ => M.mixedOriginalWeightCorrection_pointwise_error W F a i b
      (fun k => ((x k).val : ℤ)) (D a x))
  rw [Finset.expect_sum_comm] at hm
  apply hm.trans
  calc
    _ ≤ ∑ _ : Fin (s + 3) → Fin W.mixedIntegrationRoot.outputDim, ε :=
      Finset.sum_le_sum (fun d _ => herr a (mixedGroupedWeightMerge d b))
    _ = _ := by simp

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MixedPairPolynomial
namespace OAI

section

namespace Erdos3.NativeSampleCorrelation

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {n : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
  {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ))))

def mixedPairProjection (k : Fin 2) : V.MixedPairAlgebra →ₗ⁅ℚ⁆ W.L := liePiEval (some k)

theorem mixedPairFrequency_apply (x : V.MixedPairAlgebra) :
    piFrequency V.mixedPairFrequencies x =
      W.vertical.frequency (V.mixedPairProjection 0 x) -
        W.vertical.frequency (V.mixedPairProjection 1 x) := by
  have h (x₀ x₁ : W.L) :
      0 + (W.vertical.frequency x₀ + (-W.vertical.frequency) x₁) =
        W.vertical.frequency x₀ - W.vertical.frequency x₁ := by
    simp only [LinearMap.neg_apply]
    ring
  rw [piFrequency_apply, Fintype.sum_option, Fin.sum_univ_two]
  exact h (x (some 0)) (x (some 1))

theorem mixedPairFrequency_real (x : ℝ ⊗[ℚ] V.MixedPairAlgebra) :
    realifyFunctional (piFrequency V.mixedPairFrequencies) x =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedPairProjection 0) x) -
        realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedPairProjection 1) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [realifyFunctional_tmul, V.mixedPairFrequency_apply,
      realificationLieHom_tmul, Rat.cast_sub, mul_sub]
  | add x y hx hy => simp only [map_add, hx, hy]; ring

end Erdos3.NativeSampleCorrelation

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPairComparison
namespace OAI

section

namespace Erdos3.NativePolynomialOrbitFactors

open RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {n : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

theorem mixed_pair_top_agreement (x : ℝ ⊗[ℚ] V.MixedPairAlgebra)
    (hx : x ∈ (pi V.mixedPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ _ : MixedReplicatedIndex (n + 1), 1)) :
    realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedPairProjection 0) x) =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedPairProjection 1) x) := by
  have h := R.kills_top x hx
  rw [V.mixedPairFrequency_real] at h
  linarith

end Erdos3.NativePolynomialOrbitFactors

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeSampleCorrelation

variable {n : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ))))

include V in
theorem mixedPairComparison_component_cost : p + 4 ≤ mixedPairBudget p q := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  have hr : 0 ≤ raisedNiltestBudget (p + q) :=
    (add_nonneg hp hq).trans (le_raisedNiltestBudget _)
  unfold mixedPairBudget
  linarith

end NativeSampleCorrelation

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.MixedOriginalPairFrequency
namespace OAI

section

namespace Erdos3.NativePolynomialOrbitFactors

open RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {n m : ℕ} [NeZero m] {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

variable (V) in
noncomputable def _root_.OAI.Erdos3.NativeSampleCorrelation.mixedOriginalPairProjection (k : Fin 2) :
    V.MixedPairAlgebra →ₗ⁅ℚ⁆ W.L := liePiEval (some k)

theorem mixed_original_pair_top_agreement (x : ℝ ⊗[ℚ] V.MixedPairAlgebra)
    (hx : x ∈ (pi V.mixedPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ _ : MixedReplicatedIndex (n + 1), 1)) :
    realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedOriginalPairProjection 0) x) =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedOriginalPairProjection 1) x) := by
  have cancel (a b : ℝ ⊗[ℚ] W.L)
      (h : realifyFunctional (m • W.vertical.frequency) a =
        realifyFunctional (m • W.vertical.frequency) b) :
      realifyFunctional W.vertical.frequency a = realifyFunctional W.vertical.frequency b := by
    rw [realifyFunctional_nsmul, realifyFunctional_nsmul] at h
    simp only [nsmul_eq_mul] at h
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne m) : (m : ℝ) ≠ 0) h
  exact cancel _ _ (R.mixed_pair_top_agreement x hx)

end Erdos3.NativePolynomialOrbitFactors

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPairFrozenEquivalence
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeSampleCorrelation

variable {n m : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ))))

include V in
theorem mixedOriginalPairComparison_component_cost : p + 4 ≤ mixedPairBudget (tensorPowerBudget m p) q := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hpow : p ≤ tensorPowerBudget m p := (tensorPowerBudget_bounds m hp).1
  have hcost := V.mixedPairComparison_component_cost
  linarith only [hpow, hcost]

noncomputable def mixedOriginalPairFrequencies :
    ∀ k, optionLieSpace V.L (fun _ : Fin 2 => (W.tensorPower m).L) k →ₗ[ℚ] ℚ
  | none => 0
  | some k => ![W.vertical.frequency, -W.vertical.frequency] k

theorem mixedOriginalPairFrequency_apply (x : V.MixedPairAlgebra) :
    piFrequency V.mixedOriginalPairFrequencies x =
      W.vertical.frequency (V.mixedOriginalPairProjection 0 x) -
        W.vertical.frequency (V.mixedOriginalPairProjection 1 x) := by
  have h (x₀ x₁ : W.L) :
      0 + (W.vertical.frequency x₀ + (-W.vertical.frequency) x₁) =
        W.vertical.frequency x₀ - W.vertical.frequency x₁ := by
    simp only [LinearMap.neg_apply]
    ring
  rw [piFrequency_apply, Fintype.sum_option, Fin.sum_univ_two]
  exact h (x (some 0)) (x (some 1))

theorem mixedOriginalPairFrequency_real (x : ℝ ⊗[ℚ] V.MixedPairAlgebra) :
    realifyFunctional (piFrequency V.mixedOriginalPairFrequencies) x =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedOriginalPairProjection 0) x) -
        realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedOriginalPairProjection 1) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [realifyFunctional_tmul, V.mixedOriginalPairFrequency_apply,
      realificationLieHom_tmul, Rat.cast_sub, mul_sub]
  | add x y hx hy => simp only [map_add, hx, hy]; ring

noncomputable def mixedOriginalPairComparisonTests (a b : Fin W.outputDim) :
    ∀ k, (V.mixedPairModels k).Niltest (fun _ : Fin (n + 2) => 1)
  | none => (V.test.raiseStep (by rw [mixedReplicated_totalDegree]; omega :
      n + 1 ≤ ∑ _ : MixedReplicatedIndex (n + 1), 1)).oneOnOrbit
  | some k => ![W.mixedPairComponent a id, (W.mixedPairComponent b (mixedExchangeCoordinate n)).conjugate] k

theorem mixedOriginalPairComparisonTests_vertical (a b : Fin W.outputDim) (k : Option (Fin 2))
    (z : (V.mixedPairModels k).RealGroup)
    (hz : z ∈ (V.mixedPairModels k).filtration.realification.subgroup
      (∑ _ : MixedReplicatedIndex (n + 1), 1)) (x : (V.mixedPairModels k).Space) :
    (V.mixedOriginalPairComparisonTests a b k).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (V.mixedOriginalPairFrequencies k) z.coord : ℝ) :
          CircleFourier.Circle) * (V.mixedOriginalPairComparisonTests a b k).observable x := by
  cases k with
  | none => exact Niltest.oneOnOrbit_vertical _ z x
  | some k =>
    fin_cases k
    · exact W.mixedPairComponent_vertical a id z hz x
    · exact Niltest.conjugate_vertical _ _ (W.mixedPairComponent_vertical b (mixedExchangeCoordinate n)) z hz x

end NativeSampleCorrelation

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

def HasMixedPairFrozenEquivalence (u b : ℝ) : Prop :=
  ∀ den : ℕ, 0 < den → (den : ℝ) ≤ Real.exp u →
    ∀ a r : (pi V.mixedPairModels).RealGroup,
      (∀ i, |((pi V.mixedPairModels).basis.baseChange ℝ).repr a.coord i| ≤ Real.exp u) →
      ((pi V.mixedPairModels).basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid den →
      NativeIntegerVectorEquivalence (n + 1) b (R.mixedPairFrozenVector 0 a r) (R.mixedPairFrozenVector 1 a r)

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedRootCyclicComparison
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem mixedWrappedDiagonalCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (MixedNonconstantCorner s → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
        F a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : MixedNonconstantCorner s → Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedWrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) *
          star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
        W.mixedWrappedDiagonalCorrection N F a b (fun z => ((x z).val : ℤ))‖) ≤ W.outputDim * ε := by
  have hpoint (x : Fin 2 → ℤ) :
      ‖W.mixedWrappedDiagonalDerivative N a x * star (W.mixedCanonicalTensor b x) -
        W.mixedWrappedDiagonalCorrection N F a b x‖ ≤
      ∑ k, ‖W.mixedDiagonalDerivative (a.1, k) x * star (W.mixedCanonicalTensor b x) -
        F (a.1, k) b x‖ := by
    have heq : W.mixedWrappedDiagonalDerivative N a x * star (W.mixedCanonicalTensor b x) -
        W.mixedWrappedDiagonalCorrection N F a b x =
        ∑ k, W.mixedDiagonalWrapCoefficient N a.2 k x *
          (W.mixedDiagonalDerivative (a.1, k) x * star (W.mixedCanonicalTensor b x) -
            F (a.1, k) b x) := by
      rw [W.mixedWrappedDiagonalDerivative_resolution, Finset.sum_mul]
      simp only [mixedWrappedDiagonalCorrection, mul_sub, Finset.sum_sub_distrib, mul_assoc]
    rw [heq]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k _
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (W.mixedDiagonalWrapCoefficient_norm N a.2 k x)
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N,
        ∑ k, ‖W.mixedDiagonalDerivative (a.1, k) (fun z => ((x z).val : ℤ)) *
            star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
          F (a.1, k) b (fun z => ((x z).val : ℤ))‖ :=
      Finset.expect_le_expect (fun x _ => hpoint _)
    _ = ∑ k, 𝔼 x : Fin 2 → ZMod N,
        ‖W.mixedDiagonalDerivative (a.1, k) (fun z => ((x z).val : ℤ)) *
            star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
          F (a.1, k) b (fun z => ((x z).val : ℤ))‖ := Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _k : Fin W.outputDim, ε := Finset.sum_le_sum (fun k _ => herr (a.1, k) b)
    _ = _ := by simp

theorem mixedCyclicDiagonalCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (δ : ℝ≥0) (hδ : 0 < δ)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (MixedNonconstantCorner s → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
        F a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : MixedNonconstantCorner s → Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedCyclicDiagonalDerivative a x * star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
        W.mixedCyclicDiagonalCorrection N δ F a b (fun z => ((x z).val : ℤ))‖) ≤
      (W.outputDim + 1) * ε + 12 * (δ : ℝ) + 2 / N := by
  have hpoint (x : Fin 2 → ZMod N) := norm_smoothed_branch_error
    (cyclicCarry (x 0) (x 1)) (smoothCyclicCarry N δ (fun z => ((x z).val : ℤ)))
    (circleCarryCutoff_range δ _)
    (W.mixedDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
      star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))))
    (W.mixedWrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) *
      star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))))
    (F a b (fun z => ((x z).val : ℤ)))
    (W.mixedWrappedDiagonalCorrection N F a b (fun z => ((x z).val : ℤ)))
    (by
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (W.mixedDiagonalDerivative_norm a _)).trans (W.mixedCanonicalTensor_norm b _))
    (by
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (W.mixedWrappedDiagonalDerivative_norm N a _)).trans (W.mixedCanonicalTensor_norm b _))
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun x _ => hpoint x)
  simp only [Complex.ofReal_sub, Complex.ofReal_one, ← mul_assoc, ← add_mul,
    ← W.mixedCyclicDiagonalDerivative_branches] at hm
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect] at hm
  have hi := herr a b
  have hw := W.mixedWrappedDiagonalCorrection_mean_error F herr a b
  have hc := smoothCyclicCarry_mean_error (N := N) δ hδ
  dsimp only [mixedCyclicDiagonalCorrection]
  exact hm.trans ((add_le_add (add_le_add hi hw)
    (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2))).trans_eq (by ring))

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem mixedRootCyclicCorrection_mean_error {N : ℕ} [NeZero N] (δ : ℝ≥0) (hδ : 0 < δ)
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim)
    (b : MixedNonconstantCorner s → Fin W.mixedIntegrationRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedIntegrationRoot.mixedCyclicDiagonalDerivative a x *
          star (W.mixedIntegrationRoot.mixedCanonicalTensor b (fun k => ((x k).val : ℤ))) -
        W.mixedRootCyclicCorrection N δ G a b (fun k => ((x k).val : ℤ))‖) ≤
      (W.mixedIntegrationRoot.outputDim + 1) *
        ((mixedRootCornerCoefficient s : ℝ) * (W.outputDim : ℝ) ^ mixedRootCornerExponent s * ε) +
          12 * (δ : ℝ) + 2 / N :=
  W.mixedIntegrationRoot.mixedCyclicDiagonalCorrection_mean_error δ hδ (W.mixedRootCornerCorrection G)
    (W.mixedRootCornerCorrection_mean_error_power G hε hG herr) a b

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticCyclicIntegration
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

namespace NativeMultidegreeNilcharacter

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_quadratic_diagonal_niltest {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (i : Fin W.outputDim) :
    ∃ T : W.model.Niltest (fun _ : Unit => 1), T.normBound = 1 ∧ T.ComplexityLE (p + 4) ∧
      ∀ n : ℤ, T.eval (fun _ => n) = W.eval i (fun _ => n) := by
  obtain ⟨T, hT, hcomplexity, heval⟩ := W.exists_linear_niltest i
    (fun _ => { toFun := fun x : Unit → ℤ => x (), map_zero' := rfl, map_add' := fun _ _ => rfl })
  exact ⟨T, hT, hcomplexity, fun n => heval (fun _ => n)⟩

end NativeMultidegreeNilcharacter

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedPairCoordinateTest
namespace OAI

section

namespace Erdos3.NativeSampleCorrelation

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {n m : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ))))

noncomputable def mixedPairCoordinateTests (k : Fin 2) (out : Fin W.outputDim) :
    ∀ l, (V.mixedPairModels l).Niltest (fun _ : Fin (n + 2) => 1)
  | none => (V.test.raiseStep (by rw [mixedReplicated_totalDegree]; omega :
      n + 1 ≤ ∑ _ : MixedReplicatedIndex (n + 1), 1)).oneOnOrbit
  | some l =>
      ![![W.mixedPairComponent out id, (W.mixedPairComponent out (mixedExchangeCoordinate n)).oneOnOrbit],
        ![(W.mixedPairComponent out id).oneOnOrbit, W.mixedPairComponent out (mixedExchangeCoordinate n)]] k l

end Erdos3.NativeSampleCorrelation

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.QuadraticPrimitiveNiltest
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_quadratic_primitive_niltest_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p,
      ∀ i : Fin W.outputDim, ∀ χ : AddChar (ZMod N) ℂ,
      (fun n : ZMod N => star (W.eval i (fun _ => (n.val : ℤ))) * χ n) ∈
        nativeCyclicFunctions 2 N ((p + C) ^ C) := by
  obtain ⟨A, _, hproduct⟩ := exists_productNiltestBudget_bound
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + 216 + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp W i χ
  obtain ⟨T, hTnorm, hT, hTeval⟩ := W.exists_quadratic_diagonal_niltest i
  obtain ⟨U, hUnorm, hU, hUeval⟩ := exists_cyclic_character_niltest χ
  let hdegree : 1 ≤ 2 := by omega
  let r := p + 216
  have hr : 0 ≤ r := by dsimp [r]; linarith
  let K : Bool → Type := BoolLieFamily W.L (RationalTorus.Algebra 1)
  let dims : Bool → ℕ := fun b => Bool.rec 1 W.dim b
  let models : ∀ b, RationalFilteredNilmanifold (K b) 2 (dims b) := fun b => by
    cases b
    · exact (RationalTorus.nilmanifold 1).raiseStep hdegree
    · exact W.model
  let tests : ∀ b, (models b).Niltest (fun _ : Unit => 1) := fun b => by
    cases b
    · exact U.raiseStep hdegree
    · exact T.conjugate
  have htests : ∀ b, (tests b).ComplexityLE r := by
    intro b
    cases b
    · apply (U.raiseStep_complexity hdegree (by norm_num) hU).mono
      dsimp [raisedNiltestBudget, r]
      linarith
    · exact hT.mono (by dsimp [r]; linarith)
  have hcap : ∀ b, (tests b).normBound ≤ 1 := by
    intro b
    cases b
    · exact hUnorm
    · exact hTnorm.le
  have hcard : (Fintype.card Bool : ℝ) ≤ r := by
    simp only [Fintype.card_bool, Nat.cast_ofNat]
    dsimp [r]
    linarith
  let : FiniteDimensional ℚ (∀ b, K b) :=
    (RationalFilteredNilmanifold.productFinBasis models).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ b, K b))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ b, K b)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ b, K b)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis models)
  let S := RationalFilteredNilmanifold.unitBoundedPiNiltest models tests hr hcard htests hcap
  have hcost : productNiltestBudget r ≤ (p + C) ^ C := by
    apply (hproduct r hr).trans
    simpa [r, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨{
    L := ∀ b, K b
    dim := _
    model := RationalFilteredNilmanifold.pi models
    test := S
    norm := le_rfl
    complexity := (RationalFilteredNilmanifold.unitBoundedPiNiltest_complexity
      models tests hr hcard htests hcap).mono hcost
    eval := ?_ }⟩
  intro n
  change _ = S.eval (fun _ => (n.val : ℤ))
  rw [RationalFilteredNilmanifold.unitBoundedPiNiltest_eval, Fintype.prod_bool]
  change _ = star (T.eval (fun _ => (n.val : ℤ))) *
    (U.raiseStep hdegree).eval (fun _ => (n.val : ℤ))
  rw [hTeval, RationalFilteredNilmanifold.Niltest.raiseStep_eval]
  change _ = star (W.eval i (fun _ => (n.val : ℤ))) * U.evalCyclic N (fun _ => n)
  rw [hUeval]

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastPreparedScaleBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

noncomputable def preparedSamplerTransverse (j : Fin m) : ℕ :=
  finrank ℝ (euclideanSubspace (L j).space)ᗮ

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

abbrev AllocatedCongruenceCoefficientIndex (X : Type*) (E : Fin m → Type*)
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :=
  Σ j : Fin m, AllocatedCongruenceRankOutput X E inactive j × Fin L

end Erdos3.VectorPolynomial

end

end OAI
end


