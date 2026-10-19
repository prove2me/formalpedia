-- Prove2me | Definitions.Def_OAIE3v2B253
-- name    : OAIE3v2B253
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T05:36:48.317713+00:00
-- url     : https://prove2.me/theorems/3f5b72bb-be69-4cbb-b4ae-42e9c704ee96
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 259 of 311
-- statement:
--   Definitions bundle 259 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B237`, `OAIE3v2B239`, `OAIE3v2B240`, `OAIE3v2B241`, `OAIE3v2B242`, `OAIE3v2B245`, `OAIE3v2B246` of this split.
--
--   Modules: `Estimates/AllocatedCenteredNarrowPrescribedMarginal.lean`, `Estimates/AllocatedExternalCandidateKeptSymbolFactors.lean`, `Estimates/AllocatedExternalCandidateRefinementLabels.lean`, `Estimates/AntisymmetricPairVerticalModel.lean`, `Estimates/CorrelatingVerticalPair.lean`, `Estimates/DiagonalRowTransfer.lean`, `Estimates/MixedPairComparison.lean`, `Estimates/MixedPairFrozenEquivalence.lean`, `Estimates/MixedPairPartitionPrecision.lean`, `Estimates/MixedPreciseSampledExchange.lean`, `Estimates/NativeAbsorbedIntervals.lean`, `Estimates/NativeMultilinearQuadruples.lean`, `Estimates/NativeRetainedInverseIntervals.lean`, `Estimates/NativeSeparatedSumIntervals.lean`, `Estimates/QuadraticPairCorrelator.lean`, `Estimates/QuadraticPairStepDrop.lean`, `Estimates/SampledNativeDetectionEmptyTags.lean`, `Lattices/NativeRetainedIntegerMultilinearQuadruples.lean`, `Linear/AllocatedCenteredMeasurableFramedBadTail.lean`, `Linear/AllocatedShortRankWitnessWidth.lean`, `Polynomial/DegreeRankNativeInverseModels.lean`, `Probability/PreparedCommonRadiusDensityCapNested.lean`, `Sampling/AllocatedExternalCandidateSamplerFacts.lean`, `Sampling/ForecastPreparedScaleBudget.lean`, `Sampling/PreparedActualForecastSetup.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B237
import Definitions.Def_OAIE3v2B239
import Definitions.Def_OAIE3v2B240
import Definitions.Def_OAIE3v2B241
import Definitions.Def_OAIE3v2B242
import Definitions.Def_OAIE3v2B245
import Definitions.Def_OAIE3v2B246

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMultilinearQuadruples
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff
  NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_weighted_multilinear_correlation_with_equivalence (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        NativeIntegerVectorEquivalence s ((p + C) ^ C) W.mixed.eval
          (fun k x => V.eval k (fun j => x j.1)) ∧
        ∃ (k : Fin V.outputDim) (i : Fin W.family.outputDim) (weight : ZMod N → ℂ)
          (H : Finset (ZMod N)), (∀ x, ‖weight x‖ ≤ 1) ∧ H ⊆ W.shifts ∧ H.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
          ∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N ((p + C) ^ C)
            (fun _ : Unit => fun x => multiplicativeDerivative f h x * star
              ((V.eval k (fun j => correlationInput (h.val : ℤ) (x.val : ℤ) j.1) *
                W.family.evalCyclic N i h x) * weight x))) := by
  obtain ⟨a, _, hmulti⟩ := exists_fixed_multilinearized_correlation s
  obtain ⟨c, _, hsplit⟩ := exists_split_global_error s
  let X : Polynomial ℕ := Polynomial.X
  let Q₀ := (X + Polynomial.C a) ^ a
  let B₀ := 2 * X + 3 * Q₀ + 3
  let R₀ := (B₀ + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (4 * X + 4 * Q₀ + R₀ + 4)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  let q := (p + a) ^ a
  let b := 2 * p + 3 * q + 3
  let R := (b + c) ^ c
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hb : 2 ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hpb : p ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hqb : q ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hcb : p + 2 * q ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hpoly : 4 * p + 4 * q + R + 4 ≤ (p + C) ^ C := by
    simpa [X, Q₀, B₀, R₀, q, b, R, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hp, hq, hR, hpoly]
  have hRC : R ≤ (p + C) ^ C := by linarith only [hp, hq, hR, hpoly]
  have hdenseC : 3 * p + 2 * q + R ≤ (p + C) ^ C := by linarith only [hp, hq, hR, hpoly]
  obtain ⟨V, hdim, hsymm, E, j, k, z, i, H, hsub, hH, hdense, hcorr⟩ := hmulti W
  let T := (E.selectedExpansion j k).test z
  let m (h x : ZMod N) :=
    V.eval k (fun l => correlationInput (h.val : ℤ) (x.val : ℤ) l.1) *
      W.family.evalCyclic N i h x
  have hm (h x : ZMod N) : ‖m h x‖ ≤ 1 := by
    dsimp only [m]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (V.norm_eval k _)).trans
      (W.family.norm_eval i h (x.val : ℤ))
  have hinput (h n : ℤ) : correlationInput h n = ![h, n] := by
    funext t
    fin_cases t <;> rfl
  have hcor' (h : ZMod N) (hh : h ∈ H) : Real.exp (-b) ≤
      ‖𝔼 x, multiplicativeDerivative f h x * star
        (m h x * (W.selectedWitness ⟨h, hsub hh⟩).test.evalCyclic N (fun _ => x) *
          T.eval ![(h.val : ℤ), (x.val : ℤ)])‖ := by
    obtain ⟨hh', _, hc⟩ := hcorr h hh
    apply (Real.exp_le_exp.mpr (neg_le_neg hcb)).trans
    simpa only [m, T, hinput] using hc
  obtain ⟨weight, S, hweight, hSH, hS, hsize, hnew⟩ := hsplit W T b hb hpb
    (((E.selectedExpansion j k).complexity z).mono hqb) H hsub hH m hm hf hcor'
  have htotal : Real.exp (-(3 * p + 2 * q + R)) * Fintype.card (ZMod N) ≤ (S.card : ℝ) := by
    calc
      _ = Real.exp (-R) * (Real.exp (-(3 * p + 2 * q)) * Fintype.card (ZMod N)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-R) * (H.card : ℝ) := mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  refine ⟨V.mono hqC, hdim, hsymm, E.mono hqC, k, i, weight, S, hweight, hSH.trans hsub, hS, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hdenseC))
      (Nat.cast_nonneg _)).trans htotal
  · intro h hh
    obtain ⟨Z⟩ := hnew h hh
    exact ⟨Z.mono hRC⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_multilinear_quadruples_with_equivalence (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        NativeIntegerVectorEquivalence s ((p + C) ^ C) W.mixed.eval
          (fun k x => V.eval k (fun j => x j.1)) ∧
        ∃ (k : Fin V.outputDim) (i : Fin W.family.outputDim) (weight : ZMod N → ℂ)
          (H : Finset (ZMod N)), (∀ x, ‖weight x‖ ≤ 1) ∧ H ⊆ W.shifts ∧ H.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
          ∃ U : NativeCrossWitnesses (s - 1) N ((p + C) ^ C)
              (fun x => f x * star (weight x)) f
              (fun h x => V.eval k (fun j => correlationInput (h.val : ℤ) (x.val : ℤ) j.1) *
                W.family.evalCyclic N i h x) H,
            ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
              Real.exp (-((p + C) ^ C)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
              ∀ t ∈ Q, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H ∧
                Real.exp (-((p + C) ^ C)) ≤
                  additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2 := by
  obtain ⟨a, _, hweighted⟩ := exists_weighted_multilinear_correlation_with_equivalence s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (13 * (X + Polynomial.C a) ^ a + 2)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hQbudget : 13 * q + 2 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hq, hQbudget]
  obtain ⟨V, hdim, hsymm, E, k, i, weight, H, hweight, hsub, hH, hdense, hcorr⟩ := hweighted W hf
  let f₀ (x : ZMod N) := f x * star (weight x)
  let m (h x : ZMod N) := V.eval k (fun j => correlationInput (h.val : ℤ) (x.val : ℤ) j.1) *
    W.family.evalCyclic N i h x
  have hf₀ (x : ZMod N) : ‖f₀ x‖ ≤ 1 := by
    simp only [f₀, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf x)).trans (hweight x)
  have hm (h x : ZMod N) : ‖m h x‖ ≤ 1 := by
    simp only [m, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (V.norm_eval k _)).trans
      (W.family.norm_eval i h (x.val : ℤ))
  have hc (h : H) : Nonempty (NativeVectorCorrelation (s - 1) N q (nativeCrossResidual f₀ f m h.val)) := by
    obtain ⟨R⟩ := hcorr h.val h.property
    refine ⟨{ R with correlation := ?_ }⟩
    simpa only [nativeCrossResidual, f₀, m, multiplicativeDerivative, star_mul,
      mul_assoc, mul_left_comm, mul_comm] using R.correlation
  let U : NativeCrossWitnesses (s - 1) N q f₀ f m H := fun h => Classical.choice (hc h)
  obtain ⟨Q, hQ, hsize, hquad⟩ := U.exists_quadruples_budget hH hf₀ hf hm hdense
  refine ⟨V.mono hqC, hdim, hsymm, E.mono hqC, k, i, weight, H, hweight, hsub, hH, ?_, U.mono hqC,
    Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hQbudget))
      (by positivity)).trans hsize
  · intro t ht
    obtain ⟨h₁, h₂, h₃, h₄, hcor⟩ := hquad t ht
    refine ⟨h₁, h₂, h₃, h₄, ?_⟩
    change Real.exp (-((p + C) ^ C)) ≤ additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2
    exact (Real.exp_le_exp.mpr (neg_le_neg hQbudget)).trans hcor

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeRetainedIntegerMultilinearQuadruples
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_integer_multilinear_quadruples_with_equivalence (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        NativeIntegerVectorEquivalence s ((p + C) ^ C) W.mixed.eval
          (fun k x => V.eval k (fun j => x j.1)) ∧
        ∃ (k : Fin V.outputDim) (i : Fin W.family.outputDim) (weight : ZMod N → ℂ)
          (H : Finset (ZMod N)), (∀ x, ‖weight x‖ ≤ 1) ∧ H ⊆ W.shifts ∧ H.Nonempty ∧
          CyclicShortShiftSet H ∧
          Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
          ∃ U : NativeCrossWitnesses (s - 1) N ((p + C) ^ C)
              (fun x => f x * star (weight x)) f
              (fun h x => W.multilinearFactor V k i h x.val) H,
            ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
              Real.exp (-((p + C) ^ C)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
              ∀ t ∈ Q, ∃ (h₁ : t.2.1 ∈ H) (h₂ : t.2.1 - t.1 ∈ H)
                (h₃ : t.2.2 ∈ H) (h₄ : t.2.2 - t.1 ∈ H),
                -(t.2.1.val : ℤ) + (t.2.1 - t.1).val + t.2.2.val - (t.2.2 - t.1).val = 0 ∧
                Real.exp (-((p + C) ^ C)) ≤
                  additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2 ∧
                ∃ (branch : Bool) (c len : ℕ), 0 < len ∧ c + len ≤ N ∧
                  2 * ((len : ℤ) - 1) < N ∧
                  Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n ∈ Finset.Ico (c : ℤ) (c + len),
                    fourPointProduct
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.1, h₁⟩)
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.1 - t.1, h₂⟩)
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.2, h₃⟩)
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.2 - t.1, h₄⟩)
                      (cyclicBranchOffset t.1 branch) n‖ ∧
                  Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N := by
  obtain ⟨a, _, hmulti⟩ := exists_multilinear_quadruples_with_equivalence s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (17 * (X + Polynomial.C a) ^ a + 20)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : 17 * q + 20 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hq, hcost]
  have hHC : q + 1 ≤ (p + C) ^ C := by linarith only [hq, hcost]
  have hQC : 13 * (q + 1) + 2 ≤ (p + C) ^ C := by linarith only [hq, hcost]
  have hIC : 13 * (q + 1) + 2 + 4 * q + 5 ≤ (p + C) ^ C := by linarith only [hcost]
  obtain ⟨V, hdim, hsymm, E, k, i, weight, H, hweight, hsub, hH, hdense, U, _⟩ := hmulti W hf
  let M := W.multilinearFactor V k i
  have hm (h x : ZMod N) : ‖M h x.val‖ ≤ 1 := by
    dsimp only [M, NativeCorrelationStructure.multilinearFactor]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (V.norm_eval k _)).trans
      (W.family.norm_eval i h (x.val : ℤ))
  have hf₀ (x : ZMod N) : ‖f x * star (weight x)‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf x)).trans (hweight x)
  obtain ⟨S, hSH, hS, hshort, hSsize, Q, hQ, hQsize, hquad⟩ :=
    U.exists_short_quadruples hH hf₀ hf hm hdense
  refine ⟨V.mono hqC, hdim, hsymm, E.mono hqC, k, i, weight, S, hweight,
    fun x hx => hsub (hSH hx), hS, hshort, ?_, (U.restrict hSH).mono hqC, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hHC))
      (Nat.cast_nonneg _)).trans hSsize
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hQC))
      (by positivity)).trans hQsize
  · intro t ht
    obtain ⟨h₁, h₂, h₃, h₄, hrel, hc⟩ := hquad t ht
    obtain ⟨branch, c, len, hlen, hN, hlenShort, hcor, hvol⟩ :=
      U.exists_integer_quadruple_interval_budget M (fun _ _ => rfl) hm
        t.1 t.2.1 t.2.2 (hSH h₁) (hSH h₂) (hSH h₃) (hSH h₄) hc
    refine ⟨h₁, h₂, h₃, h₄, hrel, ?_, branch, c, len, hlen, hN, hlenShort, ?_, ?_⟩
    · change Real.exp (-((p + C) ^ C)) ≤
        additiveQuadrupleCorrelation (U.restrict hSH).extension t.1 t.2.1 t.2.2
      rw [U.restrict_quadruple hSH t.1 t.2.1 t.2.2 h₁ h₂ h₃ h₄]
      exact (Real.exp_le_exp.mpr (neg_le_neg hQC)).trans hc
    · change Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n ∈ Finset.Ico (c : ℤ) (c + len),
        fourPointProduct (U.integerProduct M ⟨t.2.1, hSH h₁⟩)
          (U.integerProduct M ⟨t.2.1 - t.1, hSH h₂⟩)
          (U.integerProduct M ⟨t.2.2, hSH h₃⟩)
          (U.integerProduct M ⟨t.2.2 - t.1, hSH h₄⟩) (cyclicBranchOffset t.1 branch) n‖
      exact (Real.exp_le_exp.mpr (neg_le_neg hIC)).trans hcor
    · exact (Real.exp_le_exp.mpr (neg_le_neg hIC)).trans hvol

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeAbsorbedIntervals
namespace OAI

section

namespace Erdos3

theorem exists_native_retained_multilinear_interval_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      Nonempty (NativeRetainedMultilinearIntervalFamily W ((p + C) ^ C)) := by
  obtain ⟨C, hC, hquad⟩ := exists_integer_multilinear_quadruples_with_equivalence s
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  obtain ⟨V, hdim, hsymm, E, k, i, weight, H, hweight, hsub, hH, hshort,
    hHsize, U, Q, hQ, hQsize, hinterval⟩ := hquad W hf
  classical
  have hdata (t : Q) := hinterval t.val t.property
  choose h₁ h₂ h₃ h₄ hrel hcyclic branch c len hlen hN hlenShort hcor hvol using hdata
  exact ⟨{
    mixed := V
    mixed_dim := hdim
    mixed_symmetric := hsymm
    equivalence := E
    coordinate := k
    rankCoordinate := i
    weight := weight
    weight_norm := hweight
    shifts := H
    shifts_subset := hsub
    shifts_nonempty := hH
    shifts_short := hshort
    shifts_density := hHsize
    lower := U
    quadruples := Q
    quadruples_nonempty := hQ
    quadruples_density := hQsize
    interval := fun t => {
      first_mem := h₁ t
      second_mem := h₂ t
      third_mem := h₃ t
      fourth_mem := h₄ t
      integer_relation := hrel t
      cyclic_correlation := hcyclic t
      branch := branch t
      start := c t
      length := len t
      length_pos := hlen t
      endpoint_le := hN t
      length_short := hlenShort t
      correlation := hcor t
      length_ratio := hvol t } }⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DegreeRankNativeInverseModels
namespace OAI

section

namespace Erdos3

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

theorem exists_degree_rank_native_inverse_models {s C : ℕ} (hI : CyclicNativeInverse s C) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 2) f →
      ∃ B : NativeCommonDerivativeModels s N ((p + D) ^ D) f,
        Nonempty (NativeDegreeRankDerivativeData B s ((p + D) ^ D)) := by
  obtain ⟨a, _, hmodels⟩ := exists_unit_vertical_native_inverse_models hI
  obtain ⟨b, _, hrank⟩ := RationalFilteredNilmanifold.exists_native_degree_rank_structure s
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget (P + (P + Polynomial.C b) ^ b)
  refine ⟨D, hD, ?_⟩
  intro N _ p hp f hf hG
  have hq : 0 ≤ (p + a) ^ a := by positivity
  have ht : 0 ≤ ((p + a) ^ a + b) ^ b := by positivity
  have hcost : (p + a) ^ a + ((p + a) ^ a + b) ^ b ≤ (p + D) ^ D := by
    simpa [P, X, Polynomial.eval₂_pow] using hbudget p hp
  have hqD : (p + a) ^ a ≤ (p + D) ^ D := by linarith
  have htD : ((p + a) ^ a + b) ^ b ≤ (p + D) ^ D := by linarith
  obtain ⟨B, V, ⟨U⟩⟩ := hmodels hp f hf hG
  obtain ⟨R, _, hR⟩ := hrank B.model hq B.geometry
  refine ⟨B.mono hqD, ⟨{
    vertical := V.mono hqD
    unit := U.mono hqD hqD
    rank := R
    complexity := hR.mono R htD
  }⟩⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticPairCorrelator
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_antisymmetric_pair_correlation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
        {N : ℕ} [NeZero N] (i j : Fin W.outputDim),
      Real.exp (-p) ≤ (finiteBoxCorrelation (fun x y : ZMod N =>
        star (W.evalCyclic N i (correlationInput x y)) *
          W.evalCyclic N j (correlationInput y x))).re →
      Nonempty (NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 ((p + C) ^ C)
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))) := by
  obtain ⟨A, _, hanchor⟩ := NativeMultidegreeNilcharacter.exists_antisymmetric_anchor_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + (X + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p hp W N _ i j hbox
  let K (x y : ZMod N) := W.antisymmetricKernel i j (x.val : ℤ) (y.val : ℤ)
  have hbias : Real.exp (-p) ≤ (finiteBoxCorrelation K).re := by
    simpa only [K, W.antisymmetricKernel_cyclic] using hbox
  obtain ⟨a, ha⟩ := exists_box_anchor_correlation K
  obtain ⟨E⟩ := hanchor W i j (fun k => ((a k).val : ℤ))
  have hcorr : Real.exp (-p) ≤ ‖𝔼 z : Fin 2 → ZMod N,
      W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ) *
        star (star (boxAnchorFactor (W.antisymmetricKernel i j)
          (fun k => ((a k).val : ℤ)) (fun k => ((z k).val : ℤ))))‖ := by
    simpa only [K, boxAnchorFactor, star_star] using hbias.trans ha
  obtain ⟨V⟩ := NativeSampleCorrelation.exists_of_expansion E.conjugate hp hcorr
  have hcost : p + (p + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨V.mono hcost⟩

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

theorem exists_antisymmetric_pair_frozen_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r u : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r)
      [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
      [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)],
      0 ≤ r → 0 ≤ u → R.HasPairFrozenEquivalence u ((p + q + r + u + C) ^ C) := by
  obtain ⟨a, _, hfrozen⟩ := exists_native_frozen_middle_expansion 1
  let X : Polynomial ℕ := Polynomial.X
  let B := X + (X + (X + 2) ^ 2 + 3) + 4
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r u W N _ i j V R _ _ _ _ hr hu m hm hmb left right hleft hright
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r + u
  let b := v + raisedNiltestBudget v + 4
  let t := productNiltestBudget b + v + 2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hpqv : p + q ≤ v := by dsimp [v]; linarith
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, v]; linarith
  have hut : u ≤ t := by dsimp [t, v]; linarith
  have hpt : p ≤ t := by dsimp [t, v]; linarith
  have hBt : antisymmetricPairBudget p q ≤ b := by
    dsimp [antisymmetricPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ antisymmetricPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le
  have hprodmono : productNiltestBudget (antisymmetricPairBudget p q) ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    gcongr
  have htest : productNiltestBudget (antisymmetricPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hsum : t + (t + a) ^ a ≤ (p + q + r + u + C) ^ C := by
    simpa [X, B, T, t, b, v, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget v hv
  have htC : t ≤ (p + q + r + u + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hcost : (t + a) ^ a ≤ (p + q + r + u + C) ^ C :=
    (le_add_of_nonneg_left ht).trans hsum
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp ((p + q + r + u + C) ^ C) := by
    simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr (hpt.trans htC))
  refine ⟨hdim, hdim, ?_⟩
  intro out₀ out₁
  have hN : ∀ _k : Fin 2, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨F⟩ := hfrozen (pi V.antisymmetricPairModels) (R.mono hrt hN)
    (V.pairComparisonNiltest out₀ out₁) ht ((V.pairComparisonNiltest_complexity out₀ out₁).mono htest)
    (R.pair_comparison_invariant out₀ out₁) m hm (hmb.trans (Real.exp_le_exp.mpr hut)) left right
    (fun k => (hleft k).trans (Real.exp_le_exp.mpr hut)) hright
  have hF : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
      ((p + q + r + u + C) ^ C) (fun x =>
        star ((V.pairComparisonNiltest out₀ out₁).observable
          (QuotientGroup.mk (R.frozenMiddleValue left right x))))) :=
    ⟨F.conjugate.mono hcost⟩
  simpa only [V.pairComparisonNiltest_observable, star_mul, star_star,
    NativePolynomialOrbitFactors.pairFrozenVector, mul_comm] using hF

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPairComparison
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_mixed_pair_orbit_factors (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (_F : NativeMixedPairFactorization V r), 0 ≤ r →
      Real.exp ((p + q + r + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) ((p + q + r + C) ^ C)) := by
  obtain ⟨a, _, hconstruct⟩ := exists_native_polynomial_orbit_factors
    (∑ _ : MixedReplicatedIndex (n + 1), 1)
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + Polynomial.C (n + 2)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j V F hr hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let u := p + q + r
  let b := 4 * (u + 1) + raisedNiltestBudget u + 6
  let t := productNiltestBudget b + u + ((n + 2 : ℕ) : ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpqu : p + q ≤ u := le_add_of_nonneg_right hr
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hdim : (0 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, u]; linarith
  have hdimt : ((n + 2 : ℕ) : ℝ) ≤ t := by dsimp [t]; linarith
  have hBt : mixedPairBudget p q ≤ b := by
    dsimp [mixedPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ mixedPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le
  have hprodmono : productNiltestBudget (mixedPairBudget p q) ≤ productNiltestBudget b := by
    exact productNiltestBudget_mono hB0 hBt
  have htest : productNiltestBudget (mixedPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hcost : (t + a) ^ a ≤ (p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  let := F.topology
  let := F.topologicalAdd
  let := F.continuousSMul
  let := F.hausdorff
  let D := pi V.mixedPairModels
  have hfactor : D.filtration.ControlledSymbolFactorization F.basis F.weight F.adapted
      (piFrequency V.mixedPairFrequencies) (fun _ : Fin (n + 2) => (N : ℝ))
      (D.filtration.realPolynomialSymbolHom F.basis F.weight F.adapted
        (fun _ => 1) V.mixedPairPolynomial) t := by
    have h := F.factorization
    rw [V.mixedPairNiltest_symbol] at h
    have H := NilpotentLieFiltration.ControlledSymbolFactorization.mono
      (pi V.mixedPairModels).filtration F.basis F.weight F.adapted h hrt
      (fun _ => by exact_mod_cast NeZero.pos N)
    dsimp only [D]
    exact H
  obtain ⟨R⟩ := hconstruct D F.basis F.weight F.adapted ht
    (V.mixedPairNiltest_complexity.1.mono D htest) (by simpa only [Fintype.card_fin] using hdimt)
    (fun a b => (F.height a b).trans hrt) V.mixedPairPolynomial
    (piFrequency V.mixedPairFrequencies) (fun _ : Fin (n + 2) => (N : ℝ))
    (fun _ => (Real.exp_le_exp.mpr hcost).trans hN) hfactor
  exact ⟨R.mono hcost (fun _ => by exact_mod_cast NeZero.pos N)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeRetainedInverseIntervals
namespace OAI

section

namespace Erdos3

theorem exists_initial_native_correlation_structure {s C : ℕ} (hI : CyclicNativeInverse s C) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 2) f →
      Nonempty (NativeCorrelationStructure s s N ((p + D) ^ D) f) := by
  obtain ⟨a, _, hmodels⟩ := exists_degree_rank_native_inverse_models hI
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + Polynomial.C 2)
  refine ⟨D, hD, ?_⟩
  intro N _ p hp f hf hG
  have hq : 0 ≤ (p + a) ^ a := by positivity
  have hcost : (p + a) ^ a + 2 ≤ (p + D) ^ D := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hqD : (p + a) ^ a ≤ (p + D) ^ D := by linarith
  obtain ⟨B, ⟨W⟩⟩ := hmodels hp f hf hG
  exact ⟨(W.mono le_rfl hqD).toCorrelationStructure (by linarith) (by linarith)⟩

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

theorem exists_antisymmetric_pair_frozen_reduction :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r), 0 ≤ r →
      R.HasPairFrozenReduction ((p + q + r + C) ^ C) := by
  obtain ⟨A, _, houter⟩ := exists_antisymmetric_pair_outer_control
  obtain ⟨B, _, hfrozen⟩ := exists_antisymmetric_pair_frozen_equivalence
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (X + U + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j V R hr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r
  let u := (v + A) ^ A
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsum : u + (v + u + B) ^ B ≤ (p + q + r + C) ^ C := by
    simpa [X, U, u, v, Polynomial.eval₂_pow] using hbudget v hv
  have huC : u ≤ (p + q + r + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hBC : (v + u + B) ^ B ≤ (p + q + r + C) ^ C :=
    (le_add_of_nonneg_left hu).trans hsum
  let : TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi V.antisymmetricPairModels).basis
  exact ⟨u, hu, huC, houter R hr,
    R.hasPairFrozenEquivalence_mono (hfrozen R hr hu) hBC⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_antisymmetric_pair_local_approximation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r), 0 ≤ r →
      R.HasPairLocalApproximation ((p + q + r + C) ^ C) := by
  obtain ⟨a, _, hcontrol⟩ := exists_native_orbit_local_control 2
  let X : Polynomial ℕ := Polynomial.X
  let B := X + (X + (X + 2) ^ 2 + 3) + 4
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j V R hr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let u := p + q + r
  let b := u + raisedNiltestBudget u + 4
  let t := productNiltestBudget b + u + 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpqu : p + q ≤ u := le_add_of_nonneg_right hr
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, u]; linarith
  have htwo : (Fintype.card (Fin 2) : ℝ) ≤ t := by norm_num; dsimp [t]; linarith
  have hBt : antisymmetricPairBudget p q ≤ b := by
    dsimp [antisymmetricPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ antisymmetricPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le
  have hprodmono : productNiltestBudget (antisymmetricPairBudget p q) ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    gcongr
  have htest : productNiltestBudget (antisymmetricPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hcost : t + (t + a) ^ a ≤ (p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  have hlocal : (t + a) ^ a ≤ (p + q + r + C) ^ C :=
    (le_add_of_nonneg_left ht).trans hcost
  let : TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi V.antisymmetricPairModels).basis
  let D := pi V.antisymmetricPairModels
  have hD : D.GeometryComplexityLE t :=
    (V.pairCoordinateNiltest_complexity 0 i).1.mono D htest
  have hN : ∀ _k : Fin 2, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨P, hP, hPb, hcosets, hmotion⟩ := hcontrol (R.mono hrt hN) ht hD htwo hN
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hlocal), ?_⟩
  intro y hy k out x δ hδ hx hres hnear
  let : MetricSpace (pi V.antisymmetricPairModels).RealGroup :=
    rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
      (D.basis.baseChange ℝ)
  have herror := R.pairFrozenVector_error k out x y (hcosets x y hres).1
  have hdist := hmotion x y δ hδ hx hy hnear
  apply herror.trans
  calc
    _ ≤ Real.exp t * (Real.exp ((t + a) ^ a) * δ) :=
      mul_le_mul (Real.exp_le_exp.mpr htest) hdist
        (@dist_nonneg D.RealGroup
          (rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
            (D.basis.baseChange ℝ)).toPseudoMetricSpace (R.slowValue x) (R.slowValue y))
        (Real.exp_nonneg t)
    _ = Real.exp (t + (t + a) ^ a) * δ := by rw [← mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcost) hδ

end Erdos3

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

theorem exists_antisymmetric_pair_local_partition (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b c t : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r),
      R.HasPairLocalApproximation b → R.HasPairFrozenReduction c →
      0 ≤ t → b ≤ t → c ≤ t → ∀ {ρ : ℝ}, 0 < ρ → 1 / ρ ≤ Real.exp ((t + 2) ^ a) →
      ∃ P : ℕ, ∃ hP : 0 < P,
        letI : NeZero P := ⟨hP.ne'⟩
        (P : ℝ) ≤ Real.exp ((t + C) ^ C) ∧
        ∃ n : ℕ, 0 < n ∧
          (Fintype.card (Fin 2 → Fin n × ZMod P) : ℝ) ≤ Real.exp ((t + C) ^ C) ∧
          ∃ A : (Fin n × ZMod P) → ZMod N → ℝ,
            (∀ j, PositiveCyclicNiltest.{0} 1 N ((t + C) ^ C) (A j)) ∧
            (∀ x, ∑ j, A j x = 1) ∧
            ∃ y : (Fin 2 → Fin n × ZMod P) → (Fin 2 → ZMod N),
              (∀ j, NativeIntegerVectorEquivalence 1 ((t + C) ^ C)
                (R.pairAnchoredVector (fun i => ((y j i).val : ℤ)) 0)
                (R.pairAnchoredVector (fun i => ((y j i).val : ℤ)) 1)) ∧
              ∀ (k : Fin 2) (out : Fin W.outputDim),
                (𝔼 x : Fin 2 → ZMod N,
                  ‖W.eval out (correlationInput ((x k).val : ℤ) ((x k.rev).val : ℤ)) -
                    ∑ j, ((∏ i, A (j i) (x i) : ℝ) : ℂ) * R.pairAnchoredVector
                      (fun i => ((y j i).val : ℤ)) k out (fun i => ((x i).val : ℤ))‖) ≤
                  Real.exp (t + 40) * (ρ + 1 / N) := by
  obtain ⟨B, _, hpartition⟩ := exists_interval_residue_partition a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + 40 + 2 * (X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r b c t W N _ i j V R hlocal hred ht hbt hct ρ hρ hprec
  obtain ⟨P, hP, hPb, hselect⟩ := R.select_pair_local_partition hlocal hred
  let : NeZero P := ⟨hP.ne'⟩
  have hPt : (P : ℝ) ≤ Real.exp t := hPb.trans (Real.exp_le_exp.mpr hbt)
  obtain ⟨n, hn, hcard, A, hA, hsum, hdiam⟩ := hpartition N P ht hPt hρ hprec
  have htotal : t + 40 + 2 * (t + B) ^ B ≤ (t + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget t ht
  have hpow : 0 ≤ (t + B) ^ B := by positivity
  have htC : t ≤ (t + C) ^ C := by linarith
  have hcost : (t + B) ^ B ≤ (t + C) ^ C := by linarith
  have htwo : 2 * (t + B) ^ B ≤ (t + C) ^ C := by linarith
  let w := productPartitionWeight (fun _ : Fin 2 => A)
  let E := cyclicWrapExceptional (0 : ZMod N) ρ
  have hnonneg : ∀ i j x, 0 ≤ (fun _ : Fin 2 => A) i j x :=
    fun _ j x => ((hA j).unit_interval x).1
  have hw : ∀ j x, 0 ≤ w j x := productPartitionWeight_nonneg _ hnonneg
  have hwSum : ∀ x, ∑ j, w j x = 1 := sum_productPartitionWeight _ (fun _ => hsum)
  have hcells : ∀ j x y, (∀ i, x i ∉ E) → (∀ i, y i ∉ E) → 0 < w j x → 0 < w j y →
      (∀ i, (P : ℤ) ∣ ((x i).val : ℤ) - (y i).val) ∧
      (∀ i, |((x i).val : ℝ) - (y i).val| ≤ (N : ℝ) * ρ) := by
    intro j x y hx hy hwx hwy
    have hposx := productPartitionWeight_pos_coordinate _ hnonneg j x hwx
    have hposy := productPartitionWeight_pos_coordinate _ hnonneg j y hwy
    exact ⟨fun i => (hdiam (j i) (x i) (y i) (hx i) (hy i) (hposx i) (hposy i)).2,
      fun i => (hdiam (j i) (x i) (y i) (hx i) (hy i) (hposx i) (hposy i)).1⟩
  obtain ⟨y, hequiv, herr⟩ := hselect E w hρ.le hw hwSum hcells
  refine ⟨P, hP, hPt.trans (Real.exp_le_exp.mpr htC), n, hn, ?_, A,
    fun j => (hA j).mono le_rfl hcost, hsum, y,
    fun j => (hequiv j).mono (hct.trans htC), ?_⟩
  · simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp ((t + B) ^ B)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
      _ = Real.exp (2 * (t + B) ^ B) := (Real.exp_nat_mul _ 2).symm
      _ ≤ _ := Real.exp_le_exp.mpr htwo
  · intro k out
    have hE := cyclicWrapExceptional_density_le (0 : ZMod N) hρ.le
    have hN : 0 ≤ (1 : ℝ) / N := one_div_nonneg.mpr (Nat.cast_nonneg N)
    have h40 : (40 : ℝ) ≤ Real.exp 40 := by linarith [Real.add_one_le_exp (40 : ℝ)]
    apply (herr k out).trans
    calc
      _ = Real.exp b * ρ + 4 * ((E.card : ℝ) / N) := by ring
      _ ≤ Real.exp t * ρ + 4 * (6 * ρ + 3 / N) := by gcongr
      _ ≤ Real.exp t * ρ + 4 * Real.exp t * (6 * ρ + 3 / N) := by
        gcongr
        nlinarith [Real.one_le_exp ht]
      _ = Real.exp t * (25 * ρ + 12 * (1 / N)) := by ring
      _ ≤ Real.exp t * (40 * (ρ + 1 / N)) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg t)
      _ = 40 * Real.exp t * (ρ + 1 / N) := by ring
      _ ≤ Real.exp 40 * Real.exp t * (ρ + 1 / N) := by gcongr
      _ = Real.exp (t + 40) * (ρ + 1 / N) := by rw [← Real.exp_add, add_comm 40 t]

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

theorem exists_antisymmetric_anchor_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r u : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r),
      0 ≤ r → 0 ≤ u → R.HasOuterValueControl u →
      ∀ y z : Fin 2 → ℤ, (∀ k, |(y k : ℝ)| ≤ (N : ℝ)) →
        (∀ k, |(z k : ℝ)| ≤ (N : ℝ)) → ∀ k l : Fin 2,
        NativeIntegerVectorEquivalence 1 ((p + q + r + u + C) ^ C)
          (R.pairAnchoredVector y k) (R.pairAnchoredVector z l) := by
  obtain ⟨A, _, hcomparison⟩ := exists_native_frozen_comparison 1
  let X : Polynomial ℕ := Polynomial.X
  let B := X + (X + (X + 2) ^ 2 + 3) + 4
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p q r u W N _ i j V R hr hu houter y z hy hz k l
  let := moduleTopology ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi V.antisymmetricPairModels).basis
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r + u
  let b := v + raisedNiltestBudget v + 4
  let t := productNiltestBudget b + v + 2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hpqv : p + q ≤ v := by dsimp [v]; linarith
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, v]; linarith
  have hut : u ≤ t := by dsimp [t, v]; linarith
  have hpt : p ≤ t := by dsimp [t, v]; linarith
  have hBt : antisymmetricPairBudget p q ≤ b := by
    dsimp [antisymmetricPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ antisymmetricPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le
  have hprodmono : productNiltestBudget (antisymmetricPairBudget p q) ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    gcongr
  have htest : productNiltestBudget (antisymmetricPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hsum : t + (t + A) ^ A ≤ (p + q + r + u + C) ^ C := by
    simpa [X, B, T, t, b, v, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget v hv
  have htC : t ≤ (p + q + r + u + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hcost : (t + A) ^ A ≤ (p + q + r + u + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp ((p + q + r + u + C) ^ C) := by
    simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr (hpt.trans htC))
  refine ⟨hdim, hdim, ?_⟩
  intro out₀ out₁
  obtain ⟨m, hm, hmb, hrat, hslow⟩ := houter
  have hN : ∀ _k : Fin 2, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  have hcap (k : Fin 2) (out : Fin W.outputDim) (x : (pi V.antisymmetricPairModels).Space) :
      ‖(V.pairCoordinateNiltest k out).observable x‖ ≤ 1 := by
    rw [V.pairCoordinateNiltest_observable]
    exact W.vertical.norm out _
  obtain ⟨E⟩ := hcomparison (pi V.antisymmetricPairModels) (R.mono hrt hN)
    ![V.pairCoordinateNiltest k out₀, V.pairCoordinateNiltest l out₁] ht
    (by intro a; fin_cases a
        · exact (V.pairCoordinateNiltest_complexity k out₀).mono htest
        · exact (V.pairCoordinateNiltest_complexity l out₁).mono htest)
    (by intro a x; fin_cases a
        · exact hcap k out₀ x
        · exact hcap l out₁ x)
    (fun a ha x y => R.pairCoordinate_comparison_invariant k l out₀ out₁ a ha x y)
    m hm (hmb.trans (Real.exp_le_exp.mpr hut))
    ![R.slowValue y, R.slowValue z] ![R.rationalValue y, R.rationalValue z]
    (by intro a e; fin_cases a
        · exact (hslow y hy e).trans (Real.exp_le_exp.mpr hut)
        · exact (hslow z hz e).trans (Real.exp_le_exp.mpr hut))
    (by intro a; fin_cases a
        · exact hrat y
        · exact hrat z)
  simpa only [V.pairCoordinateNiltest_observable, NativePolynomialOrbitFactors.pairAnchoredVector,
    NativePolynomialOrbitFactors.pairFrozenVector] using
    (show Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + r + u + C) ^ C)
      (fun x => (V.pairCoordinateNiltest k out₀).observable
          (QuotientGroup.mk (R.frozenMiddleValue (R.slowValue y) (R.rationalValue y) x)) *
        star ((V.pairCoordinateNiltest l out₁).observable
          (QuotientGroup.mk (R.frozenMiddleValue (R.slowValue z) (R.rationalValue z) x))))) from
      ⟨E.mono hcost⟩)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelatingVerticalPair
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

theorem exists_antisymmetric_pair_precise_partition :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b c t e : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r),
      R.HasPairLocalApproximation b → R.HasPairFrozenReduction c →
      0 ≤ t → 0 ≤ e → b ≤ t → c ≤ t → Real.exp ((t + e + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativePairPartition R ((t + e + C) ^ C) (Real.exp (-e))) := by
  obtain ⟨A, _, hpartition⟩ := exists_antisymmetric_pair_local_partition 2
  let X : Polynomial ℕ := Polynomial.X
  let T := X + 100
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C A) ^ A + 2 * T)
  refine ⟨C, hC, ?_⟩
  intro p q r b c t e W N _ i j V R hlocal hred ht he hbt hct hN
  let u := t + e + 100
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hsum : (u + A) ^ A + 2 * u ≤ (t + e + C) ^ C := by
    simpa [T, X, u, Polynomial.eval₂_pow] using hbudget (t + e) (add_nonneg ht he)
  have hcost : (u + A) ^ A ≤ (t + e + C) ^ C := by linarith
  have hscale : 2 * u ≤ (t + e + C) ^ C := by
    have : 0 ≤ (u + A) ^ A := by positivity
    linarith
  let ρ := Real.exp (-(2 * u))
  have hρ : 0 < ρ := Real.exp_pos _
  have hprec : 1 / ρ ≤ Real.exp ((u + 2) ^ 2) := by
    dsimp [ρ]
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg u]
  obtain ⟨P, hP, hPb, n, hn, hcard, weight, hpositive, htotal, anchor, hequiv, herr⟩ :=
    hpartition R hlocal hred hu (hbt.trans (by dsimp [u]; linarith))
      (hct.trans (by dsimp [u]; linarith)) hρ hprec
  let : NeZero P := ⟨hP.ne'⟩
  have hrecip : 1 / (N : ℝ) ≤ ρ := by
    have hh := one_div_le_one_div_of_le (Real.exp_pos (2 * u))
      ((Real.exp_le_exp.mpr hscale).trans hN)
    simpa only [ρ, one_div, Real.exp_neg] using hh
  have herror : Real.exp (u + 40) * (ρ + 1 / N) ≤ Real.exp (-e) := by
    calc
      _ ≤ Real.exp (u + 40) * (2 * ρ) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg _)
      _ = 2 * Real.exp (40 - u) := by
        dsimp [ρ]
        rw [← mul_assoc, mul_comm (Real.exp (u + 40)) 2, mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ 2 * (Real.exp (-e) / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply (Real.exp_le_exp.mpr (show 40 - u ≤ -e - 1 by dsimp [u]; linarith)).trans
        exact exp_sub_one_le_half_exp (-e)
      _ = _ := by ring
  exact ⟨{
    I := Fin n × ZMod P
    card_bound := hcard.trans (Real.exp_le_exp.mpr hcost)
    weight := weight
    positive := fun j => (hpositive j).mono le_rfl hcost
    total := htotal
    anchor := anchor
    equivalence := fun j => (hequiv j).mono hcost
    approximation := fun k out => (herr k out).trans herror }⟩

end Erdos3

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
  NativePairPartition.finite

theorem exists_common_anchor_approximation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r u b ε : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r),
      0 ≤ r → 0 ≤ u → 0 ≤ b → R.HasOuterValueControl u →
      (P : NativePairPartition R b ε) →
      ∀ (y : Fin 2 → ℤ), (∀ k, |(y k : ℝ)| ≤ (N : ℝ)) → ∀ l : Fin 2,
      ∃ F : Fin 2 → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
        (∀ k out a, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
          ((p + q + r + u + b + C) ^ C) (F k out a))) ∧
        (∀ k out a (x : Fin 2 → ZMod N),
          ‖F k out a (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
        (∀ k out (x : Fin 2 → ZMod N),
          ∑ a, F k out a (fun z => ((x z).val : ℤ)) *
            R.pairAnchoredVector y l a (fun z => ((x z).val : ℤ)) =
          ∑ cell, ((∏ z, P.weight (cell z) (x z) : ℝ) : ℂ) *
            R.pairAnchoredVector (fun z => ((P.anchor cell z).val : ℤ)) k out
              (fun z => ((x z).val : ℤ))) ∧
        (∀ k out,
          (𝔼 x : Fin 2 → ZMod N,
            ‖W.eval out (correlationInput ((x k).val : ℤ) ((x k.rev).val : ℤ)) -
              ∑ a, F k out a (fun z => ((x z).val : ℤ)) *
                R.pairAnchoredVector y l a (fun z => ((x z).val : ℤ))‖) ≤ ε) := by
  obtain ⟨A, _, hanchor⟩ := exists_antisymmetric_anchor_equivalence
  obtain ⟨B, _, hcommon⟩ := exists_weighted_common_factor
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r u b ε W N _ i j V R hr hu hb houter P y hy l
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r + u + b
  let t := v + (v + A) ^ A + 2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have ht : 2 ≤ t := by
    have ha : 0 ≤ (v + A) ^ A := by positivity
    dsimp [t]
    linarith
  have hbt : b ≤ t := by
    have ha : 0 ≤ (v + A) ^ A := by positivity
    dsimp [t, v]
    linarith
  have hat : (p + q + r + u + A) ^ A ≤ t := by
    calc
      _ ≤ (v + A) ^ A := by
        apply pow_le_pow_left₀ (by positivity)
        dsimp [v]
        linarith
      _ ≤ t := by dsimp [t]; linarith
  have hcost : (t + B) ^ B ≤ (p + q + r + u + b + C) ^ C := by
    simpa [X, T, t, v, Polynomial.eval₂_pow] using hbudget v hv
  let coords (cell : Fin 2 → P.I) (k : Fin 2 × Fin W.outputDim) :=
    R.pairAnchoredVector (fun z => ((P.anchor cell z).val : ℤ)) k.1 k.2
  have hbox (x : Fin 2 → ZMod N) (z : Fin 2) : |(((x z).val : ℤ) : ℝ)| ≤ (N : ℝ) := by
    simp only [Int.cast_natCast]
    rw [abs_of_nonneg (Nat.cast_nonneg ((x z).val))]
    exact Nat.cast_le.mpr (x z).val_lt.le
  have hcross (cell : Fin 2 → P.I) (k : Fin 2 × Fin W.outputDim) (a : Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 t
        (fun x => coords cell k x * star (R.pairAnchoredVector y l a x))) :=
    ((hanchor R hr hu houter (fun z => ((P.anchor cell z).val : ℤ)) y
      (hbox (P.anchor cell)) hy k.1 l).mono hat).expansion k.2 a
  obtain ⟨F, hF, _, hnorm, hrepr⟩ := hcommon ht
    (by simpa using ht : (Fintype.card (Fin 2) : ℝ) ≤ t)
    (P.card_bound.trans (Real.exp_le_exp.mpr hbt))
    (fun cell z => P.weight (cell z)) coords (R.pairAnchoredVector y l)
    (fun cell z => (P.positive (cell z)).mono le_rfl hbt)
    (sum_productPartitionWeight (fun (_ : Fin 2) a x => P.weight a x) (fun _ => P.total))
    (fun cell k x => R.pairAnchoredVector_norm _ _ _ _)
    (fun a x => R.pairAnchoredVector_norm _ _ _ _)
    (fun x => R.pairFrozenVector_unit l (R.slowValue y) (R.rationalValue y) _)
    hcross
  refine ⟨fun k out => F (k, out), ?_, ?_, ?_, ?_⟩
  · intro k out a
    exact ⟨(Classical.choice (hF (k, out) a)).mono hcost⟩
  · intro k out a x
    exact hnorm (k, out) a x
  · intro k out x
    exact hrepr (k, out) x
  · intro k out
    simpa only [hrepr] using P.approximation k out

end Erdos3

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

theorem exists_global_pair_comparison :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r u b ε : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r),
      0 ≤ r → 0 ≤ u → 0 ≤ b → R.HasOuterValueControl u →
      NativePairPartition R b ε →
      ∃ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
        (∀ out₀ out₁, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
          ((p + q + r + u + b + C) ^ C) (G out₀ out₁))) ∧
        (∀ a b (x : Fin 2 → ZMod N), ‖G a b (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
        (∀ a b, (𝔼 x : Fin 2 → ZMod N,
          ‖W.antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
            G a b (fun z => ((x z).val : ℤ))‖) ≤ 2 * ε) := by
  obtain ⟨A, _, hcommon⟩ := exists_common_anchor_approximation
  obtain ⟨B, _, hanchor⟩ := exists_antisymmetric_anchor_equivalence
  obtain ⟨D, _, hproducts⟩ := exists_native_common_factor_products
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro p q r u b ε W N _ i j V R hr hu hb houter P
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r + u + b
  let t := v + (v + A) ^ A + (v + B) ^ B + 2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hA : 0 ≤ (v + A) ^ A := by positivity
  have hB : 0 ≤ (v + B) ^ B := by positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t, v]; linarith
  have hAt : (p + q + r + u + b + A) ^ A ≤ t := by change (v + A) ^ A ≤ t; dsimp [t]; linarith
  have hBt : (p + q + r + u + B) ^ B ≤ t := by
    calc
      _ ≤ (v + B) ^ B := by
        apply pow_le_pow_left₀ (by positivity)
        dsimp [v]
        linarith
      _ ≤ t := by dsimp [t]; linarith
  have hcost : (t + D) ^ D ≤ (p + q + r + u + b + C) ^ C := by
    simpa [X, T, t, v, Polynomial.eval₂_pow] using hbudget v hv
  have hzero (k : Fin 2) : |((0 : Fin 2 → ℤ) k : ℝ)| ≤ (N : ℝ) := by simp
  obtain ⟨F, hF, _, hrepr, herr⟩ := hcommon R hr hu hb houter P 0 hzero 0
  let U := R.pairAnchoredVector 0 0
  let Q (k : Fin 2) (out : Fin W.outputDim) (x : Fin 2 → ℤ) := ∑ a, F k out a x * U a x
  let G (a b : Fin W.outputDim) (x : Fin 2 → ℤ) := Q 1 b x * star (Q 0 a x)
  have hU := (hanchor R hr hu houter 0 0 hzero hzero 0 0).mono hBt
  have hG (out₀ out₁ : Fin W.outputDim) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
      ((p + q + r + u + b + C) ^ C) (G out₀ out₁)) := by
    obtain ⟨E⟩ := hproducts ht
      (by simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpt))
      (fun k : Fin 2 × Fin W.outputDim => F k.1 k.2) U
      (fun k a => ⟨(Classical.choice (hF k.1 k.2 a)).mono hAt⟩)
      hU.expansion (1, out₁) (0, out₀)
    exact ⟨E.mono hcost⟩
  have hQcap (k : Fin 2) (out : Fin W.outputDim) (x : Fin 2 → ZMod N) :
      ‖Q k out (fun z => ((x z).val : ℤ))‖ ≤ 1 := by
    have heq := hrepr k out x
    change Q k out (fun z => ((x z).val : ℤ)) = _ at heq
    rw [heq]
    exact P.partition_sum_norm k out x
  refine ⟨G, hG, ?_, ?_⟩
  · intro a b x
    dsimp only [G]
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hQcap 1 b x)).trans (hQcap 0 a x)
  · intro a b
    have hpoint (x : Fin 2 → ZMod N) :
        ‖W.antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
          G a b (fun z => ((x z).val : ℤ))‖ ≤
        ‖W.eval b (correlationInput ((x 1).val : ℤ) ((x 0).val : ℤ)) -
          Q 1 b (fun z => ((x z).val : ℤ))‖ +
        ‖W.eval a (correlationInput ((x 0).val : ℤ) ((x 1).val : ℤ)) -
          Q 0 a (fun z => ((x z).val : ℤ))‖ := by
      dsimp only [NativeMultidegreeNilcharacter.antisymmetricKernel, G]
      rw [mul_comm (star _) (W.eval b _)]
      exact norm_mul_star_sub_mul_star_le_of_le_one (W.norm_eval a _) (hQcap 1 b x)
    have hmean := Finset.expect_le_expect (s := Finset.univ) (fun x _ => hpoint x)
    rw [Finset.expect_add_distrib] at hmean
    have hfirst := herr 1 b
    have hsecond := herr 0 a
    change (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval b (correlationInput ((x 1).val : ℤ) ((x 0).val : ℤ)) -
        Q 1 b (fun z => ((x z).val : ℤ))‖) ≤ ε at hfirst
    change (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval a (correlationInput ((x 0).val : ℤ) ((x 1).val : ℤ)) -
        Q 0 a (fun z => ((x z).val : ℤ))‖) ≤ ε at hsecond
    linarith

end Erdos3

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

theorem exists_precise_global_pair_comparison :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r e : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (_R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r),
      0 ≤ r → 0 ≤ e → Real.exp ((p + q + r + e + C) ^ C) ≤ (N : ℝ) →
      ∃ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
        (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
          ((p + q + r + e + C) ^ C) (G a b))) ∧
        (∀ a b (x : Fin 2 → ZMod N), ‖G a b (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
        (∀ a b, (𝔼 x : Fin 2 → ZMod N,
          ‖W.antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
            G a b (fun z => ((x z).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨A, _, hlocal⟩ := exists_antisymmetric_pair_local_approximation
  obtain ⟨B, _, hfrozen⟩ := exists_antisymmetric_pair_frozen_reduction
  obtain ⟨D, _, hpartition⟩ := exists_antisymmetric_pair_precise_partition
  obtain ⟨E, _, hglobal⟩ := exists_global_pair_comparison
  let X : Polynomial ℕ := Polynomial.X
  let L := (X + Polynomial.C A) ^ A
  let K := (X + Polynomial.C B) ^ B
  let T := L + K + X + 2
  let Z := (T + (X + 1) + Polynomial.C D) ^ D
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Z + (X + K + Z + Polynomial.C E) ^ E)
  refine ⟨C, hC, ?_⟩
  intro p q r e W N _ i j V R hr he hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r + e
  let b := (v + A) ^ A
  let c := (v + B) ^ B
  let t := b + c + v + 2
  let z := (t + (e + 1) + D) ^ D
  let zmax := (t + (v + 1) + D) ^ D
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hev : e ≤ v := by dsimp [v]; linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hzmax : 0 ≤ zmax := by dsimp [zmax]; positivity
  have hbt : b ≤ t := by dsimp [t]; linarith
  have hct : c ≤ t := by dsimp [t]; linarith
  have hzz : z ≤ zmax := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  have hsum : zmax + (v + c + zmax + E) ^ E ≤ (p + q + r + e + C) ^ C := by
    simpa [X, L, K, T, Z, b, c, t, zmax, v, Polynomial.eval₂_pow] using hbudget v hv
  have hzC : zmax ≤ (p + q + r + e + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hGC : (v + c + zmax + E) ^ E ≤ (p + q + r + e + C) ^ C :=
    (le_add_of_nonneg_left hzmax).trans hsum
  have hloc : R.HasPairLocalApproximation b :=
    R.hasPairLocalApproximation_mono (hlocal R hr) (by
      apply pow_le_pow_left₀ (by positivity)
      dsimp [v]
      linarith)
  have hred : R.HasPairFrozenReduction c :=
    R.hasPairFrozenReduction_mono (hfrozen R hr) (by
      apply pow_le_pow_left₀ (by positivity)
      dsimp [v]
      linarith)
  obtain ⟨P⟩ := hpartition R hloc hred ht (by linarith : 0 ≤ e + 1) hbt hct
    ((Real.exp_le_exp.mpr (hzz.trans hzC)).trans hN)
  obtain ⟨u, hu, huc, houter, _⟩ := hred
  obtain ⟨G, hG, hcap, herr⟩ := hglobal R hr hu hz houter P
  have hcost : (p + q + r + u + z + E) ^ E ≤ (p + q + r + e + C) ^ C := by
    apply le_trans _ hGC
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  refine ⟨G, ?_, hcap, ?_⟩
  · intro a b
    exact ⟨(Classical.choice (hG a b)).mono hcost⟩
  · intro a b
    apply (herr a b).trans
    have hh := exp_sub_one_le_half_exp (-e)
    have hid : -(e + 1) = -e - 1 := by ring
    rw [hid]
    linarith

end Erdos3

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

theorem exists_mixed_pair_frozen_equivalence (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r u : ℝ} {m : ℕ} [NeZero m]
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r)
      [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
      [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)],
      0 ≤ r → 0 ≤ u → R.HasMixedPairFrozenEquivalence u ((tensorPowerBudget m p + q + r + u + C) ^ C) := by
  obtain ⟨a, _, hfrozen⟩ := exists_native_frozen_middle_expansion (n + 1)
  have hdegree : n + 1 + 1 = ∑ _ : MixedReplicatedIndex (n + 1), 1 :=
    (mixedReplicated_totalDegree n).symm
  rw [hdegree] at hfrozen
  obtain ⟨C, hC, hbudget⟩ := exists_mixed_frozen_equivalence_budget a
  refine ⟨C, hC, ?_⟩
  intro p q r u m _ W N _ i j V R _ _ _ _ hr hu den hm hmb left right hleft hright
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  have hpk : p ≤ tensorPowerBudget m p := (tensorPowerBudget_bounds m hp).1
  obtain ⟨t, ht, hrt, hut, hpt, htest, hsum⟩ :=
    hbudget (tensorPowerBudget m p) q r u (hp.trans hpk) hq hr hu
  have htC : t ≤ (tensorPowerBudget m p + q + r + u + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hcost : (t + a) ^ a ≤ (tensorPowerBudget m p + q + r + u + C) ^ C :=
    (le_add_of_nonneg_left ht).trans hsum
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp ((tensorPowerBudget m p + q + r + u + C) ^ C) := by
    simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr (hpk.trans (hpt.trans htC)))
  refine ⟨hdim, hdim, ?_⟩
  intro out₀ out₁
  have hN : ∀ _k : Fin (n + 2), (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨F⟩ := hfrozen (pi V.mixedPairModels) (R.mono hrt hN)
    (V.mixedOriginalPairComparisonNiltest out₀ out₁) ht ((V.mixedOriginalPairComparisonNiltest_complexity out₀ out₁).mono htest)
    (R.mixed_original_pair_comparison_invariant out₀ out₁) den hm (hmb.trans (Real.exp_le_exp.mpr hut)) left right
    (fun k => (hleft k).trans (Real.exp_le_exp.mpr hut)) hright
  have hF : Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1)
      ((tensorPowerBudget m p + q + r + u + C) ^ C) (fun x =>
        (V.mixedOriginalPairComparisonNiltest out₀ out₁).observable
          (QuotientGroup.mk (R.frozenMiddleValue left right x)))) :=
    ⟨F.mono hcost⟩
  have heq : (fun x : Fin (n + 2) → ℤ =>
      (V.mixedOriginalPairComparisonNiltest out₀ out₁).observable
        (QuotientGroup.mk (R.frozenMiddleValue left right x))) =
      (fun x => R.mixedPairFrozenVector 0 left right out₀ x *
        star (R.mixedPairFrozenVector 1 left right out₁ x)) := by
    funext x
    rw [V.mixedOriginalPairComparisonNiltest_observable]
    rfl
  exact (congrArg (fun f : (Fin (n + 2) → ℤ) → ℂ =>
    Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1)
      ((tensorPowerBudget m p + q + r + u + C) ^ C) f)) heq).mp hF

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPairPartitionPrecision
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_mixed_pair_local_approximation (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ} {m : ℕ}
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r), 0 ≤ r →
      R.HasMixedPairLocalApproximation ((tensorPowerBudget m p + q + r + C) ^ C) := by
  obtain ⟨a, _, hcontrol⟩ := exists_native_orbit_local_control
    (∑ _ : MixedReplicatedIndex (n + 1), 1)
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + Polynomial.C (n + 2)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r m W N _ i j V R hr
  have hW : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hp : 0 ≤ tensorPowerBudget m p := hW.trans (tensorPowerBudget_bounds m hW).1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let u := tensorPowerBudget m p + q + r
  let b := 4 * (u + 1) + raisedNiltestBudget u + 6
  let t := productNiltestBudget b + u + ((n + 2 : ℕ) : ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpqu : tensorPowerBudget m p + q ≤ u := le_add_of_nonneg_right hr
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hdim : (0 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, u]; linarith
  have htwo : (Fintype.card (Fin (n + 2)) : ℝ) ≤ t := by
    simp only [Fintype.card_fin]
    dsimp [t]
    linarith
  have hBt : mixedPairBudget (tensorPowerBudget m p) q ≤ b := by
    dsimp [mixedPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ mixedPairBudget (tensorPowerBudget m p) q :=
    (by norm_num : (0 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le
  have hprodmono : productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q) ≤ productNiltestBudget b :=
    productNiltestBudget_mono hB0 hBt
  have htest : productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hcost : t + (t + a) ^ a ≤ (tensorPowerBudget m p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  have hlocal : (t + a) ^ a ≤ (tensorPowerBudget m p + q + r + C) ^ C :=
    (le_add_of_nonneg_left ht).trans hcost
  let : TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi V.mixedPairModels).basis
  let D := pi V.mixedPairModels
  have hD : D.GeometryComplexityLE t :=
    (V.mixedPairNiltest_complexity).1.mono D htest
  have hN : ∀ _k : Fin (n + 2), (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨P, hP, hPb, hcosets, hmotion⟩ := hcontrol (R.mono hrt hN) ht hD htwo hN
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hlocal), ?_⟩
  intro y hy k out x δ hδ hx hres hnear
  let : MetricSpace (pi V.mixedPairModels).RealGroup :=
    rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
      (D.basis.baseChange ℝ)
  have herror := R.mixedPairFrozenVector_error k out x y (hcosets x y hres).1
  have hdist := hmotion x y δ hδ hx hy hnear
  apply herror.trans
  calc
    _ ≤ Real.exp t * (Real.exp ((t + a) ^ a) * δ) :=
      mul_le_mul (Real.exp_le_exp.mpr htest) hdist
        (@dist_nonneg D.RealGroup
          (rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
            (D.basis.baseChange ℝ)).toPseudoMetricSpace (R.slowValue x) (R.slowValue y))
        (Real.exp_nonneg t)
    _ = Real.exp (t + (t + a) ^ a) * δ := by rw [← mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcost) hδ

end Erdos3

end

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

theorem exists_mixed_pair_frozen_reduction (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ} {m : ℕ} [NeZero m]
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r), 0 ≤ r →
      R.HasMixedPairFrozenReduction ((tensorPowerBudget m p + q + r + C) ^ C) := by
  obtain ⟨A, _, houter⟩ := exists_mixed_pair_outer_control n
  obtain ⟨B, _, hfrozen⟩ := exists_mixed_pair_frozen_equivalence n
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (X + U + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r m _ W N _ i j V R hr
  have hW : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hp : 0 ≤ tensorPowerBudget m p := hW.trans (tensorPowerBudget_bounds m hW).1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := tensorPowerBudget m p + q + r
  let u := (v + A) ^ A
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsum : u + (v + u + B) ^ B ≤ (tensorPowerBudget m p + q + r + C) ^ C := by
    simpa [X, U, u, v, Polynomial.eval₂_pow] using hbudget v hv
  have huC : u ≤ (tensorPowerBudget m p + q + r + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hBC : (v + u + B) ^ B ≤ (tensorPowerBudget m p + q + r + C) ^ C :=
    (le_add_of_nonneg_left hu).trans hsum
  let : TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi V.mixedPairModels).basis
  exact ⟨u, hu, huC, houter (W := W.tensorPower m) (V := V) R hr,
    R.hasMixedPairFrozenEquivalence_mono (hfrozen (W := W) (V := V) R hr hu) hBC⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPreciseSampledExchange
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

theorem exists_mixed_pointwise_partition (n a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b c t : ℝ} {m : ℕ}
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r),
      R.HasMixedPairLocalApproximation b → R.HasMixedPairFrozenReduction c →
      0 ≤ t → b ≤ t → c ≤ t → ∀ {ρ : ℝ}, 0 < ρ → 1 / ρ ≤ Real.exp ((t + 2) ^ a) →
      Nonempty (NativeMixedPointwisePartition R ((t + C) ^ C)
        (Real.exp t * ρ) (6 * ρ + 3 / N)) := by
  obtain ⟨B, _, hpartition⟩ := exists_interval_residue_partition a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + 60 + Polynomial.C (n + 2) * (X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r b c t m W N _ i j V R hlocal hred ht hbt hct ρ hρ hprec
  obtain ⟨P, hP, hPb, hselect⟩ := R.select_mixed_pointwise_partition hlocal hred
  let : NeZero P := ⟨hP.ne'⟩
  have hPt : (P : ℝ) ≤ Real.exp t := hPb.trans (Real.exp_le_exp.mpr hbt)
  obtain ⟨cells, hn, hcard, A, hA, hsum, hdiam⟩ := hpartition N P ht hPt hρ hprec
  have htotal : t + 60 + ((n + 2 : ℕ) : ℝ) * (t + B) ^ B ≤ (t + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget t ht
  have hpow : 0 ≤ (t + B) ^ B := by positivity
  have hdim : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + 2 by omega)
  have hmul : 0 ≤ ((n + 2 : ℕ) : ℝ) * (t + B) ^ B := mul_nonneg (by linarith) hpow
  have htC : t ≤ (t + C) ^ C := by linarith
  have hdimCost : ((n + 2 : ℕ) : ℝ) * (t + B) ^ B ≤ (t + C) ^ C := by linarith
  have hcost : (t + B) ^ B ≤ (t + C) ^ C :=
    (le_mul_of_one_le_left hpow hdim).trans hdimCost
  let w := productPartitionWeight (fun _ : Fin (n + 2) => A)
  let E := cyclicWrapExceptional (0 : ZMod N) ρ
  have hnonneg : ∀ i j x, 0 ≤ (fun _ : Fin (n + 2) => A) i j x :=
    fun _ j x => ((hA j).unit_interval x).1
  have hw : ∀ j x, 0 ≤ w j x := productPartitionWeight_nonneg _ hnonneg
  have hwSum : ∀ x, ∑ j, w j x = 1 := sum_productPartitionWeight _ (fun _ => hsum)
  have hcells : ∀ j x y, (∀ i, x i ∉ E) → (∀ i, y i ∉ E) → 0 < w j x → 0 < w j y →
      (∀ i, (P : ℤ) ∣ ((x i).val : ℤ) - (y i).val) ∧
      (∀ i, |((x i).val : ℝ) - (y i).val| ≤ (N : ℝ) * ρ) := by
    intro j x y hx hy hwx hwy
    have hposx := productPartitionWeight_pos_coordinate _ hnonneg j x hwx
    have hposy := productPartitionWeight_pos_coordinate _ hnonneg j y hwy
    exact ⟨fun i => (hdiam (j i) (x i) (y i) (hx i) (hy i) (hposx i) (hposy i)).2,
      fun i => (hdiam (j i) (x i) (y i) (hx i) (hy i) (hposx i) (hposy i)).1⟩
  obtain ⟨y, hequiv, hpoint⟩ := hselect E w hρ.le hw hwSum hcells
  let δ := Real.exp t * ρ
  let β := 6 * ρ + 3 / (N : ℝ)
  have hδ : 0 ≤ δ := mul_nonneg (Real.exp_nonneg _) hρ.le
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hbad : (E.card : ℝ) / N ≤ β := cyclicWrapExceptional_density_le (0 : ZMod N) hρ.le
  have hcard' : (Fintype.card (Fin (n + 2) → Fin cells × ZMod P) : ℝ) ≤ Real.exp ((t + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp ((t + B) ^ B)) ^ (n + 2) := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard (n + 2)
      _ = Real.exp (((n + 2 : ℕ) : ℝ) * (t + B) ^ B) := (Real.exp_nat_mul _ (n + 2)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hdimCost
  have hpoint' (a) (x) (hx : ∀ l, x l ∉ E) (hax : 0 < w a x) (k : Fin 2) (out : Fin W.outputDim) :
      ‖W.eval out (mixedSlotInput ((x (![0, 1] k)).val : ℤ) ((x (![1, 0] k)).val : ℤ) (fun l => ((x l.succ.succ).val : ℤ))) - R.mixedPairAnchoredVector
        (fun l => ((y a l).val : ℤ)) k out (fun l => ((x l).val : ℤ))‖ ≤ δ :=
    (hpoint a x hx hax k out).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hbt) hρ.le)
  have herr (k : Fin 2) (out : Fin W.outputDim) :
      (𝔼 x : Fin (n + 2) → ZMod N, ∑ a, w a x *
        ‖W.eval out (mixedSlotInput ((x (![0, 1] k)).val : ℤ) ((x (![1, 0] k)).val : ℤ) (fun l => ((x l.succ.succ).val : ℤ))) - R.mixedPairAnchoredVector
          (fun l => ((y a l).val : ℤ)) k out (fun l => ((x l).val : ℤ))‖) ≤ δ + 2 * ((n + 2 : ℕ) : ℝ) * β := by
    have h := weighted_partition_mean_error (coordinateExceptional E) w
      (fun a x => R.mixedPairAnchoredVector (fun l => ((y a l).val : ℤ)) k out
        (fun l => ((x l).val : ℤ))) _ hδ hw hwSum
      (fun a x => R.mixedPairAnchoredVector_norm _ _ _ _)
      (fun x => W.norm_eval out _) (fun a x hx hax =>
        hpoint' a x ((not_mem_coordinateExceptional E x).mp hx) hax k out)
    have hd : ((coordinateExceptional (ι := Fin (n + 2)) E).card : ℝ) / Fintype.card (Fin (n + 2) → ZMod N) ≤
        ((n + 2 : ℕ) : ℝ) * ((E.card : ℝ) / N) := by
      simpa only [Fintype.card_fin, ZMod.card, Nat.cast_ofNat, mul_div_assoc] using
        coordinateExceptional_density_le (ι := Fin (n + 2)) E
    have hbad' : ((n + 2 : ℕ) : ℝ) * ((E.card : ℝ) / N) ≤ ((n + 2 : ℕ) : ℝ) * β :=
      mul_le_mul_of_nonneg_left hbad (Nat.cast_nonneg _)
    have hsmall := hd.trans hbad'
    rw [mul_div_assoc] at h
    linarith
  let core : NativeMixedPairPartition R ((t + C) ^ C) (δ + 2 * ((n + 2 : ℕ) : ℝ) * β) := {
    I := Fin cells × ZMod P
    card_bound := hcard'
    weight := A
    positive := fun j => (hA j).mono le_rfl hcost
    total := hsum
    anchor := y
    equivalence := fun j => (hequiv j).mono (hct.trans htC)
    weighted_approximation := herr }
  exact ⟨{
    partition := core
    error_nonneg := hδ
    density_nonneg := hβ
    bad := E
    bad_density := hbad
    pointwise := hpoint' }⟩

end Erdos3

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

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  {R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r}

theorem exists_mixed_diagonal_partition (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b c t e : ℝ} {m : ℕ}
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r),
      R.HasMixedPairLocalApproximation b → R.HasMixedPairFrozenReduction c →
      0 ≤ t → 0 ≤ e → b ≤ t → c ≤ t → Real.exp ((t + e + C) ^ C) ≤ (N : ℝ) →
      ∃ δ β : ℝ, ∃ _P : NativeMixedPointwisePartition R ((t + e + C) ^ C) δ β,
        δ + 4 * β ≤ Real.exp (-e) := by
  obtain ⟨A, _, hpartition⟩ := exists_mixed_pointwise_partition n 2
  let X : Polynomial ℕ := Polynomial.X
  let T := X + 100
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C A) ^ A + 2 * T)
  refine ⟨C, hC, ?_⟩
  intro p q r b c t e m W N _ i j V R hlocal hred ht he hbt hct hN
  let u := t + e + 100
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hsum : (u + A) ^ A + 2 * u ≤ (t + e + C) ^ C := by
    simpa [X, T, u, Polynomial.eval₂_pow] using hbudget (t + e) (add_nonneg ht he)
  have hcost : (u + A) ^ A ≤ (t + e + C) ^ C := by linarith
  have hscale : 2 * u ≤ (t + e + C) ^ C := by
    have : 0 ≤ (u + A) ^ A := by positivity
    linarith
  let ρ := Real.exp (-(2 * u))
  have hρ : 0 < ρ := Real.exp_pos _
  have hprec : 1 / ρ ≤ Real.exp ((u + 2) ^ 2) := by
    dsimp [ρ]
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg u]
  obtain ⟨P⟩ := hpartition R hlocal hred hu
    (hbt.trans (by dsimp [u]; linarith)) (hct.trans (by dsimp [u]; linarith)) hρ hprec
  have hrecip : 1 / (N : ℝ) ≤ ρ := by
    have h := one_div_le_one_div_of_le (Real.exp_pos (2 * u))
      ((Real.exp_le_exp.mpr hscale).trans hN)
    simpa only [ρ, one_div, Real.exp_neg] using h
  have hρle : ρ ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
  have hthree : (3 : ℝ) / N ≤ 3 * ρ := by
    calc
      _ = 3 * (1 / (N : ℝ)) := by ring
      _ ≤ 3 * ρ := mul_le_mul_of_nonneg_left hrecip (by norm_num)
  have hδ : Real.exp u * ρ = Real.exp (-u) := by
    dsimp [ρ]
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨Real.exp u * ρ, 6 * ρ + 3 / N, P.mono hcost le_rfl le_rfl, ?_⟩
  calc
    _ ≤ 37 * Real.exp (-u) := by rw [hδ]; linarith
    _ ≤ Real.exp 100 * Real.exp (-u) := by
      gcongr
      linarith [Real.add_one_le_exp (100 : ℝ)]
    _ = Real.exp (100 - u) := by simp only [← Real.exp_add, sub_eq_add_neg]
    _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [u]; linarith)

end Erdos3

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

theorem exists_mixed_precise_sampled_exchange (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r e : ℝ} {m : ℕ} [NeZero m]
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (_R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r),
      0 ≤ r → 0 ≤ e → Real.exp ((tensorPowerBudget m p + q + r + e + C) ^ C) ≤ (N : ℝ) →
      ∃ G : (Fin (n + 2) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
        (∀ π a c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (n + 1)
          ((tensorPowerBudget m p + q + r + e + C) ^ C) (G π a c))) ∧
        (∀ π a c (x : Fin 2 → ZMod N), ‖G π a c (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
        (∀ π a c, (𝔼 x : Fin 2 → ZMod N,
          ‖W.eval a (mixedSlotInput ((x (π 0)).val : ℤ) ((x (π 1)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ))) *
              star (W.eval c (mixedSlotInput ((x (π 1)).val : ℤ) ((x (π 0)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ)))) -
            G π a c (fun z => ((x z).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨a, _, hlocal⟩ := exists_mixed_pair_local_approximation n
  obtain ⟨b, _, hfrozen⟩ := exists_mixed_pair_frozen_reduction n
  obtain ⟨d, _, hpartition⟩ := exists_mixed_diagonal_partition n
  obtain ⟨c, _, hexchange⟩ := exists_mixed_sampled_exchange n
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C a) ^ a + (X + Polynomial.C b) ^ b
  let Z := (T + X + 1 + Polynomial.C d) ^ d
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Z + (Z + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p q r e m _ W N _ i j V R hr he hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hk : 0 ≤ tensorPowerBudget m p := hp.trans (tensorPowerBudget_bounds m hp).1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := tensorPowerBudget m p + q + r + e
  let t := (v + a) ^ a + (v + b) ^ b
  let z := (t + (e + 1) + d) ^ d
  let zmax := (t + v + 1 + d) ^ d
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hzm : 0 ≤ zmax := by dsimp [zmax]; positivity
  have hzz : z ≤ zmax := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  have hsum : zmax + (zmax + c) ^ c ≤ (v + C) ^ C := by
    simpa [X, T, Z, zmax, t, Polynomial.eval₂_pow] using hbudget v hv
  have hzC : z ≤ (v + C) ^ C :=
    hzz.trans ((le_add_of_nonneg_right (by positivity)).trans hsum)
  have hcost : (z + c) ^ c ≤ (v + C) ^ C :=
    (pow_le_pow_left₀ (by positivity) (by linarith : z + c ≤ zmax + c) c).trans
      ((le_add_of_nonneg_left hzm).trans hsum)
  have ha : (tensorPowerBudget m p + q + r + a) ^ a ≤ t := by
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  have hb : (tensorPowerBudget m p + q + r + b) ^ b ≤ t := by
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  obtain ⟨δ, β, P, herr⟩ := hpartition R (hlocal (W := W) R hr) (hfrozen (W := W) R hr)
    ht (by positivity : 0 ≤ e + 1) ha hb ((Real.exp_le_exp.mpr hzC).trans hN)
  obtain ⟨G, hG, _, hcap, herror⟩ := hexchange P hz
  refine ⟨G, fun π a c => ⟨(Classical.choice (hG π a c)).mono hcost⟩, hcap, ?_⟩
  intro π a c
  apply (herror π a c).trans
  have hhalf := exp_sub_one_le_half_exp (-e)
  have hid : -(e + 1) = -e - 1 := by ring
  rw [← hid] at hhalf
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSeparatedSumIntervals
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_absorb_pair_missing_coordinate_errors (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} {D : RationalFilteredNilmanifold L s d}
      {E : RationalFilteredNilmanifold M s e} {p : ℝ}
      (T : D.Niltest (fun _ : Fin (s + 1) => 1))
      (U : E.Niltest (fun _ : Fin (s + 1) => 1)), T.ComplexityLE p → U.ComplexityLE p →
      ∀ {G X : Type*} (H : Finset G), H.Nonempty →
      ∀ (S : G → Finset X), (∀ h ∈ H, (S h).Nonempty) →
      ∀ (sample : G → X → Fin (s + 1) → ℤ) (f : G → X → ℂ),
      (∀ h ∈ H, ∀ x ∈ S h, ‖f h x‖ ≤ 1) →
      (∀ h ∈ H, Real.exp (-p) ≤
        ‖𝔼 x ∈ S h, f h x * star (T.eval (sample h x)) * star (U.eval (sample h x))‖) →
      ∃ A : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ,
        (∀ i x, ‖A i x‖ ≤ 1) ∧
        (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
        ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (H.card : ℝ) ≤ (H'.card : ℝ) ∧
          ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 x ∈ S h, f h x * ∏ i, A i (sample h x)‖ := by
  obtain ⟨a, _, habsorb⟩ := exists_absorb_missing_coordinate_error s
  let X : Polynomial ℕ := Polynomial.X
  let Q := (2 * X + Polynomial.C a) ^ a
  let R := (X + Q + 2 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + R)
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E p T U hT hU G Ω H hH S hS sample f hf hcorr
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hT.1.1
  let q := (2 * p + a) ^ a
  let t := p + q + 2
  let r := (t + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hqt : q ≤ t := by dsimp [t]; linarith
  have htotal : q + r ≤ (p + C) ^ C := by
    simpa [X, Q, R, q, t, r, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := by linarith
  let V := U.expNormalize p
  have hV : V.ComplexityLE p := U.expNormalize_complexity hU
  have hVnorm (x : Fin (s + 1) → ℤ) : ‖V.eval x‖ ≤ 1 :=
    (V.norm_eval_le x).trans (U.expNormalize_norm hU)
  let g (h : G) (x : Ω) := f h x * star (V.eval (sample h x))
  have hg : ∀ h ∈ H, ∀ x ∈ S h, ‖g h x‖ ≤ 1 := by
    intro h hh x hx
    dsimp only [g]
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf h hh x hx)).trans (hVnorm _)
  have hgcorr : ∀ h ∈ H, Real.exp (-(2 * p)) ≤
      ‖𝔼 x ∈ S h, g h x * star (T.eval (sample h x))‖ := by
    intro h hh
    have heq : (𝔼 x ∈ S h, g h x * star (T.eval (sample h x))) =
        (Real.exp (-p) : ℂ) *
          (𝔼 x ∈ S h, f h x * star (T.eval (sample h x)) * star (U.eval (sample h x))) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      simp only [g, V, RationalFilteredNilmanifold.Niltest.expNormalize_eval,
        star_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    calc
      _ = Real.exp (-p) * Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcorr h hh) (Real.exp_nonneg _)
  obtain ⟨A, hA, hAind, H₁, hsub₁, hH₁, hsize₁, hcorr₁⟩ :=
    habsorb T (hT.mono (by linarith : p ≤ 2 * p)) H hH S hS sample g hg hgcorr
  let g₁ (h : G) (x : Ω) := f h x * ∏ i, A i (sample h x)
  have hg₁ : ∀ h ∈ H₁, ∀ x ∈ S h, ‖g₁ h x‖ ≤ 1 := by
    intro h hh x hx
    dsimp only [g₁]
    rw [norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) (hf h (hsub₁ hh) x hx)).trans
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hA i _)
  have hgcorr₁ : ∀ h ∈ H₁, Real.exp (-t) ≤
      ‖𝔼 x ∈ S h, g₁ h x * star (V.eval (sample h x))‖ := by
    intro h hh
    have heq : (𝔼 x ∈ S h, g h x * ∏ i, A i (sample h x)) =
        (𝔼 x ∈ S h, g₁ h x * star (V.eval (sample h x))) := by
      apply Finset.expect_congr rfl
      intro x _
      exact mul_right_comm _ _ _
    rw [← heq]
    exact (Real.exp_le_exp.mpr (neg_le_neg hqt)).trans (hcorr₁ h hh)
  obtain ⟨B, hB, hBind, H₂, hsub₂, hH₂, hsize₂, hcorr₂⟩ :=
    habsorb V (hV.mono hpt) H₁ hH₁ S (fun h hh => hS h (hsub₁ hh)) sample g₁ hg₁ hgcorr₁
  refine ⟨(fun i x => A i x * B i x), ?_, ?_, H₂, hsub₂.trans hsub₁, hH₂, ?_, ?_⟩
  · intro i x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hA i x)).trans (hB i x)
  · intro i x y hxy
    change A i x * B i x = A i y * B i y
    rw [hAind i x y hxy, hBind i x y hxy]
  · calc
      _ ≤ Real.exp (-(q + r)) * (H.card : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg htotal)) (Nat.cast_nonneg _)
      _ = Real.exp (-r) * (Real.exp (-q) * (H.card : ℝ)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-r) * (H₁.card : ℝ) := mul_le_mul_of_nonneg_left hsize₁ (Real.exp_nonneg _)
      _ ≤ _ := hsize₂
  · intro h hh
    simpa only [g₁, Finset.prod_mul_distrib, mul_assoc] using
      (Real.exp_le_exp.mpr (neg_le_neg hrC)).trans (hcorr₂ h hh)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_absorb_fixed_target_cube_errors (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {J : Type*} [Fintype J] {N : ℕ} [NeZero N] {p q : ℝ}, 0 ≤ q →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      ∀ (M : NativeMixedCorrelation (d + 2) N p f) (η : J → (Fin 2 → ℤ) → ℂ),
      (∀ j x, ‖η j x‖ ≤ 1) → HasFixedTargetCubeIntervals f M η q →
      HasWeightedTargetCubeIntervals f M η ((q + C) ^ C) := by
  obtain ⟨a, _, habsorb⟩ := exists_absorb_pair_missing_coordinate_errors (d + 2)
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + P)
  refine ⟨C, hC, ?_⟩
  intro J _ N _ p q hq f hf M η hη H
  classical
  let r := (q + a) ^ a
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : q + r ≤ (q + C) ^ C := by
    simpa [X, P, r, Polynomial.eval₂_pow] using hbudget q hq
  have hqC : q ≤ (q + C) ^ C := by linarith
  have hrC : r ≤ (q + C) ^ C := by linarith
  obtain ⟨r₀, u, hr₀, hr₀q, hu, huq, E, F, i, b, v, l, w, z, Q, hQ, hdense, hcorr⟩ := H
  let T := ((E b).selectedExpansion (fun _ => i) v).test l
  let U := (F.selectedExpansion v w).test z
  have hT : T.ComplexityLE q := (((E b).selectedExpansion (fun _ => i) v).complexity l).mono hr₀q
  have hU : U.ComplexityLE q := ((F.selectedExpansion v w).complexity z).mono huq
  have hdata (t : Q) := hcorr t.val t.property
  choose hshift start len hlen hend hshort hvol hcor using hdata
  let I (t : Q) := Finset.Ico (start t : ℤ) (start t + len t)
  let sample (t : Q) := mixedDifferencePoint t.val
  let signal (t : Q) (n : ℤ) := cubeProduct f (t.val.2 :: List.ofFn t.val.1) (n : ZMod N) *
    star (mixedCubeObservable η w (sample t n))
  let : Nonempty Q := hQ.to_subtype
  have hI (t : Q) : (I t).Nonempty := Finset.nonempty_Ico.mpr (by
    have hh := hlen t
    change (start t : ℤ) < start t + len t
    omega)
  have hsignal (t : Q) (n : ℤ) : ‖signal t n‖ ≤ 1 := by
    dsimp only [signal]
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (cubeProduct_norm_le_one f hf _ _)).trans
      (mixedCubeObservable_norm_le_one η hη w _)
  obtain ⟨A, hA, hAi, S, _, hS, hSdense, hScor⟩ := habsorb T U hT hU
    Finset.univ Finset.univ_nonempty I (fun t _ => hI t) sample signal
    (fun t _ n _ => hsignal t n) (fun t _ => hcor t)
  let embed : Q ↪ ((Fin (d + 1) → ZMod N) × ZMod N) := ⟨Subtype.val, Subtype.val_injective⟩
  let Q' := S.map embed
  have hQ' : Q'.Nonempty := hS.map
  have hsize : Real.exp (-r) * (Q.card : ℝ) ≤ (Q'.card : ℝ) := by
    simpa only [Q', Finset.card_map, Finset.card_univ, Fintype.card_coe] using hSdense
  refine ⟨w, A, hA, hAi, Q', hQ', ?_, ?_⟩
  · calc
      _ ≤ Real.exp (-(q + r)) * (N : ℝ) ^ (d + 2) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg htotal)) (by positivity)
      _ = Real.exp (-r) * (Real.exp (-q) * (N : ℝ) ^ (d + 2)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-r) * (Q.card : ℝ) := mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
    exact ⟨hshift t', start t', len t', hlen t', hend t', hshort t',
      (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hvol t'),
      (Real.exp_le_exp.mpr (neg_le_neg hrC)).trans (hScor t' ht')⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCenteredNarrowPrescribedMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocated_centered_narrow_prescribed_marginal_pointwise (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ AllocatedCenteredNarrowPrescribedMarginalPointwiseStatement m A := by
  obtain ⟨A, hA, hmarginal⟩ := exists_allocated_centered_narrow_prescribed_marginal_oneCenter m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P E hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ
    hW hWP hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize rank hrank hRank T hT widths bases density Z
  have hcenter := hmarginal B U basis S hb o μ ν hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall hP hmSize hK hX hdim hRP hσP hcount hI hn hJ
    hAP hLP hCP hVP p hp hm stride hs hsP hW hWP hτ hτP hτhalf hτdim hξ hξ1 hξP
    N hsize hrank hRank T hT
  obtain ⟨hN, hbases, hbox, hmass, hmargin, _, _⟩ := hcenter 0
  have hnormalizer (center) : |Z center - 1| ≤ Real.exp (-E) ∧
      Z center ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z center ∧ (Z center)⁻¹ ≤ 2 := by
    obtain ⟨_, _, _, _, _, hn, _⟩ := hcenter center
    exact hn
  refine ⟨hN, hbases, hbox, hmass, hmargin, hnormalizer, ?_⟩
  intro law Sites _ _ root hroot hrootSum center
  obtain ⟨_, _, _, _, _, _, hsite⟩ := hcenter center
  exact hsite root hroot hrootSum

end Erdos3.VectorPolynomial

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

theorem enlargedPreparedCommonSampler_dimensions (Jalloc : ℕ) {M : ℕ}
    (hM : ∀ j, Fintype.card (L j).Coord ≤ M) :
    Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc)
      (PreparedSamplerContinuous L) (preparedSamplerTransverse L)
      (EnlargedPreparedCommonSamplerBlock L Jalloc)) ≤ enlargedPreparedCommonSamplerDimension m M Jalloc ∧
      (∀ j, Fintype.card (PreparedSamplerContinuous L j) ≤ enlargedPreparedCommonSamplerDimension m M Jalloc) ∧
      (∀ j, preparedSamplerTransverse L j ≤ enlargedPreparedCommonSamplerDimension m M Jalloc) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [enlargedPreparedCommonSampler_variables_card]
    have hsum : (∑ j : Fin m, Fintype.card (L j).Coord *
        ((preparedCommonBlockCount m j + Jalloc) * (j.val + 1))) ≤
        M * m * (∑ j : Fin m, (preparedCommonBlockCount m j + Jalloc)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ M * ((preparedCommonBlockCount m j + Jalloc) * m) :=
          Nat.mul_le_mul (hM j) (Nat.mul_le_mul_left _ (Nat.succ_le_of_lt j.isLt))
        _ = _ := by ring
    unfold enlargedPreparedCommonSamplerDimension
    omega
  · intro j
    have h := preparedSampler_axis_card L j
    have hb := hM j
    have hp := enlargedPreparedCommonSamplerDimension_ge m M Jalloc
    omega
  · intro j
    have h := preparedSampler_axis_card L j
    have hb := hM j
    have hp := enlargedPreparedCommonSamplerDimension_ge m M Jalloc
    omega

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedShortRankWitnessWidth
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

theorem allocatedChartResiduePrimePowerWitness_sampler_iff_actual
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (C : ℝ) (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (M : ℕ) (hdiv : ∀ p : P, p.val ^ A p.val ∣ M)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (x : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hinteger : ∀ (j : Fin m) (i : Fin (n j))
      (q : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
      allocatedReadProjection f ⟨j,Sum.inr i⟩ q = (x j).2 i q) :
    allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
      (fun q => ((allocatedReadNoise f q : ℤ) : ZMod M))
      (coefficientSamplerChartResidues M x (fun j q i => ((allocatedReadDeck f j q i : ℤ) : ZMod M))) ↔
      ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val) f := by
  rw [← allocatedReadCoefficientChartResidues_sampler M f x hinteger]
  exact allocatedChartResiduePrimePowerWitness_iff_actual inactive spatial kernel block C P A M hdiv f

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedCenteredMeasurableFramedBadTail
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

section BadDepth
variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]
variable (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ)

theorem allocatedActualPrimeBad_depth_jointFrame (A : ℕ → ℕ) (p : ℕ) (a : X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    largestTestedBadDepth A (allocatedActualPrimeBad inactive spatial kernel block P C) p
        (allocatedJointFrameRead a f) =
      largestTestedBadDepth A (allocatedActualPrimeBad inactive spatial kernel block P C) p f := by
  rw [allocatedActualPrimeBad_depth, allocatedActualPrimeBad_depth]
  exact allocatedJointFrameRead_badDepth inactive spatial kernel block P A C p a f

theorem allocatedActualPrimeBad_product_jointFrame (A : ℕ → ℕ) (a : X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    (∏ p ∈ P, p ^ largestTestedBadDepth A
      (allocatedActualPrimeBad inactive spatial kernel block P C) p (allocatedJointFrameRead a f)) =
    ∏ p ∈ P, p ^ largestTestedBadDepth A
      (allocatedActualPrimeBad inactive spatial kernel block P C) p f := by
  simp only [allocatedActualPrimeBad_depth_jointFrame]

end BadDepth

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateRefinementLabels
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    (D : RationalFilteredNilmanifold L r d) (Fmark : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M)
    (marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)

namespace AllocatedExternalCandidateProblem

variable {D Fmark φ marked observable weight cost massThreshold scoreThreshold}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem exists_common_keep_refinement :
    ∃ (keep : LayerSamplerVariables G I n B → Prop)
      (refinement : P.Refinement cost
        (massThreshold / (2 : ℝ) ^ Fintype.card (LayerSamplerVariables G I n B)) scoreThreshold),
      ∀ z : refinement.problem.productive, (refinement.problem.chart z).keep = keep := by
  let code (z : A.Path) : Finset (LayerSamplerVariables G I n B) :=
    if hz : z ∈ P.productive then Finset.univ.filter (P.chart ⟨z, hz⟩).keep else ∅
  obtain ⟨chosen, hmass⟩ := A.law.exists_code_fiber_mass P.productive code
  let retained := P.productive.filter (fun z => code z = chosen)
  have hsub : retained ⊆ P.productive := Finset.filter_subset _ _
  have hmass' : massThreshold / (2 : ℝ) ^ Fintype.card (LayerSamplerVariables G I n B)
      ≤ A.law.mass retained := by
    have hcard : (Fintype.card (Finset (LayerSamplerVariables G I n B)) : ℝ) =
        (2 : ℝ) ^ Fintype.card (LayerSamplerVariables G I n B) := by
      simp only [Fintype.card_finset, Nat.cast_pow, Nat.cast_ofNat]
    rw [hcard] at hmass
    exact (div_le_div_of_nonneg_right P.mass (by positivity)).trans hmass
  let refinement : P.Refinement cost
      (massThreshold / (2 : ℝ) ^ Fintype.card (LayerSamplerVariables G I n B)) scoreThreshold :=
    { retained := retained
      subset := hsub
      mass := hmass'
      cost_le := le_rfl
      step := fun z => (P.chart ⟨z.val, hsub z.property⟩).step
      step_pos := fun z => (P.chart ⟨z.val, hsub z.property⟩).step_pos
      slice := fun z => (P.chart ⟨z.val, hsub z.property⟩).slice
      dense := fun z => (P.chart ⟨z.val, hsub z.property⟩).dense
      inside := fun _ => Finset.Subset.refl _
      scoreLower := fun z => P.score ⟨z.val, hsub z.property⟩ }
  refine ⟨fun i => i ∈ chosen, refinement, ?_⟩
  intro z
  change (P.chart ⟨z.val, hsub z.property⟩).keep = _
  have hz : code z.val = chosen := (Finset.mem_filter.mp z.property).2
  have hc : Finset.univ.filter (P.chart ⟨z.val, hsub z.property⟩).keep = chosen := by
    simpa only [code, dite_eq_ite, dif_pos (hsub z.property)] using hz
  funext i
  apply propext
  rw [← hc]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem exists_common_keep_refinement_exp {p : ℝ}
    (hmass : 0 ≤ massThreshold)
    (hdim : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p) :
    ∃ (keep : LayerSamplerVariables G I n B → Prop)
      (refinement : P.Refinement cost (massThreshold * Real.exp (-p)) scoreThreshold),
      ∀ z : refinement.problem.productive, (refinement.problem.chart z).keep = keep := by
  obtain ⟨keep, refinement, hkeep⟩ := P.exists_common_keep_refinement
  have hpow : (2 : ℝ) ^ Fintype.card (LayerSamplerVariables G I n B) ≤ Real.exp p := by
    calc
      _ ≤ (Real.exp 1) ^ Fintype.card (LayerSamplerVariables G I n B) :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) _
      _ = Real.exp (Fintype.card (LayerSamplerVariables G I n B)) := by
        rw [← Real.exp_nat_mul]
        simp only [mul_one]
      _ ≤ _ := Real.exp_le_exp.mpr hdim
  have hsmall : massThreshold * Real.exp (-p) ≤
      massThreshold / (2 : ℝ) ^ Fintype.card (LayerSamplerVariables G I n B) := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hmass (by positivity) hpow
  let smaller : P.Refinement cost (massThreshold * Real.exp (-p)) scoreThreshold :=
    { refinement with mass := hsmall.trans refinement.mass }
  exact ⟨keep, smaller, hkeep⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateKeptSymbolFactors
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)

theorem withKeep_chart_recovered (z : P.productive) :
    AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
      P.centerLift z.val.1.val z.val.2.val (P.chart z).sample (P.chart z).read := by
  have h := (P.chart z).recovered
  simpa only [P.chart_centerLift z, P.chart_path z] using h

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedActualForecastSetup
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

section Generic

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

def preparedActualForecastShortSelection :
    PreparedActualForecastShortIndex B U b S → Σ j : Fin m, Fin (n j) :=
  Subtype.val

end Generic

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SampledNativeDetectionEmptyTags
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal

namespace NormalizedPolynomialTwist

variable {X Y : Type*} [Fintype X] [Fintype Y]
    {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def eraseEmptyTags
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (Y' : Type*) [Fintype Y'] [IsEmpty Y] :
    NormalizedPolynomialTwist X Y' periodCap coverCap L where
  modulus := W.modulus
  modulus_pos := W.modulus_pos
  modulus_bound := W.modulus_bound
  cover := W.cover
  cover_pos := W.cover_pos
  cover_bound := W.cover_bound
  mask := W.mask
  mask_bound := W.mask_bound
  smooth := fun z => W.smooth (z.1, 0)
  smooth_bound := fun z => W.smooth_bound _
  smooth_lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := W.smooth_lipschitz.dist_le_mul (x.1, 0) (y.1, 0)
    simp only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (show dist x.1 y.1 ≤ dist x y from le_max_left _ _) L.coe_nonneg)

variable [IsEmpty Y]

@[simp] theorem eraseEmptyTags_modulus
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (Y' : Type*) [Fintype Y'] : (W.eraseEmptyTags Y').modulus = W.modulus := rfl

@[simp] theorem eraseEmptyTags_cover
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (Y' : Type*) [Fintype Y'] : (W.eraseEmptyTags Y').cover = W.cover := rfl

@[simp] theorem eraseEmptyTags_mask
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (Y' : Type*) [Fintype Y'] : (W.eraseEmptyTags Y').mask = W.mask := rfl

@[simp] theorem eraseEmptyTags_smooth
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (Y' : Type*) [Fintype Y'] (z : (X → ℝ) × (Y' → UnitAddCircle)) :
    (W.eraseEmptyTags Y').smooth z = W.smooth (z.1, 0) := rfl

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PreparedCommonRadiusDensityCapNested
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal

theorem exists_prepared_commonRadius_densityCap_forward_bound (maxLayers : ℕ) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧ ∀ A : ℕ, A₀ ≤ A →
      ∀ {X J : Type} {m : ℕ} (prep : RankPreparationFamily X J m),
      m ≤ maxLayers → ∀ M Jalloc : ℕ,
      (∀ j, Fintype.card (prep j).Coord ≤ M) →
      ∀ p : ℝ, 0 ≤ p → (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ p →
      ∀ V : Fin m → ℝ≥0, (∀ j, (V j : ℝ) ≤ Real.exp p) →
      (probabilityProfileLipschitz : ℝ) ≤ Real.exp p →
      ∀ stageCountConstant : ℕ → ℕ, ∀ stage : ℕ,
      4 * ∏ j, earlyConstantDensityCap (Fintype.card (PreparedSamplerContinuous prep j))
        (preparedSamplerTransverse prep j) (allocatedCommonProductRadius m p p) (V j) ≤
          Real.exp (preparedFiniteForwardWork A stageCountConstant stage p) := by
  obtain ⟨A₀, hA₀, hcap⟩ := exists_commonRadius_densityCap_uniform_bound maxLayers
  refine ⟨A₀, hA₀, ?_⟩
  intro A hA X J m prep hm M Jalloc hM p hp hnum V hV hprofile constants stage
  obtain ⟨_, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions prep Jalloc hM
  have hmdim : m ≤ enlargedPreparedCommonSamplerDimension m M Jalloc := by
    unfold enlargedPreparedCommonSamplerDimension
    omega
  have h := hcap A hA m hm p hp ((Nat.cast_le.mpr hmdim).trans hnum)
    (fun j => Fintype.card (PreparedSamplerContinuous prep j)) (preparedSamplerTransverse prep)
    (fun j => (Nat.cast_le.mpr (hI j)).trans hnum)
    (fun j => (Nat.cast_le.mpr (hn j)).trans hnum) V hV hprofile
  apply h.trans (Real.exp_le_exp.mpr ?_)
  rw [preparedFiniteForwardWork_eq]
  exact pow_le_pow_left₀ (by positivity)
    (add_le_add (le_preparedFiniteForwardParameter A constants stage hp) le_rfl) A

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal

theorem exists_prepared_commonRadius_densityCap_nested_bound (maxLayers : ℕ) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧ ∀ A : ℕ, A₀ ≤ A →
      ∀ {X J : Type} {m : ℕ} (prep : RankPreparationFamily X J m),
      m ≤ maxLayers → ∀ M Jalloc : ℕ,
      (∀ j, Fintype.card (prep j).Coord ≤ M) →
      ∀ p : ℝ, 0 ≤ p → (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ p →
      ∀ V : Fin m → ℝ≥0, (∀ j, (V j : ℝ) ≤ Real.exp p) →
      (probabilityProfileLipschitz : ℝ) ≤ Real.exp p →
      ∀ constants : ℕ → ℕ, ∀ innerDepth outer inner : ℕ,
      4 * ∏ j, earlyConstantDensityCap (Fintype.card (PreparedSamplerContinuous prep j))
        (preparedSamplerTransverse prep j) (allocatedCommonProductRadius m p p) (V j) ≤
          Real.exp (preparedFiniteForwardWork A constants inner
            (candidateNestedForwardSeed A constants innerDepth outer p)) := by
  obtain ⟨A₀, hA₀, hcap⟩ := exists_prepared_commonRadius_densityCap_forward_bound maxLayers
  refine ⟨A₀, hA₀, ?_⟩
  intro A hA X J m prep hm M Jalloc hM p hp hnum V hV hprofile
    constants innerDepth outer inner
  have hAtwo : 2 ≤ A := hA₀.trans hA
  have h := hcap A hA prep hm M Jalloc hM p hp hnum V hV hprofile constants 0
  apply h.trans (Real.exp_le_exp.mpr ?_)
  rw [preparedFiniteForwardWork_eq, preparedFiniteForwardParameter_zero,
    preparedFiniteForwardWork_eq]
  apply pow_le_pow_left₀ (add_nonneg hp (Nat.cast_nonneg A))
  exact add_le_add
    ((le_candidateNestedForwardSeed A constants innerDepth outer hAtwo hp).trans
      (le_preparedFiniteForwardParameter A constants inner
        (candidateNestedForwardSeed_nonneg A constants innerDepth outer hp))) le_rfl

noncomputable def preparedCommonRadiusDensityCapNestedExponent (maxLayers : ℕ) : ℕ :=
  Classical.choose (exists_prepared_commonRadius_densityCap_nested_bound maxLayers)

theorem prepared_commonRadius_densityCap_nested_bound (maxLayers A : ℕ)
    (hA : preparedCommonRadiusDensityCapNestedExponent maxLayers ≤ A)
    {X J : Type} {m : ℕ} (prep : RankPreparationFamily X J m)
    (hm : m ≤ maxLayers) (M Jalloc : ℕ)
    (hM : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (p : ℝ) (hp : 0 ≤ p)
    (hnum : (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ p)
    (V : Fin m → ℝ≥0) (hV : ∀ j, (V j : ℝ) ≤ Real.exp p)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp p)
    (constants : ℕ → ℕ) (innerDepth outer inner : ℕ) :
    4 * ∏ j, earlyConstantDensityCap (Fintype.card (PreparedSamplerContinuous prep j))
      (preparedSamplerTransverse prep j) (allocatedCommonProductRadius m p p) (V j) ≤
        Real.exp (preparedFiniteForwardWork A constants inner
          (candidateNestedForwardSeed A constants innerDepth outer p)) :=
  (Classical.choose_spec (exists_prepared_commonRadius_densityCap_nested_bound maxLayers)).2
    A hA prep hm M Jalloc hM p hp hnum V hV hprofile constants innerDepth outer inner

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateSamplerFacts
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem currentGrade_spatial_support (z : P.productive) :
    z.val.2.val ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1 := by
  simpa only [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_eq]
    using z.val.2.property

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end


