-- Prove2me | Definitions.Def_OAIE3v2B277
-- name    : OAIE3v2B277
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T07:05:00.180625+00:00
-- url     : https://prove2.me/theorems/3f0ea7d6-689d-4c40-8fec-86af373efe4b
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 289 of 311
-- statement:
--   Definitions bundle 289 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B306`, `OAIE3v2B269`, `OAIE3v2B270`, `OAIE3v2B272` of this split.
--
--   Modules: `Dynamics/PreparedFiniteForwardActualNativeBudget.lean`, `Dynamics/PreparedFiniteNestedFrontNativeBudget.lean`, `Dynamics/PreparedFiniteNestedSourceLatePowerBudget.lean`, `Estimates/AllocatedExternalCandidateAdaptedOptionQuotientFactors.lean`, `Estimates/AllocatedExternalCandidateTaggedPairLongUniformFactors.lean`, `Estimates/AllocatedZeroLayerForwardFrontSourceProfile.lean`, `Estimates/AxisCompression.lean`, `Estimates/MixedPairComparison.lean`, `Estimates/MixedPrimitiveGowers.lean`, `Estimates/NativeRetainedInverseIntervals.lean`, `Estimates/NativeRetainedTargetCubeIntervals.lean`, `Estimates/NativeSeparatedSumIntervals.lean`, `Estimates/PhysicalCubeNativeDetection.lean`, `Estimates/PreparedFiniteNestedSourceArrays.lean`, `Estimates/PreparedModularGeneralDetectorLateCoarseConsumer.lean`, `Geometry/AllocatedExternalCandidateSpatialNativeAutomaticLongGeometry.lean`, `Geometry/AllocatedExternalCandidateSpatialNativeBudget.lean`, `Geometry/AllocatedExternalCandidateSpatialNativeLongCommonFactors.lean`, `Lattices/NativeIntegerBoxInverse.lean`, `Linear/NativeRankIteration.lean`, `Linear/PreparedFiniteNestedSourceProjectionBudget.lean`, `Polynomial/AllocatedNestedDegreeInduction.lean`, `Polynomial/CubeMixtureAllDegrees.lean`, `Polynomial/PreparedFiniteNestedDegreeSourceProfileScalars.lean`, `Probability/CubeMixtureNativeDetection.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B306
import Definitions.Def_OAIE3v2B269
import Definitions.Def_OAIE3v2B270
import Definitions.Def_OAIE3v2B272

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPairComparison
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_local_marked_family (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s (r + 1) N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) → W.HasLocalMarkedFamily hs C := by
  obtain ⟨a, _, hsource⟩ := exists_native_correlated_affine_comparison s hs
  let A₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (A₀ + (A₀ + 4) ^ 7)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  have hp : 0 ≤ p := (Nat.cast_nonneg _).trans W.family.complexity.1.1
  have hsum : (p + a) ^ a + ((p + a) ^ a + 4) ^ 7 ≤ (p + C) ^ C := by
    simpa [A₀, Polynomial.eval₂_pow] using hbound p hp
  have ha0 : 0 ≤ (p + a) ^ a := pow_nonneg (add_nonneg hp (Nat.cast_nonneg _)) _
  have haC : (p + a) ^ a ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hchart : ((p + a) ^ a + 4) ^ 7 ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left ha0).trans hsum
  obtain ⟨A, hpA, hAZ, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
      R, D, B, E, T, hT, hTfil, hcentral, hframe, hdata⟩ :=
    hsource W hf ((Real.exp_le_exp.mpr haC).trans hN)
  let Z := (p + nativeSharedFreeRelationConstant s hs) ^ nativeSharedFreeRelationConstant s hs
  have hZ : 0 ≤ Z := pow_nonneg (add_nonneg hp (Nat.cast_nonneg _)) _
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hfreq, ξ, hξ, hcommon, v, hv, hdep, out', H', q',
      hsub, hH', hshort', hdense, hAq', hq'Z, R', D', hcomp, htotal, hpair, hlower⟩ := hdata
  have hdense' : Real.exp (-Z) * N ≤ (H'.card : ℝ) := by
    simpa only [ZMod.card] using hdense
  have hlocal := hcomp.localMarkedFamily D E T hpA hT V (fun h => ξ * v h)
    (fun h => by rw [map_mul, hξ, hv h, one_mul]) D' hs hZ hdense'
  have htotal0 : 0 ≤ Z + (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
      sharedFreeCorrelationBudget s hs Z := by
    have hcorr0 : 0 ≤ sharedFreeCorrelationBudget s hs Z :=
      (show 0 ≤ sharedFreeCorrelationInput s Z by
        linarith only [(sharedFreeCorrelationInput_bounds s hZ le_rfl hZ).1]).trans
          (sharedFreeCorrelationInput_le_budget s hs hZ)
    exact add_nonneg (add_nonneg hZ (pow_nonneg (add_nonneg hZ (Nat.cast_nonneg _)) _)) hcorr0
  have htotalC : (Z + (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
      sharedFreeCorrelationBudget s hs Z + 4) ^ 7 ≤ (p + C) ^ C :=
    (pow_le_pow_left₀ (add_nonneg htotal0 (by norm_num))
      (add_le_add htotal (le_rfl : (4 : ℝ) ≤ 4)) 7).trans hchart
  exact ⟨A, hpA, hAZ, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
    R, D, B, E, T, hT, hTfil, hcentral, hframe, V, hfreq, ξ, hξ, hcommon,
    v, hv, hdep, out', H', q', hsub, hH', hshort', hdense, hAq', hq'Z,
    R', D', hlocal, htotalC, hpair.trans haC, hlower.trans haC⟩

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_local_induced_family (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s (r + 1) N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) → W.HasLocalInducedFamily hs C := by
  obtain ⟨a, _, hsource⟩ := exists_native_local_marked_family s hs
  obtain ⟨b, _, hlocalBudget⟩ := exists_localCoveredInducedBudget_bound s hs
  let A₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let Z₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C (nativeSharedFreeRelationConstant s hs)) ^
    nativeSharedFreeRelationConstant s hs
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (A₀ + (Z₀ + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let Z := (p + nativeSharedFreeRelationConstant s hs) ^ nativeSharedFreeRelationConstant s hs
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have htotal : (p + a) ^ a + (Z + b) ^ b ≤ (p + C) ^ C := by
    simpa [A₀, Z₀, Z, Polynomial.eval₂_pow] using hbudget p hp
  have haC : (p + a) ^ a ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans htotal
  have hbC : (Z + b) ^ b ≤ (p + C) ^ C := (le_add_of_nonneg_left (by positivity)).trans htotal
  obtain ⟨A, hpA, hAZ, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
    R, D, B, E, T, hT, hTfil, hcentral, hframe, hdata⟩ :=
    hsource W hf ((Real.exp_le_exp.mpr haC).trans hN)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hfreq, ξ, hξ, hcommon, v, hv, hdep, out', H', q', hsub, hH',
    hshort', hdense, hAq', hq'Z, R', D', hlocal, hchart, hpair, hlower⟩ := hdata
  obtain ⟨F⟩ := hframe
  have hinduced := hlocal.induce D E T hpA hT V (fun h => ξ * v h)
    (fun h => by rw [map_mul, hξ, hv h, one_mul]) D' B F hTfil hfreq hs hZ
  have hbound : localCoveredInducedBudget s hs A Z ≤ (p + C) ^ C :=
    (hlocalBudget A Z (hp.trans hpA) hAZ hZ).trans hbC
  refine ⟨A, hpA, hAZ, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
    R, D, B, E, T, hT, hTfil, hcentral, ⟨F⟩, V, hfreq, ξ, hξ, hcommon,
    v, hv, hdep, out', H', q', hsub, hH', hshort', hdense, hAq', hq'Z, R', D',
    hinduced, hbound, hchart.trans haC, hpair.trans haC, hlower.trans haC⟩

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_product_correlation (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s (r + 1) N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∃ J : Finset (ZMod N), J ⊆ W.shifts ∧ J.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (J.card : ℝ) ∧
        HasBoundedProductCorrelation (I := Fin W.family.outputDim) (s := s) (r := r) (degree := s - 1)
          (fun h : {h // h ∈ J} => h.val) (fun h z => multiplicativeDerivative f h.val z)
          W.mixed.outputDim ((p + C) ^ C) ((p + C) ^ C) ((p + C) ^ C) := by
  obtain ⟨a, _, hsource⟩ := exists_native_local_induced_family s hs
  let X : Polynomial ℕ := Polynomial.X
  let R₀ : Polynomial ℕ := (X + Polynomial.C a) ^ a
  let P₀ : Polynomial ℕ := X + 2 * R₀ + 6
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (R₀ + ((P₀ + 2) ^ 2 + P₀ + (P₀ + (P₀ ^ 2 + P₀ + 3) ^ 2) + P₀ ^ 2 + 4) + 1)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let Rcap := (p + a) ^ a
  let Pcap := p + 2 * Rcap + 6
  have hRcap : 0 ≤ Rcap := by dsimp [Rcap]; positivity
  have hPcap : 0 ≤ Pcap := by dsimp [Pcap]; positivity
  have htotal : Rcap + productNiltestBudget Pcap + 1 ≤ (p + C) ^ C := by
    simpa [X, R₀, P₀, Rcap, Pcap, productNiltestBudget, productObservableLipBudget,
      Polynomial.eval₂_pow] using hbudget p hp
  have hprod0 : 0 ≤ productNiltestBudget Pcap :=
    (sq_nonneg (Pcap + 2)).trans (productNiltestBudget_geometry hPcap)
  have hRC : Rcap ≤ (p + C) ^ C := by linarith
  have hPC : productNiltestBudget Pcap ≤ (p + C) ^ C := by linarith
  obtain ⟨A, hpA, hAZ, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
    R, D, B, E, T, hT, hTfil, hcentral, hframe, hdata⟩ :=
    hsource W hf ((Real.exp_le_exp.mpr hRC).trans hN)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hfreq, ξ, hξ, hcommon, v, hv, hdep, out', H', q', hsub, hH',
    hshort', hdense, hAq', hq'Z, R', D', hlocal, hbound, hchart, hpair, hlower⟩ := hdata
  obtain ⟨hBound, hFirst, J, hJH, hJ, hJcard, hproduct⟩ :=
    hlocal.product D E T hpA hT V (fun h => ξ * v h)
      (fun h => by rw [map_mul, hξ, hv h, one_mul]) D' hs
  refine ⟨J, hJH.trans hsub, hJ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (neg_le_neg (hchart.trans hRC))) (Nat.cast_nonneg N)).trans hJcard
  · apply hproduct.mono (hbound.trans hRC)
    · apply le_trans (productNiltestBudget_mono (by positivity) _) hPC
      change _ ≤ p + 2 * Rcap + 6
      change _ ≤ Rcap at hlower hbound
      linarith
    · apply le_trans (productNiltestBudget_mono (by positivity) _) hPC
      change _ ≤ p + 2 * Rcap + 6
      change _ ≤ Rcap at hbound
      linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankIteration
namespace OAI

section

namespace Erdos3

theorem exists_native_rank_descent (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (_W : NativeCorrelationStructure s (r + 1) N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativeCorrelationStructure s r N ((p + C) ^ C) f) := by
  obtain ⟨a, _, hproduct⟩ := exists_native_product_correlation s hs
  obtain ⟨b, _, hvertical⟩ := exists_native_product_verticalization s
  let X : Polynomial ℕ := Polynomial.X
  let R : Polynomial ℕ := X + (X + Polynomial.C a) ^ a + 2
  let Q : Polynomial ℕ := (R + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + Q)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let p₀ := (p + a) ^ a
  let p₁ := p + p₀ + 2
  let p₂ := (p₁ + b) ^ b
  have hp₀ : 0 ≤ p₀ := by dsimp [p₀]; positivity
  have hp₁ : 0 ≤ p₁ := by dsimp [p₁]; positivity
  have hp₂ : 0 ≤ p₂ := by dsimp [p₂]; positivity
  have htotal : p₁ + p₂ ≤ (p + C) ^ C := by
    simpa [X, R, Q, p₀, p₁, p₂, Polynomial.eval₂_pow] using hbudget p hp
  have hpp₁ : p ≤ p₁ := by dsimp [p₁]; linarith
  have hp₀p₁ : p₀ ≤ p₁ := by dsimp [p₁]; linarith
  have hp₀C : p₀ ≤ (p + C) ^ C := by linarith
  have hp₂C : p₂ ≤ (p + C) ^ C := by linarith
  obtain ⟨J, _, hJ, hdense, hcorr⟩ :=
    hproduct W hf ((Real.exp_le_exp.mpr hp₀C).trans hN)
  have hdense' : Real.exp (-p₁) * N ≤ (J.card : ℝ) :=
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hp₀p₁))
      (Nat.cast_nonneg _)).trans hdense
  have hdim : (W.mixed.outputDim : ℝ) ≤ Real.exp p₁ :=
    W.mixed.output_bound.trans (Real.exp_le_exp.mpr hpp₁)
  have hI : (Fintype.card (Fin W.family.outputDim) : ℝ) ≤ Real.exp p₁ := by
    simpa only [Fintype.card_fin] using W.family.output_bound.trans (Real.exp_le_exp.mpr hpp₁)
  obtain ⟨V⟩ := hvertical J W.mixed.outputDim hp₁ hf hJ hdense' hdim hI
    (hcorr.mono hp₀p₁ hp₀p₁ hp₀p₁)
  exact ⟨V.mono hp₂C⟩

end Erdos3

end

section

namespace Erdos3

theorem exists_native_rank_zero_reduction (s : ℕ) (hs : 2 ≤ s) (r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (_W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativeCorrelationStructure s 0 N ((p + C) ^ C) f) := by
  induction r with
  | zero =>
      refine ⟨2, le_rfl, ?_⟩
      intro N _ p f W _ _
      have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
      exact ⟨W.mono (by norm_num; nlinarith [sq_nonneg p])⟩
  | succ r ih =>
      obtain ⟨a, _, hstep⟩ := exists_native_rank_descent s hs
      obtain ⟨b, _, hiterate⟩ := ih
      let X : Polynomial ℕ := Polynomial.X
      let Q : Polynomial ℕ := (X + Polynomial.C a) ^ a
      obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
        (Q + (Q + Polynomial.C b) ^ b)
      refine ⟨C, hC, ?_⟩
      intro N _ p f W hf hN
      have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
      let q := (p + a) ^ a
      let q₂ := (q + b) ^ b
      have hq : 0 ≤ q := by dsimp [q]; positivity
      have hq₂ : 0 ≤ q₂ := by dsimp [q₂]; positivity
      have htotal : q + q₂ ≤ (p + C) ^ C := by
        simpa [X, Q, q, q₂, Polynomial.eval₂_pow] using hbudget p hp
      have hqC : q ≤ (p + C) ^ C := by linarith
      have hq₂C : q₂ ≤ (p + C) ^ C := by linarith
      obtain ⟨W₁⟩ := hstep W hf ((Real.exp_le_exp.mpr hqC).trans hN)
      obtain ⟨W₀⟩ := hiterate W₁ hf ((Real.exp_le_exp.mpr hq₂C).trans hN)
      exact ⟨W₀.mono hq₂C⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeRetainedInverseIntervals
namespace OAI

section

namespace Erdos3

theorem exists_retained_inverse_intervals {s A : ℕ} (hs : 2 ≤ s)
    (hI : CyclicNativeInverse s A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 2) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ W : NativeCorrelationStructure s 0 N q f,
      ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
      ∃ B : NativeRetainedMultilinearIntervalFamily W r,
      ∃ M : NativeMixedCorrelation s N ((p + C) ^ C) f,
        M.shifts = W.shifts ∧ M.mixed.dim = W.mixed.dim ∧
        NativeIntegerVectorEquivalence s ((p + C) ^ C) M.mixed.eval
          (fun k x => B.mixed.eval k (fun j => x j.1)) := by
  cases s with
  | zero => omega
  | succ s =>
    obtain ⟨a, _, hinitial⟩ := exists_initial_native_correlation_structure hI
    obtain ⟨b, _, hzero⟩ := exists_native_rank_zero_reduction (s + 1) hs (s + 1)
    obtain ⟨c, _, hfamily⟩ := exists_native_retained_multilinear_interval_family (s + 1)
    let X : Polynomial ℕ := Polynomial.X
    let P := (X + Polynomial.C a) ^ a
    let Q := (P + Polynomial.C b) ^ b
    let R := (Q + Polynomial.C c) ^ c
    let T := Q + 4
    let U := (T + 2) ^ 2 + T + (T + (T ^ 2 + T + 3) ^ 2) + T ^ 2 + 4
    obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + Q + R + U)
    refine ⟨C, hC, ?_⟩
    intro N _ p hp hN f hf hG
    let p₀ := (p + a) ^ a
    let q := (p₀ + b) ^ b
    let r := (q + c) ^ c
    have hp₀ : 0 ≤ p₀ := by dsimp [p₀]; positivity
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hu : 0 ≤ productNiltestBudget (q + 4) := by
      unfold productNiltestBudget productObservableLipBudget
      positivity
    have hsum : p₀ + q + r + productNiltestBudget (q + 4) ≤ (p + C) ^ C := by
      simpa [X, P, Q, R, T, U, p₀, q, r, productNiltestBudget,
        productObservableLipBudget, Polynomial.eval₂_pow] using hbudget p hp
    have hqC : q ≤ (p + C) ^ C := by linarith
    have hrC : r ≤ (p + C) ^ C := by linarith
    have huC : productNiltestBudget (q + 4) ≤ (p + C) ^ C := by linarith
    obtain ⟨W₁⟩ := hinitial hp f hf hG
    obtain ⟨W⟩ := hzero W₁ hf ((Real.exp_le_exp.mpr hqC).trans hN)
    obtain ⟨B⟩ := hfamily W hf
    let M := (W.absorbRankZero hq).mono huC
    exact ⟨q, hq, hqC, W, r, hr, hrC, B, M, rfl, rfl, B.equivalence.mono hrC⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeRetainedTargetCubeIntervals
namespace OAI

section

namespace Erdos3

theorem exists_retained_target_cube_intervals (d : ℕ) {A : ℕ}
    (hI : CyclicNativeInverse (d + 2) A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter
        (fun _ : ReplicatedIndex (mixedCorrelationDegree (d + 2)) => 1) q,
        W.dim ≤ 2 ^ (d + 3) * M.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
          (fun k x => W.eval k (fun j => x j.1)) ∧
        HasFixedTargetCubeIntervals f M (fun k x => W.eval k (fun j => x j.1)) ((p + C) ^ C) := by
  obtain ⟨a, _, hretained⟩ := exists_retained_inverse_intervals (by omega : 2 ≤ d + 2) hI
  obtain ⟨b, _, hfixed⟩ := NativeMixedCorrelation.exists_fixed_target_cube_intervals d
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  let R := (P + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + R)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let q := (p + a) ^ a
  let r := (q + b) ^ b
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : q + r ≤ (p + C) ^ C := by
    simpa [X, P, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  obtain ⟨q₀, hq₀, hq₀q, V, r₀, hr₀, hr₀q, B, M, hshifts, hdimension, E⟩ :=
    hretained hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hG
  let W := B.mixed.mono hr₀q
  have hdiag : NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
      (fun k x => W.eval k (fun j => x j.1)) := E
  have H := hfixed hq ((Real.exp_le_exp.mpr hrC).trans hN) f hf M
    (fun k x => W.eval k (fun j => x j.1)) (fun x => W.unit_eval _) hdiag
  have hdim : W.dim ≤ 2 ^ (d + 3) * M.mixed.dim := by
    change B.mixed.dim ≤ 2 ^ (d + 3) * M.mixed.dim
    rw [hdimension]
    exact B.mixed_dim
  exact ⟨q, hq, hqC, M, W, hdim, B.mixed_symmetric, hdiag, H.mono hrC⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSeparatedSumIntervals
namespace OAI

section

namespace Erdos3

theorem exists_retained_sum_target_intervals (d : ℕ) {A : ℕ}
    (hI : CyclicNativeInverse (d + 2) A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter
        (fun _ : ReplicatedIndex (mixedCorrelationDegree (d + 2)) => 1) q,
        W.dim ≤ 2 ^ (d + 3) * M.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
          (fun k x => W.eval k (fun j => x j.1)) ∧
        HasSumTargetIntervals f M (fun k x => W.eval k (fun j => x j.1)) ((p + C) ^ C) := by
  obtain ⟨a, _, hretained⟩ := exists_retained_target_cube_intervals d hI
  obtain ⟨b, _, habsorb⟩ := exists_absorb_fixed_target_cube_errors d
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  let R := (P + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + R)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let q := (p + a) ^ a
  let r := (q + b) ^ b
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : q + r ≤ (p + C) ^ C := by
    simpa [X, P, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  obtain ⟨q₀, hq₀, hq₀q, M, W, hdim, hsym, E, H⟩ :=
    hretained hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hG
  have hW : ∀ (k : Fin W.outputDim) (x : Fin 2 → ℤ),
      ‖W.eval k (fun j => x j.1)‖ ≤ 1 := fun k x => W.norm_eval k _
  have Hweighted := habsorb hq f hf M (fun k x => W.eval k (fun j => x j.1)) hW H
  exact ⟨q₀, hq₀, hq₀q.trans hqC, M, W, hdim, hsym, E, (Hweighted.to_sum hf hW).mono hrC⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPrimitiveGowers
namespace OAI

section

namespace Erdos3

theorem exists_retained_cyclic_sum (d : ℕ) {A : ℕ} (hI : CyclicNativeInverse (d + 2) A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
        W.dim ≤ 2 ^ (d + 3) * M.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
          (fun k x => W.eval k (fun j => x j.1)) ∧
        tensorPowerBudget (d + 2).factorial q ≤ (p + C) ^ C ∧
        HasCyclicMixedTargetCorrelation f
          (fun k x => (W.tensorPower (d + 2).factorial).eval k
            (mixedReplicatedInput (x 0) (fun j => x j.succ))) ((p + C) ^ C) := by
  obtain ⟨a, _, hretained⟩ := exists_retained_sum_target_intervals d hI
  obtain ⟨b, _, hseparate⟩ := exists_separated_sum_intervals d
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  let R := (P + Polynomial.C b) ^ b
  let T := Polynomial.C ((d + 2).factorial + 1) * (P + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (P + (2 * R + 8) + 4 * (5 * R + 10) + T)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let q := (p + a) ^ a
  let r := (q + b) ^ b
  let t := ((d + 2).factorial + 1 : ℝ) * (q + 1)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htotal : q + (2 * r + 8) + 4 * (5 * r + 10) + t ≤ (p + C) ^ C := by
    simpa [X, P, R, T, q, r, t, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hgridC : 2 * r + 8 ≤ (p + C) ^ C := by linarith
  have hcorrC : 2 * (2 * (5 * r + 10)) ≤ (p + C) ^ C := by linarith
  have htC : t ≤ (p + C) ^ C := by linarith
  obtain ⟨q₀, hq₀, hq₀q, M, W, hdim, hsym, E, H⟩ :=
    hretained hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hG
  have Hsep := hseparate hq hq₀q f hf M W hsym H
  have Hcommon := Hsep.common hr ((Real.exp_le_exp.mpr hgridC).trans hN) hf
    (fun k x => (W.tensorPower (d + 2).factorial).norm_eval k _)
  refine ⟨q₀, hq₀, hq₀q.trans hqC, M, W, hdim, hsym, E, ?_,
    ((Hcommon.positive (by positivity)).cyclic).mono hcorrC⟩
  apply le_trans ?_ htC
  have hqq : q₀ ≤ q := hq₀q
  exact mul_le_mul_of_nonneg_left (by linarith only [hqq] : q₀ + 1 ≤ q + 1) (by positivity)

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

theorem exists_retained_mixed_pair_factors (d : ℕ) {A : ℕ}
    (hI : CyclicNativeInverse (d + 2) A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
        W.dim ≤ 2 ^ (d + 3) * M.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
          (fun k x => W.eval k (fun j => x j.1)) ∧
        tensorPowerBudget (d + 2).factorial q ≤ (p + C) ^ C ∧
        ∃ u : ℝ, 0 ≤ u ∧ u ≤ (p + C) ^ C ∧
        ∃ (i j : Fin (W.tensorPower (d + 2).factorial).outputDim)
          (V : NativeSampleCorrelation (fun _ : Fin (d + 3) => 1) (d + 2) u
            Finset.univ (fun x : Fin (d + 3) → ZMod N => fun k => ((x k).val : ℤ))
            (fun x => (W.tensorPower (d + 2).factorial).mixedAntisymmetric i j (fun k => ((x k).val : ℤ)))),
          ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
            Nonempty (NativePolynomialOrbitFactors (pi V.mixedPairModels)
              V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
              (fun _ : Fin (d + 3) => (N : ℝ)) r) := by
  obtain ⟨a, _, hcyclic⟩ := exists_retained_cyclic_sum d hI
  obtain ⟨b, _, hpair⟩ := exists_cyclic_target_pair_factors d
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  let R := (P + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + R)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let q := (p + a) ^ a
  let r := (q + b) ^ b
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hsum : q + r ≤ (p + C) ^ C := by
    simpa [X, P, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  obtain ⟨q₀, hq₀, hq₀q, M, W, hdim, hsym, E, htensor, H⟩ :=
    hcyclic hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hG
  obtain ⟨u, hu, hur, i, j, V, R⟩ := hpair (W.tensorPower (d + 2).factorial) htensor f hf
    ((Real.exp_le_exp.mpr hrC).trans hN) H
  exact ⟨q₀, hq₀, hq₀q.trans hqC, M, W, hdim, hsym, E, htensor.trans hqC,
    u, hu, hur.trans hrC, i, j, V, r, hr, hrC, R⟩

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

theorem exists_retained_mixed_sampled_exchange (d : ℕ) {A : ℕ}
    (hI : CyclicNativeInverse (d + 2) A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      Real.exp ((p + e + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
        W.dim ≤ 2 ^ (d + 3) * M.mixed.dim ∧
        (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) a).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
          (fun k x => W.eval k (fun j => x j.1)) ∧
        tensorPowerBudget (d + 2).factorial q ≤ (p + C) ^ C ∧
        ∃ u : ℝ, 0 ≤ u ∧ u ≤ (p + C) ^ C ∧
        ∃ (i j : Fin (W.tensorPower (d + 2).factorial).outputDim)
          (V : NativeSampleCorrelation (fun _ : Fin (d + 3) => 1) (d + 2) u
            Finset.univ (fun x : Fin (d + 3) → ZMod N => fun k => ((x k).val : ℤ))
            (fun x => (W.tensorPower (d + 2).factorial).mixedAntisymmetric i j (fun k => ((x k).val : ℤ)))),
          ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
          ∃ _R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
            V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
            (fun _ : Fin (d + 3) => (N : ℝ)) r,
          ∃ G : (Fin (d + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
            (∀ π a c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (d + 2)
              ((p + e + C) ^ C) (G π a c))) ∧
            (∀ π a c (x : Fin 2 → ZMod N), ‖G π a c (fun k => ((x k).val : ℤ))‖ ≤ 1) ∧
            (∀ π a c, (𝔼 x : Fin 2 → ZMod N,
              ‖W.eval a (mixedSlotInput ((x (π 0)).val : ℤ) ((x (π 1)).val : ℤ)
                  (fun l => ((x (π l.succ.succ)).val : ℤ))) *
                  star (W.eval c (mixedSlotInput ((x (π 1)).val : ℤ) ((x (π 0)).val : ℤ)
                    (fun l => ((x (π l.succ.succ)).val : ℤ)))) -
                G π a c (fun k => ((x k).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨a, _, hpair⟩ := exists_retained_mixed_pair_factors d hI
  obtain ⟨b, _, hexchange⟩ := exists_mixed_precise_sampled_exchange (d + 1)
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  let S := (3 * P + X + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + S)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hG
  classical
  let v := p + e
  let t := (p + a) ^ a
  let tmax := (v + a) ^ a
  have hv : 0 ≤ v := add_nonneg hp he
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htm : 0 ≤ tmax := by dsimp [tmax]; positivity
  have hstep : t ≤ tmax := pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) a
  have hsum : tmax + (3 * tmax + v + b) ^ b ≤ (p + e + C) ^ C := by
    simpa [X, P, S, tmax, v, Polynomial.eval₂_pow] using hbudget v hv
  have htC : t ≤ (p + C) ^ C := by
    have h := hbudget p hp
    have hn : 0 ≤ (3 * t + p + b) ^ b := by positivity
    have hh : t + (3 * t + p + b) ^ b ≤ (p + C) ^ C := by
      simpa [X, P, S, t, Polynomial.eval₂_pow] using h
    linarith
  have htmaxC : tmax ≤ (p + e + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hsC : (3 * tmax + v + b) ^ b ≤ (p + e + C) ^ C :=
    (le_add_of_nonneg_left htm).trans hsum
  obtain ⟨q, hq, hqt, M, W, hdim, hsym, E, htensor, u, hu, hut, i, j, V, r, hr, hrt, ⟨R⟩⟩ :=
    hpair hp ((Real.exp_le_exp.mpr (hstep.trans htmaxC)).trans hN) f hf hG
  let : NeZero (d + 2).factorial := ⟨Nat.ne_of_gt (Nat.factorial_pos _)⟩
  have htnonneg : 0 ≤ tensorPowerBudget (d + 2).factorial q :=
    hq.trans (tensorPowerBudget_bounds (d + 2).factorial hq).1
  have hcost : (tensorPowerBudget (d + 2).factorial q + u + r + e + b) ^ b ≤
      (p + e + C) ^ C := by
    apply le_trans _ hsC
    apply pow_le_pow_left₀ (by positivity)
    dsimp only [v]
    linarith
  obtain ⟨G, hGa, hGb, hGc⟩ := hexchange (W := W) R hr he ((Real.exp_le_exp.mpr hcost).trans hN)
  refine ⟨q, hq, hqt.trans htC, M, W, hdim, hsym, E, htensor.trans htC,
    u, hu, hut.trans htC, i, j, V, r, hr, hrt.trans htC, R, G, ?_, hGb, hGc⟩
  intro π a c
  exact ⟨(Classical.choice (hGa π a c)).mono hcost⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators NNReal

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_retained_mixed_cyclic_comparison (d : ℕ) {A : ℕ}
    (hI : CyclicNativeInverse (d + 2) A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      Real.exp ((p + e + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
        W.dim ≤ 2 ^ (d + 3) * M.mixed.dim ∧
        (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) a).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
          (fun k x => W.eval k (fun j => x j.1)) ∧
        tensorPowerBudget (d + 2).factorial q ≤ (p + C) ^ C ∧
        ∃ u : ℝ, 0 ≤ u ∧ u ≤ (p + C) ^ C ∧
        ∃ (i j : Fin (W.tensorPower (d + 2).factorial).outputDim)
          (V : NativeSampleCorrelation (fun _ : Fin (d + 3) => 1) (d + 2) u
            Finset.univ (fun x : Fin (d + 3) → ZMod N => fun k => ((x k).val : ℤ))
            (fun x => (W.tensorPower (d + 2).factorial).mixedAntisymmetric i j (fun k => ((x k).val : ℤ)))),
          ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
          ∃ _R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
            V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
            (fun _ : Fin (d + 3) => (N : ℝ)) r,
          ∃ K : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
              (MixedNonconstantCorner d → Fin W.mixedIntegrationRoot.outputDim) → (Fin 2 → ℤ) → ℂ,
            (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (d + 2)
              ((p + e + C) ^ C) (K a b))) ∧
            (∀ a b, (𝔼 x : Fin 2 → ZMod N,
              ‖W.mixedIntegrationRoot.mixedCyclicDiagonalDerivative a x *
                  star (W.mixedIntegrationRoot.mixedCanonicalTensor b (fun k => ((x k).val : ℤ))) -
                K a b (fun k => ((x k).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨a, _, hmodel⟩ := exists_retained_mixed_sampled_exchange d hI
  obtain ⟨b, _, hroot⟩ := NativeMultidegreeNilcharacter.exists_mixedRootCyclicCorrection_expansion d
  let L := mixedCyclicErrorSlope d
  let J := mixedCyclicErrorBuffer d
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C a) ^ a
  let T := (X + Polynomial.C L * U + Polynomial.C J + Polynomial.C a) ^ a
  let S := (U + T + X + Polynomial.C J + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + T + X + Polynomial.C J + S)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hGowers
  let v := p + e
  let u := (p + a) ^ a
  let umax := (v + a) ^ a
  let accuracy := e + (L : ℝ) * u + J
  let t := (p + accuracy + a) ^ a
  let tmax := (v + (L : ℝ) * umax + J + a) ^ a
  let errorScale := e + J
  let smax := (umax + tmax + v + J + b) ^ b
  let δ : ℝ≥0 := ⟨Real.exp (-errorScale), (Real.exp_pos _).le⟩
  have hδval : (δ : ℝ) = Real.exp (-errorScale) := rfl
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have humax : 0 ≤ umax := by dsimp [umax]; positivity
  have ht : 0 ≤ t := by dsimp [t, accuracy]; positivity
  have htmax : 0 ≤ tmax := by dsimp [tmax]; positivity
  have hsmax : 0 ≤ smax := by dsimp [smax]; positivity
  have hb : 0 ≤ errorScale := by dsimp [errorScale]; positivity
  have hδ : 0 < δ := Real.exp_pos _
  have hinv : (δ : ℝ)⁻¹ ≤ Real.exp errorScale := by rw [hδval, ← Real.exp_neg, neg_neg]
  have hsum : umax + tmax + v + J + smax ≤ (p + e + C) ^ C := by
    simpa [X, U, T, S, umax, tmax, smax, v, Polynomial.eval₂_pow] using hbudget v hv
  have hum : u ≤ umax := pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) a
  have htm : t ≤ tmax := by
    apply pow_le_pow_left₀ (by dsimp [accuracy]; positivity)
    have hL := mul_le_mul_of_nonneg_left hum (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    dsimp [accuracy, v]
    linarith
  have htC : tmax ≤ (p + e + C) ^ C := by linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
  have hsC : smax ≤ (p + e + C) ^ C := by linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
  have hbC : errorScale ≤ (p + e + C) ^ C := by dsimp [errorScale, v] at *; linarith
  have huC : u ≤ (p + C) ^ C := by
    have hh : u + (p + (L : ℝ) * u + J + a) ^ a + p + J +
        (u + (p + (L : ℝ) * u + J + a) ^ a + p + J + b) ^ b ≤ (p + C) ^ C := by
      simpa [X, U, T, S, u, Polynomial.eval₂_pow] using hbudget p hp
    have h1 : 0 ≤ (p + (L : ℝ) * u + J + a) ^ a := by positivity
    have h2 : 0 ≤ (u + (p + (L : ℝ) * u + J + a) ^ a + p + J + b) ^ b := by positivity
    linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
  obtain ⟨q, hq, hqu, M, W, hdim, hsymm, E, htensor, u₀, hu₀, hu₀u, i, j, V, r, hr, hru,
      R, G, hG, hcap, herr⟩ :=
    hmodel hp (by dsimp [accuracy]; positivity : 0 ≤ accuracy)
      ((Real.exp_le_exp.mpr (htm.trans htC)).trans hN) f hf hGowers
  have hqmax : q ≤ umax := hqu.trans hum
  have hcost : (q + t + errorScale + b) ^ b ≤ (p + e + C) ^ C := by
    apply le_trans _ hsC
    apply pow_le_pow_left₀ (by positivity)
    dsimp [errorScale, v]
    linarith
  have herror := mixed_cyclic_error_bound d (Nat.cast_nonneg W.outputDim) hu
    (W.output_bound.trans (Real.exp_le_exp.mpr hqu)) ((Real.exp_le_exp.mpr hbC).trans hN)
  have hexchange : ∀ π a c, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval a (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval c (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π a c (fun k => ((x k).val : ℤ))‖) ≤ Real.exp (-accuracy) := by
    intro π a c
    simp only [mixedSwapSample_input]
    simpa only [mixedSampledInput_slots] using herr π a c
  refine ⟨q, hq, hqu.trans huC, M, W, hdim, hsymm, E, htensor.trans huC,
    u₀, hu₀, hu₀u.trans huC, i, j, V, r, hr, hru.trans huC, R,
    W.mixedRootCyclicCorrection N δ G, ?_, ?_⟩
  · intro a c
    exact ⟨(Classical.choice (hroot W N δ hδ ht hb hinv hsymm G hG a c)).mono hcost⟩
  · intro a c
    apply (W.mixedRootCyclicCorrection_mean_error δ hδ G (Real.exp_nonneg _) hcap hexchange a c).trans
    simpa only [W.mixedIntegrationRoot_outputDim, Nat.cast_pow, hδval, errorScale, accuracy, L, J] using herror

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

theorem exists_retained_mixed_original_integration (d : ℕ) {A : ℕ}
    (hI : CyclicNativeInverse (d + 2) A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      Real.exp ((p + e + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
        W.dim ≤ 2 ^ (d + 3) * M.mixed.dim ∧
        (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) a).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
          (fun k x => W.eval k (fun j => x j.1)) ∧
        tensorPowerBudget (d + 2).factorial q ≤ (p + C) ^ C ∧
        ∃ u : ℝ, 0 ≤ u ∧ u ≤ (p + C) ^ C ∧
        ∃ (i j : Fin (W.tensorPower (d + 2).factorial).outputDim)
          (V : NativeSampleCorrelation (fun _ : Fin (d + 3) => 1) (d + 2) u
            Finset.univ (fun x : Fin (d + 3) → ZMod N => fun k => ((x k).val : ℤ))
            (fun x => (W.tensorPower (d + 2).factorial).mixedAntisymmetric i j (fun k => ((x k).val : ℤ)))),
          ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
          ∃ _R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
            V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
            (fun _ : Fin (d + 3) => (N : ℝ)) r,
          ∃ K : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
              Fin M.mixed.outputDim → (MixedMiddleCorner d → Fin W.mixedIntegrationRoot.outputDim) →
              Fin W.mixedIntegrationRoot.outputDim → (Fin 2 → ℤ) → ℂ,
            (∀ a i b c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (d + 2)
              ((p + e + C) ^ C) (K a i b c))) ∧
            (∀ a i b c, (𝔼 x : Fin 2 → ZMod N,
              ‖W.mixedIntegrationRoot.mixedCyclicDiagonalDerivative a x *
                  (M.mixed.eval i (fun k => ((x k).val : ℤ)) *
                    (W.mixedIntegrationRoot.mixedMiddleTensor b (fun k => ((x k).val : ℤ)) *
                      W.mixedIntegrationRoot.eval c (fun _ => ((x 0).val : ℤ)))) -
                K a i b c (fun k => ((x k).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨a, _, hmodel⟩ := exists_retained_mixed_cyclic_comparison d hI
  obtain ⟨b, _, hexpansion⟩ := NativeMultidegreeNilcharacter.exists_mixedOriginalWeightCorrection_expansion d
  let L := mixedRootTensorExponent d * (d + 3)
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C a) ^ a
  let T := (X + Polynomial.C L * U + Polynomial.C a) ^ a
  let S := (U + T + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + T + S)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hGowers
  let v := p + e
  let u := (p + a) ^ a
  let umax := (v + a) ^ a
  let accuracy := e + (L : ℝ) * u
  let t := (p + accuracy + a) ^ a
  let tmax := (v + (L : ℝ) * umax + a) ^ a
  let smax := (umax + tmax + b) ^ b
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have humax : 0 ≤ umax := by dsimp [umax]; positivity
  have ht : 0 ≤ t := by dsimp [t, accuracy]; positivity
  have htmax : 0 ≤ tmax := by dsimp [tmax]; positivity
  have hsmax : 0 ≤ smax := by dsimp [smax]; positivity
  have hsum : umax + tmax + smax ≤ (p + e + C) ^ C := by
    simpa [X, U, T, S, umax, tmax, smax, v, Polynomial.eval₂_pow] using hbudget v hv
  have hum : u ≤ umax := pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) a
  have htm : t ≤ tmax := by
    apply pow_le_pow_left₀ (by dsimp [accuracy]; positivity)
    have hL := mul_le_mul_of_nonneg_left hum (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    dsimp [accuracy, v]
    linarith
  have htC : tmax ≤ (p + e + C) ^ C := by linarith
  have hsC : smax ≤ (p + e + C) ^ C := by linarith
  have huC : u ≤ (p + C) ^ C := by
    have hh : u + (p + (L : ℝ) * u + a) ^ a +
        (u + (p + (L : ℝ) * u + a) ^ a + b) ^ b ≤ (p + C) ^ C := by
      simpa [X, U, T, S, u, Polynomial.eval₂_pow] using hbudget p hp
    have h1 : 0 ≤ (p + (L : ℝ) * u + a) ^ a := by positivity
    have h2 : 0 ≤ (u + (p + (L : ℝ) * u + a) ^ a + b) ^ b := by positivity
    linarith
  obtain ⟨q, hq, hqu, M, W, hdim, hsymm, E, htensor, u₀, hu₀, hu₀u, i, j, V, r, hr, hru,
      R, K, hK, herr⟩ :=
    hmodel hp (by dsimp [accuracy]; positivity : 0 ≤ accuracy)
      ((Real.exp_le_exp.mpr (htm.trans htC)).trans hN) f hf hGowers
  have hqmax : q ≤ umax := hqu.trans hum
  have hcost : (q + t + b) ^ b ≤ (p + e + C) ^ C := by
    apply le_trans _ hsC
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hd : (W.outputDim : ℝ) ≤ Real.exp u :=
    W.output_bound.trans (Real.exp_le_exp.mpr hqu)
  have hpow : (W.outputDim : ℝ) ^ L ≤ Real.exp ((L : ℝ) * u) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hd L).trans_eq (Real.exp_nat_mul u L).symm
  have hrootDim : (W.mixedIntegrationRoot.outputDim : ℝ) ^ (d + 3) ≤ Real.exp ((L : ℝ) * u) := by
    simpa only [W.mixedIntegrationRoot_outputDim, Nat.cast_pow, ← pow_mul, L] using hpow
  have herror : (W.mixedIntegrationRoot.outputDim : ℝ) ^ (d + 3) * Real.exp (-accuracy) ≤ Real.exp (-e) := by
    calc
      _ ≤ Real.exp ((L : ℝ) * u) * Real.exp (-accuracy) :=
        mul_le_mul_of_nonneg_right hrootDim (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [accuracy]; ring
  refine ⟨q, hq, hqu.trans huC, M, W, hdim, hsymm, E, htensor.trans huC,
    u₀, hu₀, hu₀u.trans huC, i, j, V, r, hr, hru.trans huC, R,
    (fun a i b c => M.mixed.mixedOriginalWeightCorrection W K a i (mixedSplitHigherMerge b c)), ?_, ?_⟩
  · intro a i b c
    exact ⟨(Classical.choice (hexpansion M.mixed W ht E K hK a i (mixedSplitHigherMerge b c))).mono hcost⟩
  · intro a i b c
    have H := M.mixed.mixedOriginalWeightCorrection_mean_error W K
      (fun a (x : Fin 2 → ZMod N) => W.mixedIntegrationRoot.mixedCyclicDiagonalDerivative a x)
      herr a i (mixedSplitHigherMerge b c)
    simpa only [NativeMultidegreeNilcharacter.mixedHigherTensor_split] using H.trans herror

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_mixed_primitive_rows (d : ℕ) {I : ℕ} (hI : CyclicNativeInverse (d + 2) I) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
      ∃ a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim,
      ∃ b : (MixedMiddleCorner d → Fin W.mixedIntegrationRoot.outputDim),
        Nonempty (NativeMeanRowCorrelation (fun _ : Fin 2 => 1) (d + 2) ((p + C) ^ C)
          (fun h n : ZMod N => ![(h.val : ℤ), (n.val : ℤ)])
          (M.mixedPrimitiveRow W.mixedIntegrationRoot a b)) := by
  obtain ⟨A, _, hintegrate⟩ := exists_retained_mixed_original_integration d hI
  let L := mixedRowCoordinateCount d
  let B0 := mixedRootTensorExponent d + 1
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let R := Polynomial.C B0 * (U + 1)
  let E := 4 * U + Polynomial.C L * R + 4
  let T := (X + E + Polynomial.C A) ^ A
  let V := 4 * U + 2 + Polynomial.C L * R + T
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + R + E + T + V)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let u := (p + A) ^ A
  let r := (B0 : ℝ) * (u + 1)
  let e := 4 * u + (L : ℝ) * r + 4
  let t := (p + e + A) ^ A
  let v := 4 * u + 2 + (L : ℝ) * r + t
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hsum : u + r + e + t + v ≤ (p + C) ^ C := by
    simpa [X, U, R, E, T, V, u, r, e, t, v, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := by linarith
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  obtain ⟨q, hq, hqu, M, W, hdim, hsymm, E, htensor, u0, hu0, hu0u,
    i, j, Vpair, rpair, hrpair, hrbound, R, K, hK, herr⟩ :=
    hintegrate hp he ((Real.exp_le_exp.mpr htC).trans hN) f hf hGowers
  obtain ⟨out, H, hHM, hH, hdense, hcorr⟩ := M.exists_fixed_normalized_residual_coordinate
  let B := W.mixedIntegrationRoot
  have hroot : tensorPowerBudget (mixedRootTensorExponent d) q ≤ r := by
    dsimp [tensorPowerBudget, r, B0]
    push_cast
    exact mul_le_mul_of_nonneg_left (show q + 1 ≤ u + 1 by dsimp [u]; linarith) (by positivity)
  have hD : (B.outputDim : ℝ) ≤ Real.exp r :=
    B.output_bound.trans (Real.exp_le_exp.mpr hroot)
  have hDL : (B.outputDim : ℝ) ^ L ≤ Real.exp ((L : ℝ) * r) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hD L).trans_eq (Real.exp_nat_mul r L).symm
  let J := ((Fin B.outputDim × Fin B.outputDim) × (MixedMiddleCorner d → Fin B.outputDim)) × Fin B.outputDim
  let z (abc : J) := 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
    M.normalizedResidualRow h n *
      (B.mixedCyclicDiagonalDerivative abc.1.1 ![h, n] *
        B.mixedMiddleTensor abc.1.2 ![(h.val : ℤ), (n.val : ℤ)]) *
          star (K abc.1.1 out abc.1.2 abc.2 ![(h.val : ℤ), (n.val : ℤ)])‖
  have hcard : (Fintype.card J : ℝ) ≤ Real.exp ((L : ℝ) * r) := by
    have hc : (Fintype.card J : ℝ) = (B.outputDim : ℝ) ^ L := mixedRowIndex_card d B.outputDim
    rw [hc]
    exact hDL
  have hmass : Real.exp (-(4 * u)) ≤ 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
      M.normalizedResidualRow h n * star (M.mixed.evalCyclic N out (correlationInput h n))‖ := by
    have hh := dense_set_mean_lower_bound H _ (fun _ => norm_nonneg _)
      (Real.exp_nonneg (-(2 * q))) (by simpa only [ZMod.card] using hdense) hcorr
    have heq : Real.exp (-(2 * q)) * Real.exp (-(2 * q)) = Real.exp (-(4 * q)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [heq] at hh
    exact (Real.exp_le_exp.mpr (by linarith)).trans hh
  have htransfer := M.mixed.mixed_original_row_correlation_bound W out
    M.normalizedResidualRow (M.normalizedResidualRow_norm hf)
    (fun a b c => K a out b c) (fun a b c => herr a out b c)
  change _ ≤ (∑ abc : J, z abc) + (B.outputDim : ℝ) ^ L * Real.exp (-e) at htransfer
  let δ := Real.exp (-(4 * u + 2))
  have hδ : 0 < δ := Real.exp_pos _
  have herror : (B.outputDim : ℝ) ^ L * Real.exp (-e) ≤ δ := by
    calc
      _ ≤ Real.exp ((L : ℝ) * r) * Real.exp (-e) :=
        mul_le_mul_of_nonneg_right hDL (Real.exp_nonneg _)
      _ = Real.exp (-(4 * u + 4)) := by rw [← Real.exp_add]; congr 1; dsimp [e]; ring
      _ ≤ δ := Real.exp_le_exp.mpr (by linarith)
  have htwo : 2 * δ ≤ Real.exp (-(4 * u)) := by
    calc
      _ ≤ Real.exp 2 * δ := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) hδ.le
      _ = _ := by dsimp [δ]; rw [← Real.exp_add]; congr 1; ring
  have hmass' : δ ≤ ∑ abc : J, z abc := by linarith
  obtain ⟨abc, habc⟩ := exists_large_nonnegative_weighted_term (fun _ : J => (1 : ℝ)) z
    (fun _ => by norm_num) (fun _ => Finset.expect_nonneg (fun _ _ => norm_nonneg _))
    hδ (Real.exp_pos _) (by simpa using hcard) (by simpa only [one_mul] using hmass')
  have habc' : Real.exp (-(4 * u + 2 + (L : ℝ) * r)) ≤ z abc := by
    have heq : δ / Real.exp ((L : ℝ) * r) = Real.exp (-(4 * u + 2 + (L : ℝ) * r)) := by
      dsimp [δ]; rw [← Real.exp_sub]; congr 1; ring
    rwa [heq] at habc
  let expansion := Classical.choice (hK abc.1.1 out abc.1.2 abc.2)
  obtain ⟨P⟩ := NativeMeanRowCorrelation.exists_of_expansion expansion
    (by positivity : 0 ≤ 4 * u + 2 + (L : ℝ) * r) habc'
  have heq : (fun h n : ZMod N => M.normalizedResidualRow h n *
      (B.mixedCyclicDiagonalDerivative abc.1.1 ![h, n] *
        B.mixedMiddleTensor abc.1.2 ![(h.val : ℤ), (n.val : ℤ)])) =
      M.mixedPrimitiveRow B abc.1.1 abc.1.2 := by
    funext h n
    exact (M.mixedPrimitiveRow_eq B abc.1.1 abc.1.2 h n).symm
  refine ⟨q, hq, hqu.trans huC, M, W, abc.1.1, abc.1.2, ?_⟩
  exact ⟨heq ▸ P.mono hvC⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_mixed_residual_cross_rows (d : ℕ) {I : ℕ} (hI : CyclicNativeInverse (d + 2) I) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
      ∃ a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim,
      ∃ b : (MixedMiddleCorner d → Fin W.mixedIntegrationRoot.outputDim),
        Nonempty (NativeMeanRowCorrelation (fun _ : Fin 2 => 1) (d + 2) ((p + C) ^ C)
          (fun h n : ZMod N => ![(h.val : ℤ), (n.val : ℤ)])
          (fun h n =>
            (W.mixedIntegrationRoot.mixedPrimitiveFactor f a.1 n *
              star (W.mixedIntegrationRoot.mixedPrimitiveFactor f a.2 (n + h))) *
                star (M.mixedResidualRowFactor W.mixedIntegrationRoot b h (fun _ => (n.val : ℤ))))) ∧
        (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (d + 1) ((p + C) ^ C)
          (M.mixedResidualRowFactor W.mixedIntegrationRoot b h))) ∧
        (∀ h x, ‖M.mixedResidualRowFactor W.mixedIntegrationRoot b h x‖ ≤ 1) := by
  obtain ⟨A, _, hrows⟩ := exists_mixed_primitive_rows d hI
  obtain ⟨B, _, hfactor⟩ := NativeMixedCorrelation.exists_mixedResidualRowFactor_expansion d
  let n := mixedRootTensorExponent d
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (Polynomial.C (n + 2) * (U + 1) + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let u := (p + A) ^ A
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsum : u + (((n : ℝ) + 2) * (u + 1) + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, U, u, Polynomial.eval₂_pow] using hbudget p hp
  have huC : u ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  obtain ⟨q, hq, hqu, M, W, a, b, ⟨V⟩⟩ :=
    hrows hp ((Real.exp_le_exp.mpr huC).trans hN) f hf hGowers
  have hcost : (q + tensorPowerBudget (mixedRootTensorExponent d) q + B) ^ B ≤ (p + C) ^ C := by
    apply le_trans _ ((le_add_of_nonneg_left hu).trans hsum)
    apply pow_le_pow_left₀ (by unfold tensorPowerBudget; positivity)
    simp only [tensorPowerBudget]
    have hm := mul_le_mul_of_nonneg_left (show q + 1 ≤ u + 1 by dsimp [u]; linarith)
      (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
    change q + ((n : ℝ) + 1) * (q + 1) + B ≤ ((n : ℝ) + 2) * (u + 1) + B
    nlinarith
  have heq : M.mixedPrimitiveRow W.mixedIntegrationRoot a b =
      (fun h n =>
        (W.mixedIntegrationRoot.mixedPrimitiveFactor f a.1 n *
          star (W.mixedIntegrationRoot.mixedPrimitiveFactor f a.2 (n + h))) *
            star (M.mixedResidualRowFactor W.mixedIntegrationRoot b h (fun _ => (n.val : ℤ)))) := by
    funext h n
    exact M.mixedPrimitiveRow_cross_residual W.mixedIntegrationRoot a b h n
  refine ⟨q, hq, hqu.trans huC, M, W, a, b, ⟨heq ▸ V.mono huC⟩, ?_, ?_⟩
  · intro h
    exact ⟨(Classical.choice (hfactor M W.mixedIntegrationRoot b h)).mono hcost⟩
  · intro h x
    exact M.mixedResidualRowFactor_norm W.mixedIntegrationRoot b h x

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeMeanRowCorrelation.lie NativeMeanRowCorrelation.algebra
  NativeMeanRowCorrelation.topology NativeMeanRowCorrelation.topologicalAdd
  NativeMeanRowCorrelation.continuousSMul NativeMeanRowCorrelation.hausdorff

theorem exists_mixed_primitive_gowers (d : ℕ) {I : ℕ} (hI : CyclicNativeInverse (d + 2) I) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
        ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
        ∃ i : Fin W.outputDim,
          Real.exp (-((p + C) ^ C)) ≤ gowersNorm (d + 3) (W.mixedPrimitiveFactor f i) := by
  obtain ⟨A, _, hrows⟩ := exists_mixed_residual_cross_rows d hI
  obtain ⟨B, _, hcross⟩ := RationalFilteredNilmanifold.exists_gowers_of_residual_cross_rows (d + 2) (by omega)
  let n := mixedRootTensorExponent d
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + Polynomial.C (n + 1) * (U + 1) + (U + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let u := (p + A) ^ A
  let v := (u + B) ^ B
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have htotal : u + ((n : ℝ) + 1) * (u + 1) + v ≤ (p + C) ^ C := by
    simpa [X, U, u, v, Polynomial.eval₂_pow] using hbudget p hp
  have hr : 0 ≤ ((n : ℝ) + 1) * (u + 1) := by positivity
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  obtain ⟨q, hq, hqu, M, W, a, b, ⟨V⟩, hR, hRnorm⟩ :=
    hrows hp ((Real.exp_le_exp.mpr huC).trans hN) f hf hGowers
  have hc := hcross V.model V.test hu V.complexity
    ((Real.exp_le_exp.mpr hvC).trans hN)
    (W.mixedIntegrationRoot.mixedPrimitiveFactor f a.1) (W.mixedIntegrationRoot.mixedPrimitiveFactor f a.2)
    (M.mixedResidualRowFactor W.mixedIntegrationRoot b)
    (W.mixedIntegrationRoot.mixedPrimitiveFactor_norm f hf a.1)
    (W.mixedIntegrationRoot.mixedPrimitiveFactor_norm f hf a.2)
    (fun h n => hRnorm h (fun _ => (n.val : ℤ))) hR V.correlation
  have hroot : 0 ≤ tensorPowerBudget (mixedRootTensorExponent d) q := by unfold tensorPowerBudget; positivity
  have hrootC : tensorPowerBudget (mixedRootTensorExponent d) q ≤ (p + C) ^ C := by
    have hm := mul_le_mul_of_nonneg_left (show q + 1 ≤ u + 1 by dsimp [u]; linarith)
      (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
    change ((n : ℝ) + 1) * (q + 1) ≤ (p + C) ^ C
    linarith
  exact ⟨tensorPowerBudget (mixedRootTensorExponent d) q, hroot, hrootC, W.mixedIntegrationRoot, a.2,
    (Real.exp_le_exp.mpr (neg_le_neg hvC)).trans hc⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AxisCompression
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology
  NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_mixed_primitive_correlation_large_modulus (d : ℕ) {I : ℕ}
    (hI : CyclicNativeInverse (d + 2) I) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ g ∈ nativeCyclicFunctions (d + 3) N ((p + C) ^ C),
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n, f n * star (g n)‖ := by
  obtain ⟨A, _, hprimitive⟩ := exists_mixed_primitive_gowers d hI
  let B := I
  have hinverse : CyclicNativeInverse (d + 2) B := hI
  obtain ⟨D, _, hmodel⟩ := NativeMultidegreeNilcharacter.exists_mixed_primitive_niltest_budget d
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let V := (U + 2 + Polynomial.C B) ^ B
  let R := U + V + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + V + (R + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let u := (p + A) ^ A
  let v := (u + 2 + B) ^ B
  let r := u + v + 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : u + v + (r + D) ^ D ≤ (p + C) ^ C := by
    simpa [X, U, V, R, u, v, r, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (r + D) ^ D := by positivity
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  have hmC : (r + D) ^ D ≤ (p + C) ^ C := by linarith
  obtain ⟨q, hq, hqu, W, i, hW⟩ :=
    hprimitive hp ((Real.exp_le_exp.mpr huC).trans hN) f hf hGowers
  obtain ⟨g, ⟨G⟩, hg⟩ := hinverse (by linarith : 2 ≤ u + 2)
    (W.mixedPrimitiveFactor f i) (W.mixedPrimitiveFactor_norm f hf i)
    ((Real.exp_le_exp.mpr (by linarith : -(u + 2) ≤ -u)).trans hW)
  have hqr : q ≤ r := by dsimp [r]; linarith
  have hvr : v ≤ r := by dsimp [r]; linarith
  have hgmodel : g ∈ nativeCyclicFunctions (d + 2) N r :=
    ⟨{ G with complexity := G.complexity.mono hvr }⟩
  have hm := hmodel hr (W.mono hqr) i g hgmodel
  have hm' : (fun n : ZMod N => star (W.eval i (fun _ => (n.val : ℤ))) * g n) ∈
      nativeCyclicFunctions (d + 3) N ((r + D) ^ D) := by
    simpa only [NativeMultidegreeNilcharacter.mono_eval] using hm
  obtain ⟨M⟩ := hm'
  refine ⟨fun n => star (W.eval i (fun _ => (n.val : ℤ))) * g n,
    ⟨{ M with complexity := M.complexity.mono hmC }⟩, ?_⟩
  have heq : (𝔼 n : ZMod N, f n * star (star (W.eval i (fun _ => (n.val : ℤ))) * g n)) =
      𝔼 n : ZMod N, W.mixedPrimitiveFactor f i n * star (g n) := by
    apply Finset.expect_congr rfl
    intro n _
    simp only [NativeMultidegreeNilcharacter.mixedPrimitiveFactor, star_mul, star_star]
    ring
  rw [heq]
  exact (Real.exp_le_exp.mpr (neg_le_neg hvC)).trans hg

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology
  NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_cyclicNativeInverse_step (d : ℕ) {I : ℕ}
    (hI : CyclicNativeInverse (d + 2) I) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicNativeInverse (d + 3) C := by
  obtain ⟨A, _, hlarge⟩ := exists_mixed_primitive_correlation_large_modulus d hI
  let L := 2 ^ (d + 4)
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + Polynomial.C L * X + 211)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hGowers
  have hp0 : 0 ≤ p := by linarith
  let u := (p + A) ^ A
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hLp : 0 ≤ (L : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp0
  have hsum : u + (L : ℝ) * p + 211 ≤ (p + C) ^ C := by
    simpa [X, u, Polynomial.eval₂_pow] using hbudget p hp0
  have huC : u ≤ (p + C) ^ C := by linarith
  by_cases hN : Real.exp u ≤ (N : ℝ)
  · obtain ⟨g, ⟨M⟩, hcorr⟩ := hlarge hp0 hN f hf hGowers
    exact ⟨g, ⟨{ M with complexity := M.complexity.mono huC }⟩,
      (Real.exp_le_exp.mpr (neg_le_neg huC)).trans hcorr⟩
  · obtain ⟨g, ⟨M⟩, hcorr⟩ :=
      exists_native_cyclic_small_modulus_correlation (d + 3) (by omega) (not_le.mp hN).le f hf hGowers
    have h211 : (211 : ℝ) ≤ (p + C) ^ C := by linarith
    have hc : (L : ℝ) * p + u ≤ (p + C) ^ C := by linarith
    exact ⟨g, ⟨{ M with complexity := M.complexity.mono h211 }⟩,
      (Real.exp_le_exp.mpr (neg_le_neg hc)).trans hcorr⟩

theorem exists_cyclicNativeInverse_add_two (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicNativeInverse (d + 2) C := by
  induction d with
  | zero => exact exists_cyclicNativeInverse_two
  | succ d ih =>
      obtain ⟨I, _, hI⟩ := ih
      exact exists_cyclicNativeInverse_step d hI

end Erdos3

end

section

namespace Erdos3

theorem exists_cyclicNativeInverse_positive (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicNativeInverse s C := by
  cases s with
  | zero => omega
  | succ s =>
      cases s with
      | zero => exact ⟨2, le_rfl, cyclicNativeInverse_one⟩
      | succ s => exact exists_cyclicNativeInverse_add_two s

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology
  NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_native_inverse_on_cyclic_encoding (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] [DecidableEq σ] {N : ℕ} [NeZero N]
      (Q : Finset (σ → ℤ)), Q.Nonempty → ∀ (φ : (σ → ℤ) →+ ℤ),
      ReflectsPairSums ((Int.castAddHom (ZMod N)).comp φ) (Q : Set (σ → ℤ)) →
      (∀ x ∈ Q, 0 ≤ φ x ∧ φ x < (N : ℤ)) →
      ∀ {p q : ℝ}, 2 ≤ p → 0 ≤ q → Real.exp (-q) ≤ (Q.card : ℝ) / (N : ℝ) →
      ∀ f : (σ → ℤ) → ℂ, (∀ x ∈ Q, ‖f x‖ ≤ 1) →
      Real.exp (-p) ≤ finiteSupportGowersNorm (s + 1) Q f →
      ∃ V : NativeSampleCorrelation (fun _ : σ => 1) s ((p + q + C) ^ C) Q id f,
        V.test.normBound ≤ 1 := by
  obtain ⟨C, hC, hinverse⟩ := exists_cyclicNativeInverse_positive s hs
  refine ⟨C, hC, ?_⟩
  intro σ _ _ N _ Q hQ φ hφ hrep p q hp hq hden f hf hGowers
  let ψ : (σ → ℤ) →+ ZMod N := (Int.castAddHom (ZMod N)).comp φ
  let F := imageExtension ψ Q f
  have hF : ∀ y, ‖F y‖ ≤ 1 := imageExtension_norm_le_one ψ Q f hφ.injOn hf
  have hG : Real.exp (-(p + q)) ≤ gowersNorm (s + 1) F :=
    exp_le_gowers_imageExtension s ψ Q hφ f (by simpa only [ZMod.card] using hden) hGowers
  obtain ⟨g, ⟨M⟩, hcorr⟩ := hinverse (by linarith : 2 ≤ p + q) F hF hG
  let T := M.test.linearPullbackHom (fun _ : Unit => φ)
  have heval (x : σ → ℤ) (hx : x ∈ Q) : T.eval x = g (ψ x) := by
    change (M.test.linearPullbackHom (fun _ : Unit => φ)).eval x = g (ψ x)
    rw [RationalFilteredNilmanifold.Niltest.eval_linearPullbackHom, M.eval]
    change M.test.eval (fun _ => φ x) = M.test.eval (fun _ => (((φ x : ZMod N).val) : ℤ))
    simp only [ZMod.val_intCast, Int.emod_eq_of_lt (hrep x hx).1 (hrep x hx).2]
  refine ⟨{
    L := M.L
    dim := M.dim
    model := M.model
    test := T
    complexity := M.complexity
    correlation := ?_ }, ?_⟩
  · have hmean : (𝔼 x ∈ Q, f x * star (T.eval x)) =
        (𝔼 x ∈ Q, f x * star (g (ψ x))) := by
      apply Finset.expect_congr rfl
      intro x hx
      rw [heval x hx]
    change Real.exp (-((p + q + C) ^ C)) ≤ ‖𝔼 x ∈ Q, f x * star (T.eval x)‖
    rw [hmean]
    exact hcorr.trans (norm_expect_imageExtension_mul_le ψ Q hQ hφ.injOn f (fun y => star (g y)))
  · exact M.norm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerBoxInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_native_integer_box_inverse (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {n : ℕ} (T : Fin n → ℕ) [∀ i, NeZero (T i)]
      {p : ℝ}, 2 ≤ p → ∀ f : (Fin n → ℤ) → ℂ,
      (∀ x ∈ integerBox T, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ integerBoxGowersNorm T (s + 1) f →
      ∃ V : NativeSampleCorrelation (fun _ : Fin n => 1) s ((p + n + C) ^ C) (integerBox T) id f,
        V.test.normBound ≤ 1 := by
  obtain ⟨A, _, htransfer⟩ := exists_native_inverse_on_cyclic_encoding s hs
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((4 * X + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro n T _ p hp f hf hGowers
  have hp0 : 0 ≤ p := by linarith
  have hcost : (p + 4 * (n : ℝ) + A) ^ A ≤ (p + n + C) ^ C := by
    apply (pow_le_pow_left₀ (by positivity)
      (show p + 4 * (n : ℝ) + A ≤ 4 * (p + n) + A by linarith) A).trans
    simpa [X, Polynomial.eval₂_pow] using hbudget (p + n) (by positivity)
  obtain ⟨V, hV⟩ := htransfer (integerBox T) (integerBox_nonempty T) (boxIntegerCode T)
    (boxCyclicCode_reflectsPairSums T) (fun x hx => boxIntegerCode_bounds T x hx)
    hp (by positivity : (0 : ℝ) ≤ 4 * n) (boxCode_density_lower T) f hf hGowers
  exact ⟨V.mono hcost, hV⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CubeMixtureNativeDetection
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_native_partner_of_cube_mixture (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {n : ℕ} (N : Fin n → ℕ) [∀ i, NeZero (N i)]
      {I : Type*} [Fintype I] (p : ℝ), 0 ≤ p → (n : ℝ) ≤ p →
      ∀ (f : (Fin n → ℤ) → ℂ) (c : I → ℂ)
        (twist : I → (Fin (s + 1) → Bool) → (Fin n → ℤ) → ℂ),
      (∀ x ∈ integerBox N, ‖f x‖ ≤ 1) →
      (∀ i ω x, x ∈ integerBox N → ‖twist i ω x‖ ≤ 1) →
      (∑ i, ‖c i‖) ≤ Real.exp p →
      ∀ z : ℂ, Real.exp (-p) ≤ z.re →
      ‖z - ∑ i, c i * normalizedSupportedCubeSum (s + 1) (integerBox N)
        (fun ω x => f x * twist i ω x)‖ ≤ Real.exp (-p) / 2 →
      ∀ ω : Fin (s + 1) → Bool,
      ∃ (i : I) (V : NativeSampleCorrelation (fun _ : Fin n => 1) s ((p + 2) ^ C)
        (integerBox N) id (fun x => f x * twist i ω x)),
        V.test.normBound ≤ 1 ∧
        Real.exp (-((p + 2) ^ C)) ≤
          ‖𝔼 x ∈ integerBox N, f x * star (star (twist i ω x) * V.test.eval x)‖ := by
  obtain ⟨A, _, hinverse⟩ := exists_native_integer_box_inverse s hs
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget ((3 * X + 2 + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro n N _ I _ p hp hn f c twist hf htwist hc z hz herr ω
  let F := fun i ω x => f x * twist i ω x
  have hF (i) (ω) (x) (hx : x ∈ integerBox N) : ‖F i ω x‖ ≤ 1 := by
    dsimp only [F]
    rw [norm_mul]
    exact (mul_le_mul (hf x hx) (htwist i ω x hx) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hlarge : Real.exp (-p) / 2 ≤
      ‖∑ i, c i * normalizedSupportedCubeSum (s + 1) (integerBox N) (F i)‖ := by
    have h := norm_sub_norm_le z (∑ i, c i * normalizedSupportedCubeSum (s + 1) (integerBox N) (F i))
    have hreal := Complex.re_le_norm z
    linarith
  obtain ⟨i, hi⟩ := exists_large_weighted_term c
    (fun i => normalizedSupportedCubeSum (s + 1) (integerBox N) (F i))
    (half_pos (Real.exp_pos _)) (Real.exp_pos p) hc hlarge
  have hG : Real.exp (-(2 * p + 2)) ≤ integerBoxGowersNorm N (s + 1) (F i ω) := by
    have he : Real.exp (-(2 * p)) / 2 = (Real.exp (-p) / 2) / Real.exp p := by
      rw [div_right_comm, ← Real.exp_sub]
      congr 2
      ring
    have hsmall : Real.exp (-(2 * p + 2)) ≤ Real.exp (-(2 * p)) / 2 :=
      (Real.exp_le_exp.mpr (by linarith : -(2 * p + 2) ≤ -(2 * p) - 1)).trans
        (exp_sub_one_le_half_exp (-(2 * p)))
    rw [he] at hsmall
    exact (hsmall.trans hi).trans
      (normalizedSupportedCubeSum_le_vertex (boxReduction_reflectsPairSums N) s (F i) (hF i) ω)
  obtain ⟨V, hV⟩ := hinverse N (by linarith : 2 ≤ 2 * p + 2) (F i ω) (hF i ω) hG
  have hcost : (2 * p + 2 + n + A) ^ A ≤ (p + 2) ^ C := by
    apply (pow_le_pow_left₀ (by positivity)
      (show 2 * p + 2 + (n : ℝ) + A ≤ 3 * p + 2 + A by linarith) A).trans
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨i, V.mono hcost, hV, ?_⟩
  simpa only [star_mul, star_star, F, id_eq, mul_assoc, mul_left_comm, mul_comm] using
    (V.mono hcost).correlation

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalCubeNativeDetection
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_native_partner_of_physical_cube_mixture (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {n : ℕ} (N : Fin n → ℕ) [∀ i, NeZero (N i)]
      {I : Type*} [Fintype I] (p : ℝ), 0 ≤ p → (n : ℝ) ≤ p →
      ∀ (f : (Fin n → ℤ) → ℂ) (c : I → ℂ)
        (twist : I → Finset (Fin (s + 1)) → (Fin n → ℤ) → ℂ),
      (∀ x ∈ integerBox N, ‖f x‖ ≤ 1) →
      (∀ i ω x, x ∈ integerBox N → ‖twist i ω x‖ ≤ 1) →
      (∑ i, ‖c i‖) ≤ Real.exp p →
      ∀ z : ℂ, Real.exp (-p) ≤ z.re →
      ‖z - ∑ i, c i * (𝔼 cube : SupportedCube (s + 1) (integerBox N : Set ((Fin n) → ℤ)),
        let u := (physicalCubeParametersEquiv (Fin n) (s + 1)).symm cube.val
        ∏ ω, conjugationPower ω.card (f (physicalCubeVertexValue u ω)) *
          twist i ω (physicalCubeVertexValue u ω))‖ ≤ Real.exp (-p) / 2 →
      ∃ (i : I) (V : NativeSampleCorrelation (fun _ : Fin n => 1) s ((p + 2) ^ C)
        (integerBox N) id (fun x => f x * twist i ∅ x)),
        V.test.normBound ≤ 1 ∧
        Real.exp (-((p + 2) ^ C)) ≤
          ‖𝔼 x ∈ integerBox N, f x * star (star (twist i ∅ x) * V.test.eval x)‖ := by
  obtain ⟨C, hC, hdetect⟩ := exists_native_partner_of_cube_mixture s hs
  refine ⟨C, hC, ?_⟩
  intro n N _ I _ p hp hn f c twist hf htwist hc z hz herr
  simp_rw [physical_twisted_cube_mean] at herr
  have ht : ∀ i ω x, x ∈ integerBox N →
      ‖conjugationPower (booleanWeight ω) (twist i (vertexFinsetEquiv (s + 1) ω) x)‖ ≤ 1 := by
    intro i ω x hx
    rw [conjugationPower_norm]
    exact htwist i _ x hx
  have h := hdetect N p hp hn f c
    (fun i ω x => conjugationPower (booleanWeight ω) (twist i (vertexFinsetEquiv (s + 1) ω) x))
    hf ht hc z hz herr (fun _ => false)
  have hweight : booleanWeight (fun _ : Fin (s + 1) => false) = 0 := by
    simp [booleanWeight]
  have hsite : vertexFinsetEquiv (s + 1) (fun _ => false) = ∅ := by
    ext i
    simp [vertexFinsetEquiv]
  rw [hweight, hsite] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CubeMixtureAllDegrees
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_native_partner_of_physical_cube_mixture_all_degrees (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {n : ℕ} (N : Fin n → ℕ) [∀ i, NeZero (N i)]
      {I : Type*} [Fintype I] (p : ℝ), 0 ≤ p → (n : ℝ) ≤ p →
      ∀ (f : (Fin n → ℤ) → ℂ) (c : I → ℂ)
        (twist : I → Finset (Fin (s + 1)) → (Fin n → ℤ) → ℂ),
      (∀ x ∈ integerBox N, ‖f x‖ ≤ 1) →
      (∀ i ω x, x ∈ integerBox N → ‖twist i ω x‖ ≤ 1) →
      (∑ i, ‖c i‖) ≤ Real.exp p →
      ∀ z : ℂ, Real.exp (-p) ≤ z.re →
      ‖z - ∑ i, c i * (𝔼 cube : SupportedCube (s + 1) (integerBox N : Set ((Fin n) → ℤ)),
        let u := (physicalCubeParametersEquiv (Fin n) (s + 1)).symm cube.val
        ∏ ω, conjugationPower ω.card (f (physicalCubeVertexValue u ω)) *
          twist i ω (physicalCubeVertexValue u ω))‖ ≤ Real.exp (-p) / 2 →
      ∃ (i : I) (V : NativeSampleCorrelation (fun _ : Fin n => 1) s ((p + 2) ^ C)
        (integerBox N) id (fun x => f x * twist i ∅ x)),
        V.test.normBound ≤ 1 ∧
        Real.exp (-((p + 2) ^ C)) ≤
          ‖𝔼 x ∈ integerBox N, f x * star (star (twist i ∅ x) * V.test.eval x)‖ := by
  by_cases hs : s = 0
  · subst s
    refine ⟨2, le_rfl, ?_⟩
    intro n N _ I _ p hp hn f c twist hf ht hc z hz herr
    obtain ⟨i, hi⟩ := exists_site_twist_of_degree_zero_cube_mixture (X := Fin n)
      (I := I) N p f c twist hf ht hc z hz herr
    have hcost : 2 * p + 2 ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
    have hlow : 2 ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
    let V : NativeSampleCorrelation (fun _ : Fin n => 1) 0 ((p + 2) ^ 2)
        (integerBox N) id (fun x => f x * twist i ∅ x) :=
      NativeSampleCorrelation.ofMean hlow ((Real.exp_le_exp.mpr (neg_le_neg hcost)).trans hi)
    refine ⟨i, V, ?_, ?_⟩
    · simp only [V, NativeSampleCorrelation.ofMean, RationalFilteredNilmanifold.Niltest.const,
        nnnorm_one, le_refl]
    · simpa only [star_mul, star_star, id_eq, mul_assoc, mul_left_comm, mul_comm] using V.correlation
  · exact exists_native_partner_of_physical_cube_mixture s (Nat.one_le_iff_ne_zero.mpr hs)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularGeneralDetectorLateCoarseConsumer
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

noncomputable def preparedModularGeneralDetectorConstants (m s : ℕ) :
    PreparedModularCanonicalDetectorResourceConstants :=
  let Cgrid := Classical.choose (exists_preparedModularCanonicalDetector_grid_parameters.{0} m (s + 1) canonicalTransitionLip)
  let Acover := Classical.choose (exists_allocated_canonical_constructed_projection.{0,0,0,0,0} m (s + 1))
  let Amass := Classical.choose (exists_allocatedAffineModelMass_budget m (s + 1))
  let Aanalytic := Classical.choose (exists_allocatedAffineAnalytic_budget m (s + 1))
  let Anorm := Classical.choose (exists_allocatedRecenteredFactor_normalization.{0,0,0,0,0,0} m (s + 1))
  let Anative := Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s)
  { m := m
    Cgrid := Cgrid
    Cperiod := Classical.choose (exists_preparedModularCanonicalDetector_period_budget.{0,0} m (s + 1) Cgrid)
    Acover := Acover
    Asample := Classical.choose (exists_allocatedCanonicalProjection_composed_budget m (s + 1) Acover)
    Cpref := Classical.choose (exists_canonicalSlicedModelPrefactor_budget.{0,0} m (s + 1))
    Apert := Classical.choose (exists_translated_physical_jet_l1_perturbation.{0,0,0} m (s + 1))
    AmassWindow := Classical.choose (exists_translated_physical_jet_density_window_mass.{0,0,0,0} m (s + 1))
    Aproj := Classical.choose (Classical.choose_spec (exists_allocated_canonical_constructed_projection.{0,0,0,0,0} m (s + 1)))
    Aside := Classical.choose (exists_allocatedCanonicalSpatial_cutoff.{0,0,0,0} m)
    Cnative := Classical.choose (exists_canonicalSlicedNative_input_budget m (s + 1) Amass Aanalytic)
    Anorm := Classical.choose (exists_normalizedNative_uniform_budget m Anorm Anative)
    Amarginal := Classical.choose (exists_allocated_fullBox_normalized_approximation.{0,0,0,0,0,0} m) }

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteForwardActualNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedFiniteScheduleUniformLocalResourceBudget
    (m : ℕ) (Pdetect : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ s : Fin (m + 1), ∀ {G : Type} [Fintype G] {count nX : ℕ}
      {P Bstruct pnum Pchart Qstride u pModel : ℝ},
      0 ≤ P → Bstruct ∈ Set.Icc 0 P → pnum ∈ Set.Icc 0 P →
      Pchart ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P →
      u ∈ Set.Icc 0 P → pModel ∈ Set.Icc 0 P →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
      let D := allocatedComparisonDimension m pnum
      let pDetect := allocatedModelTestLog u pModel
      let gainLog := slicedDetectionGainLog s.val (sampledSupportedSlicedDetectionConstant s.val Pdetect) count
        pDetect pDetect (2 * u + 4 * pModel + 7)
      let Pk := scalarKernelLogarithmicBudget (Fin (s.val + 1)) G
        (gainLog + pDetect + 4)
      let Pphysical := preparedFiniteScheduleLocalPhysical m nX count Qstride Pk
      let target := gainLog + 40 + coefficientErrorSpatialLog Pphysical
      let Eprofile := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let Prho := 2 * affineProfileInputEnvelope D
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ)
        Eprofile (pDetect + 2) + 2
      let Pmaster := preparedFiniteScheduleLocalMaster Pchart D pRadius Qstride
        Pphysical u pModel Prho target gainLog
      ∀ L : ℝ,
      let r := preparedModularGeneralDetectorResources
        (preparedModularGeneralDetectorConstants m s.val) (s.val + 1) Pmaster L
      let budget := (P + C) ^ C
      Pmaster ∈ Set.Icc 0 budget ∧ r.Pnative ∈ Set.Icc 0 budget ∧
      r.nativeBudget ∈ Set.Icc 0 budget ∧ r.E ∈ Set.Icc 0 budget := by
  let Cs (s : Fin (m + 1)) := Classical.choose
    (exists_preparedFiniteScheduleLocalResourceBudget m s.val
      (sampledSupportedSlicedDetectionConstant s.val Pdetect)
      (preparedModularGeneralDetectorConstants m s.val))
  let poly : Polynomial ℕ := ∑ s : Fin (m + 1),
    (Polynomial.X + Polynomial.C (Cs s)) ^ Cs s
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro s G _ count nX P Bstruct pnum Pchart Qstride u pModel
    hP hB hnum hchart hstride hu hmodel hcount hnX hG
    pRadius D pDetect gainLog Pk Pphysical target Eprofile Prho Pmaster L r budget
  have hbound : (P + Cs s) ^ Cs s ≤ budget := by
    have hsum : (P + Cs s) ^ Cs s ≤
        ∑ t : Fin (m + 1), (P + Cs t) ^ Cs t :=
      Finset.single_le_sum (f := fun t : Fin (m + 1) => (P + (Cs t : ℝ)) ^ Cs t)
        (fun t _ => by positivity) (Finset.mem_univ s)
    apply hsum.trans
    simpa [poly, budget, Polynomial.eval₂_finsetSum, Polynomial.eval₂_pow] using hpoly P hP
  have hlocal := (Classical.choose_spec
    (exists_preparedFiniteScheduleLocalResourceBudget m s.val
      (sampledSupportedSlicedDetectionConstant s.val Pdetect)
      (preparedModularGeneralDetectorConstants m s.val))).2
    (G := G) (Nat.le_of_lt_succ s.isLt) hP hB hnum hchart hstride hu hmodel
    hcount hnX hG L
  have lift {a : ℝ} (ha : a ∈ Set.Icc 0 ((P + Cs s) ^ Cs s)) :
      a ∈ Set.Icc 0 budget := ⟨ha.1, ha.2.trans hbound⟩
  exact ⟨lift hlocal.1, lift hlocal.2.1, lift hlocal.2.2.1, lift hlocal.2.2.2⟩

theorem exists_preparedFiniteScheduleUniformLocalResourceBudget_source_model
    (m : ℕ) (Pdetect : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ s : Fin (m + 1), ∀ {G : Type} [Fintype G] {count nX : ℕ}
      {Bstruct pnum Pchart Qstride u pModel : ℝ},
      0 ≤ u → 0 ≤ pModel →
      Bstruct ∈ Set.Icc 0 (u + pModel) → pnum ∈ Set.Icc 0 (u + pModel) →
      Pchart ∈ Set.Icc 0 (u + pModel) → Qstride ∈ Set.Icc 0 (u + pModel) →
      (count : ℝ) ≤ u + pModel → (nX : ℝ) ≤ u + pModel →
      (Fintype.card G : ℝ) ≤ u + pModel →
      let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
      let D := allocatedComparisonDimension m pnum
      let pDetect := allocatedModelTestLog u pModel
      let gainLog := slicedDetectionGainLog s.val (sampledSupportedSlicedDetectionConstant s.val Pdetect) count
        pDetect pDetect (2 * u + 4 * pModel + 7)
      let Pk := scalarKernelLogarithmicBudget (Fin (s.val + 1)) G
        (gainLog + pDetect + 4)
      let Pphysical := preparedFiniteScheduleLocalPhysical m nX count Qstride Pk
      let target := gainLog + 40 + coefficientErrorSpatialLog Pphysical
      let Eprofile := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let Prho := 2 * affineProfileInputEnvelope D
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ)
        Eprofile (pDetect + 2) + 2
      let Pmaster := preparedFiniteScheduleLocalMaster Pchart D pRadius Qstride
        Pphysical u pModel Prho target gainLog
      ∀ L : ℝ,
      let r := preparedModularGeneralDetectorResources
        (preparedModularGeneralDetectorConstants m s.val) (s.val + 1) Pmaster L
      let budget := (u + pModel + C) ^ C
      Pmaster ∈ Set.Icc 0 budget ∧ r.Pnative ∈ Set.Icc 0 budget ∧
      r.nativeBudget ∈ Set.Icc 0 budget ∧ r.E ∈ Set.Icc 0 budget := by
  obtain ⟨C, hC, hbound⟩ := exists_preparedFiniteScheduleUniformLocalResourceBudget m Pdetect
  refine ⟨C, hC, ?_⟩
  intro s G _ count nX Bstruct pnum Pchart Qstride u pModel
    hu hmodel hB hnum hchart hstride hcount hnX hG
  exact hbound s (add_nonneg hu hmodel) hB hnum hchart hstride
    ⟨hu, le_add_of_nonneg_right hmodel⟩ ⟨hmodel, le_add_of_nonneg_left hu⟩
    hcount hnX hG

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedFiniteForwardActualNativeBudget
    (m : ℕ) (Pdetect : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ s : Fin (m + 1),
      ∀ (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (isDirect : Bool),
      ∀ {G : Type} [Fintype G] {count nX : ℕ}
      {x gainLog stageLog Bstruct pnum Pchart Qstride : ℝ},
      2 ≤ A → 0 ≤ x → gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      Bstruct ∈ Set.Icc 0 x → pnum ∈ Set.Icc 0 x →
      Pchart ∈ Set.Icc 0 x → Qstride ∈ Set.Icc 0 x →
      (count : ℝ) ≤ x → (nX : ℝ) ≤ x → (Fintype.card G : ℝ) ≤ x →
      let u := preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n
        isDirect x gainLog stageLog
      let pModel := preparedFiniteForwardWork A stageCountConstant n x
      let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
      let D := allocatedComparisonDimension m pnum
      let pDetect := allocatedModelTestLog u pModel
      let gainLog := slicedDetectionGainLog s.val (sampledSupportedSlicedDetectionConstant s.val Pdetect) count
        pDetect pDetect (2 * u + 4 * pModel + 7)
      let Pk := scalarKernelLogarithmicBudget (Fin (s.val + 1)) G
        (gainLog + pDetect + 4)
      let Pphysical := preparedFiniteScheduleLocalPhysical m nX count Qstride Pk
      let target := gainLog + 40 + coefficientErrorSpatialLog Pphysical
      let Eprofile := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let Prho := 2 * affineProfileInputEnvelope D
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ)
        Eprofile (pDetect + 2) + 2
      let Pmaster := preparedFiniteScheduleLocalMaster Pchart D pRadius Qstride
        Pphysical u pModel Prho target gainLog
      ∀ Plate : ℝ,
      let r := preparedModularGeneralDetectorResources
        (preparedModularGeneralDetectorConstants m s.val) (s.val + 1) Pmaster Plate
      let budget := (u + pModel + C) ^ C
      Pmaster ∈ Set.Icc 0 budget ∧ r.Pnative ∈ Set.Icc 0 budget ∧
      r.nativeBudget ∈ Set.Icc 0 budget ∧ r.E ∈ Set.Icc 0 budget := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_preparedFiniteScheduleUniformLocalResourceBudget_source_model m Pdetect
  refine ⟨C, hC, ?_⟩
  intro s A Cdirect stageCountConstant n isDirect G _ count nX
    x gainLog stageLog Bstruct pnum Pchart Qstride
    hA hx hg hs hB hnum hchart hstride hcount hnX hG u pModel
  have hu : 0 ≤ u :=
    preparedFiniteForwardPairedSourcePrecision_nonneg A Cdirect stageCountConstant n isDirect hx hg hs
  have hpModel : 0 ≤ pModel := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  have hxWork : x ≤ pModel := by
    have h := preparedFiniteForward_shiftedPower_le_work A 1 stageCountConstant n
      hA (by omega) hx
    simp only [Nat.cast_one, pow_one] at h
    exact (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans h
  have hxTotal : x ≤ u + pModel := hxWork.trans (le_add_of_nonneg_left hu)
  exact hbound s hu hpModel ⟨hB.1, hB.2.trans hxTotal⟩
    ⟨hnum.1, hnum.2.trans hxTotal⟩ ⟨hchart.1, hchart.2.trans hxTotal⟩
    ⟨hstride.1, hstride.2.trans hxTotal⟩
    (hcount.trans hxTotal) (hnX.trans hxTotal) (hG.trans hxTotal)

noncomputable def preparedFiniteForwardActualNativeBudgetExponent
    (m : ℕ) (Pdetect : Polynomial ℕ) : ℕ :=
  Classical.choose (exists_preparedFiniteForwardActualNativeBudget m Pdetect)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {A} {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ t : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck Ω Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

theorem rawCorrelation_fullSliceLaw (a : Ω) (j : Pivot)
    (hcorr : Real.exp (-r) ≤ ‖F.correlation a j‖) :
    Real.exp (-r) ≤
      ‖((F.chart a).slice.fullSliceLaw
        ((F.chart a).slice.length_pos_of_dense (F.chart a).dense)).complexMean (fun u =>
        (star ((F.twist a j).eval N poly (F.physicalBox a u).val) *
          F.nativeValue j (F.physicalBox a u)) * (F.localTest a j).eval u.val)‖ := by
  have hm := (F.chart a).localLaw_complexMean_eq_fullSliceLaw_site (fun site =>
    star ((F.twist a j).eval N poly (F.sitePhysicalBox a site).val) *
      ((F.reference a j).observable ((F.sourceCandidate a).siteValue site) *
        F.nativeValue j (F.sitePhysicalBox a site)))
  rw [F.chart_localLaw] at hm
  unfold correlation at hcorr
  rw [hm] at hcorr
  convert hcorr using 2
  congr 1
  funext u
  have hv : (F.sourceCandidate a).siteValue ((F.chart a).site u.val u.property) =
      (F.candidate a).value u.val := by
    rw [← (F.sourceCandidate a).withKeep_siteValue keep (F.keep_eq a)]
    change (F.candidate a).value
      ((F.chart a).retainedParameter ((F.chart a).parameter u.val)) = _
    rw [(F.chart a).retainedParameter_parameter]
  simp only [localTest, hv]
  change (star ((F.twist a j).eval N poly (F.physicalBox a u).val) *
      F.nativeValue j (F.physicalBox a u)) *
      (F.reference a j).observable ((F.candidate a).value u.val) =
    star ((F.twist a j).eval N poly (F.physicalBox a u).val) *
      ((F.reference a j).observable ((F.candidate a).value u.val) *
        F.nativeValue j (F.physicalBox a u))
  ring

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedNestedDegreeInduction
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal
attribute [local irreducible] AllocatedExternalCandidateSampler.DegreeGlobalizationAt

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

theorem degreeGlobalizationAt_nested_suffix
    (weight : (X → ℤ) → ℂ) (total initial exponent innerDepth : ℕ)
    (constants : ℕ → ℕ) {x : ℝ} (hexponent : 2 ≤ exponent) (hx : 0 ≤ x)
    (step : ∀ j < total, ∀ q : ℝ,
      candidateNestedForwardSeed exponent constants innerDepth (2 * (j + 1)) x ≤ q →
      A.DegreeGlobalizationAt (E := E) weight (total - (j + 1))
        (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0}
          (total - (j + 1)) 1 (candidateNestedDegreeNetExponent total initial j) + 2)
        (candidateNestedForwardSeed exponent constants innerDepth (2 * (j + 1)) x) q →
      A.DegreeGlobalizationAt (E := E) weight (total - j)
        (candidateNestedDegreeNetExponent total initial j)
        (candidateNestedForwardSeed exponent constants innerDepth (2 * j) x) (3 * q + 2)) :
    ∀ j ≤ total,
      A.DegreeGlobalizationAt (E := E) weight (total - j)
        (candidateNestedDegreeNetExponent total initial j)
        (candidateNestedForwardSeed exponent constants innerDepth (2 * j) x)
        (candidateDegreeReturnBudget (total - j)
          (candidateNestedForwardSeed exponent constants innerDepth (2 * total) x)) := by
  let terminal := candidateNestedForwardSeed exponent constants innerDepth (2 * total) x
  have hterminal : 0 ≤ terminal :=
    candidateNestedForwardSeed_nonneg exponent constants innerDepth (2 * total) hx
  have all : ∀ d j, d + j = total →
      A.DegreeGlobalizationAt (E := E) weight d
        (candidateNestedDegreeNetExponent total initial j)
        (candidateNestedForwardSeed exponent constants innerDepth (2 * j) x)
        (candidateDegreeReturnBudget d terminal) := by
    intro d
    induction d with
    | zero =>
        intro j hj
        have hjeq : j = total := by omega
        subst j
        simpa only [candidateDegreeReturnBudget_zero] using
          A.degreeGlobalizationAt_zero (E := E) weight
            (candidateNestedDegreeNetExponent total initial total) terminal
    | succ d ih =>
        intro j hj
        have hjlt : j < total := by omega
        have hd : total - (j + 1) = d := by omega
        have hd' : total - j = d + 1 := by omega
        have lower := ih (j + 1) (by omega)
        have hnext : candidateNestedForwardSeed exponent constants innerDepth (2 * (j + 1)) x ≤
            candidateDegreeReturnBudget d terminal := by
          apply le_trans
            (candidateNestedForwardSeed_monotone exponent constants innerDepth hexponent hx
              (by omega : 2 * (j + 1) ≤ 2 * total))
          exact le_candidateDegreeReturnBudget d hterminal
        have current := step j hjlt (candidateDegreeReturnBudget d terminal) hnext
          (by simpa only [candidateNestedDegreeNetExponent_succ, hd] using lower)
        simpa only [hd', candidateDegreeReturnBudget_succ] using current
  intro j hj
  exact all (total - j) j (by omega)

theorem degreeGlobalizationAt_nested
    (weight : (X → ℤ) → ℂ) (total initial exponent innerDepth : ℕ)
    (constants : ℕ → ℕ) {x : ℝ} (hexponent : 2 ≤ exponent) (hx : 0 ≤ x)
    (step : ∀ j < total, ∀ q : ℝ,
      candidateNestedForwardSeed exponent constants innerDepth (2 * (j + 1)) x ≤ q →
      A.DegreeGlobalizationAt (E := E) weight (total - (j + 1))
        (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0}
          (total - (j + 1)) 1 (candidateNestedDegreeNetExponent total initial j) + 2)
        (candidateNestedForwardSeed exponent constants innerDepth (2 * (j + 1)) x) q →
      A.DegreeGlobalizationAt (E := E) weight (total - j)
        (candidateNestedDegreeNetExponent total initial j)
        (candidateNestedForwardSeed exponent constants innerDepth (2 * j) x) (3 * q + 2)) :
    A.DegreeGlobalizationAt (E := E) weight total initial x
      (candidateDegreeReturnBudget total
        (candidateNestedForwardSeed exponent constants innerDepth (2 * total) x)) := by
  simpa only [Nat.sub_zero, Nat.mul_zero, candidateNestedDegreeNetExponent_zero,
    candidateNestedForwardSeed_zero] using
    A.degreeGlobalizationAt_nested_suffix (E := E) weight total initial exponent innerDepth
      constants hexponent hx step 0 (Nat.zero_le total)

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedZeroLayerForwardFrontSourceProfile
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

local instance preparedFrontSourceProfileSiteNonempty : Nonempty A.Site := A.site_nonempty

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
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
    (sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler
local instance forwardFrontSourceSiteNonempty : Nonempty sampler.Site := sampler.site_nonempty

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
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
    (sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler
local instance actualForwardFrontSourceSiteNonempty : Nonempty sampler.Site := sampler.site_nonempty

attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler

variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

local instance zeroLayerForwardFrontSiteNonempty : Nonempty A.Site := A.site_nonempty
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteNestedSourceArrays
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def preparedFiniteNestedSourceNativeExponent
    (m cutoff Cdirect : ℕ) : ℕ :=
  preparedFiniteForwardInnerSourceExponent Cdirect
    (preparedFiniteForwardActualNativeBudgetExponent m (preparedFiniteForwardDetectorPolynomial cutoff))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

noncomputable def preparedFiniteNestedSourceNative
    (m : ℕ) (G : Type) [Fintype G] (count nX : ℕ) (Pdetect : Polynomial ℕ)
    (A Cdirect : ℕ) (constants : ℕ → ℕ)
    (Bstruct pnum Qstride gainLog stageLog Plate : ℝ)
    {outerDepth innerDepth cutoff : ℕ}
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) : ℝ :=
  (preparedModularGeneralDetectorResources
    (preparedModularGeneralDetectorConstants m
      (preparedFiniteNestedForwardAllDegreeDegree k))
    (preparedFiniteNestedForwardAllDegreeDegree k + 1)
    (preparedFiniteNestedSourceMaster m G count nX Pdetect A Cdirect constants
      Bstruct pnum Qstride gainLog stageLog k) Plate).nativeBudget

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAdaptedOptionQuotientFactors
namespace OAI

section

universe u v

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    {cost : ℝ} {C : AllocatedExternalLocalChart (E := Deck) A cost}
    {Pivot : Type v} [Fintype Pivot]
    {L M : Type u} {P : Pivot → Type u}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [∀ j, LieRing (P j)] [∀ j, LieAlgebra ℚ (P j)]
    {s d dQ : ℕ} {dp : Pivot → ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalCandidate

variable (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (ideal : LieIdeal ℚ L) (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hI)
    (hker : ∀ x ∈ ideal, φ x = 0)
    (partners : ∀ j, RationalFilteredNilmanifold (P j) s (dp j))
    (partnerOrbit : ∀ j, (partners j).filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))

attribute [local irreducible] NilpotentLieFiltration.realPolynomialGroupMap

theorem optionJoint_lieQuotient_polynomialCoordinates :
    (⟨⟨((candidate.lieQuotient ideal hI Q hQ hker).optionJoint partners partnerOrbit).orbit.log,
        ((candidate.lieQuotient ideal hI Q hQ hker).optionJoint partners partnerOrbit).orbit.property⟩⟩ :
      ((optionProduct Q partners).filtration.realification.adaptedPolynomialFiltration
        (fun _ : C.Variables => 1)).Group) =
      (optionProduct D partners).filtration.realPolynomialGroupMap
        (optionProduct Q partners).filtration
        (optionMarkedLieMap (L := P) (lieQuotientMap ideal))
        (D.optionQuotientMap_mem_layer ideal hI Q hQ partners)
        (fun _ : C.Variables => 1)
        ⟨⟨(candidate.optionJoint partners partnerOrbit).orbit.log,
          (candidate.optionJoint partners partnerOrbit).orbit.property⟩⟩ := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  rw [realPolynomialGroupMap_log]
  exact candidate.optionJoint_lieQuotient_log ideal hI Q hQ hker partners partnerOrbit

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteNestedFrontNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

theorem preparedFiniteNestedSourceNative_front_mem
    (q : ℕ) (G : Type) [Fintype G] (count nX : ℕ) (Pdetect : Polynomial ℕ)
    (exponent Cdirect : ℕ) (constants : ℕ → ℕ)
    {outerDepth innerDepth cutoff : ℕ}
    (outer : Fin (outerDepth + 1)) (degree : Fin (cutoff + 1))
    {Bstruct pnum Qstride gainLog stageLog : ℝ} (Plate : ℝ)
    (hA : 2 ≤ exponent) (hB : 0 ≤ Bstruct) (hdegree : degree.val ≤ q)
    (hnum : pnum ∈ Set.Icc 0 Bstruct) (hstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hg : gainLog ∈ Set.Icc 0 Bstruct) (hs : stageLog ∈ Set.Icc 0 Bstruct)
    (hcount : (count : ℝ) ≤ Bstruct) (hnX : (nX : ℝ) ≤ Bstruct)
    (hG : (Fintype.card G : ℝ) ≤ Bstruct) :
    let x := candidateNestedForwardSeed exponent constants innerDepth outer.val Bstruct
    let u := preparedFiniteForwardPairedSourcePrecision exponent Cdirect constants 0 false
      x gainLog stageLog
    let w := preparedFiniteForwardWork exponent constants 0 x
    let C := preparedFiniteForwardActualNativeBudgetExponent q Pdetect
    preparedFiniteNestedSourceNative q G count nX Pdetect exponent Cdirect constants
      Bstruct pnum Qstride gainLog stageLog Plate
      (outer, (0 : Fin (innerDepth + 1)), degree, false) ∈ Set.Icc 0 ((u + w + C) ^ C) := by
  intro x u w C
  have hx : 0 ≤ x := candidateNestedForwardSeed_nonneg exponent constants innerDepth outer.val hB
  have hBx : Bstruct ≤ x := le_candidateNestedForwardSeed exponent constants innerDepth outer.val hA hB
  have lift {r : ℝ} (hr : r ∈ Set.Icc 0 Bstruct) : r ∈ Set.Icc 0 x := ⟨hr.1, hr.2.trans hBx⟩
  have hresource := (Classical.choose_spec
      (exists_preparedFiniteForwardActualNativeBudget q Pdetect)).2
    ⟨degree.val, Nat.lt_succ_of_le hdegree⟩ exponent Cdirect constants 0 false
    (G := G) hA hx (lift hg) (lift hs) ⟨hB, hBx⟩ (lift hnum)
    ⟨hB, hBx⟩ (lift hstride) (hcount.trans hBx) (hnX.trans hBx) (hG.trans hBx) Plate
  exact hresource.2.2.1

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteNestedSourceLatePowerBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

def PreparedEmptyLayerLocalScheduleBudget
    (m : ℕ) {K G : Type} [Fintype K] [Fintype G]
    (degree Cdetect : K → ℕ) (nX count : ℕ)
    (Bstruct pnum Qstride Qσ requestedCoarse extraLate : ℝ)
    (u model : K → ℝ) (cap : ℝ) : Prop :=
  let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
  let D := allocatedComparisonDimension m pnum
  let pDetect := fun k => allocatedModelTestLog (u k) (model k)
  let aDetect := fun k => 2 * u k + 4 * model k + 7
  let gain := fun k => slicedDetectionGainLog (degree k) (Cdetect k) count
    (pDetect k) (pDetect k) (aDetect k)
  let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1)) G
    (gain k + pDetect k + 4)
  let physical := fun k => preparedFiniteScheduleLocalPhysical m nX count Qstride (Pk k)
  let target := fun k => gain k + 40 + coefficientErrorSpatialLog (physical k)
  let E := fun k => target k + D * ((m * 2 ^ (m + 1) : ℕ) * Pk k) + 5
  let rho := fun k => 2 * affineProfileInputEnvelope D
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2) + 2
  let tail := fun k => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2)
  let scale := preparedUniformDegreeScaleLog (D + pRadius) tail Qσ
  let tmod := fun k => ((m + 1 : ℕ) : ℝ) * Pk k + nX * Qstride
  let lengths := fun k => allocatedAffineLengthLog m D scale (rho k) (Pk k)
    (target k) (pDetect k + 2) (tmod k)
  let master := fun k => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
    (physical k) (u k) (model k) (rho k) (target k) (gain k)
  let coarse := preparedFiniteScheduleDirectCoarse gain requestedCoarse
  let late := ∑ k, preparedUniformDegreeDirectLate (master k) scale (physical k) coarse extraLate
  pRadius ∈ Set.Icc 0 cap ∧ D ∈ Set.Icc 0 cap ∧ scale ∈ Set.Icc 0 cap ∧
    coarse ∈ Set.Icc 0 cap ∧ late ∈ Set.Icc 0 cap ∧
    ∀ k, gain k ∈ Set.Icc 0 cap ∧ Pk k ∈ Set.Icc 0 cap ∧
      physical k ∈ Set.Icc 0 cap ∧ target k ∈ Set.Icc 0 cap ∧
      rho k ∈ Set.Icc 0 cap ∧ tail k ∈ Set.Icc 0 cap ∧
      lengths k ∈ Set.Icc 0 cap ∧ master k ∈ Set.Icc 0 cap ∧
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (master k) late).Bounds cap

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

def PreparedFiniteScheduleWitnessBudget
    (m : ℕ) {K G : Type} [Fintype K] [Fintype G]
    (degree Cdetect : K → ℕ) (nX count : ℕ)
    (Bstruct pnum Qstride Qσ Pmin Qw requestedCoarse : ℝ)
    (u model : K → ℝ) (cap : ℝ) : Prop :=
  let seed := preparedFiniteScheduleWitnessSeed (G := G) m degree Cdetect nX count
    Bstruct pnum Qstride Qσ Pmin u model
  seed ∈ Set.Icc 0 cap ∧ allocatedWitnessScaleLog seed Qw ∈ Set.Icc 0 cap ∧
    PreparedEmptyLayerLocalScheduleBudget (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ requestedCoarse (allocatedWitnessScaleLog seed Qw) u model cap

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairLongUniformFactors
namespace OAI

universe u

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

namespace AllocatedExternalCandidateTaggedPairFamily

variable {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Ω] [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] MG j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] MG j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] MG j)] [∀ j, T2Space (ℝ ⊗[ℚ] MG j)]
    {s d₀ t : ℕ} {d : Pivot → ℕ}
    {D : RationalFilteredNilmanifold LG s d₀}
    {E : ∀ j, RationalFilteredNilmanifold (MG j) s (d j)}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p periodCap coverCap : ℝ} {Lip : ℝ≥0}
    {H : Finset Ω}

def LongCommonFactors
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck {a // a ∈ H} Pivot
      D E Fmark φ marked keep cost p periodCap coverCap Lip)
    (keepLong : LayerSamplerVariables G I n B → Prop)
    (outer : FiniteProbabilityWeights Ω)
    {α : Type*} [Fintype α]
    (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG MG i)) (ω : α → ℕ)
    (hF : ∀ k, (optionProduct D E).filtration.layer k =
      Submodule.span ℚ (e '' {i | k ≤ ω i})) (q : ℝ) : Prop :=
  ∃ (W : LieSubalgebra ℚ (optionProduct D E).filtration.AssociatedGraded)
    (v : Fin (Fintype.card α) → (optionProduct D E).filtration.AssociatedGraded)
    (den : ℕ) (H' : Finset Ω),
    H' ⊆ H ∧ 0 < outer.mass H' ∧
    Real.exp (-((q + 2) ^ 5 + q)) * outer.mass H ≤ outer.mass H' ∧
    Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
    BasisGradedSubmodule ((optionProduct D E).filtration.associatedGradedBasis e ω hF)
      ω W.toSubmodule ∧
    (∀ i k, rationalLogHeight
      (((optionProduct D E).filtration.associatedGradedBasis e ω hF).repr (v i) k) ≤ q) ∧
    (∀ j x, x ∈ (optionProduct D E).filtration.realGradedRefiltrationLayer W s →
      realifyFunctional ((pairFrequency (F.η j) (F.θ j)).comp
        (optionPairProjection j).toLinearMap) x = 0) ∧
    0 < den ∧ (den : ℝ) ≤ Real.exp q ∧
    ∀ a ∈ H', (optionProduct D E).filtration.HasCommonRefilteredOrbitFactors
      e ω hF (fun i : {i // keepLong i} => (A.sides i.val : ℝ)) q den W
      ⟨⟨(piRealOrbit (fun i => (optionFactors D E i).filtration)
          (F.extendedLongJointOrbit keepLong a)).log,
        (piRealOrbit (fun i => (optionFactors D E i).filtration)
          (F.extendedLongJointOrbit keepLong a)).property⟩⟩

end AllocatedExternalCandidateTaggedPairFamily

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeLongCommonFactors
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Ω] [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ t : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck Ω Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

def longJointOrbit (keepLong : LayerSamplerVariables G I n B → Prop) (a : Ω) :
    ∀ i : Option Pivot,
      (optionFactors D (fun j => (F.native j).model) i).filtration.realification.PolynomialOrbit
        (fun _ : {i // keepLong i} => 1) :=
  fun i => (optionFactors D (fun j => (F.native j).model) i).filtration.polynomialOrbitRealChart
    (fun _ : {i // keep i} => 1) (fun _ : {i // keepLong i} => 1)
    ((F.chart a).axisPolynomial keepLong (fun _ => 0))
    ((F.chart a).axisPolynomial_support keepLong (fun _ => 0)) (F.jointOrbit a i)

def LongCommonFactors
    (keepLong : LayerSamplerVariables G I n B → Prop)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω)
    {α : Type*} [Fintype α]
    (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG (fun j => (F.native j).L) i))
    (ω : α → ℕ)
    (hF : ∀ k, (optionProduct D (fun j => (F.native j).model)).filtration.layer k =
      Submodule.span ℚ (e '' {i | k ≤ ω i})) (qVertical qCommon : ℝ) : Prop :=
  ∃ (theta : ∀ j, (F.native j).L →ₗ[ℚ] ℚ)
    (W : LieSubalgebra ℚ (optionProduct D (fun j => (F.native j).model)).filtration.AssociatedGraded)
    (v : Fin (Fintype.card α) →
      (optionProduct D (fun j => (F.native j).model)).filtration.AssociatedGraded)
    (den : ℕ) (H' : Finset Ω),
    H' ⊆ H ∧ 0 < outer.mass H' ∧
    Real.exp (-(verticalDecompositionBudget qVertical * Fintype.card Pivot +
      ((qCommon + 2) ^ 5 + qCommon))) * outer.mass H ≤ outer.mass H' ∧
    Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
    BasisGradedSubmodule
      ((optionProduct D (fun j => (F.native j).model)).filtration.associatedGradedBasis e ω hF)
      ω W.toSubmodule ∧
    (∀ i k, rationalLogHeight
      (((optionProduct D (fun j => (F.native j).model)).filtration.associatedGradedBasis
        e ω hF).repr (v i) k) ≤ qCommon) ∧
    (∀ j x, x ∈ (optionProduct D (fun j => (F.native j).model)).filtration.realGradedRefiltrationLayer W s →
      realifyFunctional ((pairFrequency (F.η j) (theta j)).comp
        (optionPairProjection j).toLinearMap) x = 0) ∧
    0 < den ∧ (den : ℝ) ≤ Real.exp qCommon ∧
    ∀ a ∈ H', (optionProduct D (fun j => (F.native j).model)).filtration.HasCommonRefilteredOrbitFactors
      e ω hF (fun i : {i // keepLong i} => (A.sides i.val : ℝ)) qCommon den W
      ⟨⟨(piRealOrbit (fun i => (optionFactors D (fun j => (F.native j).model) i).filtration)
          (F.longJointOrbit keepLong a)).log,
        (piRealOrbit (fun i => (optionFactors D (fun j => (F.native j).model) i).filtration)
          (F.longJointOrbit keepLong a)).property⟩⟩

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeAutomaticLongGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit
  weightedAdaptedRealChartHom realPolynomialGroupMap

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {Deck : Fin m → Type*} {Pivot : Type*} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

    (keepLong : LayerSamplerVariables G I n B → Prop)
    (H : Finset A.Path)
    (sourceCenter : ∀ j, U j)
    (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
    (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
    (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
    (scoreThreshold : ℝ)
    (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)

variable {α : Type*} [Fintype α]
    (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG (fun j => (F.native j).L) i))
    (ω : α → ℕ)
    (hF : ∀ k, (optionProduct D (fun j => (F.native j).model)).filtration.layer k =
      Submodule.span ℚ (e '' {i | k ≤ ω i}))
    (js : List Pivot)
    {dQ : ℕ}
    (Q : RationalFilteredNilmanifold (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js) s dQ)
    (hQ : Q.filtration = D.filtration.pivotQuotientFiltration φ F.η js)
    (hker : ∀ x ∈ D.filtration.pivotAnnihilatorIdeal φ F.η js, φ x = 0)
    (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup),
      descended x (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) g)) =
        observable x (QuotientGroup.mk g))
    (adapted : (optionProduct Q (fun j => (F.native j).model)).AdaptedModelData)

theorem longJointOrbit_polynomialCoordinates (a : A.Path) :
    (optionProduct D (fun j => (F.native j).model)).filtration.realification.polynomialOrbitCoordinates
      (fun _ : {i // keepLong i} => 1)
      (piRealOrbit (fun i => (optionFactors D (fun j => (F.native j).model) i).filtration)
        (F.longJointOrbit keepLong a)) =
    (optionProduct D (fun j => (F.native j).model)).filtration.weightedAdaptedRealChartHom
      (fun _ : {i // keep i} => 1) (fun _ : {i // keepLong i} => 1)
      ((F.chart a).axisPolynomial keepLong (fun _ => 0))
      ((F.chart a).axisPolynomial_support keepLong (fun _ => 0))
      ((optionProduct D (fun j => (F.native j).model)).filtration.realification.polynomialOrbitCoordinates
        (fun _ : {i // keep i} => 1)
        (piRealOrbit (fun i => (optionFactors D (fun j => (F.native j).model) i).filtration)
          (F.jointOrbit a))) :=
  piRealOrbit_polynomialOrbitRealChart_coordinates
    (fun i => (optionFactors D (fun j => (F.native j).model) i).filtration)
    (F.jointOrbit a) ((F.chart a).axisPolynomial keepLong (fun _ => 0))
    ((F.chart a).axisPolynomial_support keepLong (fun _ => 0))

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedFiniteNestedSourceProjectionBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedFiniteNestedSourceProjectionPrecision
    {outerDepth innerDepth cutoff : ℕ} (m : ℕ) (G : Type) [Fintype G]
    (count nX A Cdirect : ℕ) (constants : ℕ → ℕ)
    (Bstruct pnum Qstride gainLog stageLog Plate endpoint : ℝ) : ℝ :=
  preparedNestedFrontProjectionEnvelope A constants innerDepth
    (fun k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff => k.1.val)
    (fun k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff => k.2.1.val)
    (preparedFiniteNestedSourceNative m G count nX (preparedFiniteForwardDetectorPolynomial cutoff)
      A Cdirect constants Bstruct pnum Qstride gainLog stageLog Plate)
    Bstruct gainLog stageLog endpoint

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedFiniteNestedDegreeSourceProfileScalars
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {X₀ J₀ G X : Type} [Fintype G] [Fintype X]
    (prep : RankPreparationFamily X₀ J₀ m)
    {B : LayerSamplerAxis (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) → Type}
    [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ ((prep j).Coord → ℝ)}
    {b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ ((prep j).Coord → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern
      (Option (LayerSamplerVariables G (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((prep j).Coord)) (euclideanSubspace (U j)))]
    (sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

local instance nestedDegreeSourceSiteNonempty : Nonempty sampler.Site := sampler.site_nonempty

attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {X₀ J₀ G X : Type} [Fintype G] [Fintype X]
    (prep : RankPreparationFamily X₀ J₀ m)
    {B : LayerSamplerAxis (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) → Type}
    [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ ((prep j).Coord → ℝ)}
    {b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ ((prep j).Coord → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern
      (Option (LayerSamplerVariables G (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((prep j).Coord)) (euclideanSubspace (U j)))]
    (sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

local instance nestedDegreeSourceFullScalarsSiteNonempty : Nonempty sampler.Site := sampler.site_nonempty

attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end


