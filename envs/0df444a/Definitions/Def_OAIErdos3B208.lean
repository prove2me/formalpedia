-- Prove2me | Definitions.Def_OAIErdos3B208
-- name    : OAIErdos3B208
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T17:33:55.037673+00:00
-- url     : https://prove2.me/theorems/63fc2ab4-58fa-47f9-be59-114cbb34e259
-- title:
--   OpenAI Erdős-3 split, definitions bundle 209 of 217
-- statement:
--   Definitions bundle 209 of 217 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B207`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 209 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomial_constant`, `OAI.Erdos3.NilpotentLieFiltration.realHomogeneousAdaptedSymbolRepresentativeLie`, `OAI.Erdos3.NilpotentLieFiltration.realHomogeneousAssociatedGradedMapQ`, `OAI.Erdos3.NilpotentLieFiltration.realHomogeneousPolynomialSymbolLiftHom`, `OAI.Erdos3.NilpotentLieFiltration.realHomogeneousPolynomialSymbolLiftHom_apply`, `OAI.Erdos3.NilpotentLieFiltration.realHomogeneousSymbolRepresentativeLie`, `OAI.Erdos3.NilpotentLieFiltration.realHomogeneousSymbolRepresentativeLie_apply`, `OAI.Erdos3.OrdinaryPolynomialPhase.budget_le_factorizationInputBudget`, `OAI.Erdos3.OrdinaryPolynomialPhase.budget_le_factorizationInputOffset`, `OAI.Erdos3.OrdinaryPolynomialPhase.exists_factorizationBudget`, `OAI.Erdos3.OrdinaryPolynomialPhase.exists_ordinary_polynomial_phase_affine_inverse`, `OAI.Erdos3.OrdinaryPolynomialPhase.exists_ordinary_polynomial_phase_inverse`, `OAI.Erdos3.OrdinaryPolynomialPhase.exists_polynomial_phase_factorization`, `OAI.Erdos3.OrdinaryPolynomialPhase.factorizationInputBudget_le_power`, `OAI.Erdos3.OrdinaryPolynomialPhase.factorizationInputBudget_nonneg`, `OAI.Erdos3.OrdinaryPolynomialPhase.factorizationInputOffset`, `OAI.Erdos3.OrdinaryPolynomialPhase.le_factorizationInputBudget`, `OAI.Erdos3.OrdinaryPolynomialPhase.orbit`, `OAI.Erdos3.OrdinaryPolynomialPhase.orbit_buffered_eval`, `OAI.Erdos3.OrdinaryPolynomialPhase.orbit_coordinate`, `OAI.Erdos3.OrdinaryPolynomialPhase.orbit_eq_pure`, `OAI.Erdos3.OrdinaryPolynomialPhase.orbit_log`, `OAI.Erdos3.OrdinaryPolynomialPhase.orbit_realEval`, `OAI.Erdos3.OrdinaryPolynomialPhase.orbit_symbol_constantCoefficient`, `OAI.Erdos3.OrdinaryPolynomialPhase.pairOrbitSymbol_scalar_top`, `OAI.Erdos3.OrdinaryPolynomialPhase.phasePair_finrank_le`, `OAI.Erdos3.OrdinaryPolynomialPhase.phasePair_finrank_le_of_geometry`, `OAI.Erdos3.OrdinaryPolynomialPhase.phaseSlotCoefficient_rename`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBasePolynomial_constant`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationGroupEval`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationGroupEval_base`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationGroupEval_fast_potential`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationGroupEval_major_factorization`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationSymbolLift`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationSymbolLift_apply`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationSymbolLift_base_coordinate`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationSymbolLift_log`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationSymbolLift_pairOrbitSymbol`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationSymbolLift_value_mem_fast`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationSymbolProjection`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationSymbolProjection_coord`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationSymbolProjection_pairOrbitSymbol`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslation_samplingRank_le_base_span`, `OAI.Erdos3.PolynomialTranslationLie.exists_detectedTranslation_samplingRank_le_base_span`, `OAI.Erdos3.PolynomialTranslationLie.exists_detectedTranslation_separated_base`, `OAI.Erdos3.PolynomialTranslationLie.exists_majorTranslation_samplingRank_le_real_base_image`, `OAI.Erdos3.PolynomialTranslationLie.exists_reduced_majorPolynomial_degree_twisted_correlation_potential_data`, `OAI.Erdos3.PolynomialTranslationLie.exists_reduced_majorPolynomial_degree_twisted_correlation_separated_data`, `OAI.Erdos3.PolynomialTranslationLie.exists_reduced_majorPolynomial_degree_twisted_correlation_step_drop`, `OAI.Erdos3.PolynomialTranslationLie.majorTranslationDegreeReduced_twisted_integerEval`, `OAI.Erdos3.PolynomialTranslationLie.translationPolynomialSymbolLiftHom`, `OAI.Erdos3.PolynomialTranslationLie.translationPolynomialSymbolLiftHom_apply`, `OAI.Erdos3.PolynomialTranslationLie.translationPolynomialSymbolLift_mul`, `OAI.Erdos3.PolynomialTranslationLie.translationPolynomialSymbolLift_one`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasisIndex_card_le_pair_basis`, `OAI.Erdos3.VectorPolynomial.MajorPhaseDetectedConclusion`, `OAI.Erdos3.VectorPolynomial.MajorPhaseVectorDetectedConclusion`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.exists_low_localized_correlating_frequency`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.exists_rank_localized_correlating_frequency`, `OAI.Erdos3.VectorPolynomial.exists_majorPhase_low_localized_correlating_frequency`, `OAI.Erdos3.VectorPolynomial.exists_native_major_correlation_family`, `OAI.Erdos3.VectorPolynomial.exists_native_major_correlation_family_of_detections`, `OAI.Erdos3.VectorPolynomial.exists_normalizedTwist_high_frequency_removal_on_progression`, `OAI.Erdos3.VectorPolynomial.exists_normalizedTwist_uniform_ambient_haar_comparison`, `OAI.Erdos3.VectorPolynomial.exists_normalizedTwist_uniform_box_fourier_comparison`, `OAI.Erdos3.VectorPolynomial.exists_normalizedTwist_uniform_box_frequency_comparison`, `OAI.Erdos3.VectorPolynomial.exists_normalizedTwist_uniform_progression_haar_comparison`, `OAI.Erdos3.VectorPolynomial.majorPhaseDetectedRealBase`, `OAI.Erdos3.VectorPolynomial.majorPhaseSample`, `OAI.Erdos3.VectorPolynomial.majorPhaseTaggedGenerators`, `OAI.Erdos3.VectorPolynomial.majorPhaseTaggedGenerators_logHeight`, `OAI.Erdos3.VectorPolynomial.majorPhaseTaggedGenerators_mem_iff`, `OAI.Erdos3.VectorPolynomial.majorPhaseTaggedGenerators_span`, `OAI.Erdos3.VectorPolynomial.majorPhaseVectorDetectedConclusion_of_coordinates`, `OAI.Erdos3.VectorPolynomial.normalizedTwistFrequencyPolynomial_eq_zero_of_annihilates`, `OAI.Erdos3.VectorPolynomial.normalizedTwistFrequencyPolynomial_truncate_correlation`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardDetectorOffset`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardDetectorOffset_phase`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardDetectorPolynomial`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardDetectorPolynomial_bounds`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardDetectorPolynomial_eval`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardDetectorPolynomial_stage_bounds`, `OAI.Erdos3.VectorPolynomial.uniform_majorPhase_correlation_eq`, `OAI.Erdos3.exists_majorPhaseLowFourierExtraction_budget`, `OAI.Erdos3.exists_samplingProjectedImage_budget`, `OAI.Erdos3.exists_samplingProjectedImage_complete_budget`, `OAI.Erdos3.realSpanIntegerRowBound_le_exp_of_imageHeight`, `OAI.Erdos3.samplingProjectedImage_row_le_exp`, `_private.Polynomial.OrdinaryPolynomialPhaseAffineInverse.0.OAI.Erdos3.OrdinaryPolynomialPhase.zero_base_orbit`, `_private.Polynomial.TranslationPolynomialSymbolLiftHom.0.OAI.Erdos3.NilpotentLieFiltration.lieHomSubalgebra`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B158
import Definitions.Def_OAIErdos3B173
import Definitions.Def_OAIErdos3B187
import Definitions.Def_OAIErdos3B209

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OrdinaryPolynomialPhaseAffineInverse
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

noncomputable def factorizationInputOffset (s : ℕ) : ℕ :=
  ⌈budget s⌉₊ + 2

theorem budget_le_factorizationInputOffset (s : ℕ) :
    budget s ≤ (factorizationInputOffset s : ℝ) := by
  apply (Nat.le_ceil _).trans
  exact_mod_cast (Nat.le_add_right ⌈budget s⌉₊ 2)

theorem le_factorizationInputBudget (s : ℕ) {p : ℝ} (_hp : 0 ≤ p) :
    p ≤ p + factorizationInputOffset s :=
  le_add_of_nonneg_right (Nat.cast_nonneg _)

theorem factorizationInputBudget_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ p + factorizationInputOffset s :=
  hp.trans (le_factorizationInputBudget s hp)

theorem budget_le_factorizationInputBudget (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    budget s ≤ p + factorizationInputOffset s :=
  (budget_le_factorizationInputOffset s).trans (le_add_of_nonneg_left hp)

theorem factorizationInputBudget_le_power (s c : ℕ) (hc : 2 ≤ c)
    {p : ℝ} (hp : 0 ≤ p) :
    p + factorizationInputOffset s ≤ (p + factorizationInputOffset s + c) ^ c := by
  have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have hbase : 1 ≤ p + factorizationInputOffset s + c := by
    linarith [factorizationInputBudget_nonneg s hp]
  calc
    p + factorizationInputOffset s ≤ p + factorizationInputOffset s + c :=
      le_add_of_nonneg_right (Nat.cast_nonneg _)
    _ = (p + factorizationInputOffset s + c) ^ 1 := (pow_one _).symm
    _ ≤ (p + factorizationInputOffset s + c) ^ c := pow_le_pow_right₀ hbase (by omega)

theorem exists_factorizationBudget (s c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + factorizationInputOffset s + c) ^ c ≤ (p + C) ^ C := by
  let P : Polynomial ℕ :=
    (Polynomial.X + Polynomial.C (factorizationInputOffset s) + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, Polynomial.eval₂_pow] using hbudget p hp

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open _root_.MvPolynomial PolynomialTranslationLie
open scoped TensorProduct NNReal

variable {U : Type*}

noncomputable def orbit (s : ℕ) (_hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) :
    (nilmanifold s).filtration.realification.PolynomialOrbit (fun _ : U => 1) :=
  translationCoordinatePolynomialOrbit weight s weight_pos (weight_le s)
    (fun _ : Fin 0 => (0 : MvPolynomial U ℝ)) (fun i => Fin.elim0 i)
    (rename Sum.inl P)
    (majorParameterRename_degree (fun _ : U => 1) weight
      ((mem_weightedSupportLE_one_iff P s).mpr hP))

theorem orbit_realEval (s : ℕ) (hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) (u : U → ℝ) :
    bchRealTranslationHom weight s (weight_le s)
      ((nilmanifold s).filtration.realification.polynomialOrbitRealEval
        (fun _ : U => 1) u (orbit s hs P hP)) = ⟨0, C (eval u P)⟩ := by
  have hslot : ∀ u : U → ℝ,
      specializeMajorParameters (RingHom.id ℝ) (rename (Sum.inl : U → U ⊕ Fin 0) P) u ∈
        weightedSupportLT weight s := by
    intro u α _
    have hα : α = 0 := Subsingleton.elim _ _
    change Finsupp.weight weight α < s
    simpa only [hα, map_zero] using hs
  change bchRealTranslationHom weight s (weight_le s)
    ((weightedFiltration weight s (weight_le s)).realification.polynomialOrbitRealEval
      (fun _ : U => 1) u _) = _
  rw [orbit, translationCoordinatePolynomialOrbit_realEval _ _ _ _ _ _ _ _ hslot,
    specialize_rename]
  rfl

theorem orbit_buffered_eval (s : ℕ) (hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) (u : U → ℝ) :
    bufferedTranslationPhase (localTentKernel 0 8 (by decide)) 0
      (bchRealTranslationHom weight s (weight_le s)
        ((nilmanifold s).filtration.realification.polynomialOrbitRealEval
          (fun _ : U => 1) u (orbit s hs P hP))) =
      (Real.fourierChar (eval u P) : ℂ) := by
  rw [orbit_realEval]
  rw [bufferedTranslationPhase_eq_chart (localTentKernel 0 8 (by decide)) 0 _ 0
    (fun i => Fin.elim0 i)]
  have hd : ∀ x y : Fin 0 → ℝ, dist x y = 0 := by
    intro x y
    rw [Subsingleton.elim x y, dist_self]
  simp [bufferedTranslationTerm, translationPhaseArgument, localTentKernel, hd]

theorem zero_base_orbit (s : ℕ) :
    translationBasePolynomialOrbit weight s weight_pos (weight_le s)
      (fun _ : Fin 0 => (0 : MvPolynomial U ℝ)) (fun i => Fin.elim0 i) = 1 := by
  let := phaseBasisFintype s
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change (translationBasePolynomialOrbit weight s weight_pos (weight_le s)
    (fun _ : Fin 0 => (0 : MvPolynomial U ℝ)) (fun i => Fin.elim0 i)).log = 0
  rw [translationBasePolynomialOrbit_log]
  apply VectorPolynomial.coefficients.injective
  ext α
  rw [VectorPolynomial.coefficients_ofCoordinates]
  simp [translationBaseCoordinatePolynomial]

theorem orbit_eq_pure (s : ℕ) (hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) :
    orbit s hs P hP = translationPurePolynomialOrbit weight s weight_pos (weight_le s)
      (rename Sum.inl P)
      (majorParameterRename_degree (fun _ : U => 1) weight
        ((mem_weightedSupportLE_one_iff P s).mpr hP)) := by
  rw [orbit, translationCoordinatePolynomialOrbit, zero_base_orbit, one_mul]

theorem orbit_log (s : ℕ) (hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) :
    letI := phaseBasisFintype s
    (orbit s hs P hP).log =
      VectorPolynomial.ofCoordinates (R := ℚ) ((weightedBasis weight s weight_pos).baseChange ℝ)
        (translationPolynomialCoordinatePolynomial weight s (rename Sum.inl P)) := by
  rw [orbit_eq_pure]
  rfl

theorem phaseSlotCoefficient_rename (P : MvPolynomial U ℝ) :
    polynomialSlotCoefficient (0 : Fin 0 →₀ ℕ)
      (rename (Sum.inl : U → U ⊕ Fin 0) P) = P := by
  ext α
  rw [polynomialSlotCoefficient_coeff, Finsupp.sumElim_eq_add]
  simp only [Finsupp.mapDomain_zero, add_zero]
  exact coeff_rename_mapDomain _ Sum.inl_injective P α

theorem orbit_coordinate (s : ℕ) (hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s)
    (i : WeightedBasisIndex weight s) :
    VectorPolynomial.coordinate
      (((weightedBasis weight s weight_pos).baseChange ℝ).coord i).toAddMonoidHom
      (orbit s hs P hP).log = P := by
  let := phaseBasisFintype s
  rw [orbit_log, VectorPolynomial.coordinate_ofCoordinates]
  cases i with
  | inl i => exact Fin.elim0 i
  | inr α =>
      change polynomialSlotCoefficient α.val (rename Sum.inl P) = P
      rw [Subsingleton.elim α.val 0, phaseSlotCoefficient_rename]

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def preparedFiniteForwardDetectorOffset (depth : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (depth + 1), OrdinaryPolynomialPhase.factorizationInputOffset r

noncomputable def preparedFiniteForwardDetectorPolynomial (depth : ℕ) : Polynomial ℕ :=
  Polynomial.X + Polynomial.C (preparedFiniteForwardDetectorOffset depth)

theorem preparedFiniteForwardDetectorOffset_phase (depth r : ℕ) (hr : r ≤ depth) :
    OrdinaryPolynomialPhase.budget r ≤ (preparedFiniteForwardDetectorOffset depth : ℝ) := by
  apply (OrdinaryPolynomialPhase.budget_le_factorizationInputOffset r).trans
  exact_mod_cast (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (show r ∈ Finset.range (depth + 1) by simpa using Nat.lt_succ_of_le hr) :
    OrdinaryPolynomialPhase.factorizationInputOffset r ≤ preparedFiniteForwardDetectorOffset depth)

@[simp] theorem preparedFiniteForwardDetectorPolynomial_eval (depth : ℕ) (p : ℝ) :
    (preparedFiniteForwardDetectorPolynomial depth).eval₂ (Nat.castRingHom ℝ) p =
      p + preparedFiniteForwardDetectorOffset depth := by
  simp [preparedFiniteForwardDetectorPolynomial]

theorem preparedFiniteForwardDetectorPolynomial_bounds (depth : ℕ)
    {u p : ℝ} (hu : 0 ≤ u) (hp : 0 ≤ p) :
    p ≤ (preparedFiniteForwardDetectorPolynomial depth).eval₂ (Nat.castRingHom ℝ)
      (allocatedModelTestLog u p) ∧
    ∀ r ≤ depth, OrdinaryPolynomialPhase.budget r ≤
      (preparedFiniteForwardDetectorPolynomial depth).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog u p) := by
  rw [preparedFiniteForwardDetectorPolynomial_eval]
  have hc : 0 ≤ (preparedFiniteForwardDetectorOffset depth : ℝ) := Nat.cast_nonneg _
  have hlog : 0 ≤ allocatedModelTestLog u p := by
    unfold allocatedModelTestLog
    positivity
  constructor
  · unfold allocatedModelTestLog
    linarith only [hu, hp, hc]
  · intro r hr
    exact (preparedFiniteForwardDetectorOffset_phase depth r hr).trans
      (le_add_of_nonneg_left hlog)

theorem preparedFiniteForwardDetectorPolynomial_stage_bounds
    (depth A Cdirect : ℕ) (constants : ℕ → ℕ) (n : ℕ) (isDirect : Bool)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    preparedFiniteForwardWork A constants n x ≤
      (preparedFiniteForwardDetectorPolynomial depth).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision A Cdirect constants n isDirect x gainLog stageLog)
          (preparedFiniteForwardWork A constants n x)) ∧
    ∀ r ≤ depth, OrdinaryPolynomialPhase.budget r ≤
      (preparedFiniteForwardDetectorPolynomial depth).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision A Cdirect constants n isDirect x gainLog stageLog)
          (preparedFiniteForwardWork A constants n x)) :=
  preparedFiniteForwardDetectorPolynomial_bounds depth
    (preparedFiniteForwardPairedSourcePrecision_nonneg A Cdirect constants n isDirect hx hg hs)
    (preparedFiniteForwardWork_nonneg A constants n hx)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open Module PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

theorem phasePair_finrank_le_of_geometry
    {L : Type} [LieRing L] [LieAlgebra ℚ L] {s t e : ℕ}
    (D : RationalFilteredNilmanifold L t e) {p : ℝ}
    (hD : D.GeometryComplexityLE p) :
    (finrank ℚ (PairAlgebra (weightedSubalgebra weight s) L) : ℝ) ≤ budget s + p := by
  let : FiniteDimensional ℚ (weightedSubalgebra weight s) :=
    (nilmanifold s).basis.finiteDimensional_of_finite
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let : ∀ i : Bool, Module.Finite ℚ (BoolLieFamily (weightedSubalgebra weight s) L i) := by
    intro i
    cases i
    · exact (inferInstance : Module.Finite ℚ L)
    · exact (inferInstance : Module.Finite ℚ (weightedSubalgebra weight s))
  have hphase : (finrank ℚ (weightedSubalgebra weight s) : ℝ) ≤ budget s := by
    rw [Module.finrank_eq_card_basis (nilmanifold s).basis, Fintype.card_fin]
    exact (nilmanifold_geometry s).1
  have hdim : (finrank ℚ L : ℝ) ≤ p := by
    rw [Module.finrank_eq_card_basis D.basis, Fintype.card_fin]
    exact hD.1
  have hpair : finrank ℚ (PairAlgebra (weightedSubalgebra weight s) L) =
      finrank ℚ (weightedSubalgebra weight s) + finrank ℚ L := by
    change finrank ℚ (∀ i : Bool, BoolLieFamily (weightedSubalgebra weight s) L i) = _
    rw [Module.finrank_pi_fintype, Fintype.sum_bool]
    rfl
  rw [hpair, Nat.cast_add]
  exact add_le_add hphase hdim

theorem phasePair_finrank_le
    {L : Type} [LieRing L] [LieAlgebra ℚ L] {s t e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L t e) {U : Type*} {ω : U → ℕ}
    (R : D.Niltest ω) {p : ℝ} (hR : R.ComplexityLE p) :
    (finrank ℚ (PairAlgebra (weightedSubalgebra weight s) L) : ℝ) ≤ budget s + p :=
  phasePair_finrank_le_of_geometry D hR.1

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open _root_.MvPolynomial Module PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem exists_polynomial_phase_factorization (s : ℕ) (hs : 0 < s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L t e) (hts : t < s)
      (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s)
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        (Real.fourierChar (eval (fun i => (x i : ℝ)) P) : ℂ) * R.eval x‖ →
      let N := pi (pairModels (nilmanifold s) (D.raiseStep hts.le))
      ∃ (η : weightedSubalgebra weight s →ₗ[ℚ] ℚ)
        (b : Basis (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra weight s) L)))
          ℚ (PairAlgebra (weightedSubalgebra weight s) L))
        (ω : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra weight s) L)) → ℕ)
        (hLayers : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        η (centralRationalElement weight s hs 1) = 1 ∧
        (∀ i, rationalLogHeight (η ((nilmanifold s).basis i)) ≤ (p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        (finrank ℚ (PairAlgebra (weightedSubalgebra weight s) L) : ℝ) ≤ (p + C) ^ C ∧
        N.filtration.ControlledSymbolFactorization b ω hLayers
          (pairFrequency η (0 : L →ₗ[ℚ] ℚ)) (fun i => (lengths i : ℝ))
          (pairOrbitSymbol (nilmanifold s) (D.raiseStep hts.le)
            (orbit s hs P hP) (D.raiseStepRealOrbit hts.le R.orbit) b ω hLayers)
          ((p + C) ^ C) := by
  obtain ⟨c, hc, hstep⟩ := exists_translation_major_correlation_step_drop s hs
  obtain ⟨C, hC, hbudget⟩ := exists_factorizationBudget s c
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ t e _ _ _ _ _ _ _ _ D hts P hP R p hp hR hRcap
    origin lengths hlengths hU hlarge hcorr
  let := phaseBasisFintype s
  dsimp only
  let q : ℝ := p + factorizationInputOffset s
  have hpq : p ≤ q := le_factorizationInputBudget s hp
  have hq : 0 ≤ q := hp.trans hpq
  have hfixed : budget s ≤ q := budget_le_factorizationInputBudget s hp
  have hcost : (q + c) ^ c ≤ (p + C) ^ C := hbudget p hp
  have hgeometry : (nilmanifold s).GeometryComplexityLE q :=
    GeometryComplexityLE.mono _ (nilmanifold_geometry s) hfixed
  have hlog : Real.log (3 + (2 * bufferedTranslationTermLip weight s
      (localTentKernel 0 8 (by decide)) 0 : ℝ≥0)) ≤ q :=
    (le_max_right _ _).trans hfixed
  have hdetector (x : U → ℤ) :
      bufferedTranslationPhase (localTentKernel 0 8 (by decide)) 0
        (bchRealTranslationHom weight s (weight_le s)
          ((nilmanifold s).filtration.realification.polynomialOrbitEval (fun _ : U => 1)
            x (orbit s hs P hP))) = (Real.fourierChar (eval (fun i => (x i : ℝ)) P) : ℂ) := by
    rw [← NilpotentLieFiltration.polynomialOrbitRealEval_integer]
    exact orbit_buffered_eval s hs P hP (fun i => (x i : ℝ))
  have hcorrelation : Real.exp (-q) ≤
      ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        bufferedTranslationPhase (localTentKernel 0 8 (by decide)) 0
          (bchRealTranslationHom weight s (weight_le s)
            ((nilmanifold s).filtration.realification.polynomialOrbitEval (fun _ : U => 1)
              x (orbit s hs P hP))) * R.eval x‖ := by
    simp_rw [hdetector]
    exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hcorr
  obtain ⟨η, b, ω, hLayers, hη, hηheight, hbheight, hfactor⟩ :=
    hstep weight weight_pos (weight_le s) D hts (localTentKernel 0 8 (by decide)) 0 0
      (by simp) (by simp [realPolynomialMass]) (orbit s hs P hP)
      R q hq hgeometry hlog (hR.mono hpq) hRcap origin lengths hlengths (hU.trans hpq)
      (fun i => (Real.exp_le_exp.mpr hcost).trans (hlarge i)) hcorrelation
  have hdim : (finrank ℚ (PairAlgebra (weightedSubalgebra weight s) L) : ℝ) ≤
      (p + C) ^ C := by
    apply (phasePair_finrank_le (s := s) D R hR).trans
    apply le_trans (b := q)
    · dsimp [q]
      linarith [budget_le_factorizationInputOffset s]
    · exact (factorizationInputBudget_le_power s c hc hp).trans hcost
  refine ⟨η, b, ω, hLayers, hη, fun i => (hηheight i).trans hcost,
    fun i j => (hbheight i j).trans hcost, hdim, ?_⟩
  exact NilpotentLieFiltration.ControlledSymbolFactorization.mono _ b ω hLayers
    hfactor hcost (fun i => by exact_mod_cast hlengths i)

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open _root_.MvPolynomial Module PolynomialTranslationLie RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

theorem orbit_symbol_constantCoefficient {U : Type*} (s : ℕ) (hs : 0 < s)
    (G : NilpotentLieFiltration (weightedSubalgebra weight s) s)
    (hG : ∀ j, G.layer j = Submodule.span ℚ
      (weightedBasis weight s weight_pos '' {i | j ≤ weightedBasisGrade weight s i}))
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) :
    coordinate (realifyFunctional (constantCoefficient s)).toAddMonoidHom
      (G.realSymbolRepresentative
        (weightedBasis weight s weight_pos) (weightedBasisGrade weight s)
        hG (fun _ : U => 1)
        (G.realSymbolOfPolynomial
          (weightedBasis weight s weight_pos) (weightedBasisGrade weight s)
          hG (fun _ : U => 1)
          (orbit s hs P hP).log)) = homogeneousComponent s P := by
  let := phaseBasisFintype s
  rw [orbit_log, NilpotentLieFiltration.realSymbolRepresentative_ofCoordinates,
    constantCoefficient_coordinate_ofCoordinates s hs]
  have hcoord := orbit_coordinate s hs P hP (constantBasisIndex s hs)
  rw [orbit_log, coordinate_ofCoordinates] at hcoord
  rw [hcoord, constantBasisIndex_grade]
  rfl

theorem pairOrbitSymbol_scalar_top {U ι L : Type} [LieRing L] [LieAlgebra ℚ L]
    (s : ℕ) (hs : 0 < s) {e : ℕ} (D : RationalFilteredNilmanifold L s e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra weight s) L)) (ω : ι → ℕ)
    (hF : ∀ j, (pi (pairModels (nilmanifold s) D)).filtration.layer j =
      Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s)
    (q : D.filtration.realification.PolynomialOrbit (fun _ : U => 1)) :
    (pi (pairModels (nilmanifold s) D)).filtration.scalarSymbolPolynomial b ω hF
      (fun _ : U => 1)
      ((constantCoefficient s).comp
        (gradedProjection (pi (pairModels (nilmanifold s) D)).filtration
          (liePiEval (R := ℚ)
            (M := BoolLieFamily (weightedSubalgebra weight s) L) true)).toLinearMap)
      (pairOrbitSymbol (nilmanifold s) D (orbit s hs P hP) q b ω hF) =
        homogeneousComponent s P := by
  let N := pi (pairModels (nilmanifold s) D)
  let c := weightedBasis weight s weight_pos
  let ν := weightedBasisGrade weight s
  have hG : ∀ j, (weightedFiltration weight s (weight_le s)).layer j =
      Submodule.span ℚ (c '' {i | j ≤ ν i}) :=
    weightedFiltration_layer_eq_span weight s weight_pos (weight_le s)
  let φ : PairAlgebra (weightedSubalgebra weight s) L →ₗ⁅ℚ⁆ weightedSubalgebra weight s :=
    liePiEval (R := ℚ) (M := BoolLieFamily (weightedSubalgebra weight s) L) true
  have hfirst := pairOrbitSymbol_first_projection (nilmanifold s) D (fun _ : U => 1)
    b ω hF c ν hG (orbit s hs P hP) q
  have hphase : coordinate (realifyFunctional (constantCoefficient s)).toAddMonoidHom
      ((weightedFiltration weight s (weight_le s)).realSymbolRepresentative c ν hG (fun _ : U => 1)
        ((weightedFiltration weight s (weight_le s)).realSymbolOfPolynomial c ν hG (fun _ : U => 1)
          (orbit s hs P hP).log)) = homogeneousComponent s P := by
    have hh := orbit_symbol_constantCoefficient s hs (weightedFiltration weight s (weight_le s)) hG P hP
    simpa only [c, ν] using hh
  have hresult := N.filtration.homogeneousProjected_scalar_identity
    (weightedFiltration weight s (weight_le s)) b ω hF c ν hG
    (weightedBasis_homogeneous_brackets weight s weight_pos) φ
    (projection_filtered N.filtration φ) (fun _ : U => 1)
    (constantCoefficient s)
    (pairOrbitSymbol (nilmanifold s) D (orbit s hs P hP) q b ω hF).coord
    ((weightedFiltration weight s (weight_le s)).realSymbolOfPolynomial c ν hG (fun _ : U => 1)
      (orbit s hs P hP).log) (homogeneousComponent s P) hfirst hphase
  simpa only [N, c, ν, φ,
    NilpotentLieFiltration.scalarSymbolPolynomial, gradedProjection] using hresult

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open _root_.MvPolynomial Module PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_ordinary_polynomial_phase_inverse (s : ℕ) (hs : 0 < s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L t e) (_hts : t < s)
      (P : MvPolynomial U ℝ) (_hP : P.totalDegree ≤ s)
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        (Real.fourierChar (eval (fun i => (x i : ℝ)) P) : ℂ) * R.eval x‖ →
      PolynomialRationalApproximation (fun i => (lengths i : ℝ))
        (Real.exp ((p + C) ^ C)) (homogeneousComponent s P) := by
  obtain ⟨a, _ha, hfactorization⟩ := exists_polynomial_phase_factorization s hs
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + 3) ^ 3)
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ t e _ _ _ _ D hts P hP R p hp hR hRcap
    origin lengths hlengths hU hlarge hcorr
  let : FiniteDimensional ℚ (weightedSubalgebra weight s) :=
    (nilmanifold s).basis.finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight s)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra weight s) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] weightedSubalgebra weight s) :=
    realification_moduleTopology_t2 (nilmanifold s).basis
  let q : ℝ := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : q + (q + 3) ^ 3 ≤ (p + C) ^ C := by
    simpa [Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hfirst : q ≤ (p + C) ^ C := by nlinarith [show 0 ≤ (q + 3) ^ 3 by positivity]
  have hlast : (q + 3) ^ 3 ≤ (p + C) ^ C := by linarith
  obtain ⟨η, b, ω, hF, hη, _hηheight, hb, hdim, hfactor⟩ :=
    hfactorization D hts P hP R p hp hR hRcap origin lengths hlengths hU
      (fun i => (Real.exp_le_exp.mpr hfirst).trans (hlarge i)) hcorr
  let N := pi (pairModels (nilmanifold s) (D.raiseStep hts.le))
  let φ : PairAlgebra (weightedSubalgebra weight s) L →ₗ⁅ℚ⁆ weightedSubalgebra weight s :=
    liePiEval (R := ℚ) (M := BoolLieFamily (weightedSubalgebra weight s) L) true
  let X := pairOrbitSymbol (nilmanifold s) (D.raiseStep hts.le)
    (orbit s hs P hP) (D.raiseStepRealOrbit hts.le R.orbit) b ω hF
  have hT : ∀ i, 0 < (lengths i : ℝ) := fun i => by exact_mod_cast hlengths i
  have hθ : ∀ i, rationalLogHeight
      (projectedScalarFunctional N.filtration φ
        (N.filtration.associatedGradedBasis b ω hF i)) ≤ q :=
    pairScalarFunctional_basis_logHeight s hs (D.raiseStep hts.le) b ω hF hq hb
  have hfactor' : N.filtration.ControlledSymbolFactorization b ω hF
      (η.comp φ.toLinearMap) (fun i => (lengths i : ℝ)) X q := by
    rw [← pairFrequency_zero_comp]
    exact hfactor
  have happ := controlledFactorization_approximation_of_normalized_frequency
    N.filtration b ω hF φ hs η hη (fun i => (lengths i : ℝ)) hT X q hq
    (by simpa only [Fintype.card_fin] using hdim) hθ hfactor'
  have htop : N.filtration.scalarSymbolPolynomial b ω hF (fun _ : U => 1)
      (projectedScalarFunctional N.filtration φ) X = homogeneousComponent s P :=
    pairOrbitSymbol_scalar_top s hs (D.raiseStep hts.le) b ω hF P hP
      (D.raiseStepRealOrbit hts.le R.orbit)
  rw [htop] at happ
  exact happ.mono (Real.exp_le_exp.mpr hlast) hT

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open _root_.MvPolynomial Module PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_ordinary_polynomial_phase_affine_inverse (s : ℕ) (hs : 0 < s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L t e) (_hts : t < s)
      (P : MvPolynomial U ℝ) (_hP : P.totalDegree ≤ s)
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∀ (r : U → ℤ) (K : ℝ), 1 ≤ K → K ≤ Real.exp p →
      ∀ (N : U → ℝ), (∀ i, 0 < N i) →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, N i ≤ K * (q : ℝ) * lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        (Real.fourierChar (eval (fun i => ((r i + (q : ℤ) * x i : ℤ) : ℝ)) P) : ℂ) *
          R.eval x‖ →
      PolynomialRationalApproximation N (Real.exp ((p + C) ^ C))
        (homogeneousComponent s P) := by
  obtain ⟨a, _, hinverse⟩ := exists_ordinary_polynomial_phase_inverse s hs
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a + Polynomial.C s * Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ t e _ _ _ _ D hts P hP R p hp hR hRcap
    q hq hqp r K hK hKp N hN origin lengths hlengths hNL hdim hlarge hcorr
  let b : ℝ := (p + a) ^ a
  have hcost : b + (s : ℝ) * p ≤ (p + C) ^ C := by
    simpa [Q, b, Polynomial.eval₂_pow] using hbudget p hp
  have hfirst : b ≤ (p + C) ^ C := by
    exact (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg s) hp)).trans hcost
  let P' := residueAffinePolynomial q r P
  have hP' : P'.totalDegree ≤ s := residueAffinePolynomial_totalDegree_le q r P s hP
  have hcorr' : Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
      (Real.fourierChar (eval (fun i => (x i : ℝ)) P') : ℂ) * R.eval x‖ := by
    simpa only [P', residueAffinePolynomial_eval] using hcorr
  have happ : PolynomialRationalApproximation (fun i => (lengths i : ℝ))
      (Real.exp b) (homogeneousComponent s P') :=
    hinverse D hts P' hP' R p hp hR hRcap origin lengths hlengths hdim
      (fun i => (Real.exp_le_exp.mpr hfirst).trans (hlarge i)) hcorr'
  have hbound {z : ℝ} (hz : 0 ≤ z) (hzp : z ≤ Real.exp p) :
      z ^ s * Real.exp b ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ ≤ (Real.exp p) ^ s * Real.exp b :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz hzp s) (Real.exp_nonneg b)
      _ = Real.exp (b + (s : ℝ) * p) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr hcost
  exact happ.affine_pullback N (fun i => (lengths i : ℝ)) hN
    (fun i => by exact_mod_cast hlengths i) q s hq r K hK hNL
    (Real.exp b) (Real.exp ((p + C) ^ C))
    (hbound (Nat.cast_nonneg q) hqp) (hbound (by linarith) hKp) P hP

end Erdos3.OrdinaryPolynomialPhase

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.MajorPhaseLowFourierExtraction
namespace OAI

section

namespace Erdos3

theorem exists_majorPhaseLowFourierExtraction_budget (a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let q := (p + a) ^ a + p + 1
      q ≤ (p + C) ^ C ∧ (q + b) ^ b ≤ (p + C) ^ C ∧
        3 * q + 16 ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a + Polynomial.X + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C b) ^ b + 3 * Q + 16)
  refine ⟨C, hC, ?_⟩
  intro p hp
  dsimp only
  let q : ℝ := (p + a) ^ a + p + 1
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hb : 0 ≤ (q + b) ^ b := by positivity
  have htotal : q + (q + b) ^ b + 3 * q + 16 ≤ (p + C) ^ C := by
    simpa [Q, q, Polynomial.eval₂_pow] using hbudget p hp
  change q ≤ _ ∧ (q + b) ^ b ≤ _ ∧ 3 * q + 16 ≤ _
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators

theorem normalizedTwistFrequencyPolynomial_truncate_correlation
    {X Ω : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (cover d : ℕ) (W : ∀ j, Submodule ℝ (J j → ℝ))
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ W j)
    (hann : ∀ j, d < j.val + 1 →
      W j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩)))
    (s : Finset Ω) (u : Ω → X → ℝ) (signal : Ω → ℂ) :
    ‖𝔼 x ∈ s, (Real.fourierChar (MvPolynomial.eval (u x)
      (normalizedTwistFrequencyPolynomial cover a poly)) : ℂ) * signal x‖ =
    ‖𝔼 x ∈ s, (Real.fourierChar (MvPolynomial.eval (u x)
      (normalizedTwistFrequencyPolynomial cover (truncateTaggedFrequency d a) poly)) : ℂ) *
        signal x‖ := by
  have he (x : Ω) :
      (Real.fourierChar (MvPolynomial.eval (u x)
        (normalizedTwistFrequencyPolynomial cover a poly)) : ℂ) * signal x =
      (Real.fourierChar (normalizedTwistHighFrequencyConstant cover d a poly) : ℂ) *
        ((Real.fourierChar (MvPolynomial.eval (u x)
          (normalizedTwistFrequencyPolynomial cover (truncateTaggedFrequency d a) poly)) : ℂ) *
            signal x) := by
    rw [normalizedTwistFrequencyPolynomial_low_add_constant cover d W a poly hcoeff hann,
      map_add, eval_C, Real.fourierChar.map_add_eq_mul, Circle.coe_mul]
    ring
  simp_rw [he]
  rw [← Finset.mul_expect, norm_mul, Circle.norm_coe, one_mul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_normalizedTwist_high_frequency_removal_on_progression (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L : Type} [Fintype X] [DecidableEq X]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (J : Fin m → Type) [∀ j, Fintype (J j)] (d : ℕ)
      (D : RationalFilteredNilmanifold L t e) (_htd : t ≤ d)
      (R : D.Niltest (fun _ : X => 1))
      (cover : ℕ) (_hcover : 0 < cover) (a : (Σ j, J j) → ℤ)
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (W : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ W j)
      (p Rrank : ℝ), 0 ≤ p → R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      (cover : ℝ) ≤ Real.exp p → (∀ i, |(a i : ℝ)| ≤ Real.exp p) →
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∀ (start : X → ℤ) (K : ℝ), 1 ≤ K → K ≤ Real.exp p →
      ∀ (N : X → ℝ), (∀ i, 0 < N i) →
      ∀ (origin : X → ℤ) (lengths : X → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, N i ≤ K * (q : ℝ) * (lengths i : ℝ)) →
      (Fintype.card X : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, d < j.val + 1 → HasLayerSamplingRank (j.val + 1)
        N Rrank (W j) (poly j)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        (Real.fourierChar (MvPolynomial.eval (fun i => (start i : ℝ) + (q : ℝ) * (x i : ℝ))
          (normalizedTwistFrequencyPolynomial cover a poly)) : ℂ) * R.eval x‖ →
      ∀ j, d < j.val + 1 → W j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩)) := by
  classical
  choose c hc hinverse using fun j : Fin m =>
    OrdinaryPolynomialPhase.exists_ordinary_polynomial_phase_affine_inverse (j.val + 1)
      (Nat.succ_pos _)
  let B := (∑ j, c j) + 2
  have hcB (j : Fin m) : c j ≤ B :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      (Nat.le_add_right _ _)
  have hB : 2 ≤ B := by dsimp [B]; omega
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C B) ^ B + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro X L _ _ _ _ t e _ _ _ _ J _ d D htd R cover hcover a poly hpoly W hcoeff p Rrank hp
    hR hRcap hcoverp ha q hq hqp start K hK hKp N hN origin lengths hlengths hNL hX hlarge hRrank hrank hcorr
  have hbudget' : p + (p + B) ^ B + 2 ≤ (p + C) ^ C := by
    simpa [Q, Polynomial.eval₂_pow] using hbudget p hp
  have hbase : 1 ≤ p + B := by
    have hb : (2 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have hlocal (j : Fin m) : (p + c j) ^ c j ≤ (p + B) ^ B := by
    have hb : p + (c j : ℝ) ≤ p + B := by
      have hh : (c j : ℝ) ≤ B := Nat.cast_le.mpr (hcB j)
      linarith
    apply (pow_le_pow_left₀ (by positivity) hb _).trans
    exact pow_le_pow_right₀ hbase (hcB j)
  rcases highest_nonannihilating_tag d W a with hann | ⟨h, hd, hw, hhigher⟩
  · exact hann
  · exfalso
    have hhigh (j : Fin m) (hj : h < j) :
        integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j) =
          MvPolynomial.C ((integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j)).coeff 0) :=
      integerRowPolynomial_constant_of_annihilates (W j) _ _ (hcoeff j) (hhigher j hj)
    have hdegree (j : Fin m) := integerRowPolynomial_totalDegree_le
      (fun i => a ⟨j, i⟩) (hpoly j)
    have hphase : (normalizedTwistFrequencyPolynomial cover a poly).totalDegree ≤ h.val + 1 := by
      apply (totalDegree_mul _ _).trans
      simp only [totalDegree_C, zero_add]
      exact taggedScalar_sum_degree h _ hdegree hhigh
    have htop : homogeneousComponent (h.val + 1) (normalizedTwistFrequencyPolynomial cover a poly) =
        MvPolynomial.C (1 / (cover : ℝ)) * homogeneousComponent (h.val + 1)
          (integerRowPolynomial (fun i => a ⟨h, i⟩) (poly h)) := by
      rw [normalizedTwistFrequencyPolynomial, homogeneousComponent_C_mul,
        taggedScalar_sum_top h _ hdegree hhigh]
    have hcost : p + (p + c h) ^ c h ≤ (p + C) ^ C := by linarith [hlocal h]
    have hap := hinverse h D (by omega) (normalizedTwistFrequencyPolynomial cover a poly)
      hphase R p hp hR hRcap q hq hqp start K hK hKp N hN origin lengths hlengths hNL hX
      (fun i => (Real.exp_le_exp.mpr (by linarith : (p + c h) ^ c h ≤ (p + C) ^ C)).trans
        (hlarge i)) (by
          simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using hcorr)
    apply normalizedTwistFrequencyPolynomial_top_not_approximation cover hcover h a poly
      (W h) N Rrank (Real.exp ((p + c h) ^ c h)) hN
      ?_ (hrank h hd) ?_ hw htop hap
    · calc
        _ ≤ Real.exp p * Real.exp ((p + c h) ^ c h) :=
          mul_le_mul_of_nonneg_right hcoverp (Real.exp_nonneg _)
        _ = Real.exp (p + (p + c h) ^ c h) := (Real.exp_add _ _).symm
        _ ≤ Rrank := (Real.exp_le_exp.mpr hcost).trans hRrank
    · intro i
      exact (ha ⟨h, i⟩).trans ((Real.exp_le_exp.mpr
        (by linarith [pow_nonneg (show 0 ≤ p + B by positivity) B] : p ≤ (p + C) ^ C)).trans hRrank)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

theorem exists_rank_localized_correlating_frequency (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L : Type} [Fintype X] [DecidableEq X]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (d : ℕ) (D : RationalFilteredNilmanifold L t e) (_htd : t ≤ d)
      (R : D.Niltest (fun _ : X => 1))
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (p Rrank : ℝ), 0 ≤ p → R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      (Fintype.card X : ℝ) ≤ p → (Fintype.card (Σ j, J j) : ℝ) ≤ p →
      (W.modulus : ℝ) ≤ Real.exp p → (W.cover : ℝ) ≤ Real.exp p →
      (Lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, d < j.val + 1 → HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N, W.eval N poly u * R.eval u‖ →
      ∃ (start length : X → ℕ) (a : (Σ j, J j) → ℤ),
        (∀ i, 0 < length i) ∧
        (∀ i, (N i : ℝ) * Real.exp (-(3 * p + 16)) ≤ length i) ∧
        (∀ i, (N i : ℝ) ≤ Real.exp (3 * p + 16) * W.modulus * length i) ∧
        (∀ v ∈ integerBox length,
          (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i) ∈ integerBox N) ∧
        (∀ j, |(a j : ℝ)| ≤ Real.exp ((p + C) ^ C)) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 v ∈ integerBox length,
          (Real.fourierChar (MvPolynomial.eval
            (fun i => (start i : ℝ) + (W.modulus : ℝ) * v i)
            (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
          R.eval (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i)‖ ∧
        ∀ j, d < j.val + 1 → U j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩)) := by
  obtain ⟨aC, _, hselect⟩ := exists_localized_correlating_frequency
  obtain ⟨bC, _, hremove⟩ := exists_normalizedTwist_high_frequency_removal_on_progression m
  obtain ⟨C, hC, hbudget⟩ := exists_normalizedTwistExtractionBudget aC bC
  refine ⟨C, hC, ?_⟩
  intro X L _ _ _ _ t e _ _ _ _ J _ periodCap coverCap Lip W d D htd R N poly hpoly
    U hcoeff p Rrank hp hR hcap hX hJ hmod hcover hLip hN hRrank hrank hcorr
  let q : ℝ := (p + aC) ^ aC + 3 * p + 16
  have hpow : 0 ≤ (p + aC) ^ aC := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hsideq : 3 * p + 16 ≤ q := by dsimp [q]; linarith
  have hfreqq : (p + aC) ^ aC ≤ q := by dsimp [q]; linarith
  have hbudget' : q + (q + bC) ^ bC + 3 * p + 16 ≤ (p + C) ^ C := hbudget p hp
  have hremoven : 0 ≤ (q + bC) ^ bC := by positivity
  have hqfinal : q ≤ (p + C) ^ C := by linarith
  have hremovefinal : (q + bC) ^ bC ≤ (p + C) ^ C := by linarith
  have hsidefinal : 3 * p + 16 ≤ (p + C) ^ C := hsideq.trans hqfinal
  have hsmallN (i : X) : Real.exp (3 * p + 16) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr hsidefinal).trans (hN i)
  obtain ⟨start, length, a, hpos, hlength, hcomparison, hinside, ha, hselected⟩ :=
    hselect W N poly R.eval p hp hJ hmod hLip hsmallN
      (fun u _ => (R.norm_eval_le u).trans hcap) hcorr
  let R' := R.scalarAffinePullback (W.modulus : ℚ) (fun i => (start i : ℚ))
  have hR' : R'.ComplexityLE q := hR.mono hpq
  have hR'cap : (R'.normBound : ℝ) ≤ 1 := hcap
  have hR'eval (v : X → ℤ) :
      R'.eval v = R.eval (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i) := by
    simpa only [R', Int.cast_natCast, add_comm] using
      R.scalarAffinePullback_eval_integer (W.modulus : ℤ) (fun i => (start i : ℤ)) v
  have hzero : translatedIntegerBox (0 : X → ℤ) length = integerBox length := by
    ext v
    simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
  have hlong (i : X) : Real.exp ((q + bC) ^ bC) ≤ (length i : ℝ) := by
    calc
      _ = Real.exp ((q + bC) ^ bC + (3 * p + 16)) * Real.exp (-(3 * p + 16)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp ((p + C) ^ C) * Real.exp (-(3 * p + 16)) := by
        gcongr
        linarith
      _ ≤ (N i : ℝ) * Real.exp (-(3 * p + 16)) :=
        mul_le_mul_of_nonneg_right (hN i) (Real.exp_nonneg _)
      _ ≤ _ := hlength i
  have hselected' : Real.exp (-q) ≤ ‖𝔼 v ∈ translatedIntegerBox (0 : X → ℤ) length,
      (Real.fourierChar (MvPolynomial.eval
        (fun i => ((start i : ℤ) : ℝ) + (W.modulus : ℝ) * (v i : ℝ))
        (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) * R'.eval v‖ := by
    rw [hzero]
    simpa only [hR'eval, Int.cast_natCast] using
      (Real.exp_le_exp.mpr (neg_le_neg hfreqq)).trans hselected
  have hann := hremove J d D htd R' W.cover W.cover_pos a poly hpoly U hcoeff q Rrank
    hq hR' hR'cap (hcover.trans (Real.exp_le_exp.mpr hpq))
    (fun i => (ha i).trans (Real.exp_le_exp.mpr hfreqq))
    W.modulus W.modulus_pos (hmod.trans (Real.exp_le_exp.mpr hpq))
    (fun i => (start i : ℤ)) (Real.exp (3 * p + 16))
    (Real.one_le_exp (by positivity)) (Real.exp_le_exp.mpr hsideq)
    (fun i => (N i : ℝ)) (fun i => (Real.exp_pos _).trans_le (hN i))
    0 length hpos hcomparison (hX.trans hpq) hlong
    ((Real.exp_le_exp.mpr hremovefinal).trans hRrank) hrank hselected'
  refine ⟨start, length, a, hpos, hlength, hcomparison, hinside, ?_, ?_, hann⟩
  · exact fun i => (ha i).trans (Real.exp_le_exp.mpr (hfreqq.trans hqfinal))
  · exact (Real.exp_le_exp.mpr (neg_le_neg (hfreqq.trans hqfinal))).trans hselected

theorem exists_low_localized_correlating_frequency (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L : Type} [Fintype X] [DecidableEq X]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (d : ℕ) (D : RationalFilteredNilmanifold L t e) (_htd : t ≤ d)
      (R : D.Niltest (fun _ : X => 1))
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (p Rrank : ℝ), 0 ≤ p → R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      (Fintype.card X : ℝ) ≤ p → (Fintype.card (Σ j, J j) : ℝ) ≤ p →
      (W.modulus : ℝ) ≤ Real.exp p → (W.cover : ℝ) ≤ Real.exp p →
      (Lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, d < j.val + 1 → HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N, W.eval N poly u * R.eval u‖ →
      ∃ (start length : X → ℕ) (a : (Σ j, J j) → ℤ),
        (∀ i, 0 < length i) ∧
        (∀ i, (N i : ℝ) * Real.exp (-(3 * p + 16)) ≤ length i) ∧
        (∀ i, (N i : ℝ) ≤ Real.exp (3 * p + 16) * W.modulus * length i) ∧
        (∀ v ∈ integerBox length,
          (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i) ∈ integerBox N) ∧
        (∀ j, |(a j : ℝ)| ≤ Real.exp ((p + C) ^ C)) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 v ∈ integerBox length,
          (Real.fourierChar (MvPolynomial.eval
            (fun i => (start i : ℝ) + (W.modulus : ℝ) * v i)
            (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
          R.eval (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i)‖ ∧
        (∀ j, d < j.val + 1 → ∀ i, a ⟨j, i⟩ = 0) ∧
        (normalizedTwistFrequencyPolynomial W.cover a poly).totalDegree ≤ d := by
  obtain ⟨C, hC, hextract⟩ := exists_rank_localized_correlating_frequency m
  refine ⟨C, hC, ?_⟩
  intro X L _ _ _ _ t e _ _ _ _ J _ periodCap coverCap Lip W d D htd R N poly hpoly
    U hcoeff p Rrank hp hR hcap hX hJ hmod hcover hLip hN hRrank hrank hcorr
  obtain ⟨start, length, a, hpos, hlength, hcomparison, hinside, ha, hselected, hann⟩ :=
    hextract J W d D htd R N poly hpoly U hcoeff p Rrank hp hR hcap hX hJ
      hmod hcover hLip hN hRrank hrank hcorr
  refine ⟨start, length, truncateTaggedFrequency d a, hpos, hlength, hcomparison, hinside,
    ?_, ?_, ?_, normalizedTwistFrequencyPolynomial_low_degree W.cover d a poly hpoly⟩
  · intro i
    by_cases hi : i.1.val + 1 ≤ d
    · simpa only [truncateTaggedFrequency, if_pos hi] using ha i
    · simp only [truncateTaggedFrequency, if_neg hi, Int.cast_zero, abs_zero]
      exact Real.exp_nonneg _
  · rw [← normalizedTwistFrequencyPolynomial_truncate_correlation W.cover d U a poly
      hcoeff hann (integerBox length)
      (fun v i => (start i : ℝ) + (W.modulus : ℝ) * v i)
      (fun v => R.eval (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i))]
    exact hselected
  · intro j hj i
    simp only [truncateTaggedFrequency, if_neg (not_le_of_gt hj)]

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial RationalFilteredNilmanifold
open scoped BigOperators TensorProduct Classical

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem normalizedTwistFrequencyPolynomial_eq_zero_of_annihilates
    (cover : ℕ) (a : (Σ j, J j) → ℤ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (hm : ∀ j α, coefficients (poly j) α ∈ U j)
    (ha : ∀ j, U j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩))) :
    normalizedTwistFrequencyPolynomial cover a poly = 0 := by
  have hz (j : Fin m) : integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j) = 0 := by
    ext α
    rw [integerRowPolynomial_coeff, MvPolynomial.coeff_zero, ← integerRowLinear_apply]
    exact ha j (hm j α)
  simp only [normalizedTwistFrequencyPolynomial, hz, Finset.sum_const_zero, mul_zero]

theorem exists_normalizedTwist_uniform_box_frequency_comparison (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X : Type} [Fintype X] [DecidableEq X]
      {J : Fin m → Type} [∀ j, Fintype (J j)]
      (cover : ℕ), 0 < cover → ∀ (a : (Σ j, J j) → ℤ)
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
      (∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j)) →
      ∀ (U : ∀ j, Submodule ℝ (J j → ℝ)),
      (∀ j α, coefficients (poly j) α ∈ U j) →
      ∀ (p Rrank : ℝ), 2 ≤ p →
      (cover : ℝ) ≤ Real.exp p → (∀ i, |(a i : ℝ)| ≤ Real.exp p) →
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∀ (start : X → ℤ) (K : ℝ), 1 ≤ K → K ≤ Real.exp p →
      ∀ (N : X → ℝ), (∀ i, 0 < N i) →
      ∀ (origin : X → ℤ) (lengths : X → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, N i ≤ K * (q : ℝ) * (lengths i : ℝ)) →
      (Fintype.card X : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1) N Rrank (U j) (poly j)) →
      ‖(𝔼 x ∈ translatedIntegerBox origin lengths,
        (Real.fourierChar (MvPolynomial.eval
          (fun i => (start i : ℝ) + (q : ℝ) * (x i : ℝ))
          (normalizedTwistFrequencyPolynomial cover a poly)) : ℂ)) -
        (if ∀ j, U j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩))
          then 1 else 0)‖ ≤ Real.exp (-p) := by
  classical
  obtain ⟨C, hC, hremove⟩ := exists_normalizedTwist_high_frequency_removal_on_progression m
  refine ⟨C, hC, ?_⟩
  intro X _ _ J _ cover hcover a poly hpoly U hm p Rrank hp hcoverp ha
    q hq hqp start K hK hKp N hN origin lengths hlengths hNL hdim hlarge hRrank hrank
  by_cases hann : ∀ j, U j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩))
  · rw [if_pos hann, normalizedTwistFrequencyPolynomial_eq_zero_of_annihilates cover a poly U hm hann]
    let : ∀ i, NeZero (lengths i) := fun i => ⟨(hlengths i).ne'⟩
    simp only [map_zero, Real.fourierChar.map_zero_eq_one, Circle.coe_one,
      Finset.expect_const (translatedIntegerBox_nonempty lengths origin), sub_self, norm_zero]
    exact (Real.exp_pos _).le
  · rw [if_neg hann, sub_zero]
    apply le_of_lt
    by_contra! hcorr
    let R := Niltest.const (RationalTorus.trivialNilmanifold 0) (fun _ : X => 1) 1
    have hR : R.ComplexityLE p := RationalTorus.trivialNilmanifold_const_one_complexity 0 _ hp
    have hcap : (R.normBound : ℝ) ≤ 1 := by simp [R, Niltest.const]
    have hcorr' : Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        (Real.fourierChar (MvPolynomial.eval
          (fun i => (start i : ℝ) + (q : ℝ) * (x i : ℝ))
          (normalizedTwistFrequencyPolynomial cover a poly)) : ℂ) * R.eval x‖ := by
      simpa only [R, Niltest.eval_const, mul_one] using hcorr
    have hall := hremove J 0 (RationalTorus.trivialNilmanifold 0) le_rfl R cover hcover a poly hpoly U
      (fun j α _ => hm j α) p Rrank (by linarith) hR hcap hcoverp ha q hq hqp
      start K hK hKp N hN origin lengths hlengths hNL hdim hlarge hRrank
      (fun j _ => hrank j) hcorr'
    exact hann (fun j => hall j (Nat.succ_pos _))

theorem exists_normalizedTwist_uniform_box_fourier_comparison (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X : Type} [Fintype X] [DecidableEq X]
      {J : Fin m → Type} [∀ j, Fintype (J j)]
      {F : Type*} [Fintype F] (cover : ℕ), 0 < cover →
      ∀ (frequency : F → (Σ j, J j) → ℤ) (coeff : F → ℂ)
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
      (∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j)) →
      ∀ (U : ∀ j, Submodule ℝ (J j → ℝ)),
      (∀ j α, coefficients (poly j) α ∈ U j) →
      ∀ (p Rrank : ℝ), 2 ≤ p →
      (cover : ℝ) ≤ Real.exp p → (∀ b i, |(frequency b i : ℝ)| ≤ Real.exp p) →
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∀ (start : X → ℤ) (K : ℝ), 1 ≤ K → K ≤ Real.exp p →
      ∀ (N : X → ℝ), (∀ i, 0 < N i) →
      ∀ (origin : X → ℤ) (lengths : X → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, N i ≤ K * (q : ℝ) * (lengths i : ℝ)) →
      (Fintype.card X : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1) N Rrank (U j) (poly j)) →
      ‖(𝔼 x ∈ translatedIntegerBox origin lengths,
        ∑ b, coeff b * (Real.fourierChar (MvPolynomial.eval
          (fun i => (start i : ℝ) + (q : ℝ) * (x i : ℝ))
          (normalizedTwistFrequencyPolynomial cover (frequency b) poly)) : ℂ)) -
        ∑ b, coeff b * (if ∀ j, U j ≤ LinearMap.ker
          (integerRowLinear (fun i => frequency b ⟨j, i⟩)) then 1 else 0)‖ ≤
        (∑ b, ‖coeff b‖) * Real.exp (-p) := by
  obtain ⟨C, hC, hfreq⟩ := exists_normalizedTwist_uniform_box_frequency_comparison m
  refine ⟨C, hC, ?_⟩
  intro X _ _ J _ F _ cover hcover frequency coeff poly hpoly U hm p Rrank hp hcoverp ha
    q hq hqp start K hK hKp N hN origin lengths hlengths hNL hdim hlarge hRrank hrank
  simp_rw [Finset.expect_sum_comm, ← Finset.mul_expect]
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b _
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (hfreq cover hcover (frequency b) poly hpoly U hm p Rrank hp hcoverp (ha b)
      q hq hqp start K hK hKp N hN origin lengths hlengths hNL hdim hlarge hRrank hrank)
    (norm_nonneg _)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial Module RationalFilteredNilmanifold PolynomialTranslationLie
open scoped TensorProduct NNReal BigOperators

noncomputable def majorPhaseSample {m : ℕ} {X : Type}
    (J : Fin m → Type) [∀ j, Fintype (J j)] (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (F : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
    (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
    (r : (X → ℤ) → ℂ) (u : X → ℤ) : ℂ :=
  ((Ψ.value (fun i => MvPolynomial.eval (fun x => (u x : ℝ))
      (lowTaggedPolynomial J d poly i) - c i - (β u i : ℝ)) : ℂ) *
    (Real.fourierChar (MvPolynomial.eval (fun j => ((Sum.elim u (β u) j : ℤ) : ℝ)) F) : ℂ)) * r u

theorem exists_majorPhase_low_localized_correlating_frequency (m d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L : Type} [Fintype X] [DecidableEq X]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (D : RationalFilteredNilmanifold L t e) (_htd : t ≤ d)
      (R : D.Niltest (fun _ : X => 1)) (_hd : 0 < d)
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
      (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
      (F : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
      (_hF : F ∈ weightedSupportLE
        (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) d)
      (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
      (_hβ : ∀ u ∈ integerBox N, ∀ i,
        |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J d poly i) -
          c i - (β u i : ℝ)| ≤ 1 / 2)
      (p Rrank : ℝ), 0 ≤ p → R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p →
      (W.modulus : ℝ) ≤ Real.exp p → (W.cover : ℝ) ≤ Real.exp p →
      (Lip : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, d < j.val + 1 → HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        W.eval N poly u * majorPhaseSample J d poly Ψ c F β R.eval u‖ →
      ∃ (start length : X → ℕ) (a : (Σ j, J j) → ℤ),
        (∀ i, 0 < length i) ∧
        (∀ i, (N i : ℝ) * Real.exp (-((p + C) ^ C)) ≤ length i) ∧
        (∀ i, (N i : ℝ) ≤ Real.exp ((p + C) ^ C) * W.modulus * length i) ∧
        (∀ v ∈ integerBox length,
          (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i) ∈ integerBox N) ∧
        (∀ j, |(a j : ℝ)| ≤ Real.exp ((p + C) ^ C)) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 v ∈ integerBox length,
          (Real.fourierChar (MvPolynomial.eval
            (fun i => (start i : ℝ) + (W.modulus : ℝ) * v i)
            (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
          majorPhaseSample J d poly Ψ c F β R.eval
            (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i)‖ ∧
        (∀ j, d < j.val + 1 → ∀ i, a ⟨j, i⟩ = 0) ∧
        (normalizedTwistFrequencyPolynomial W.cover a poly).totalDegree ≤ d := by
  obtain ⟨aC, _, hpartner⟩ := exists_majorTranslation_partner_niltest d
  obtain ⟨bC, _, hextract⟩ :=
    NormalizedPolynomialTwist.exists_low_localized_correlating_frequency m
  obtain ⟨C, hC, hbudget⟩ := exists_majorPhaseLowFourierExtraction_budget aC bC
  refine ⟨C, hC, ?_⟩
  intro X L _ _ _ _ t e _ _ _ _ J _ periodCap coverCap Lip W D htd R hd
    N poly hpoly U hcoeff Ψ c F hF β hβ p Rrank hp hR hcap hdim hmod hcover hLip hΨ
    hN hRrank hrank hcorr
  let w := lowTaggedWeight J d
  have hw : ∀ i, 0 < w i := lowTaggedWeight_pos J d
  have hwd : ∀ i, w i ≤ d := lowTaggedWeight_le J d
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  let := moduleTopology ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    realification_moduleTopology_t2 (weightedBasis w d hw)
  let A := fun i => lowTaggedPolynomial J d poly i - MvPolynomial.C (c i)
  have hA : ∀ i, (A i).totalDegree ≤ w i := fun i =>
    (MvPolynomial.totalDegree_sub_C_le _ _).trans (lowTaggedPolynomial_degree J d poly hpoly i)
  have hdimMajor : ((Fintype.card X + Fintype.card (LowTaggedIndex J d) : ℕ) : ℝ) ≤ p := by
    apply le_trans _ hdim
    exact_mod_cast Nat.add_le_add_left (lowTaggedIndex_card_le J d) _
  let M := majorTranslationPartnerModel w d hw hwd D htd
  let : FiniteDimensional ℚ (PairAlgebra (weightedSubalgebra w d) L) :=
    M.basis.finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L) :=
    realification_moduleTopology_t2 M.basis
  obtain ⟨S, hSnorm, hS, hSeval⟩ :=
    hpartner w hw hwd D htd R hd Ψ F hF A hA p hp hdimMajor hΨ hR hcap
  have hsample (u : X → ℤ) (hu : u ∈ integerBox N) :
      S.eval u = majorPhaseSample J d poly Ψ c F β R.eval u := by
    have hclose : ∀ i, |MvPolynomial.eval (fun j => (u j : ℝ)) (A i) - (β u i : ℝ)| ≤ 1/2 := by
      simpa only [A, map_sub, eval_C] using hβ u hu
    simpa only [majorPhaseSample, A, map_sub, eval_C] using hSeval u (β u) hclose
  let q : ℝ := (p + aC) ^ aC + p + 1
  have hpow : 0 ≤ (p + aC) ^ aC := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hSq : S.ComplexityLE q := hS.mono (by dsimp [q]; linarith)
  have hcapS : (S.normBound : ℝ) ≤ 1 := by rw [hSnorm]; rfl
  have hX : (Fintype.card X : ℝ) ≤ p := by
    apply le_trans _ hdim
    exact_mod_cast Nat.le_add_right (Fintype.card X) (Fintype.card (Σ j, J j))
  have hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p := by
    apply le_trans _ hdim
    exact_mod_cast Nat.le_add_left (Fintype.card (Σ j, J j)) (Fintype.card X)
  obtain ⟨_, hfinal, hside⟩ := hbudget p hp
  have hcorrS : Real.exp (-q) ≤ ‖𝔼 u ∈ integerBox N, W.eval N poly u * S.eval u‖ := by
    have heq : (𝔼 u ∈ integerBox N, W.eval N poly u * S.eval u) =
        𝔼 u ∈ integerBox N, W.eval N poly u * majorPhaseSample J d poly Ψ c F β R.eval u := by
      apply Finset.expect_congr rfl
      intro u hu
      rw [hsample u hu]
    rw [heq]
    exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hcorr
  obtain ⟨start, length, a, hpos, hlength, hcomparison, hinside, ha, hselected, hhigh, hdegree⟩ :=
    hextract J W d M le_rfl S N poly hpoly U hcoeff q Rrank hq hSq hcapS
      (hX.trans hpq) (hJ.trans hpq)
      (hmod.trans (Real.exp_le_exp.mpr hpq)) (hcover.trans (Real.exp_le_exp.mpr hpq))
      (hLip.trans (Real.exp_le_exp.mpr hpq))
      (fun i => (Real.exp_le_exp.mpr hfinal).trans (hN i))
      ((Real.exp_le_exp.mpr hfinal).trans hRrank) hrank hcorrS
  refine ⟨start, length, a, hpos, ?_, ?_, hinside, ?_, ?_, hhigh, hdegree⟩
  · intro i
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hside))
      (Nat.cast_nonneg (N i))).trans (hlength i)
  · intro i
    exact (hcomparison i).trans (by
      gcongr)
  · exact fun j => (ha j).trans (Real.exp_le_exp.mpr hfinal)
  · have heq : (𝔼 v ∈ integerBox length,
        (Real.fourierChar (MvPolynomial.eval
          (fun i => (start i : ℝ) + (W.modulus : ℝ) * v i)
          (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
        S.eval (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i)) =
        𝔼 v ∈ integerBox length,
        (Real.fourierChar (MvPolynomial.eval
          (fun i => (start i : ℝ) + (W.modulus : ℝ) * v i)
          (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
        majorPhaseSample J d poly Ψ c F β R.eval
          (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i) := by
      apply Finset.expect_congr rfl
      intro v hv
      rw [hsample _ (hinside v hv)]
    rw [heq] at hselected
    exact (Real.exp_le_exp.mpr (neg_le_neg hfinal)).trans hselected

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMajorCorrelationFamily
namespace OAI

section

namespace Erdos3.VectorPolynomial

open RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

theorem uniform_majorPhase_correlation_eq
    {m d : ℕ} {X L : Type} [Fintype X] [DecidableEq X]
    [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (D : RationalFilteredNilmanifold L t e) (T : D.Niltest (fun _ : X => 1))
    (N : X → ℕ) (hN : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (F : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
    (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
    (g : integerBox N → ℂ) (heval : ∀ u, g u = T.eval u.val) :
    (FiniteProbabilityWeights.uniformFinset (integerBox N) hN).correlation
      (fun u => majorPhaseSample J d poly Ψ c F β (fun _ => 1) u.val)
      (fun u => star (W.eval N poly u.val) * g u) =
    𝔼 u ∈ integerBox N,
      W.eval N poly u * majorPhaseSample J d poly Ψ c F β T.conjugate.eval u := by
  rw [← FiniteProbabilityWeights.uniformFinset_complexMean (integerBox N) hN]
  unfold FiniteProbabilityWeights.correlation FiniteProbabilityWeights.complexMean
  apply Finset.sum_congr rfl
  intro u _
  dsimp only
  rw [heval u]
  simp only [majorPhaseSample, Niltest.eval_conjugate, star_mul, star_star, mul_one]
  ring

attribute [local instance] NativeSampleModelFamily.lie NativeSampleModelFamily.algebra NativeSampleModelFamily.topology NativeSampleModelFamily.topologicalAdd NativeSampleModelFamily.continuousSMul NativeSampleModelFamily.hausdorff

theorem exists_native_major_correlation_family
    {m d t : ℕ} {X η : Type} [Fintype X] [DecidableEq X] [Fintype η]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (W : η → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (N : X → ℕ) (hN : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (F : η → MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
    (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
    (g : η → integerBox N → ℂ) (p : ℝ) (hp : 2 ≤ p)
    (hη : (Fintype.card η : ℝ) ≤ p)
    (native : ∀ j, NativeSampleModel (fun _ : X => 1) t p
      (fun u : integerBox N => u.val) (g j))
    (hcorr : ∀ j, Real.exp (-p) ≤
      ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hN).correlation
        (fun u => majorPhaseSample J d poly Ψ c (F j) β (fun _ => 1) u.val)
        (fun u => star ((W j).eval N poly u.val) * g j u)‖) :
    ∃ common : NativeSampleModelFamily (fun _ : X => 1) t (productNiltestBudget p)
      (fun u : integerBox N => u.val) g,
      ∀ j, Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        (W j).eval N poly u *
          majorPhaseSample J d poly Ψ c (F j) β (common.test j).conjugate.eval u‖ := by
  let common := NativeSampleModelFamily.ofModels native hp hη
  refine ⟨common, ?_⟩
  intro j
  rw [← uniform_majorPhase_correlation_eq J (W j) common.model (common.test j)
    N hN poly Ψ c (F j) β (g j) (common.eval j)]
  exact hcorr j

theorem exists_native_major_correlation_family_of_detections
    {m d t : ℕ} {X η : Type} [Fintype X] [DecidableEq X] [Fintype η]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (N : X → ℕ) (hN : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (F : η → MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
    (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
    (p : ℝ) (hp : 2 ≤ p) (hη : (Fintype.card η : ℝ) ≤ p)
    (hdetected : ∀ j,
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
        (g : integerBox N → ℂ),
        Nonempty (NativeSampleModel (fun _ : X => 1) t p
          (fun u : integerBox N => u.val) g) ∧
        Real.exp (-p) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hN).correlation
            (fun u => majorPhaseSample J d poly Ψ c (F j) β (fun _ => 1) u.val)
            (fun u => star (W.eval N poly u.val) * g u)‖) :
    ∃ (W : η → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (g : η → integerBox N → ℂ)
      (common : NativeSampleModelFamily (fun _ : X => 1) t (productNiltestBudget p)
        (fun u : integerBox N => u.val) g),
      ∀ j, Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        (W j).eval N poly u *
          majorPhaseSample J d poly Ψ c (F j) β (common.test j).conjugate.eval u‖ := by
  classical
  choose W g hnative hcorr using hdetected
  let native := fun j => Classical.choice (hnative j)
  obtain ⟨common, hcommon⟩ := exists_native_major_correlation_family J W N hN
    poly Ψ c F β g p hp hη native hcorr
  exact ⟨W, g, common, hcommon⟩

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedTwistUniformBoxHaar
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_normalizedTwist_uniform_progression_haar_comparison (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X : Type} [Fintype X] [DecidableEq X]
      {J : Fin m → Type} [∀ j, Fintype (J j)]
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
      [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
      (∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j)) →
      (∀ j α, coefficients (poly j) α ∈ U j) →
      ∀ {periodCap coverCap : ℝ} {L : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
      (residue : X → ZMod W.modulus) (center : X → ℝ)
      {η Q p Rrank : ℝ}, 0 < η → 0 ≤ Q →
      (Fintype.card (Σ j, J j) : ℝ) ≤ Q →
      (L : ℝ) ≤ Real.exp Q → η⁻¹ ≤ Real.exp Q →
      2 ≤ p → (2 * Q + 2) ^ 4 ≤ p →
      (W.cover : ℝ) ≤ Real.exp p →
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∀ (start : X → ℤ) (K : ℝ), 1 ≤ K → K ≤ Real.exp p →
      ∀ (N : X → ℝ), (∀ i, 0 < N i) →
      ∀ (origin : X → ℤ) (lengths : X → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, N i ≤ K * (q : ℝ) * (lengths i : ℝ)) →
      (Fintype.card X : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1) N Rrank (U j) (poly j)) →
      ‖(𝔼 x ∈ translatedIntegerBox origin lengths,
        W.frozenTorus residue center (physicalGridFactorInput W.cover poly
          (fun i => (start i : ℝ) + (q : ℝ) * (x i : ℝ)))) -
        W.frozenSingleSiteHaarReference U ν residue center‖ ≤
        2 * η + Real.exp (2 * Q * (2 * Q + 2) ^ 4 - p) := by
  obtain ⟨C, hC, hfourier⟩ := exists_normalizedTwist_uniform_box_fourier_comparison m
  refine ⟨C, hC, ?_⟩
  intro X _ _ J _ U ν _ _ poly hp hm periodCap coverCap L W residue center
    η Q p Rrank hη hQ hdim hL hηQ hp2 hfreq hcover q hq hqp start K hK hKp N hN
    origin lengths hlengths hNL hX hlarge hRrank hrank
  obtain ⟨F, inst, frequency, coeff, _, hfreqB, hmass, herr⟩ :=
    exists_ambient_torus_fourier_approximation (W.frozenTorus residue center) L 1
      (W.frozenTorus_lipschitz residue center) (W.norm_frozenTorus_le residue center)
      hη hQ hdim hL hηQ
  let := inst
  let : ∀ i, NeZero (lengths i) := fun i => ⟨(hlengths i).ne'⟩
  let μ := Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))
  let chart : EuclideanJetLayers U (fun _ => Unit) → (Σ j, J j) → UnitAddCircle :=
    fun y a => coveredJetAmbientTorus U 1 y ⟨a.1, (), a.2⟩
  let f := W.frozenTorus residue center
  let g : ((Σ j, J j) → UnitAddCircle) → ℂ :=
    fun y => ∑ b, coeff b * ambientIntegerCharacter (frequency b) y
  let point (x : X → ℤ) := physicalGridFactorInput W.cover poly
    (fun i => (start i : ℝ) + (q : ℝ) * (x i : ℝ))
  have hfg (y) : ‖f y - g y‖ ≤ η := herr y
  have hmean : ‖(𝔼 x ∈ translatedIntegerBox origin lengths, f (point x)) -
      (𝔼 x ∈ translatedIntegerBox origin lengths, g (point x))‖ ≤ η := by
    rw [← Finset.expect_sub_distrib]
    exact (RCLike.norm_expect_le (K := ℂ)).trans
      (Finset.expect_le (translatedIntegerBox_nonempty lengths origin) (fun x _ => hfg _))
  have hf : Integrable (fun y => f (chart y)) μ :=
    W.frozenSingleSiteHaarReference_integrable U ν residue center
  have hgi (b : F) : Integrable (fun y => coeff b * ambientIntegerCharacter (frequency b) (chart y)) μ :=
    (singleSiteHaar_ambientIntegerCharacter_integrable U ν (frequency b)).const_mul _
  have hg : Integrable (fun y => g (chart y)) μ := integrable_finsetSum _ (fun b _ => hgi b)
  have hint : ‖(∫ y, g (chart y) ∂μ) - ∫ y, f (chart y) ∂μ‖ ≤ η :=
    probability_integral_approximation μ _ _ hg hf (fun y => by
      simpa only [norm_sub_rev] using hfg (chart y))
  have hge : (∫ y, g (chart y) ∂μ) =
      ∑ b, coeff b * (if ∀ j, U j ≤ LinearMap.ker
        (integerRowLinear (fun i => frequency b ⟨j, i⟩)) then 1 else 0) := by
    rw [show (fun y => g (chart y)) =
      (fun y => ∑ b, coeff b * ambientIntegerCharacter (frequency b) (chart y)) from rfl,
       integral_finsetSum _ (fun b _ => hgi b)]
    apply Finset.sum_congr rfl
    intro b _
    rw [integral_const_mul]
    exact congrArg (coeff b * ·) (singleSiteHaar_ambientIntegerCharacter_integral U ν (frequency b))
  have hcomp := hfourier W.cover W.cover_pos frequency coeff poly hp U hm p Rrank hp2 hcover
    (fun b i => (hfreqB b i).trans (Real.exp_le_exp.mpr hfreq)) q hq hqp start K hK hKp
    N hN origin lengths hlengths hNL hX hlarge hRrank hrank
  have hgpoint (x) : g (point x) = ∑ b, coeff b *
      (Real.fourierChar (MvPolynomial.eval
        (fun i => (start i : ℝ) + (q : ℝ) * (x i : ℝ))
        (normalizedTwistFrequencyPolynomial W.cover (frequency b) poly)) : ℂ) := by
    simp only [g, point, ambientIntegerCharacter, physicalGrid_character_eq_polynomial_phase]
  rw [← hge] at hcomp
  simp_rw [← hgpoint] at hcomp
  have hmass' : (∑ b, ‖coeff b‖) * Real.exp (-p) ≤
      Real.exp (2 * Q * (2 * Q + 2) ^ 4 - p) := by
    calc
      _ ≤ Real.exp (2 * Q * (2 * Q + 2) ^ 4) * Real.exp (-p) :=
        mul_le_mul_of_nonneg_right (by simpa using hmass) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; rfl
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (𝔼 x ∈ translatedIntegerBox origin lengths, f (point x))
    (𝔼 x ∈ translatedIntegerBox origin lengths, g (point x)) (∫ y, f (chart y) ∂μ)
  have ht' := norm_sub_le_norm_sub_add_norm_sub
    (𝔼 x ∈ translatedIntegerBox origin lengths, g (point x))
    (∫ y, g (chart y) ∂μ) (∫ y, f (chart y) ∂μ)
  change ‖(𝔼 x ∈ translatedIntegerBox origin lengths, f (point x)) -
    ∫ y, f (chart y) ∂μ‖ ≤ _
  linarith [hcomp.trans hmass']

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedTwistUniformAmbientHaar
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_normalizedTwist_uniform_ambient_haar_comparison (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X : Type} [Fintype X] [DecidableEq X]
      {J : Fin m → Type} [∀ j, Fintype (J j)]
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
      [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
      (∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j)) →
      (∀ j α, coefficients (poly j) α ∈ U j) →
      ∀ {periodCap coverCap : ℝ} {L : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
      {η Q p Rrank : ℝ}, 0 < η → 0 ≤ Q →
      (Fintype.card (Σ j, J j) : ℝ) ≤ Q →
      (L : ℝ) ≤ Real.exp Q → η⁻¹ ≤ Real.exp Q →
      3 * Q + 16 ≤ p → (2 * Q + 2) ^ 4 ≤ p →
      (W.cover : ℝ) ≤ Real.exp p → (W.modulus : ℝ) ≤ Real.exp Q →
      ∀ (N : X → ℕ), (Fintype.card X : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C + 3 * Q + 16) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      ‖(𝔼 x ∈ integerBox N, W.eval N poly x) -
        (𝔼 x ∈ integerBox N, W.frozenSingleSiteHaarReference U ν
          (fun i => (x i : ZMod W.modulus)) (fun i => (x i : ℝ) / N i))‖ ≤
        2 * η + Real.exp (2 * Q * (2 * Q + 2) ^ 4 - p) +
          (L : ℝ) * Real.exp (-2 * Q) / 2 := by
  obtain ⟨C, hC, hlocal⟩ := exists_normalizedTwist_uniform_progression_haar_comparison m
  refine ⟨C, hC, ?_⟩
  intro X _ _ J _ U ν _ _ poly hp hm periodCap coverCap L W
    η Q p Rrank hη hQ hdim hL hηQ hpQ hfreq hcover hmod N hX hlarge hRrank hrank
  have hp2 : 2 ≤ p := by linarith
  have hpow : 0 ≤ (p + C) ^ C := pow_nonneg (by positivity) _
  have hNloc (i) : Real.exp (3 * Q + 16) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans (hlarge i)
  have hNpos (i) : 0 < (N i : ℝ) := (Real.exp_pos _).trans_le (hNloc i)
  let H (x : X → ℤ) := W.frozenSingleSiteHaarReference U ν
    (fun i => (x i : ZMod W.modulus)) (fun i => (x i : ℝ) / N i)
  obtain ⟨start, length, hpos, hlen, hscale, _, _, hdiam, _, hselect⟩ :=
    exists_correlated_integer_residue_box N W.modulus Q hQ W.modulus_pos hmod hNloc
      (fun x => W.eval N poly x - H x)
  let u (v : X → ℤ) (i : X) : ℤ := (start i : ℤ) + (W.modulus : ℤ) * v i
  let center (i : X) : ℝ := (start i : ℝ) / N i
  let residue (i : X) : ZMod W.modulus := (start i : ZMod W.modulus)
  let F (v : X → ℤ) := W.frozenSpatialEval center poly (u v)
  let H₀ := W.frozenSingleSiteHaarReference U ν residue center
  have hresidue (v) : (fun i => (u v i : ZMod W.modulus)) = residue := by
    funext i
    simp [u, residue]
  have hdist (v) (hv : v ∈ integerBox length) :
      dist (fun i => (u v i : ℝ) / N i) center ≤ Real.exp (-2 * Q) / 4 := by
    apply (dist_pi_le_iff (by positivity)).mpr
    intro i
    simpa only [u, center, Real.dist_eq, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      neg_mul] using hdiam v hv i
  have hFerr (v) (hv : v ∈ integerBox length) :
      ‖W.eval N poly (u v) - F v‖ ≤ (L : ℝ) * (Real.exp (-2 * Q) / 4) :=
    (W.eval_sub_frozenSpatialEval N center poly (u v)).trans
      (mul_le_mul_of_nonneg_left (hdist v hv) L.coe_nonneg)
  have hHerr (v) (hv : v ∈ integerBox length) :
      ‖H (u v) - H₀‖ ≤ (L : ℝ) * (Real.exp (-2 * Q) / 4) := by
    dsimp only [H, H₀]
    rw [hresidue]
    exact ((W.frozenSingleSiteHaarReference_lipschitz U ν residue).norm_sub_le _ _).trans
      (mul_le_mul_of_nonneg_left (hdist v hv) L.coe_nonneg)
  let : ∀ i, NeZero (length i) := fun i => ⟨(hpos i).ne'⟩
  have hmeanerr : ‖(𝔼 v ∈ integerBox length, (W.eval N poly (u v) - H (u v))) -
      (𝔼 v ∈ integerBox length, (F v - H₀))‖ ≤ (L : ℝ) * Real.exp (-2 * Q) / 2 := by
    rw [← Finset.expect_sub_distrib]
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le (integerBox_nonempty length)
    intro v hv
    have he : W.eval N poly (u v) - H (u v) - (F v - H₀) =
        (W.eval N poly (u v) - F v) - (H (u v) - H₀) := by ring
    rw [he]
    have hh := (norm_sub_le (W.eval N poly (u v) - F v) (H (u v) - H₀)).trans
      (add_le_add (hFerr v hv) (hHerr v hv))
    convert hh using 1; ring
  have hlong (i) : Real.exp ((p + C) ^ C) ≤ (length i : ℝ) := by
    calc
      _ = Real.exp ((p + C) ^ C + 3 * Q + 16) * Real.exp (-(3 * Q + 16)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ (N i : ℝ) * Real.exp (-(3 * Q + 16)) :=
        mul_le_mul_of_nonneg_right (hlarge i) (Real.exp_nonneg _)
      _ ≤ _ := hlen i
  have hzero : translatedIntegerBox (0 : X → ℤ) length = integerBox length := by
    ext v
    simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
  have hcomp := hlocal U ν poly hp hm W residue center hη hQ hdim hL hηQ hp2 hfreq hcover
    W.modulus W.modulus_pos (hmod.trans (Real.exp_le_exp.mpr (by linarith)))
    (fun i => (start i : ℤ)) (Real.exp (3 * Q + 16))
    (Real.one_le_exp (by positivity)) (Real.exp_le_exp.mpr hpQ)
    (fun i => (N i : ℝ)) hNpos 0 length hpos hscale hX hlong hRrank hrank
  rw [hzero] at hcomp
  have hF (v) : F v = W.frozenTorus residue center (physicalGridFactorInput W.cover poly
      (fun i => (start i : ℝ) + (W.modulus : ℝ) * (v i : ℝ))) := by
    dsimp only [F, NormalizedPolynomialTwist.frozenSpatialEval]
    rw [hresidue]
    simp only [u, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  simp only [Int.cast_natCast] at hcomp
  simp_rw [← hF] at hcomp
  have hcomp' : ‖𝔼 v ∈ integerBox length, (F v - H₀)‖ ≤
      2 * η + Real.exp (2 * Q * (2 * Q + 2) ^ 4 - p) := by
    rw [Finset.expect_sub_distrib, Finset.expect_const (integerBox_nonempty length)]
    simpa only [Int.cast_natCast] using hcomp
  change ‖(𝔼 x ∈ integerBox N, W.eval N poly x) - 𝔼 x ∈ integerBox N, H x‖ ≤ _
  rw [← Finset.expect_sub_distrib]
  apply hselect.trans
  change ‖𝔼 v ∈ integerBox length, (W.eval N poly (u v) - H (u v))‖ ≤ _
  have ht := norm_le_norm_sub_add
    (𝔼 v ∈ integerBox length, (W.eval N poly (u v) - H (u v)))
    (𝔼 v ∈ integerBox length, (F v - H₀))
  linarith

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationMajorTwistedCorrelationStepDropPolynomial
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem majorTranslationDegreeReduced_twisted_integerEval
    {U : Type*} {m : ℕ} (w : Fin m → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (M : ℕ) (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (x : U → ℤ) (β : Fin m → ℤ)
    (hβ : ∀ i, |eval (fun j => (x j : ℝ)) (A i) - (β i : ℝ)| ≤ 1 / 2) :
    twistedBufferedTranslationPhase M Ψ
        (specializeMajorParameters (RingHom.id ℝ) (fractionalCoefficientPolynomial F) 0) T
        (bchRealTranslationHom w d hwd
          ((weightedFiltration w d hwd).realification.polynomialOrbitEval
            (fun _ : U => 1) x
            (majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial F)
              (fractionalCoefficientPolynomial_mem_weightedSupportLE F
                (Sum.elim (fun _ : U => 1) w) d hF) A hA))) =
      T (fun i => eval (fun j => (x j : ℝ)) (A i) - (β i : ℝ))
          (fun i => (β i : ZMod M)) *
        (Ψ.value (fun i => eval (fun j => (x j : ℝ)) (A i) - (β i : ℝ)) : ℂ) *
        (Real.fourierChar (eval (fun j => ((Sum.elim x β j : ℤ) : ℝ)) F) : ℂ) := by
  rw [majorTranslationPolynomialOrbit_integerEval,
    twistedBufferedTranslationPhase_majorSymbol M Ψ _ _ T A _ β hβ]
  have hcast : Sum.elim (fun j => (x j : ℝ)) (fun i => (β i : ℝ)) =
      (fun j => ((Sum.elim x β j : ℤ) : ℝ)) := by
    funext j
    cases j <;> rfl
  rw [hcast, fractionalCoefficientPolynomial_fourierChar]

theorem exists_reduced_majorPolynomial_degree_twisted_correlation_step_drop
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (M : ℕ) (hM : 0 < M)
      (D : RationalFilteredNilmanifold L t e) (htd : t < d)
      (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
      (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
      (K : ℝ≥0) (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (_hT : ∀ x r, ‖T x r‖ ≤ 1) (_hLip : ∀ r, LipschitzWith K (fun x => T x r))
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p →
      Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ
        (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d) K : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      ∀ (β : (U → ℤ) → Fin m → ℤ),
      (∀ x ∈ translatedIntegerBox origin lengths, ∀ i,
        |eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)| ≤ 1 / 2) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        T (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ))
            (fun i => (β x i : ZMod M)) *
          (Ψ.value (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)) : ℂ) *
          (Real.fourierChar (eval (fun j => ((Sum.elim x (β x) j : ℤ) : ℝ)) F) : ℂ) *
          R.eval x‖ →
      let N := pi (pairModels
        (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
      ∃ (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
        (b : Basis (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)))
          ℚ (PairAlgebra (weightedSubalgebra w d) L))
        (ω : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → ℕ)
        (hLayers : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        η (centralRationalElement w d hd 1) = 1 ∧
        (∀ i, rationalLogHeight
          (η ((weightedTranslationResidueNilmanifold w d hw hwd M hM).basis i)) ≤
            (p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        N.filtration.ControlledSymbolFactorization b ω hLayers
          (pairFrequency η (0 : L →ₗ[ℚ] ℚ)) (fun i => (lengths i : ℝ))
          (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
            (D.raiseStep htd.le)
            (majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial F)
              (fractionalCoefficientPolynomial_mem_weightedSupportLE F
                (Sum.elim (fun _ : U => 1) w) d hF) A hA)
            (D.raiseStepRealOrbit htd.le R.orbit) b ω hLayers) ((p + C) ^ C) := by
  obtain ⟨C, hC, hstep⟩ := exists_translation_major_twisted_correlation_step_drop d hd
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ M hM D htd Ψ F hF A hA
    K T hT hLip R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge β hβ hcorr
  let B : ℝ≥0 := ((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d
  have hmass : realPolynomialMass (fractionalCoefficientPolynomial F) ≤ B := by
    change realPolynomialMass (fractionalCoefficientPolynomial F) ≤
      (((Fintype.card U + m + 1 : ℕ) : ℝ) ^ d)
    have hv : ∀ i : U ⊕ Fin m, 0 < Sum.elim (fun _ : U => 1) w i := by
      intro i
      cases i with
      | inl i => exact Nat.zero_lt_one
      | inr i => exact hw i
    have hh := fractionalCoefficientPolynomial_mass_le_of_weightedSupportLE F
      (Sum.elim (fun _ : U => 1) w) hv d hF
    simpa only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hh
  apply hstep w hw hwd M hM D htd Ψ
    (specializeMajorParameters (RingHom.id ℝ) (fractionalCoefficientPolynomial F) 0) B K
    (majorZeroParameterSlice_degree w hw (fractionalCoefficientPolynomial_mem_weightedSupportLE F
                (Sum.elim (fun _ : U => 1) w) d hF))
    ((majorZeroParameterSlice_mass _).trans hmass) T hT hLip
    (majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial F)
      (fractionalCoefficientPolynomial_mem_weightedSupportLE F
                (Sum.elim (fun _ : U => 1) w) d hF) A hA)
    R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge
  convert hcorr using 1
  congr 1
  apply Finset.expect_congr rfl
  intro x hx
  rw [majorTranslationDegreeReduced_twisted_integerEval w d hw hwd M Ψ F hF A hA T x (β x) (hβ x hx)]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem exists_reduced_majorPolynomial_degree_twisted_correlation_potential_data
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (M : ℕ) (hM : 0 < M)
      (D : RationalFilteredNilmanifold L t e) (htd : t < d)
      (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
      (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
      (K : ℝ≥0) (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (_hT : ∀ x r, ‖T x r‖ ≤ 1) (_hLip : ∀ r, LipschitzWith K (fun x => T x r))
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p →
      Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ
        (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d) K : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      ∀ (β : (U → ℤ) → Fin m → ℤ),
      (∀ x ∈ translatedIntegerBox origin lengths, ∀ i,
        |eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)| ≤ 1 / 2) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        T (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ))
            (fun i => (β x i : ZMod M)) *
          (Ψ.value (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)) : ℂ) *
          (Real.fourierChar (eval (fun j => ((Sum.elim x (β x) j : ℤ) : ℝ)) F) : ℂ) *
          R.eval x‖ →
      let N := pi (pairModels
        (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
      let orbit := majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial F)
        (fractionalCoefficientPolynomial_mem_weightedSupportLE F
          (Sum.elim (fun _ : U => 1) w) d hF) A hA
      let partner := D.raiseStepRealOrbit htd.le R.orbit
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)))
          ℚ (PairAlgebra (weightedSubalgebra w d) L))
        (ω : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → ℕ)
        (hLayers : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ (p + C)^C) ∧
      ∃ (l : ℕ) (E P S : N.filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
        (W : LieSubalgebra ℚ N.filtration.AssociatedGraded)
        (v : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → N.filtration.AssociatedGraded)
        (Vfast : LieSubalgebra ℚ (weightedSubalgebra w d)) (V : MvPolynomial (Fin m) ℚ) (q : ℕ),
        0 < l ∧ (l : ℝ) ≤ Real.exp ((p + C)^C) ∧
        E * P * S = pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
          (D.raiseStep htd.le) orbit partner b ω hLayers ∧
        N.filtration.SymbolSlowBound b ω hLayers (fun _ => 1)
          (fun i => (lengths i : ℝ)) (Real.exp ((p + C)^C)) E ∧
        N.filtration.SymbolRationalGrid b ω hLayers (fun _ => 1) l S ∧
        (∀ t : U → ℝ,
          eval₂ t ((weightedFiltration w d hwd).realSymbolRepresentative
            (weightedBasis w d hw) (weightedBasisGrade w d)
            (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
            (realificationLieHom (N.filtration.filteredPolynomialSymbolMap
              (weightedFiltration w d hwd) (liePiEval (R := ℚ) true)
              (pairFirstProjection_filtered
                (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
              (fun _ : U => 1)) P.coord)) ∈ realificationLieSubalgebra Vfast) ∧
        Vfast = W.map (weightedTranslationGradedProjection N.filtration w d hw hwd
          (liePiEval (R := ℚ) true) (pairFirstProjection_filtered
            (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))) ∧
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule (N.filtration.associatedGradedBasis b ω hLayers) ω W.toSubmodule ∧
        (∀ i j, rationalLogHeight ((N.filtration.associatedGradedBasis b ω hLayers).repr (v i) j) ≤ (p+C)^C) ∧
        P.coord ∈ realificationLieSubalgebra
          (N.filtration.symbolPointwiseSubalgebra b ω hLayers (fun _ : U => 1) W) ∧
        V.IsWeightedHomogeneous w d ∧
        (∀ x ∈ Vfast, ∀ z ∈ Vfast.toSubmodule.map
            (baseLinear.comp (weightedSubalgebra w d).subtype),
          eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) ∧
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + C)^C) ∧
        (fun α => V.coeff α) ∈ denominatorGrid q ∧
        realPolynomialMass (MvPolynomial.map (algebraMap ℚ ℝ) V) ≤ Real.exp ((p + C)^C) ∧
        ∀ α, ((V.coeff α).num.natAbs : ℝ) ≤ Real.exp ((p + C)^C) ∧
          ((V.coeff α).den : ℝ) ≤ Real.exp ((p + C)^C) := by
  obtain ⟨a, ha, hdetect⟩ := exists_reduced_majorPolynomial_degree_twisted_correlation_step_drop d hd
  obtain ⟨c, hc, hpotential⟩ := exists_translationMajorDetectedPotentialData d hd
  obtain ⟨C, hC, hbudget⟩ := exists_translationMajor_detected_potential_budget a c
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ M hM D htd Ψ F hF A hA
    K T hT hLip R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge β hβ hcorr
    N orbit partner
  let p₁ : ℝ := (p + a)^a
  have hp₁ : 0 ≤ p₁ := (translationMajor_initial_budget_bounds a ha p hp).1
  have hpp₁ : p ≤ p₁ := (translationMajor_initial_budget_bounds a ha p hp).2.1
  have hbudget₁ : p₁ ≤ (p + C)^C := (hbudget p hp).2
  have hbudget₂ : (p₁ + (p₁ + 2)^4 + 1 + c)^c ≤ (p + C)^C := (hbudget p hp).1
  have hlarge₁ (i : U) : Real.exp ((p + a)^a) ≤ (lengths i : ℝ) :=
    (Real.exp_le_exp.mpr hbudget₁).trans (hlarge i)
  obtain ⟨η, b, ω, hLayers, hη, _, hb, hfactor⟩ :=
    hdetect w hw hwd M hM D htd Ψ F hF A hA K T hT hLip R p hp hgeometry hbound hR hRcap
      origin lengths hlengths hU hlarge₁ β hβ hcorr
  have hdim : (Fintype.card (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L))) : ℝ) ≤ p₁ := by
    simpa only [Fintype.card_fin] using
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).geometry_pair_finrank_le_budget
        (D.raiseStep htd.le) hgeometry (D.raiseStep_geometry htd.le hR.1) ha
  have hbase : (Fintype.card (Fin m) : ℝ) ≤ p₁ :=
    (weightedTranslationResidueNilmanifold_base_card_le w d hw hwd M hM hgeometry).trans hpp₁
  obtain ⟨l, E, P, S, W, v, Vfast, V, q, hl, hlp, hprod, hE, hS, hfast, hVfast, hv, hW, hh, hP, hV,
      hderiv, hq, hqp, hgrid, hmass, hcoeff⟩ :=
    hpotential w hw hwd M hM (D.raiseStep htd.le) orbit partner b ω hLayers η hη
      (fun i => (lengths i : ℝ)) p₁ hp₁ hdim hbase hb hfactor
  have hexp₁ := Real.exp_le_exp.mpr hbudget₁
  have hexp₂ := Real.exp_le_exp.mpr hbudget₂
  refine ⟨b, ω, hLayers, fun i j => (hb i j).trans hbudget₁, ?_⟩
  refine ⟨l, E, P, S, W, v, Vfast, V, q, hl, hlp.trans hexp₁, hprod, ?_⟩
  refine ⟨?_, hS, ?_⟩
  · exact N.filtration.symbolSlowBound_mono b ω hLayers (fun _ : U => 1)
      (fun i => (lengths i : ℝ)) (fun i => by exact_mod_cast hlengths i) hexp₁ E hE
  refine ⟨?_, hVfast, hv, ?_⟩
  · convert hfast using 1
  refine ⟨hW, ?_, ?_, hV, hderiv, ?_⟩
  · exact fun i j => (hh i j).trans hbudget₁
  · convert hP using 1
  refine ⟨hq, hqp.trans hexp₂, hgrid, hmass.trans hexp₂, ?_⟩
  intro α
  exact ⟨(hcoeff α).1.trans hexp₂, (hcoeff α).2.trans hexp₂⟩

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationPolynomialSymbolLiftHom
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

def lieHomSubalgebra {A B : Type*} [LieRing A] [LieAlgebra ℚ A]
    [LieRing B] [LieAlgebra ℚ B] (f : A →ₗ⁅ℚ⁆ B) (K : LieSubalgebra ℚ B)
    (hf : ∀ x, f x ∈ K) : A →ₗ⁅ℚ⁆ K where
  toLinearMap := f.toLinearMap.codRestrict K.toSubmodule hf
  map_lie' {x y} := Subtype.ext (f.map_lie x y)

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (hb : BasisHomogeneousBrackets b ω) (w : σ → ℕ)

noncomputable def realHomogeneousAssociatedGradedMapQ :
    (ℝ ⊗[ℚ] F.AssociatedGraded) →ₗ⁅ℚ⁆ (ℝ ⊗[ℚ] L) where
  toLinearMap :=
    (realificationLieHom (F.homogeneousAssociatedGradedEquiv b ω hF hb).toLieHom).toLinearMap.restrictScalars ℚ
  map_lie' {x y} := (realificationLieHom
    (F.homogeneousAssociatedGradedEquiv b ω hF hb).toLieHom).map_lie x y

noncomputable def realHomogeneousSymbolRepresentativeLie :
    F.RealPolynomialSymbol w →ₗ⁅ℚ⁆ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
  (LieAlgebra.ExtendScalars.map (AlgHom.id ℚ (MvPolynomial σ ℚ))
    (F.realHomogeneousAssociatedGradedMapQ b ω hF hb)).comp
      (F.realGradedSymbolPolynomial b ω hF w)

@[simp] theorem realHomogeneousSymbolRepresentativeLie_apply (x : F.RealPolynomialSymbol w) :
    F.realHomogeneousSymbolRepresentativeLie b ω hF hb w x =
      F.realSymbolRepresentative b ω hF w x := by
  exact (F.realSymbolRepresentative_eq_homogeneous_map b ω hF hb w x).symm

noncomputable def realHomogeneousAdaptedSymbolRepresentativeLie :
    F.RealPolynomialSymbol w →ₗ⁅ℚ⁆ F.realification.adaptedLieSubalgebra w :=
  lieHomSubalgebra (F.realHomogeneousSymbolRepresentativeLie b ω hF hb w)
    (F.realification.adaptedLieSubalgebra w) (fun x => by
      rw [F.realHomogeneousSymbolRepresentativeLie_apply]
      exact (F.realification.mem_adaptedSubmodule w _).mpr
        (F.realSymbolRepresentative_adapted b ω hF w x))

noncomputable def realHomogeneousPolynomialSymbolLiftHom :
    F.RealPolynomialSymbolGroup w →* (F.realification.adaptedPolynomialFiltration w).Group :=
  NilpotentLieBCHGroup.map (F.realHomogeneousAdaptedSymbolRepresentativeLie b ω hF hb w)

@[simp] theorem realHomogeneousPolynomialSymbolLiftHom_apply (g : F.RealPolynomialSymbolGroup w) :
    F.realHomogeneousPolynomialSymbolLiftHom b ω hF hb w g =
      F.realPolynomialSymbolLift b ω hF w g := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  exact F.realHomogeneousSymbolRepresentativeLie_apply b ω hF hb w g.coord

end Erdos3.NilpotentLieFiltration

namespace Erdos3.PolynomialTranslationLie

open NilpotentLieFiltration

variable {U B : Type*} [Fintype B]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)

noncomputable def translationPolynomialSymbolLiftHom :
    (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1) →*
      (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) :=
  ((weightedFiltration w d hwd).realification.polynomialOrbitCoordinates
    (fun _ : U => 1)).symm.toMonoidHom.comp
      ((weightedFiltration w d hwd).realHomogeneousPolynomialSymbolLiftHom
        (weightedBasis w d hw) (weightedBasisGrade w d)
        (weightedFiltration_layer_eq_span w d hw hwd)
        (weightedBasis_homogeneous_brackets w d hw) (fun _ : U => 1))

@[simp] theorem translationPolynomialSymbolLiftHom_apply
    (g : (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1)) :
    translationPolynomialSymbolLiftHom w d hw hwd g =
      translationPolynomialSymbolLift w d hw hwd g := by
  unfold translationPolynomialSymbolLiftHom translationPolynomialSymbolLift
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    realHomogeneousPolynomialSymbolLiftHom_apply]

@[simp] theorem translationPolynomialSymbolLift_one :
    translationPolynomialSymbolLift w d hw hwd
      (1 : (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1)) = 1 := by
  simpa only [translationPolynomialSymbolLiftHom_apply] using
    (translationPolynomialSymbolLiftHom (U := U) w d hw hwd).map_one

@[simp] theorem translationPolynomialSymbolLift_mul
    (g h : (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1)) :
    translationPolynomialSymbolLift w d hw hwd (g * h) =
      translationPolynomialSymbolLift w d hw hwd g * translationPolynomialSymbolLift w d hw hwd h := by
  simpa only [translationPolynomialSymbolLiftHom_apply] using
    (translationPolynomialSymbolLiftHom w d hw hwd).map_mul g h

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.DetectedTranslationMajorSamplingContainment
namespace OAI

section

namespace Erdos3

theorem realSpanIntegerRowBound_le_exp_of_imageHeight (n m H : ℕ) {p a : ℝ}
    (hp : 0 ≤ p) (ha : 0 ≤ a) (hm : (m : ℝ) ≤ p)
    (himage : (imageDefiningHeight n m H : ℝ) ≤ Real.exp a) :
    (realSpanIntegerRowBound n m H : ℝ) ≤ Real.exp ((p * p + 1) * a) := by
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (imageDefiningHeight n m H)) himage (m * m)
  rw [← Real.exp_nat_mul] at hpow
  rw [realSpanIntegerRowBound, Nat.cast_mul, Nat.cast_pow]
  calc
    _ ≤ Real.exp ((m * m : ℕ) * a) * Real.exp a :=
      mul_le_mul hpow himage (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp ((((m : ℝ) * m) + 1) * a) := by
      rw [← Real.exp_add, Nat.cast_mul]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ ha
      have hsq := mul_le_mul hm hm (Nat.cast_nonneg _) hp
      linarith

theorem samplingProjectedImage_row_le_exp (n m : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) :
    (realSpanIntegerRowBound n m ⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤
      Real.exp ((p * p + 1) * (((p + 2) ^ 4 + 3) ^ 10)) := by
  have hpq : p ≤ (p + 2) ^ 4 + 1 :=
    (le_power_budget hp (by decide : 1 ≤ 4)).trans (le_add_of_nonneg_right (by norm_num))
  have hheight := imageDefiningHeight_le_exp n m ⌈Real.exp ((p + 2) ^ 4)⌉₊
    (by positivity : 0 ≤ (p + 2) ^ 4 + 1) (hn.trans hpq) (hm.trans hpq)
    (ceil_exp_le_exp_add_one (by positivity : 0 ≤ (p + 2) ^ 4))
  apply realSpanIntegerRowBound_le_exp_of_imageHeight n m _ hp (by positivity) hm
  convert hheight using 1
  congr 2
  ring

theorem exists_samplingProjectedImage_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (n m : ℕ) (p : ℝ),
      0 ≤ p → (n : ℝ) ≤ p → (m : ℝ) ≤ p →
      (realSpanIntegerRowBound n m ⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤
        Real.exp ((p + C) ^ C) ∧
      (m : ℝ) * realSpanIntegerRowBound n m ⌈Real.exp ((p + 2) ^ 4)⌉₊ *
          Real.exp ((p + 3) ^ 3) ≤ Real.exp ((p + C) ^ C) := by
  let T : Polynomial ℕ := Polynomial.X +
    (Polynomial.X * Polynomial.X + 1) * (((Polynomial.X + 2) ^ 4 + 3) ^ 10) +
      (Polynomial.X + 3) ^ 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro n m p hp hn hm
  let R : ℝ := (p * p + 1) * (((p + 2) ^ 4 + 3) ^ 10)
  have htotal : p + R + (p + 3) ^ 3 ≤ (p + C) ^ C := by
    simpa only [T, R, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_one, Polynomial.eval₂_ofNat]
      using hbudget p hp
  have hrow := samplingProjectedImage_row_le_exp n m hp hn hm
  change (realSpanIntegerRowBound n m ⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤ Real.exp R at hrow
  have hR : R ≤ (p + C) ^ C := by
    have hcubic : 0 ≤ (p + 3) ^ 3 := by positivity
    linarith
  refine ⟨hrow.trans (Real.exp_le_exp.mpr hR), ?_⟩
  have hmexp : (m : ℝ) ≤ Real.exp p := hm.trans (by linarith [Real.add_one_le_exp p])
  calc
    _ ≤ Real.exp p * Real.exp R * Real.exp ((p + 3) ^ 3) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hmexp hrow (Nat.cast_nonneg _) (Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = Real.exp (p + R + (p + 3) ^ 3) := by rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr htotal

end Erdos3

end

section

namespace Erdos3

theorem exists_samplingProjectedImage_complete_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (n m : ℕ) (p : ℝ),
      0 ≤ p → (n : ℝ) ≤ p → (m : ℝ) ≤ p →
      Real.exp ((p + 3) ^ 3) ≤ Real.exp ((p + C) ^ C) ∧
      (realSpanIntegerRowBound n m ⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤
        Real.exp ((p + C) ^ C) ∧
      (m : ℝ) * realSpanIntegerRowBound n m ⌈Real.exp ((p + 2) ^ 4)⌉₊ *
        Real.exp ((p + 3) ^ 3) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨a, ha, hbudget⟩ := exists_samplingProjectedImage_budget
  refine ⟨a + 3, by omega, ?_⟩
  intro n m p hp hn hm
  have hbase : (1 : ℝ) ≤ p + (a + 3 : ℕ) := by
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    push_cast
    linarith
  have haC : p + a ≤ p + (a + 3 : ℕ) := by push_cast; linarith
  have hthreeC : p + 3 ≤ p + (a + 3 : ℕ) := by
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    push_cast
    linarith
  have hlarge : (p + a) ^ a ≤ (p + (a + 3 : ℕ)) ^ (a + 3) :=
    (pow_le_pow_left₀ (by positivity) haC a).trans
      (pow_le_pow_right₀ hbase (by omega))
  have hsmall : (p + 3) ^ 3 ≤ (p + (a + 3 : ℕ)) ^ (a + 3) :=
    (pow_le_pow_left₀ (by positivity) hthreeC 3).trans
      (pow_le_pow_right₀ hbase (by omega))
  obtain ⟨hrow, herror⟩ := hbudget n m p hp hn hm
  exact ⟨Real.exp_le_exp.mpr hsmall,
    hrow.trans (Real.exp_le_exp.mpr hlarge),
    herror.trans (Real.exp_le_exp.mpr hlarge)⟩

end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold VectorPolynomial
open scoped Matrix

variable {B L : Type} {σ ι J : Type*} [Fintype B] [Fintype ι] [Fintype J]
    [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslation_samplingRank_le_base_span
    (hd : 1 ≤ d) {p : ℝ} (hp : 0 ≤ p)
    (hB : (Fintype.card B : ℝ) ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (W : LieSubalgebra ℚ
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (v : J → (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (hvheight : ∀ j i, rationalLogHeight
      (((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hN).repr (v j) i) ≤ p)
    (E P Q X : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hprod : E * P * Q = X)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : σ => 1) T (Real.exp p) E)
    (hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra
        b ω hN (fun _ : σ => 1) W))
    (m : ℕ) (hm : 0 < m) (hmp : (m : ℝ) ≤ Real.exp p)
    (hQ : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : σ => 1) m Q)
    (h : ℕ) (R : ℝ) (retained : Submodule ℝ (B → ℝ))
    (hrank : HasLayerSamplingRank h T R retained
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN X))
    (hgridR : Real.exp ((p + 3)^3) ≤ R)
    (hrowR : (realSpanIntegerRowBound (Fintype.card J) (Fintype.card B)
      ⌈Real.exp ((p + 2)^4)⌉₊ : ℝ) ≤ R)
    (hcost : (Fintype.card B : ℝ) *
      (realSpanIntegerRowBound (Fintype.card J) (Fintype.card B)
        ⌈Real.exp ((p + 2)^4)⌉₊ : ℝ) * Real.exp ((p + 3)^3) ≤ R) :
    retained ≤ Submodule.span ℝ (Set.range (fun j i =>
      (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ))) := by
  let H : ℕ := ⌈Real.exp ((p + 2)^4)⌉₊
  let A : Matrix B J ℚ := fun i j => detectedTranslationBaseMap w d hw hwd M hM D (v j) i
  have hA : ∀ i j, RationalHeightLE (A i j) H := by
    intro i j
    exact rationalHeightLE_ceil_exp
      (detectedTranslationBaseFunctional_value_logHeight w d hw hwd M hM D
        b ω hN hp hι hb (v j) (hvheight j) i)
  obtain ⟨q, hq, hqbound, hgrid⟩ :=
    detectedTranslationBasePolynomial_exists_coefficient_grid w d hw hwd M hM D
      b ω hN hp hι hb hB m hm hmp Q hQ
  apply samplingRank_le_real_column_span_of_decomposition A (one_le_ceil_exp _) hA
    h T R (Real.exp ((p + 3)^3)) retained
    (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN X)
    (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN E)
    (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN P)
    (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN Q)
    q hq hT hrank
    (detectedTranslationBasePolynomial_factorization w d hw hwd M hM D b ω hN hd E P Q X hprod)
    (detectedTranslationBasePolynomial_slow_coefficients w d hw hwd M hM D b ω hN hp hι hb T hT E hE)
    (detectedTranslationBasePolynomial_fast_coefficients_mem_span w d hw hwd M hM D b ω hN W v hv P hP)
    hgrid (hqbound.trans hgridR) hrowR hcost

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold VectorPolynomial
open scoped Matrix

universe u v z

theorem exists_detectedTranslation_samplingRank_le_base_span :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {B L : Type} {σ : Type u} {ι : Type v} {J : Type z}
    [Fintype B] [Fintype ι] [Fintype J] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (_hd : 1 ≤ d) {p : ℝ} (_hp : 0 ≤ p)
    (_hB : (Fintype.card B : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hJ : (Fintype.card J : ℝ) ≤ p)
    (_hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (W : LieSubalgebra ℚ
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (v : J → (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hvheight : ∀ j i, rationalLogHeight
      (((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hN).repr (v j) i) ≤ p)
    (E P Q X : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (_hprod : E * P * Q = X)
    (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
    (_hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : σ => 1) T (Real.exp p) E)
    (_hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra
        b ω hN (fun _ : σ => 1) W))
    (m : ℕ) (_hm : 0 < m) (_hmp : (m : ℝ) ≤ Real.exp p)
    (_hQ : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : σ => 1) m Q)
    (h : ℕ) (R : ℝ) (retained : Submodule ℝ (B → ℝ))
    (_hrank : HasLayerSamplingRank h T R retained
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN X))
    (_hR : Real.exp ((p + C)^C) ≤ R),
    retained ≤ Submodule.span ℝ (Set.range (fun j i =>
      (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ))) := by
  obtain ⟨C, hC, hbudget⟩ := exists_samplingProjectedImage_complete_budget
  refine ⟨C, hC, ?_⟩
  intro B L σ ι J _ _ _ _ _ w d hw hwd _ M hM e D b ω hN hd p hp hB hι hJ
    hb W v hv hvheight E P Q X hprod T hT hE hP m hm hmp hQ h R retained hrank hR
  obtain ⟨hgrid, hrow, hcost⟩ := hbudget (Fintype.card J) (Fintype.card B) p hp hJ hB
  exact detectedTranslation_samplingRank_le_base_span w d hw hwd M hM D b ω hN
    hd hp hB hι hb W v hv hvheight E P Q X hprod T hT hE hP m hm hmp hQ
    h R retained hrank (hgrid.trans hR) (hrow.trans hR) (hcost.trans hR)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped Matrix

theorem exists_majorTranslation_samplingRank_le_real_base_image :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {B L : Type} {σ ι J : Type}
    [Fintype B] [Fintype ι] [Fintype J] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (_hd : 1 ≤ d) {p : ℝ} (_hp : 0 ≤ p)
    (_hB : (Fintype.card B : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hJ : (Fintype.card J : ℝ) ≤ p)
    (_hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (W : LieSubalgebra ℚ
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (v : J → (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hvheight : ∀ j i, rationalLogHeight
      (((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hN).repr (v j) i) ≤ p)
    (F : MvPolynomial (σ ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) d)
    (A : B → MvPolynomial σ ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (partner : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (E P Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (_hprod : E * P * Q = pairOrbitSymbol
      (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
      (majorTranslationPolynomialOrbit w d hw hwd F hF A hA) partner b ω hN)
    (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
    (_hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : σ => 1) T (Real.exp p) E)
    (_hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra
        b ω hN (fun _ : σ => 1) W))
    (m : ℕ) (_hm : 0 < m) (_hmp : (m : ℝ) ≤ Real.exp p)
    (_hQ : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : σ => 1) m Q)
    (h : ℕ) (R : ℝ) (retained : Submodule ℝ (B → ℝ))
    (_hrank : HasLayerSamplingRank h T R retained
      (ofCoordinates (R := ℝ) (Pi.basisFun ℝ B)
        (fun i => weightedHomogeneousComponent (fun _ : σ => 1) (w i) (A i))))
    (_hR : Real.exp ((p + C)^C) ≤ R),
    retained ≤
      (((W.map (weightedTranslationGradedProjection
        (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
        w d hw hwd (liePiEval (R := ℚ) true)
        (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D))).toSubmodule).baseChange ℝ).map
          (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) := by
  obtain ⟨C, hC, hcontain⟩ := exists_detectedTranslation_samplingRank_le_base_span
  refine ⟨C, hC, ?_⟩
  intro B L σ ι J _ _ _ _ _ w d hw hwd _ M hM e D b ω hN hd p hp hB hι hJ
    hb W v hv hvheight F hF A hA partner E P Q hprod T hT hE hP m hm hmp hQ
    h R retained hrank hR
  rw [← detectedTranslationBase_span_eq_real_image w d hw hwd M hM D W v hv]
  apply hcontain w d hw hwd M hM D b ω hN hd hp hB hι hJ hb W v hv hvheight
    E P Q _ hprod T hT hE hP m hm hmp hQ h R retained _ hR
  rw [detectedTranslationBasePolynomial_majorOrbitSymbol w d hw hwd M hM D b ω hN F hF A hA partner]
  exact hrank

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslationMajorCorrelationIdentity
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

variable {σ L : Type} {U ι : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M) {e : ℕ}
    (D : RationalFilteredNilmanifold L d e)

noncomputable def detectedTranslationSymbolProjection :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1) →*
      (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1) :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.polynomialSymbol_lowerCentralSeries_eq_bot (fun _ : U => 1))
    (hM := (weightedFiltration w d hwd).polynomialSymbol_lowerCentralSeries_eq_bot (fun _ : U => 1))
    ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.filteredPolynomialSymbolMap (weightedFiltration w d hwd) (liePiEval (R := ℚ) true)
      (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D) (fun _ : U => 1))

@[simp] theorem detectedTranslationSymbolProjection_coord
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    (detectedTranslationSymbolProjection w d hw hwd M hM D P).coord =
      realificationLieHom
        ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.filteredPolynomialSymbolMap (weightedFiltration w d hwd) (liePiEval (R := ℚ) true)
          (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D) (fun _ : U => 1)) P.coord := rfl

noncomputable def detectedTranslationSymbolLift :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1) →*
      (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) :=
  (translationPolynomialSymbolLiftHom w d hw hwd).comp
    (detectedTranslationSymbolProjection w d hw hwd M hM D)

@[simp] theorem detectedTranslationSymbolLift_apply
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    detectedTranslationSymbolLift w d hw hwd M hM D P =
      translationPolynomialSymbolLift w d hw hwd
        (detectedTranslationSymbolProjection w d hw hwd M hM D P) := by
  simp only [detectedTranslationSymbolLift, MonoidHom.comp_apply,
    translationPolynomialSymbolLiftHom_apply]

@[simp] theorem detectedTranslationSymbolLift_log
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    (detectedTranslationSymbolLift w d hw hwd M hM D P).log =
      (weightedFiltration w d hwd).realSymbolRepresentative (weightedBasis w d hw) (weightedBasisGrade w d)
        (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
        (realificationLieHom
          ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.filteredPolynomialSymbolMap (weightedFiltration w d hwd) (liePiEval (R := ℚ) true)
            (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D) (fun _ : U => 1)) P.coord) := by
  rw [detectedTranslationSymbolLift_apply, translationPolynomialSymbolLift_log,
    detectedTranslationSymbolProjection_coord]

variable (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j, (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationSymbolProjection_pairOrbitSymbol
    (p : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1))
    (q : D.filtration.realification.PolynomialOrbit (fun _ : U => 1)) :
    detectedTranslationSymbolProjection w d hw hwd M hM D
      (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D p q b ω hN) = translationPolynomialSymbolHom w d hw hwd p := by
  apply NilpotentLieBCHGroup.ext
  rw [detectedTranslationSymbolProjection_coord, translationPolynomialSymbolHom_coord]
  exact pairOrbitSymbol_first_projection (weightedTranslationResidueNilmanifold w d hw hwd M hM) D (fun _ : U => 1) b ω hN
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) p q

theorem detectedTranslationSymbolLift_pairOrbitSymbol
    (p : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1))
    (q : D.filtration.realification.PolynomialOrbit (fun _ : U => 1)) :
    detectedTranslationSymbolLift w d hw hwd M hM D (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D p q b ω hN) =
      translationPolynomialSymbolLift w d hw hwd (translationPolynomialSymbolHom w d hw hwd p) := by
  rw [detectedTranslationSymbolLift_apply,
    detectedTranslationSymbolProjection_pairOrbitSymbol w d hw hwd M hM D b ω hN]

theorem detectedTranslationSymbolLift_value_mem_fast
    (W : LieSubalgebra ℚ (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra b ω hN (fun _ : U => 1) W)) (t : U → ℝ) :
    ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval (fun _ : U => 1) t
      (detectedTranslationSymbolLift w d hw hwd M hM D P)).coord ∈
      realificationLieSubalgebra
        (W.map (weightedTranslationGradedProjection (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration w d hw hwd
          (liePiEval (R := ℚ) true) (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D))) := by
  change eval₂ t (detectedTranslationSymbolLift w d hw hwd M hM D P).log ∈ _
  rw [detectedTranslationSymbolLift_log]
  unfold weightedTranslationGradedProjection
  have h := (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.projected_realSymbolRepresentative_mem_homogeneous_image (weightedFiltration w d hwd) b ω hN
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (weightedBasis_homogeneous_brackets w d hw)
    (liePiEval (R := ℚ) true) (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D) (fun _ : U => 1) W P.coord hP t
  convert h using 1

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (v : σ → ℕ)

theorem realGradedSymbolPolynomial_constant (x : F.RealPolynomialSymbol v) :
    coefficients (F.realGradedSymbolPolynomial b ω hF v x) 0 = 0 := by
  apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
  ext i
  change ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
    (coefficients (F.realGradedSymbolPolynomial b ω hF v x) 0) i = 0
  apply F.realGradedSymbolPolynomial_coordinate_of_ne
  rw [map_zero]
  exact (F.adaptedBasis_weight_pos b ω hF i).ne

end Erdos3.NilpotentLieFiltration

namespace Erdos3.PolynomialTranslationLie

open Module RationalFilteredNilmanifold VectorPolynomial

variable {B L : Type} {σ ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationBasePolynomial_constant
    (g : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup
      (fun _ : σ => 1)) :
    coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN g) 0 = 0 := by
  rw [detectedTranslationBasePolynomial_coefficients,
    NilpotentLieFiltration.realGradedSymbolPolynomial_constant, map_zero]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

noncomputable def detectedTranslationGroupEval (u : U → ℝ) :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1) →*
      PolynomialTranslationGroupOver ℝ B :=
  (bchRealTranslationHom w d hwd).comp
    (((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
      (fun _ : U => 1) u).comp (detectedTranslationSymbolLift w d hw hwd M hM D))

variable (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j, (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationGroupEval_major_factorization
    (F : MvPolynomial (U ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (partner : D.filtration.realification.PolynomialOrbit (fun _ : U => 1))
    (E P Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hprod : E * P * Q = pairOrbitSymbol
      (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
      (majorTranslationPolynomialOrbit w d hw hwd F hF A hA) partner b ω hN)
    (u : U → ℝ) :
    algebraicMajorSymbol
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d F)
      (specializeMajorParameters (RingHom.id ℝ)
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d F) 0)
      (majorTranslationTopCoordinates w A) u =
        detectedTranslationGroupEval w d hw hwd M hM D u E *
          detectedTranslationGroupEval w d hw hwd M hM D u P *
            detectedTranslationGroupEval w d hw hwd M hM D u Q := by
  rw [← majorTranslationPolynomialOrbit_degree_symbolLift_realEval w d hw hwd F hF A hA u,
    ← detectedTranslationSymbolLift_pairOrbitSymbol w d hw hwd M hM D b ω hN
      (majorTranslationPolynomialOrbit w d hw hwd F hF A hA) partner,
    ← hprod]
  exact (detectedTranslationGroupEval w d hw hwd M hM D u).map_mul (E * P) Q |>.trans
    (congrArg (· * detectedTranslationGroupEval w d hw hwd M hM D u Q)
      ((detectedTranslationGroupEval w d hw hwd M hM D u).map_mul E P))

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationSymbolLift_base_coordinate
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) (i : B) :
    coordinate (((weightedBasis w d hw).baseChange ℝ).coord (Sum.inl i)).toAddMonoidHom
      (detectedTranslationSymbolLift w d hw hwd M hM D P).log =
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial
      b ω hN (fun _ : U => 1) (detectedTranslationBaseFunctional w d hw hwd M hM D i) P := by
  rw [detectedTranslationSymbolLift_log]
  let N := pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
  let η := (LinearMap.proj i).comp (baseLinear.comp (weightedSubalgebra w d).subtype)
  have h := N.filtration.homogeneousProjected_scalar_coordinate
    (weightedFiltration w d hwd) b ω hN
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw)
    (liePiEval (R := ℚ) true)
    (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
    (fun _ : U => 1) η P.coord
  change N.filtration.scalarSymbolPolynomial b ω hN (fun _ : U => 1)
    (detectedTranslationBaseFunctional w d hw hwd M hM D i) P = _ at h
  dsimp only [η] at h
  rw [realifyTranslationBaseFunctional_eq_coord w d hw] at h
  convert h.symm using 1

theorem detectedTranslationGroupEval_base
    (u : U → ℝ)
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    (detectedTranslationGroupEval w d hw hwd M hM D u P).base =
      eval₂ u (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN P) := by
  funext i
  change (bchRealTranslationHom w d hwd
    ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval (fun _ : U => 1) u
      (detectedTranslationSymbolLift w d hw hwd M hM D P))).base i = _
  rw [bchRealTranslationHom_base_coordinate w d hw hwd]
  change ((weightedBasis w d hw).baseChange ℝ).coord (Sum.inl i)
      (eval₂ u (detectedTranslationSymbolLift w d hw hwd M hM D P).log) =
    (LinearMap.proj i : (B → ℝ) →ₗ[ℝ] ℝ)
      (eval₂ u (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN P))
  rw [coordinate_eval₂, coordinate_eval₂,
    detectedTranslationSymbolLift_base_coordinate w d hw hwd M hM D b ω hN,
    detectedTranslationBasePolynomial_coordinate w d hw hwd M hM D b ω hN]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j, (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationGroupEval_fast_potential
    (hd : 0 < d)
    (W : LieSubalgebra ℚ (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra b ω hN (fun _ : U => 1) W))
    (V : MvPolynomial B ℚ) :
    let fast := W.map (weightedTranslationGradedProjection
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
        w d hw hwd (liePiEval (R := ℚ) true)
        (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D))
    (∀ x ∈ fast, ∀ z ∈ fast.toSubmodule.map
      (baseLinear.comp (weightedSubalgebra w d).subtype),
      eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) →
    ∀ u z, z ∈ (fast.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) →
    eval z (detectedTranslationGroupEval w d hw hwd M hM D u P).polynomial =
      eval₂ (algebraMap ℚ ℝ) z V -
        eval₂ (algebraMap ℚ ℝ) (z - (detectedTranslationGroupEval w d hw hwd M hM D u P).base) V := by
  intro fast hderiv u z hz
  have hg := detectedTranslationSymbolLift_value_mem_fast w d hw hwd M hM D b ω hN W P hP u
  have h := bchRealTranslationHom_eval_potential w d hw hd hwd fast V hderiv
    ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
      (fun _ : U => 1) u (detectedTranslationSymbolLift w d hw hwd M hM D P)) hg z hz
  simpa only [detectedTranslationGroupEval, MonoidHom.comp_apply, eval_map] using h

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped Matrix

universe u v z

theorem exists_detectedTranslation_separated_base :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {B L : Type} {σ : Type u} {ι : Type v} {J : Type z}
    [Fintype B] [Fintype ι] [Fintype J] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (_hd : 1 ≤ d) {p : ℝ} (_hp : 0 ≤ p)
    (_hB : (Fintype.card B : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hJ : (Fintype.card J : ℝ) ≤ p)
    (_hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (W : LieSubalgebra ℚ
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (v : J → (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hvheight : ∀ j i, rationalLogHeight
      (((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hN).repr (v j) i) ≤ p)
    (E P Q X : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (_hprod : E * P * Q = X)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C)^C) ≤ T i)
    (_hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : σ => 1) T (Real.exp p) E)
    (_hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra
        b ω hN (fun _ : σ => 1) W))
    (m : ℕ) (_hm : 0 < m) (_hmp : (m : ℝ) ≤ Real.exp p)
    (_hQ : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : σ => 1) m Q)
    (retained : Submodule ℝ (B → ℝ))
    (_hX : ∀ α, coefficients
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN X) α ∈ retained)
    (_hretained : retained ≤ Submodule.span ℝ (Set.range (fun j i =>
      (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ)))),
    (∀ α, coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN E) α ∈
      Submodule.span ℝ (Set.range (fun j i =>
        (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ)))) ∧
    (∀ α, coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN Q) α ∈
      Submodule.span ℝ (Set.range (fun j i =>
        (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ)))) ∧
    ∀ u : σ → ℝ,
      (detectedTranslationGroupEval w d hw hwd M hM D u E).base ∈
        Submodule.span ℝ (Set.range (fun j i =>
          (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ))) ∧
      (detectedTranslationGroupEval w d hw hwd M hM D u Q).base ∈
        Submodule.span ℝ (Set.range (fun j i =>
          (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ))) := by
  let budget : Polynomial ℕ := (Polynomial.X + 3)^5
  obtain ⟨C, hC, hsep⟩ := exists_vectorPolynomial_subspace_separation budget
  refine ⟨C, hC, ?_⟩
  intro B L σ ι J _ _ _ _ _ w d hw hwd _ M hM e D b ω hN hd p hp hB hι hJ
    hb W v hv hvheight E P Q X hprod T hT hE hP m hm hmp hQ retained hX hretained
  have hbudget : budget.eval₂ (Nat.castRingHom ℝ) p = (p + 3)^5 := by
    simp [budget, Polynomial.eval₂_pow]
  obtain ⟨hpbudget, hsmall, hceil⟩ := detectedTranslationSeparation_budget hp
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  let H : ℕ := ⌈Real.exp ((p + 2)^4)⌉₊
  let A : Matrix B J ℚ := fun i j => detectedTranslationBaseMap w d hw hwd M hM D (v j) i
  have hA : ∀ i j, RationalHeightLE (A i j) H := by
    intro i j
    exact rationalHeightLE_ceil_exp
      (detectedTranslationBaseFunctional_value_logHeight w d hw hwd M hM D
        b ω hN hp hι hb (v j) (hvheight j) i)
  obtain ⟨q, hq, hqbound, hgrid⟩ :=
    detectedTranslationBasePolynomial_exists_coefficient_grid w d hw hwd M hM D
      b ω hN hp hι hb hB m hm hmp Q hQ
  have hslow := detectedTranslationBasePolynomial_slow_coefficients w d hw hwd M hM D
    b ω hN hp hι hb T hTpos E hE
  have hqbudget : (q : ℝ) ≤ Real.exp (budget.eval₂ (Nat.castRingHom ℝ) p) := by
    rw [hbudget]
    exact hqbound.trans (Real.exp_le_exp.mpr hsmall)
  obtain ⟨hEco, hQco, hEeval, hQeval⟩ :=
    hsep A H q (one_le_ceil_exp _) hq hA p hp
      (by rw [hbudget]; exact hB.trans hpbudget)
      (by rw [hbudget]; exact hJ.trans hpbudget)
      (by rw [hbudget]; exact hceil) hqbudget T hT
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN X)
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN E)
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN P)
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN Q)
      (detectedTranslationBasePolynomial_factorization w d hw hwd M hM D b ω hN hd E P Q X hprod)
      (fun α => hretained (hX α))
      (detectedTranslationBasePolynomial_fast_coefficients_mem_span w d hw hwd M hM D b ω hN W v hv P hP)
      (detectedTranslationBasePolynomial_constant w d hw hwd M hM D b ω hN E)
      (detectedTranslationBasePolynomial_constant w d hw hwd M hM D b ω hN Q)
      (fun α i => (hslow α i).trans (by
        rw [hbudget]
        exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hsmall)
          (monomialScale_pos T hTpos α).le)) hgrid
  refine ⟨hEco, hQco, fun u => ?_⟩
  rw [detectedTranslationGroupEval_base w d hw hwd M hM D b ω hN,
    detectedTranslationGroupEval_base w d hw hwd M hM D b ω hN]
  have heval (Y : VectorPolynomial σ ℝ (B → ℝ)) : eval₂ u Y = eval u Y := by
    simpa using (eval₂_algebraMap (S := ℝ) u Y)
  rw [heval, heval]
  exact ⟨hEeval u, hQeval u⟩

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem exists_reduced_majorPolynomial_degree_twisted_correlation_separated_data
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (M : ℕ) (hM : 0 < M)
      (D : RationalFilteredNilmanifold L t e) (htd : t < d)
      (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
      (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
      (K : ℝ≥0) (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (_hT : ∀ x r, ‖T x r‖ ≤ 1) (_hLip : ∀ r, LipschitzWith K (fun x => T x r))
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p →
      Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ
        (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d) K : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      ∀ (β : (U → ℤ) → Fin m → ℤ),
      (∀ x ∈ translatedIntegerBox origin lengths, ∀ i,
        |eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)| ≤ 1 / 2) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        T (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ))
            (fun i => (β x i : ZMod M)) *
          (Ψ.value (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)) : ℂ) *
          (Real.fourierChar (eval (fun j => ((Sum.elim x (β x) j : ℤ) : ℝ)) F) : ℂ) *
          R.eval x‖ →
      ∀ (retained : Fin d → Submodule ℝ (Fin m → ℝ)),
      (∀ h, HasLayerSamplingRank (h.val + 1) (fun i => (lengths i : ℝ))
        (Real.exp ((p + C)^C)) (retained h)
        (ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin m))
          (fun i => weightedHomogeneousComponent (fun _ : U => 1) (w i) (A i)))) →
      (∀ α, coefficients (ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin m))
          (fun i => weightedHomogeneousComponent (fun _ : U => 1) (w i) (A i))) α ∈
        ⨆ h, retained h) →
      let N := pi (pairModels
        (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
      let orbit := majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial F)
        (fractionalCoefficientPolynomial_mem_weightedSupportLE F
          (Sum.elim (fun _ : U => 1) w) d hF) A hA
      let partner := D.raiseStepRealOrbit htd.le R.orbit
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)))
          ℚ (PairAlgebra (weightedSubalgebra w d) L))
        (ω : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → ℕ)
        (hLayers : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ (p + C)^C) ∧
      ∃ (l : ℕ) (E P S : N.filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
        (W : LieSubalgebra ℚ N.filtration.AssociatedGraded)
        (v : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → N.filtration.AssociatedGraded)
        (Vfast : LieSubalgebra ℚ (weightedSubalgebra w d)) (V : MvPolynomial (Fin m) ℚ) (q : ℕ),
        0 < l ∧ (l : ℝ) ≤ Real.exp ((p + C)^C) ∧
        E * P * S = pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
          (D.raiseStep htd.le) orbit partner b ω hLayers ∧
        N.filtration.SymbolSlowBound b ω hLayers (fun _ => 1)
          (fun i => (lengths i : ℝ)) (Real.exp ((p + C)^C)) E ∧
        N.filtration.SymbolRationalGrid b ω hLayers (fun _ => 1) l S ∧
        (∀ t : U → ℝ,
          eval₂ t ((weightedFiltration w d hwd).realSymbolRepresentative
            (weightedBasis w d hw) (weightedBasisGrade w d)
            (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
            (realificationLieHom (N.filtration.filteredPolynomialSymbolMap
              (weightedFiltration w d hwd) (liePiEval (R := ℚ) true)
              (pairFirstProjection_filtered
                (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
              (fun _ : U => 1)) P.coord)) ∈ realificationLieSubalgebra Vfast) ∧
        Vfast = W.map (weightedTranslationGradedProjection N.filtration w d hw hwd
          (liePiEval (R := ℚ) true) (pairFirstProjection_filtered
            (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))) ∧
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule (N.filtration.associatedGradedBasis b ω hLayers) ω W.toSubmodule ∧
        (∀ i j, rationalLogHeight ((N.filtration.associatedGradedBasis b ω hLayers).repr (v i) j) ≤ (p+C)^C) ∧
        P.coord ∈ realificationLieSubalgebra
          (N.filtration.symbolPointwiseSubalgebra b ω hLayers (fun _ : U => 1) W) ∧
        V.IsWeightedHomogeneous w d ∧
        (∀ x ∈ Vfast, ∀ z ∈ Vfast.toSubmodule.map
            (baseLinear.comp (weightedSubalgebra w d).subtype),
          eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) ∧
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + C)^C) ∧
        (fun α => V.coeff α) ∈ denominatorGrid q ∧
        realPolynomialMass (MvPolynomial.map (algebraMap ℚ ℝ) V) ≤ Real.exp ((p + C)^C) ∧
        (∀ α, ((V.coeff α).num.natAbs : ℝ) ≤ Real.exp ((p + C)^C) ∧
          ((V.coeff α).den : ℝ) ≤ Real.exp ((p + C)^C)) ∧
        (∀ h, retained h ≤ (Vfast.toSubmodule.baseChange ℝ).map
          (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) ∧
        ∀ u : U → ℝ,
          (detectedTranslationGroupEval w d hw hwd M hM (D.raiseStep htd.le) u E).base ∈
            (Vfast.toSubmodule.baseChange ℝ).map
              (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) ∧
          (detectedTranslationGroupEval w d hw hwd M hM (D.raiseStep htd.le) u S).base ∈
            (Vfast.toSubmodule.baseChange ℝ).map
              (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) := by
  obtain ⟨a, ha, hdata⟩ := exists_reduced_majorPolynomial_degree_twisted_correlation_potential_data d hd
  obtain ⟨c, hc, hcontain⟩ := exists_majorTranslation_samplingRank_le_real_base_image
  obtain ⟨s, hs, hsep⟩ := exists_detectedTranslation_separated_base
  obtain ⟨C, hC, hbudget⟩ := exists_translationMajorSeparated_budget a c s
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ M hM D htd Ψ F hF A hA
    K T hT hLip R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge β hβ hcorr
    retained hrank hAret N orbit partner
  let p₁ : ℝ := (p + a)^a
  have hp₁ : 0 ≤ p₁ := (translationMajor_initial_budget_bounds a ha p hp).1
  have hpp₁ : p ≤ p₁ := (translationMajor_initial_budget_bounds a ha p hp).2.1
  obtain ⟨hb₁, hb₂, hb₃⟩ := hbudget p hp
  have hlarge₁ (i : U) : Real.exp ((p + a)^a) ≤ (lengths i : ℝ) :=
    (Real.exp_le_exp.mpr hb₁).trans (hlarge i)
  obtain ⟨b, ω, hLayers, hb, l, E, P, S, W, v, Vfast, V, q,
      hl, hlp, hprod, hE, hS, hfast, hVfast, hv, hW, hh, hP, hV,
      hderiv, hq, hqp, hgrid, hmass, hcoeff⟩ :=
    hdata w hw hwd M hM D htd Ψ F hF A hA K T hT hLip R p hp hgeometry hbound hR hRcap
      origin lengths hlengths hU hlarge₁ β hβ hcorr
  have hdim : (Fintype.card (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L))) : ℝ) ≤ p₁ := by
    simpa only [Fintype.card_fin] using
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).geometry_pair_finrank_le_budget
        (D.raiseStep htd.le) hgeometry (D.raiseStep_geometry htd.le hR.1) ha
  have hbase : (Fintype.card (Fin m) : ℝ) ≤ p₁ :=
    (weightedTranslationResidueNilmanifold_base_card_le w d hw hwd M hM hgeometry).trans hpp₁
  let Kfast := (Vfast.toSubmodule.baseChange ℝ).map
    (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))
  have hspan : Submodule.span ℝ (Set.range (fun j i =>
      (detectedTranslationBaseMap w d hw hwd M hM (D.raiseStep htd.le) (v j) i : ℝ))) = Kfast := by
    dsimp only [Kfast]
    rw [hVfast]
    exact detectedTranslationBase_span_eq_real_image w d hw hwd M hM (D.raiseStep htd.le) W v hv
  have hTpos (i : U) : 0 < (lengths i : ℝ) := by exact_mod_cast hlengths i
  have hret : ∀ h, retained h ≤ Kfast := by
    intro h
    dsimp only [Kfast]
    rw [hVfast]
    apply hcontain w d hw hwd M hM (D.raiseStep htd.le) b ω hLayers hd hp₁ hbase hdim hdim
      hb W v hv hh (fractionalCoefficientPolynomial F)
      (fractionalCoefficientPolynomial_mem_weightedSupportLE F (Sum.elim (fun _ : U => 1) w) d hF)
      A hA partner E P S hprod (fun i => (lengths i : ℝ)) hTpos hE hP l hl hlp hS
      (h.val + 1) (Real.exp ((p + C)^C)) (retained h) (hrank h)
    exact Real.exp_le_exp.mpr hb₂
  let X := pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
    (D.raiseStep htd.le) orbit partner b ω hLayers
  have hX : ∀ α, coefficients
      (detectedTranslationBasePolynomial w d hw hwd M hM (D.raiseStep htd.le) b ω hLayers X) α ∈
        ⨆ h, retained h := by
    intro α
    rw [detectedTranslationBasePolynomial_majorOrbitSymbol w d hw hwd M hM (D.raiseStep htd.le)
      b ω hLayers (fractionalCoefficientPolynomial F)
      (fractionalCoefficientPolynomial_mem_weightedSupportLE F (Sum.elim (fun _ : U => 1) w) d hF)
      A hA partner]
    exact hAret α
  have hjoin : (⨆ h, retained h) ≤ Submodule.span ℝ (Set.range (fun j i =>
      (detectedTranslationBaseMap w d hw hwd M hM (D.raiseStep htd.le) (v j) i : ℝ))) := by
    rw [hspan]
    exact iSup_le hret
  obtain ⟨_, _, hgroup⟩ := hsep w d hw hwd M hM (D.raiseStep htd.le) b ω hLayers
    hd hp₁ hbase hdim hdim hb W v hv hh E P S X hprod (fun i => (lengths i : ℝ))
    (fun i => (Real.exp_le_exp.mpr hb₃).trans (hlarge i)) hE hP l hl hlp hS
    (⨆ h, retained h) hX hjoin
  have hexp := Real.exp_le_exp.mpr hb₁
  refine ⟨b, ω, hLayers, fun i j => (hb i j).trans hb₁, ?_⟩
  refine ⟨l, E, P, S, W, v, Vfast, V, q, hl, hlp.trans hexp, hprod, ?_⟩
  refine ⟨?_, hS, ?_⟩
  · exact N.filtration.symbolSlowBound_mono b ω hLayers (fun _ : U => 1)
      (fun i => (lengths i : ℝ)) hTpos hexp E hE
  refine ⟨?_, hVfast, hv, ?_⟩
  · convert hfast using 1
  refine ⟨hW, ?_, ?_, hV, hderiv, ?_⟩
  · exact fun i j => (hh i j).trans hb₁
  · convert hP using 1
  refine ⟨hq, hqp.trans hexp, hgrid, hmass.trans hexp, ?_, hret, ?_⟩
  · intro α
    exact ⟨(hcoeff α).1.trans hexp, (hcoeff α).2.trans hexp⟩
  · intro u
    have hu := hgroup u
    rw [hspan] at hu
    exact hu

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorPhaseVectorDecomposition
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial Module PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

def MajorPhaseDetectedConclusion {m : ℕ} {X L : Type}
    [Fintype X] [LieRing L] [LieAlgebra ℚ L]
    (J : Fin m → Type) [∀ j, Fintype (J j)] (d : ℕ)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (F : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
    (N : X → ℕ) (B : ℝ) : Prop :=
  let w := lowTaggedWeight J d
  ∃ (fast : LieSubalgebra ℚ (weightedSubalgebra w d))
    (g : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → weightedSubalgebra w d)
    (S : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
    (R : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℚ) (q : ℕ),
    (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L) : ℝ) ≤ B ∧
    Submodule.span ℚ (Set.range g) = fast.toSubmodule ∧
    BasisGradedSubmodule (weightedBasis w d (lowTaggedWeight_pos J d))
      (weightedBasisGrade w d) fast.toSubmodule ∧
    (∀ j i, rationalLogHeight ((weightedBasis w d (lowTaggedWeight_pos J d)).repr (g j) i) ≤ B) ∧
    BasisGradedSubmodule (Pi.basisFun ℝ _) w ((fast.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) ∧
    (∀ h, lowTaggedRetained J d U h ≤ (fast.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) ∧
    realPolynomialMass S ≤ Real.exp B ∧
    (∀ α, |S.coeff α| ≤ Real.exp B) ∧
    0 < q ∧ (q : ℝ) ≤ Real.exp B ∧
    (fun α => R.coeff α) ∈ denominatorGrid q ∧
    (∀ α, (R.coeff α).den ≤ q) ∧
    S ∈ weightedSupportLE (Sum.elim (fun _ : X => 1) w) d ∧
    R ∈ weightedSupportLE (Sum.elim (fun _ : X => 1) w) d ∧
    ∀ (u : X → ℝ) (z : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ),
      z ∈ (fast.toSubmodule.baseChange ℝ).map
        (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) →
      MvPolynomial.eval (Sum.elim u z)
          (weightedHomogeneousComponent (Sum.elim (fun _ : X => 1) w) d F) =
        MvPolynomial.eval (Sum.elim (fun i => u i / (N i : ℝ))
          (fun j => z j - MvPolynomial.eval u
            (majorTranslationTopCoordinates w
              (fun i => lowTaggedPolynomial J d poly i - MvPolynomial.C (c i)) j))) S +
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Sum.elim u z) R

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module RationalFilteredNilmanifold PolynomialTranslationLie

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)] (d : ℕ)

noncomputable def majorPhaseTaggedGenerators {A : Type*}
    (g : A → weightedSubalgebra (lowTaggedWeight J d) d)
    (j : Fin m) (hj : j.val + 1 ≤ d) (a : A) (i : J j) : ℚ :=
  (g a).val.base (lowTaggedSlot J d j hj i)

 theorem majorPhaseTaggedGenerators_span {A : Type*}
    (fast : LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J d) d))
    (g : A → weightedSubalgebra (lowTaggedWeight J d) d)
    (hg : Submodule.span ℚ (Set.range g) = fast.toSubmodule)
    (hgraded : BasisGradedSubmodule
      (weightedBasis (lowTaggedWeight J d) d (lowTaggedWeight_pos J d))
      (weightedBasisGrade (lowTaggedWeight J d) d) fast.toSubmodule)
    (j : Fin m) (hj : j.val + 1 ≤ d) :
    lowTaggedSubspaceFamily J d
      ((fast.toSubmodule.baseChange ℝ).map
        (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra (lowTaggedWeight J d) d).subtype))) j =
      Submodule.span ℝ (Set.range (fun a i => (majorPhaseTaggedGenerators J d g j hj a i : ℝ))) := by
  have hK := weightedTranslationBase_real_image_graded (lowTaggedWeight J d) d
    (lowTaggedWeight_pos J d) fast.toSubmodule hgraded g hg
  have hspan := realifyCoordinateMap_image_eq_span fast.toSubmodule g hg
    (baseLinear.comp (weightedSubalgebra (lowTaggedWeight J d) d).subtype)
  rw [hspan] at hK ⊢
  exact lowTaggedSubspaceFamily_span J d _ hK j hj

 theorem majorPhaseTaggedGenerators_logHeight {A : Type*}
    (g : A → weightedSubalgebra (lowTaggedWeight J d) d) {B : ℝ}
    (hheight : ∀ a i, rationalLogHeight
      ((weightedBasis (lowTaggedWeight J d) d (lowTaggedWeight_pos J d)).repr (g a) i) ≤ B)
    (j : Fin m) (hj : j.val + 1 ≤ d) (a : A) (i : J j) :
    rationalLogHeight (majorPhaseTaggedGenerators J d g j hj a i) ≤ B := by
  have h := hheight a (Sum.inl (lowTaggedSlot J d j hj i))
  simpa only [weightedBasis_repr_inl, majorPhaseTaggedGenerators] using h

theorem majorPhaseTaggedGenerators_mem_iff {A : Type*}
    (fast : LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J d) d))
    (g : A → weightedSubalgebra (lowTaggedWeight J d) d)
    (hg : Submodule.span ℚ (Set.range g) = fast.toSubmodule)
    (hgraded : BasisGradedSubmodule
      (weightedBasis (lowTaggedWeight J d) d (lowTaggedWeight_pos J d))
      (weightedBasisGrade (lowTaggedWeight J d) d) fast.toSubmodule)
    (x : ∀ j, J j → ℝ) :
    lowTaggedCoordinates J d x ∈ (fast.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra (lowTaggedWeight J d) d).subtype)) ↔
      ∀ j (hj : j.val + 1 ≤ d), x j ∈
        Submodule.span ℝ (Set.range (fun a i => (majorPhaseTaggedGenerators J d g j hj a i : ℝ))) := by
  have hK := weightedTranslationBase_real_image_graded (lowTaggedWeight J d) d
    (lowTaggedWeight_pos J d) fast.toSubmodule hgraded g hg
  rw [lowTaggedCoordinates_mem_iff_low J d _ hK x]
  constructor
  · intro hx j hj
    rw [← majorPhaseTaggedGenerators_span J d fast g hg hgraded j hj]
    exact hx j hj
  · intro hx j hj
    rw [majorPhaseTaggedGenerators_span J d fast g hg hgraded j hj]
    exact hx j hj

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial Module PolynomialTranslationLie RationalFilteredNilmanifold
open scoped BigOperators TensorProduct

variable {m : ℕ} {X L : Type} [Fintype X] [LieRing L] [LieAlgebra ℚ L]
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (d : ℕ)

noncomputable def majorPhaseDetectedRealBase
    (fast : LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J d) d)) :
    Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) :=
  (fast.toSubmodule.baseChange ℝ).map
    (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra (lowTaggedWeight J d) d).subtype))

variable {η V : Type*} [Fintype η] [AddCommGroup V] [Module ℚ V] [Module ℝ V]
  [IsScalarTower ℚ ℝ V]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
variable (N : X → ℕ) (B : ℝ) (eV : Basis η ℝ V)
variable (p : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℚ V)

def MajorPhaseVectorDetectedConclusion : Prop :=
  let w := lowTaggedWeight J d
  let wt := Sum.elim (fun _ : X => 1) w
  ∃ (fast : η → LieSubalgebra ℚ (weightedSubalgebra w d))
    (g : η → Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → weightedSubalgebra w d)
    (slow rat : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℚ V) (q : ℕ),
    (∀ i, (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L) : ℝ) ≤ B ∧
      Submodule.span ℚ (Set.range (g i)) = (fast i).toSubmodule ∧
      BasisGradedSubmodule (weightedBasis w d (lowTaggedWeight_pos J d))
        (weightedBasisGrade w d) (fast i).toSubmodule ∧
      ∀ j a, rationalLogHeight ((weightedBasis w d (lowTaggedWeight_pos J d)).repr (g i j) a) ≤ B) ∧
    (∀ i, BasisGradedSubmodule (Pi.basisFun ℝ _) w (majorPhaseDetectedRealBase J d (fast i))) ∧
    (∀ i h, lowTaggedRetained J d U h ≤ majorPhaseDetectedRealBase J d (fast i)) ∧
    (∀ i, realPolynomialMass (coordinate (eV.coord i).toAddMonoidHom slow) ≤ Real.exp B) ∧
    (∀ i α, |eV.coord i (coefficients slow α)| ≤ Real.exp B) ∧
    0 < q ∧ (q : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * B) ∧
    (∀ i, realPolynomialCoefficientGrid q (coordinate (eV.coord i).toAddMonoidHom rat)) ∧
    (∀ i, coordinate (eV.coord i).toAddMonoidHom slow ∈ weightedSupportLE wt d) ∧
    (∀ i, coordinate (eV.coord i).toAddMonoidHom rat ∈ weightedSupportLE wt d) ∧
    ∀ (u : X → ℝ) (z : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ),
      (∀ i, z ∈ majorPhaseDetectedRealBase J d (fast i)) →
      eval₂ (Sum.elim u z) p =
        eval₂ (Sum.elim u z) (realChartSubstitute
          (normalizedRealPolynomialChart (fun i => (N i : ℝ))
            (majorTranslationTopCoordinates w
              (fun i => lowTaggedPolynomial J d poly i - MvPolynomial.C (c i)))) slow) +
        eval₂ (Sum.elim u z) rat

theorem majorPhaseVectorDetectedConclusion_of_coordinates
    (hp : ∀ α, Finsupp.weight (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) α ≠ d →
      coefficients p α = 0)
    (hscalar : ∀ i, MajorPhaseDetectedConclusion (L := L) J d U poly c
      (coordinate (eV.coord i).toAddMonoidHom p) N B) :
    MajorPhaseVectorDetectedConclusion (L := L) J d U poly c N B eV p := by
  classical
  simp only [MajorPhaseDetectedConclusion] at hscalar
  choose fast g S Q q hdim hspan hgrade hheight hbase hretain hmass hcoeff
    hq hqB hgrid hden hS hQ hvalue using hscalar
  let slow := ofCoordinates (R := ℚ) eV S
  let rat := ofCoordinates (R := ℚ) eV (fun i => MvPolynomial.map (algebraMap ℚ ℝ) (Q i))
  refine ⟨fast, g, slow, rat, ∏ i, q i,
    (fun i => ⟨hdim i, hspan i, hgrade i, hheight i⟩), hbase, hretain, ?_, ?_,
    majorPhaseCoordinateDenominator_pos q hq,
    majorPhaseCoordinateDenominator_le_exp q B hqB, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [slow, coordinate_ofCoordinates] using hmass i
  · intro i α
    have h := congrArg (fun polynomial : MvPolynomial _ _ => polynomial.coeff α)
      (coordinate_ofCoordinates (R := ℚ) eV S i)
    rw [coeff_coordinate] at h
    exact h ▸ hcoeff i α
  · intro i
    dsimp only [rat]
    rw [coordinate_ofCoordinates]
    exact (realPolynomialCoefficientGrid_ratCast_iff _ _).mpr
      (majorPhaseCoordinateDenominator_grid q Q hgrid i)
  · intro i
    simpa only [slow, coordinate_ofCoordinates] using hS i
  · intro i
    dsimp only [rat]
    rw [coordinate_ofCoordinates]
    intro α hα
    apply hQ i
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    apply MvPolynomial.mem_support_iff.mp hα
    change (Q i).coeff α = 0 at hz
    change (MvPolynomial.map (algebraMap ℚ ℝ) (Q i)).coeff α = 0
    rw [MvPolynomial.coeff_map, hz, map_zero]
  · intro u z hz
    rw [eval₂_normalizedRealPolynomialChart]
    apply eV.equivFun.injective
    funext i
    change eV.coord i (eval₂ (Sum.elim u z) p) = eV.coord i (_ + _)
    rw [map_add, coordinate_eval₂, coordinate_eval₂, coordinate_eval₂]
    simp only [slow, rat, coordinate_ofCoordinates, MvPolynomial.eval_map]
    have hhom : (coordinate (eV.coord i).toAddMonoidHom p).IsWeightedHomogeneous
        (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) d := by
      intro α hα
      by_contra hweight
      apply hα
      rw [coeff_coordinate, hp α hweight, map_zero]
    simpa only [weightedHomogeneousComponent_eq_self hhom] using hvalue i u z (hz i)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.WeightedTranslationProjectionGridBudget
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

universe u v

variable {σ : Type u} {ι : Type v} [Fintype σ] [Fintype ι]
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) [Fintype (WeightedBasisIndex w d)]

include hw in

theorem weightedBasisIndex_card_le_pair_basis
    {L : Type u} [LieRing L] [LieAlgebra ℚ L]
    (b : Module.Basis ι ℚ
      (RationalFilteredNilmanifold.PairAlgebra (weightedSubalgebra w d) L)) :
    Fintype.card (WeightedBasisIndex w d) ≤ Fintype.card ι := by
  let : Module.Finite ℚ
      (RationalFilteredNilmanifold.PairAlgebra (weightedSubalgebra w d) L) :=
    b.finiteDimensional_of_finite
  have hproj := LinearMap.finrank_le_finrank_of_surjective
    (LinearMap.proj_surjective (R := ℚ) (φ := BoolLieFamily (weightedSubalgebra w d) L) true)
  change Module.finrank ℚ (weightedSubalgebra w d) ≤
    Module.finrank ℚ (RationalFilteredNilmanifold.PairAlgebra (weightedSubalgebra w d) L) at hproj
  rw [Module.finrank_eq_card_basis (weightedBasis w d hw),
    Module.finrank_eq_card_basis b] at hproj
  exact hproj

end Erdos3.PolynomialTranslationLie

end

end OAI

end


