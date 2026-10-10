-- Prove2me | Definitions.Def_OAIErdos3B189
-- name    : OAIErdos3B189
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T08:36:34.044254+00:00
-- url     : https://prove2.me/theorems/76048eb8-0051-428d-8561-7cd285156214
-- title:
--   OpenAI Erdős-3 split, definitions bundle 190 of 205
-- statement:
--   Definitions bundle 190 of 205 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B188`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 190 available.
--
--   Modules: `OAI.Erdos3.MultidegreeLieFiltration.affineMixedLog_adapted`, `OAI.Erdos3.MultidegreeLieFiltration.affineMixedOrbit`, `OAI.Erdos3.MultidegreeLieFiltration.affineMixedOrbit_eval`, `OAI.Erdos3.NativeRankRelation.CommonData.HasCoveredDependentComparison`, `OAI.Erdos3.NativeRankRelation.CommonData.commonAffineMarkedLift`, `OAI.Erdos3.NativeRankRelation.CommonData.commonAffineMarkedLift_eval`, `OAI.Erdos3.NativeRankRelation.CommonData.commonAffineMarkedOrbit`, `OAI.Erdos3.NativeRankRelation.CommonData.commonAffineMarkedOrbit_eval`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_controlled_dependentQuotient_model`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_covered_dependentQuotient_comparison`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_native_dependentQuotient_unit_model`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_native_freeCoefficientPolynomialOrbit`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_native_freeCoefficient_corrections`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_sharedFreeComparisonSpace_basis`, `OAI.Erdos3.NativeRankRelation.CommonData.localAffineMarkedBase`, `OAI.Erdos3.NativeRankRelation.CommonData.localAffineMarkedLift`, `OAI.Erdos3.NativeRankRelation.CommonData.localAffineMarkedLift_eq_polynomial_eval`, `OAI.Erdos3.NativeRankRelation.CommonData.localAffineMarkedLift_eval`, `OAI.Erdos3.NativeRankRelation.CommonData.realAffineMarkedBase`, `OAI.Erdos3.NativeRankRelation.CommonData.realAffineMarkedBase_eval`, `OAI.Erdos3.NativeRankRelation.CommonData.realAffineMarkedSlope`, `OAI.Erdos3.NativeRankRelation.CommonData.realAffineMarkedSlope_eval`, `OAI.Erdos3.NativeRankRelation.CommonData.scaledLocalAffineCorrectingElement`, `OAI.Erdos3.NilpotentLieFiltration.PolynomialOrbit.logSum`, `OAI.Erdos3.NilpotentLieFiltration.PolynomialOrbit.logSum_log`, `OAI.Erdos3.NilpotentLieFiltration.PolynomialOrbit.logSum_normalized`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.exists_layer_basis_of_eq`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.withLattice`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.withLattice_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.restrictVertical`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_direction_lattice_scale`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_direction_lattice_scale_with_budget`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_exact_source_lattice_cover`, `OAI.Erdos3.VectorPolynomial.monomialLinearMap`, `OAI.Erdos3.VectorPolynomial.realAffinePolynomial`, `OAI.Erdos3.VectorPolynomial.realAffinePolynomial_eval`, `OAI.Erdos3.VectorPolynomial.realMonomial_eval`, `OAI.Erdos3.affineBoxCellCount_le_exp`, `OAI.Erdos3.affineBoxScale_le_exp`, `OAI.Erdos3.affineMixedLog`, `OAI.Erdos3.affineMixedLog_eval`, `OAI.Erdos3.affineRecoveryLogLoss`, `OAI.Erdos3.correlationExponent`, `OAI.Erdos3.correlationExponent_apply`, `OAI.Erdos3.direction_lattice_scale_bound`, `OAI.Erdos3.eval_correlation_monomial`, `OAI.Erdos3.exists_firstProjection_basis_logHeight`, `OAI.Erdos3.exists_fourPetalSpace_basis_logHeight`, `OAI.Erdos3.exists_marked_direction_lattice_scale`, `OAI.Erdos3.exists_marked_evaluation_lattice`, `OAI.Erdos3.exists_normalizedMarkedLattice_model`, `OAI.Erdos3.exists_quadratic_affine_budget`, `OAI.Erdos3.exists_sharedFreeAffineSelection_bound`, `OAI.Erdos3.exists_sharedFreeAffineUniform_bound`, `OAI.Erdos3.exists_sharedFreeComparisonBasisBudget_bound`, `OAI.Erdos3.exp_neg_affineRecoveryLogLoss_card_le`, `OAI.Erdos3.fourRefinementBasisBudget_mono`, `OAI.Erdos3.markedLocalCoefficientValue`, `OAI.Erdos3.markedLocalCoefficientValue_apply`, `OAI.Erdos3.markedLocalCoefficientValue_eq_on_small_cosets`, `OAI.Erdos3.markedLocalCoefficientValue_scaled_parameter`, `OAI.Erdos3.markedShiftLayerPolynomialMap_mem`, `OAI.Erdos3.normalizedMarkedLattice`, `OAI.Erdos3.normalizedMarkedLattice_direction`, `OAI.Erdos3.normalizedMarkedLattice_integral`, `OAI.Erdos3.normalizedMarkedLattice_le`, `OAI.Erdos3.normalizedMarkedPhase_real_eq_zero_iff`, `OAI.Erdos3.normalizedMarkedPhase_real_parameter`, `OAI.Erdos3.normalizedMarkedPhase_real_pure`, `OAI.Erdos3.normalizedMarkedPhase_real_scaled_parameter`, `OAI.Erdos3.normalizedMarkedPureRetraction`, `OAI.Erdos3.normalizedMarkedRetraction`, `OAI.Erdos3.normalizedMarkedRetraction_phase`, `OAI.Erdos3.normalizedMarkedRetraction_pure`, `OAI.Erdos3.normalizedMarkedRetraction_scaled_parameter`, `OAI.Erdos3.preimageBasisBudget_mono`, `OAI.Erdos3.properAffineRankBound`, `OAI.Erdos3.properAffineRecoveryLogLoss`, `OAI.Erdos3.properAffineScaleLog`, `OAI.Erdos3.properAffineSelection_bounds`, `OAI.Erdos3.properAffineVolumeLog`, `OAI.Erdos3.properAffineVolume_bound`, `OAI.Erdos3.realAffinePolynomial_mem_marked`, `OAI.Erdos3.realMarkedAffineMixedOrbit`, `OAI.Erdos3.realMarkedAffineMixedOrbit_eval`, `OAI.Erdos3.realMarkedAffineShift`, `OAI.Erdos3.realMarkedAffineShift_apply`, `OAI.Erdos3.realMarkedAffineShift_conjugation`, `OAI.Erdos3.realMarkedAffineShift_eval`, `OAI.Erdos3.realMarkedAffineShift_eval_affine`, `OAI.Erdos3.realMarkedAffineShift_quotient`, `OAI.Erdos3.realMarkedParameterOrbit`, `OAI.Erdos3.realMarkedParameterOrbit_eval`, `OAI.Erdos3.realMarkedPolynomialLift`, `OAI.Erdos3.realMarkedPolynomialLift_eval`, `OAI.Erdos3.realMarkedPolynomialLift_mem`, `OAI.Erdos3.realMarkedPolynomialLift_quotient_mem`, `OAI.Erdos3.realMarkedQuotientCoefficient`, `OAI.Erdos3.realMonomial_mem_markedPolynomialLayer`, `OAI.Erdos3.sharedFreeComparisonBasisBudget`, `OAI.Erdos3.sharedFreeRecoveryThreshold_coefficient_bounds`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B190

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDependentCoveredModel
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_controlled_dependentQuotient_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p q P Q v : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (B : D.CoefficientBases Q) {n : ℕ}
      (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
      (T : E.DegreeRankStructure r), T.filtration = D.coefficientFreeFiltration →
      0 ≤ v → T.ComplexityLE v →
      (∀ i j, rationalLogHeight (E.basis.repr (D.coefficientFreeGenerator i) j) ≤ v) →
      (∀ i, rationalLogHeight (B.freeFrequency D (E.basis i)) ≤ v) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp v →
      ∃ d : ℕ, d ≤ n ∧ ∃ G : RationalFilteredNilmanifold D.DependentQuotient s d,
        ∃ S : G.DegreeRankStructure r,
          S.filtration = D.dependentQuotientFiltration ∧ S.ComplexityLE ((v + C) ^ C) ∧
          l ∣ G.grid ∧ bchSubgroupCoordinates G.basis G.lattice = scaledIntegerGrid G.grid ∧
          (∀ i j, rationalLogHeight (G.basis.repr (D.dependentQuotientMap (E.basis j)) i) ≤
            (v + C) ^ C) ∧
          ∃ ξ : D.DependentQuotient →ₗ[ℚ] ℚ,
            (∀ x ∈ D.coefficientFreeFiltration.layer s r,
              ξ (D.dependentQuotientMap x) = B.freeFrequency D x) ∧
            (∀ i, rationalLogHeight (ξ (G.basis i)) ≤ (v + C) ^ C) ∧
            ∀ z : G.RealGroup, z ∈ G.realLattice → ∃ a : ℤ, realifyFunctional ξ z.coord = a := by
  let k := (6 * s + 4) * 424
  let a := bchIntegralDenominatorBound s + 5
  let P₀ : Polynomial ℕ := (Polynomial.X + 3) ^ k
  let R₀ := ((P₀ + 2) ^ 2 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P₀ + R₀)
  refine ⟨C, hC, ?_⟩
  intro r N _ b p q P Q v W out H R D B n E T hT hv hcomplex hgen hfreq l hl hlv
  let H₁ := ⌈Real.exp v⌉₊
  obtain ⟨m, hm, d, hd, u, hu, G, S, hSF, hdiv, hgrid, hcoords, hproj,
      ξ, hξ, hξH, hint, hSc⟩ :=
    B.exists_dependentQuotient_integral_model D E T hT (one_le_ceil_exp v)
      (fun i j k => rationalHeightLE_ceil_exp (hcomplex.1.2.2.1 i j k))
      (fun i a j => rationalHeightLE_ceil_exp (hcomplex.1.2.2.2 i a j))
      (fun i j a k => rationalHeightLE_ceil_exp (hcomplex.2 i j a k))
      (fun i j => rationalHeightLE_ceil_exp (hgen i j))
      (fun i => rationalHeightLE_ceil_exp (hfreq i)) l hl
  let K := rankQuotientHeight n m d u (lieTreeHeight n H₁ s)
  let P₁ := (v + 3) ^ k
  let R₁ := ((P₁ + 2) ^ 2 + a) ^ a
  have hv1 : 0 ≤ v + 1 := by linarith
  have hn : (n : ℝ) ≤ v + 1 := hcomplex.1.1.trans (by linarith)
  have hm' : (m : ℝ) ≤ v + 1 := (Nat.cast_le.mpr hm).trans hn
  have hd' : (d : ℝ) ≤ v + 1 := (Nat.cast_le.mpr hd).trans hn
  have hu' : (u : ℝ) ≤ v + 1 := (Nat.cast_le.mpr hu).trans hd'
  have hK : (K : ℝ) ≤ Real.exp P₁ := by
    have h := dependentQuotientHeight_le_exp s n m d u H₁ hv1 hn hm' hd' hu'
      (ceil_exp_le_exp_add_one hv)
    simpa only [show v + 1 + 2 = v + 3 by ring] using h
  have hvP : v ≤ P₁ := by
    have h := le_power_budget hv1 (show 1 ≤ k by dsimp [k]; omega)
    exact (show v ≤ v + 1 by linarith).trans (by
      simpa only [show v + 1 + 2 = v + 3 by ring] using h)
  have hP : 0 ≤ P₁ := hv.trans hvP
  have hdP : (d : ℝ) ≤ P₁ := (Nat.cast_le.mpr hd).trans (hcomplex.1.1.trans hvP)
  have hgrid' : (G.grid : ℝ) ≤ Real.exp R₁ :=
    (Nat.cast_le.mpr hgrid).trans (integral_frequency_grid_allowance_le_exp
      (bchIntegralDenominatorBound s) d K l hP hdP hK
      (hlv.trans (Real.exp_le_exp.mpr hvP)))
  have htotal : P₁ + R₁ ≤ (v + C) ^ C := by
    simpa [P₀, R₀, P₁, R₁, Polynomial.eval₂_pow] using hbudget v hv
  have hPC : P₁ ≤ (v + C) ^ C :=
    (le_add_of_nonneg_right (by dsimp [R₁]; positivity)).trans htotal
  have hRC : R₁ ≤ (v + C) ^ C := (le_add_of_nonneg_left hP).trans htotal
  refine ⟨d, hd, G, S, hSF, hSc _ (hdP.trans hPC)
    (hgrid'.trans (Real.exp_le_exp.mpr hRC)) (hK.trans (Real.exp_le_exp.mpr hPC)),
    hdiv, hcoords, ?_, ξ, hξ, ?_, G.realLattice_functional_integral ξ hint⟩
  · intro i j
    exact (rationalLogHeight_le_of_height (hproj i j) hK).trans hPC
  · intro i
    exact (rationalLogHeight_le_of_height (hξH i) hK).trans hPC

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct

noncomputable def restrictVertical {L I : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype I] [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s d : ℕ}
    {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p : ℝ}
    (V : D.UnitVerticalObservable T I p) (S : Subgroup D.RealGroup) (hS : S ≤ T) :
    D.UnitVerticalObservable S I p where
  observable := V.observable
  unit := V.unit
  norm := V.norm
  lipBound := V.lipBound
  lip_bound := V.lip_bound
  lipschitz := V.lipschitz
  frequency := V.frequency
  height := V.height
  vertical i z hz := V.vertical i z (hS hz)
  integral z hz := V.integral z (hS hz)

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_dependentQuotient_unit_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p q P Q v : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (B : D.CoefficientBases Q) {n : ℕ}
      (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
      (T : E.DegreeRankStructure r), T.filtration = D.coefficientFreeFiltration →
      0 ≤ v → T.ComplexityLE v →
      (∀ i j, rationalLogHeight (E.basis.repr (D.coefficientFreeGenerator i) j) ≤ v) →
      (∀ i, rationalLogHeight (B.freeFrequency D (E.basis i)) ≤ v) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp v →
      ∃ d : ℕ, d ≤ n ∧ ∃ G : RationalFilteredNilmanifold D.DependentQuotient s d,
        ∃ S : G.DegreeRankStructure r,
          S.filtration = D.dependentQuotientFiltration ∧ S.ComplexityLE ((v + C) ^ C) ∧
          l ∣ G.grid ∧ bchSubgroupCoordinates G.basis G.lattice = scaledIntegerGrid G.grid ∧
          (∀ i j, rationalLogHeight (G.basis.repr (D.dependentQuotientMap (E.basis j)) i) ≤
            (v + C) ^ C) ∧
          ∃ ξ : D.DependentQuotient →ₗ[ℚ] ℚ,
            (∀ x ∈ D.coefficientFreeFiltration.layer s r,
              ξ (D.dependentQuotientMap x) = B.freeFrequency D x) ∧
            (∀ i, rationalLogHeight (ξ (G.basis i)) ≤ (v + C) ^ C) ∧
            (∀ z : G.RealGroup, z ∈ G.realLattice → ∃ a : ℤ, realifyFunctional ξ z.coord = a) ∧
            (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.DependentQuotient)
             letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient) :=
               IsModuleTopology.topologicalAddGroup ℝ _
             letI := realification_moduleTopology_t2 G.basis
             ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ Real.exp ((v + C) ^ C) ∧
               ∃ U : G.UnitVerticalObservable (S.realSubgroup s r) (Fin k) ((v + C) ^ C),
                 U.frequency = ξ) := by
  obtain ⟨a, _, hmodel⟩ := exists_controlled_dependentQuotient_model s
  obtain ⟨c, _, hunit⟩ := RationalFilteredNilmanifold.exists_native_prescribed_unit s
  let A₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (A₀ + (A₀ + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro r N _ b p q P Q v W out H R D B n E T hT hv hcomplex hgen hfreq l hl hlv
  obtain ⟨d, hd, G, S, hSF, hSc, hdiv, hcoords, hproj, ξ, hξ, hξH, hint⟩ :=
    hmodel D B E T hT hv hcomplex hgen hfreq l hl hlv
  let A := (v + a) ^ a
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have htotal : A + (A + c) ^ c ≤ (v + C) ^ C := by
    simpa [A₀, A, Polynomial.eval₂_pow] using hbudget v hv
  have hAC : A ≤ (v + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (A + c) ^ c)).trans htotal
  have hUC : (A + c) ^ c ≤ (v + C) ^ C := (le_add_of_nonneg_left hA).trans htotal
  refine ⟨d, hd, G, S, hSF, hSc.mono S hAC, hdiv, hcoords,
    (fun i j => (hproj i j).trans hAC), ξ, hξ, (fun i => (hξH i).trans hAC), hint, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.DependentQuotient)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 G.basis
  obtain ⟨k, hk, hkbound, U, hU⟩ := hunit G hA hSc.1 ξ hξH hint
  refine ⟨k, hk, hkbound.trans (Real.exp_le_exp.mpr hUC),
    (U.restrictVertical (S.realSubgroup s r) (S.realSubgroup_le_degree s r)).mono hUC, ?_⟩
  exact hU

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

def HasCoveredDependentComparison {s r N : ℕ} [NeZero N] {b p q P v : ℝ}
    {W : NativeDegreeRankFamily s (r + 1) (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
    (D : R.CommonData P) {n : ℕ}
    (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
    (T : E.DegreeRankStructure (r + 1)) {I : Type} [Fintype I]
    [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) I v) (l : ℕ) (Q : ℝ) : Prop :=
  ∃ d : ℕ, d ≤ n ∧ ∃ G : RationalFilteredNilmanifold D.DependentQuotient s d,
    ∃ S : G.DegreeRankStructure (r + 1),
      S.filtration = D.dependentQuotientFiltration ∧ S.ComplexityLE Q ∧
      l ∣ G.grid ∧ bchSubgroupCoordinates G.basis G.lattice = scaledIntegerGrid G.grid ∧
      (∀ i j, rationalLogHeight (G.basis.repr (D.dependentQuotientMap (E.basis j)) i) ≤ Q) ∧
      ∃ Λ : Subgroup E.filtration.Group, Λ ≤ E.lattice ∧
        (Λ.subgroupOf E.lattice).Characteristic ∧ (Λ.subgroupOf E.lattice).Normal ∧
        (Λ.subgroupOf E.lattice).FiniteIndex ∧ (Λ.relIndex E.lattice : ℝ) ≤ Real.exp Q ∧
        ∃ (m : ℕ) (hm : 0 < m)
          (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates E.basis Λ)
          (hout : bchSubgroupCoordinates E.basis Λ ⊆ denominatorGrid m),
          (T.withLattice Λ m hm hin hout).ComplexityLE Q ∧
          ∃ hmap : Λ ≤ G.lattice.comap (mapOfSteps
              (hL := E.filtration.lowerCentralSeries_eq_bot)
              (hM := G.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap),
            ∃ V₀ : (E.withLattice Λ m hm hin hout).UnitVerticalObservable
                ((T.withLattice Λ m hm hin hout).realSubgroup s (r + 1)) I Q,
              V₀.frequency = V.frequency ∧ V₀.lipBound = V.lipBound ∧
              (∀ i x, V₀.observable i (QuotientGroup.mk x) = V.observable i (QuotientGroup.mk x)) ∧
              (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.DependentQuotient)
               letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient) :=
                 IsModuleTopology.topologicalAddGroup ℝ _
               letI := realification_moduleTopology_t2 G.basis
               ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ Real.exp Q ∧
                 ∃ U : G.UnitVerticalObservable (S.realSubgroup s (r + 1)) (Fin k) Q,
                   (∀ x ∈ D.coefficientFreeFiltration.layer s (r + 1),
                     U.frequency (D.dependentQuotientMap x) = V.frequency x) ∧
                   (∀ z : G.RealGroup, z ∈ G.realLattice →
                     ∃ a : ℤ, realifyFunctional U.frequency z.coord = a) ∧
                   ∀ (σ : Type) (w : σ → ℕ),
                     (E.withLattice Λ m hm hin hout).HasUniformLowerRankUnitFamily
                       (T.withLattice Λ m hm hin hout)
                       (mapDifferenceObservable V₀ U D.dependentQuotientMap hmap) w Q)

theorem exists_covered_dependentQuotient_comparison (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p q P Q v : ℝ}
      {W : NativeDegreeRankFamily s (r + 1) (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (J : D.CoefficientBases Q) {n : ℕ}
      (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
      (T : E.DegreeRankStructure (r + 1)) {I : Type} [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) I v),
      T.filtration = D.coefficientFreeFiltration → 0 ≤ v → T.ComplexityLE v →
      (∀ i j, rationalLogHeight (E.basis.repr (D.coefficientFreeGenerator i) j) ≤ v) →
      V.frequency = J.freeFrequency D →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp v →
        D.HasCoveredDependentComparison E T V l ((v + C) ^ C) := by
  obtain ⟨a, ha, hmodel⟩ := exists_native_dependentQuotient_unit_model s
  obtain ⟨c, hc, hcover⟩ := exists_native_source_unit_cover
  obtain ⟨b, _, hcomparison⟩ := exists_uniform_dependentQuotient_comparison s
  let A₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let K₀ := (A₀ + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (K₀ + (K₀ + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro r N _ b₀ p q P Q v W out H R D J n E T I _ _ _ _ _ V hT hv hTc hgen hV l hl hlv
  have hshift (x : ℝ) (hx : 0 ≤ x) (a : ℕ) (ha : 2 ≤ a) : x ≤ (x + a) ^ a := by
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
    calc
      x ≤ x + a := le_add_of_nonneg_right (Nat.cast_nonneg _)
      _ = (x + a) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega : 1 ≤ a)
  let A := (v + a) ^ a
  let K := (A + c) ^ c
  have hvA : v ≤ A := hshift v hv a ha
  have hA : 0 ≤ A := hv.trans hvA
  have hAK : A ≤ K := hshift A hA c hc
  have hK : 0 ≤ K := hA.trans hAK
  have htotal : K + (K + b) ^ b ≤ (v + C) ^ C := by
    simpa [A₀, K₀, A, K, Polynomial.eval₂_pow] using hbudget v hv
  have hKC : K ≤ (v + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (K + b) ^ b)).trans htotal
  have hAC : A ≤ (v + C) ^ C := hAK.trans hKC
  have hcomparisonC : (K + b) ^ b ≤ (v + C) ^ C := (le_add_of_nonneg_left hK).trans htotal
  obtain ⟨d, hd, G, S, hSF, hSc, hdiv, hcoords, hproj, ξ, hξ, _, hint, hunit⟩ :=
    hmodel D J E T hT hv hTc hgen (fun i => by rw [← hV]; exact V.height i) l hl hlv
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, m, hm, hin, hout, hcoverT, hmap, hpreserve⟩ :=
    hcover (I := I) E T G D.dependentQuotientMap hA (hTc.mono T hvA) hSc.1 hproj
  obtain ⟨V₀, hV₀, hVlip, hVobs⟩ := hpreserve (V.mono hvA)
  refine ⟨d, hd, G, S, hSF, hSc.mono S hAC, hdiv, hcoords,
    (fun i j => (hproj i j).trans hAC), Λ, hΛ, hchar, hnormal, hfinite,
    hindex.trans (Real.exp_le_exp.mpr hKC), m, hm, hin, hout,
    hcoverT.mono _ hKC, hmap, V₀.mono hKC, hV₀, hVlip, hVobs, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.DependentQuotient)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 G.basis
  obtain ⟨k, hk, hkbound, U, hU⟩ := hunit
  refine ⟨k, hk, hkbound.trans (Real.exp_le_exp.mpr hAC), U.mono hAC, ?_, ?_, ?_⟩
  · intro x hx
    change U.frequency (D.dependentQuotientMap x) = V.frequency x
    rw [hU, hV]
    exact hξ x hx
  · intro z hz
    change ∃ a : ℤ, realifyFunctional U.frequency z.coord = a
    rw [hU]
    exact hint z hz
  · intro σ w
    have hfreq₀ : V₀.frequency = J.freeFrequency D := hV₀.trans hV
    have hfreqU : ∀ x ∈ D.coefficientFreeFiltration.layer s (r + 1),
        (U.mono hAK).frequency (D.dependentQuotientMap x) = J.freeFrequency D x := by
      intro x hx
      change U.frequency (D.dependentQuotientMap x) = _
      rw [hU]
      exact hξ x hx
    have h := hcomparison D J (E.withLattice Λ m hm hin hout) G
      (T.withLattice Λ m hm hin hout) S I (Fin k) σ V₀ (U.mono hAK) hmap
      hT hSF hK hcoverT (hSc.mono S hAK) (fun i j => (hproj i j).trans hAK)
      hfreq₀ hfreqU w
    exact h.mono hcomparisonC

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeCoefficientCorrectionControl
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N n : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
  (T : E.DegreeRankStructure r) (hT : T.filtration = D.coefficientFreeFiltration)

include T hT

theorem exists_native_freeCoefficientPolynomialOrbit
    (v : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (hv : ∀ d, v d ∈ (D.coefficientFreeSpan d).baseChange ℝ) :
    ∃ u : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      u.log = positiveUnivariate v ∧
      E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 := by
  have hfil := D.coefficientFreeRealFiltration_eq_native E T hT
  have hlayer (d : Fin s) : v d ∈ E.filtration.realification.layer (d.val + 1) := by
    rw [← hfil]
    change v d ∈ (D.coefficientFreeFiltration.layer (d.val + 1) 0).baseChange ℝ
    rw [D.coefficientFreeFiltration.rank_zero_eq_one]
    exact Submodule.baseChange_mono ℝ (D.coefficientFreeSpan_le_layer d) (hv d)
  have hadapt : E.filtration.realification.Adapted (fun _ : Unit => 1)
      (positiveUnivariate v) := by
    apply (E.filtration.realification.adapted_iff_coefficients _ _).mpr
    apply positiveUnivariate_coefficients_mem
    intro d
    simpa only [Finsupp.weight_single, smul_eq_mul, mul_one] using hlayer d
  let u := NilpotentLieFiltration.polynomialOrbitOfLog (positiveUnivariate v) hadapt
  refine ⟨u, rfl, ?_⟩
  apply NilpotentLieBCHGroup.ext
  change eval (fun _ : Unit => (0 : ℚ)) (positiveUnivariate v) = 0
  rw [eval_zero_eq_coefficient, positiveUnivariate_zero]

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N n : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
  (T : E.DegreeRankStructure r) (hT : T.filtration = D.coefficientFreeFiltration)

include T hT

theorem exists_native_freeCoefficient_corrections
    (γ e q : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (hγ : ∀ d, γ d ∈ (D.coefficientFreeSpan d).baseChange ℝ)
    (he : ∀ d, e d ∈ (D.coefficientFreeSpan d).baseChange ℝ)
    (hq : ∀ d, q d ∈ (D.coefficientFreeSpan d).baseChange ℝ)
    (l : Fin s → ℕ) (hl : ∀ d, 0 < l d) {L : ℝ}
    (hlb : ∀ d, (l d : ℝ) ≤ Real.exp L)
    (herr : ∀ d, ‖(E.basis.baseChange ℝ).equivFun (e d)‖ ≤
      Real.exp L / (N : ℝ) ^ (d.val + 1))
    (hgrid : ∀ d, (E.basis.baseChange ℝ).equivFun (q d) ∈ realDenominatorGrid (l d)) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((s : ℝ) * L) ∧ (∀ d, l d ∣ m) ∧
      ∃ Γ ε ρ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
        Γ.log = positiveUnivariate γ ∧ ε.log = positiveUnivariate e ∧
        ρ.log = positiveUnivariate q ∧
        E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 Γ = 1 ∧
        E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ε = 1 ∧
        E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ρ = 1 ∧
        CoefficientBound (E.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
          (Real.exp L) ε.log ∧
        CoefficientGrid (E.basis.baseChange ℝ) m ρ.log := by
  classical
  obtain ⟨Γ, hΓ, hΓ0⟩ := D.exists_native_freeCoefficientPolynomialOrbit E T hT γ hγ
  obtain ⟨ε, hε, hε0⟩ := D.exists_native_freeCoefficientPolynomialOrbit E T hT e he
  obtain ⟨ρ, hρ, hρ0⟩ := D.exists_native_freeCoefficientPolynomialOrbit E T hT q hq
  let m := ∏ d, l d
  have hm : 0 < m := Finset.prod_pos (fun d _ => hl d)
  have hdiv (d : Fin s) : l d ∣ m := Finset.dvd_prod_of_mem l (Finset.mem_univ d)
  have hmb : (m : ℝ) ≤ Real.exp ((s : ℝ) * L) := by
    change ((∏ d, l d : ℕ) : ℝ) ≤ _
    rw [Nat.cast_prod]
    calc
      _ ≤ ∏ _d : Fin s, Real.exp L :=
        Finset.prod_le_prod (fun d _ => Nat.cast_nonneg (l d)) (fun d _ => hlb d)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.exp_nat_mul]
  refine ⟨m, hm, hmb, hdiv, Γ, ε, ρ, hΓ, hε, hρ, hΓ0, hε0, hρ0, ?_, ?_⟩
  · rw [hε]
    apply positiveUnivariate_coefficientBound (E.basis.baseChange ℝ) e
      (fun _ : Unit => (N : ℝ)) (fun _ => by exact_mod_cast NeZero.pos N) (Real.exp_pos L).le
    intro d
    simpa only [monomialScale, Finsupp.prod_single_index, pow_zero] using herr d
  · rw [hρ]
    apply positiveUnivariate_coefficientGrid
    intro d
    exact realDenominatorGrid_subset_of_dvd (hl d) (hdiv d) (hgrid d)

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MarkedDirectionLatticeScale
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

theorem direction_lattice_scale_bound (d t B H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p)
    (hB : (B : ℝ) ≤ Real.exp p) (hH : (H : ℝ) ≤ Real.exp p) :
    ((B * H ^ (d * t) : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
  rw [Nat.cast_mul, Nat.cast_pow]
  calc
    _ ≤ Real.exp p * (Real.exp p) ^ (d * t) :=
      mul_le_mul hB (pow_le_pow_left₀ (Nat.cast_nonneg _) hH _) (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (p + (d * t : ℕ) * p) := by rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hdt : (d : ℝ) * t ≤ p * p :=
        mul_le_mul hd ht (Nat.cast_nonneg _) hp
      have hmul := mul_le_mul_of_nonneg_right hdt hp
      push_cast
      nlinarith only [hp, hmul, sq_nonneg p]

namespace RationalFilteredNilmanifold

variable {L V : Type*} [LieRing L] [LieAlgebra ℚ L] [AddCommGroup V] [Module ℚ V]
  {s d t : ℕ} (E : RationalFilteredNilmanifold L s d) (e : Basis (Fin t) ℚ V)
  (φ : V →ₗ[ℚ] L)

theorem exists_direction_lattice_scale {H : ℕ}
    (hφ : ∀ i j, RationalHeightLE (E.basis.repr (φ (e i)) j) H) :
    ∃ m : ℕ, 0 < m ∧ m ≤ E.grid * H ^ (d * t) ∧
      ∀ x : V, IntegralVector (e.equivFun x) →
        (⟨(m : ℚ) • φ x⟩ : E.filtration.Group) ∈ E.lattice := by
  classical
  let A := LinearMap.toMatrix e E.basis φ
  let m := E.grid * matrixDenominator A
  have hA : ∀ j i, RationalHeightLE (A j i) H := by
    intro j i
    simpa only [A, LinearMap.toMatrix_apply] using hφ i j
  have hm : m ≤ E.grid * H ^ (d * t) := by
    exact Nat.mul_le_mul_left _ (by simpa only [Fintype.card_fin] using matrixDenominator_le A hA)
  refine ⟨m, Nat.mul_pos E.grid_pos (matrixDenominator_pos A), hm, ?_⟩
  intro x hx
  apply (bchSubgroupCoordinates_repr E.basis E.lattice _).mp
  apply E.inner_grid
  have he : A *ᵥ e.equivFun x = E.basis.equivFun (φ x) :=
    LinearMap.toMatrix_mulVec_repr e E.basis φ x
  have hint := integralVector_denominator_mulVec A (e.equivFun x) hx
  rw [he] at hint
  obtain ⟨z, hz⟩ := hint
  refine ⟨z, ?_⟩
  change E.basis.equivFun ((m : ℚ) • φ x) = _
  calc
    _ = (E.grid : ℚ) • ((matrixDenominator A : ℚ) • E.basis.equivFun (φ x)) := by
      simp only [m, Nat.cast_mul, map_smul, mul_smul]
    _ = _ := congrArg (fun v : Fin d → ℚ => (E.grid : ℚ) • v) (funext hz)

theorem exists_direction_lattice_scale_with_budget {H : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p)
    (hgrid : (E.grid : ℝ) ≤ Real.exp p) (hH : (H : ℝ) ≤ Real.exp p)
    (hφ : ∀ i j, RationalHeightLE (E.basis.repr (φ (e i)) j) H) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 3) ∧
      ∀ x : V, IntegralVector (e.equivFun x) →
        (⟨(m : ℚ) • φ x⟩ : E.filtration.Group) ∈ E.lattice := by
  obtain ⟨m, hm, hmb, hmem⟩ := E.exists_direction_lattice_scale e φ hφ
  exact ⟨m, hm, (Nat.cast_le.mpr hmb).trans
    (direction_lattice_scale_bound d t E.grid H hp hd ht hgrid hH), hmem⟩

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r k d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ) (E : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) k d)

theorem exists_marked_direction_lattice_scale {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) (hgrid : (E.grid : ℝ) ≤ Real.exp p)
    (hdir : ∀ i j, rationalLogHeight
      (E.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 3) ^ 3) ∧
      ∀ a : Fin t → ℤ,
        (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
          E.filtration.Group) ∈ E.lattice := by
  have hp1 : p ≤ p + 1 := le_add_of_nonneg_right zero_le_one
  obtain ⟨m, hm, hmb, hmem⟩ := E.exists_direction_lattice_scale_with_budget (RationalTorus.basis t)
    (markedQuotientDirectionLinear F v w marked t)
    (p := p + 1) (hp.trans hp1) (hd.trans hp1) (ht.trans hp1)
    (hgrid.trans (Real.exp_le_exp.mpr hp1)) (ceil_exp_le_exp_add_one hp)
    (fun i j => rationalHeightLE_ceil_exp (hdir i j))
  refine ⟨m, hm, ?_, ?_⟩
  · simpa only [add_assoc, show (1 : ℝ) + 2 = 3 by norm_num] using hmb
  · intro a
    exact hmem (fun i => (a i : ℚ))
      ⟨a, fun i => congrFun (RationalTorus.basis_equivFun t (fun j => (a j : ℚ))) i⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonAffineOrbitEvaluation
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators TensorProduct

namespace VectorPolynomial

variable {σ L : Type*} [AddCommGroup L] [Module ℚ L]

noncomputable def monomialLinearMap (α : σ →₀ ℕ) : L →ₗ[ℚ] VectorPolynomial σ ℚ L where
  toFun := monomial α
  map_add' x y := by simp only [monomial, TensorProduct.tmul_add]
  map_smul' a x := by
    change monomial α (a • x) = a • monomial α x
    simp only [monomial, TensorProduct.tmul_smul]

theorem realMonomial_eval (α : σ →₀ ℕ) (x : ℝ ⊗[ℚ] L) (a : σ → ℚ) :
    (eval a).baseChange ℝ ((monomialLinearMap α).baseChange ℝ x) =
      (α.prod (fun i n => a i ^ n)) • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    change r ⊗ₜ[ℚ] eval a (monomial α x) = (α.prod (fun i n => a i ^ n)) • (r ⊗ₜ[ℚ] x)
    rw [eval_monomial, TensorProduct.tmul_smul]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

noncomputable def realAffinePolynomial [Fintype σ] (x : ℝ ⊗[ℚ] L) (y : σ → ℝ ⊗[ℚ] L) :
    ℝ ⊗[ℚ] VectorPolynomial σ ℚ L :=
  (monomialLinearMap (0 : σ →₀ ℕ)).baseChange ℝ x +
    ∑ i, (monomialLinearMap (Finsupp.single i 1)).baseChange ℝ (y i)

theorem realAffinePolynomial_eval [Fintype σ] (x : ℝ ⊗[ℚ] L) (y : σ → ℝ ⊗[ℚ] L) (a : σ → ℚ) :
    (eval a).baseChange ℝ (realAffinePolynomial x y) = x + ∑ i, a i • y i := by
  classical
  simp only [realAffinePolynomial, map_add, map_sum, realMonomial_eval,
    Finsupp.prod_zero_index, one_smul, Finsupp.prod_single_index, pow_one, pow_zero]

end VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realMonomial_mem_markedPolynomialLayer
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (d k l : ℕ) (α : σ →₀ ℕ)
    {x : ℝ ⊗[ℚ] L}
    (hx : x ∈ (markedLieSpan v w marked d (k + Finsupp.weight (fun _ : σ => 1) α) l).baseChange ℝ) :
    (monomialLinearMap α).baseChange ℝ x ∈
      (markedPolynomialLayer v w marked d k l).baseChange ℝ := by
  have hmap : (markedLieSpan v w marked d (k + Finsupp.weight (fun _ : σ => 1) α) l).map
      (monomialLinearMap α) ≤ markedPolynomialLayer v w marked d k l := by
    rintro z ⟨y, hy, rfl⟩
    exact monomial_mem_markedPolynomialLayer v w marked d k l α hy
  have h := Submodule.baseChange_mono ℝ hmap
  rw [realification_map] at h
  exact h ⟨x, hx, rfl⟩

theorem realAffinePolynomial_mem_marked [Fintype σ]
    (v : I → L) (w : I → ℕ) (marked : I → Bool) {d k l : ℕ}
    {x : ℝ ⊗[ℚ] L} {y : σ → ℝ ⊗[ℚ] L}
    (hx : x ∈ (markedLieSpan v w marked d k l).baseChange ℝ)
    (hy : ∀ i, y i ∈ (markedLieSpan v w marked d (k + 1) l).baseChange ℝ) :
    realAffinePolynomial x y ∈ (markedPolynomialLayer v w marked d k l).baseChange ℝ := by
  apply Submodule.add_mem
  · apply realMonomial_mem_markedPolynomialLayer v w marked d k l 0
    simpa only [map_zero, Nat.add_zero] using hx
  · apply Submodule.sum_mem
    intro i _
    apply realMonomial_mem_markedPolynomialLayer v w marked d k l (Finsupp.single i 1)
    simpa only [Finsupp.weight_single, one_smul] using hy i

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

noncomputable def correlationExponent (h n : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 h + Finsupp.single 1 n

@[simp] theorem correlationExponent_apply (h n : ℕ) (i : Fin 2) :
    correlationExponent h n i = correlationInput h n i := by
  fin_cases i
  · change correlationExponent h n 0 = h
    simp [correlationExponent]
  · change correlationExponent h n 1 = n
    simp [correlationExponent]

theorem eval_correlation_monomial {L : Type*} [AddCommGroup L] [Module ℚ L]
    (h n : ℕ) (v : L) (x : Fin 2 → ℚ) :
    eval x (monomial (correlationExponent h n) v) = (x 0 ^ h * x 1 ^ n) • v := by
  classical
  rw [eval_monomial]
  simp [correlationExponent, Finsupp.prod_add_index, pow_add]

noncomputable def affineMixedLog {L : Type*} [AddCommGroup L] [Module ℚ L]
    {m : ℕ} (c d : Fin m → L) : VectorPolynomial (Fin 2) ℚ L :=
  ∑ j, (monomial (correlationExponent 0 (j.val + 1)) (c j) +
    monomial (correlationExponent 1 (j.val + 1)) (d j))

theorem affineMixedLog_eval {L : Type*} [AddCommGroup L] [Module ℚ L]
    {m : ℕ} (c d : Fin m → L) (x : Fin 2 → ℚ) :
    eval x (affineMixedLog c d) =
      ∑ j, x 1 ^ (j.val + 1) • (c j + x 0 • d j) := by
  simp only [affineMixedLog, map_sum, map_add, eval_correlation_monomial,
    pow_zero, one_mul, pow_one, smul_add, smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm (x 0)]

namespace MultidegreeLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s m : ℕ} {bound : Fin 2 → ℕ}
  (F : MultidegreeLieFiltration (Fin 2) L s bound)
  (c d : Fin m → L)
  (hc : ∀ j, c j ∈ F.layer (correlationInput 0 (j.val + 1)))
  (hd : ∀ j, d j ∈ F.layer (correlationInput 1 (j.val + 1)))

include hc hd in
theorem affineMixedLog_adapted : F.Adapted (affineMixedLog c d) := by
  apply F.adaptedSubmodule.sum_mem
  intro j _
  apply F.adaptedSubmodule.add_mem
  · apply F.monomial_mem_adaptedSubmodule
    simpa only [correlationExponent_apply] using hc j
  · apply F.monomial_mem_adaptedSubmodule
    simpa only [correlationExponent_apply] using hd j

noncomputable def affineMixedOrbit : F.PolynomialOrbit :=
  F.polynomialOrbitOfLog (affineMixedLog c d) (F.affineMixedLog_adapted c d hc hd)

theorem affineMixedOrbit_eval (x : Fin 2 → ℤ) :
    (F.polynomialOrbitEval x (F.affineMixedOrbit c d hc hd)).coord =
      ∑ j, (x 1 : ℚ) ^ (j.val + 1) • (c j + (x 0 : ℚ) • d j) :=
  affineMixedLog_eval c d _

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)

theorem markedShiftLayerPolynomialMap_mem (t d k l : ℕ)
    (p : markedPolynomialLayer (σ := Fin t) v w marked d k l) :
    markedShiftLayerPolynomialMap F v w marked hw hv t d k l p ∈
      markedShiftBiLayer F v w marked t k d := by
  refine ⟨?_, fun _ => rfl⟩
  exact markedPolynomialLayer_antitone v w marked le_rfl le_rfl (Nat.zero_le l) p.property

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  (t l : ℕ) (x : Fin s → L) (y : Fin s → Fin t → L)
  (hx : ∀ j, x j ∈ markedLieSpan v w marked (j.val + 1) 0 l)
  (hy : ∀ j i, y j i ∈ markedLieSpan v w marked (j.val + 1) 1 l)
  (u : Fin t → ℚ)

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)

noncomputable def realMarkedPolynomialLift (t d k l : ℕ) :
    (markedPolynomialLayer (σ := Fin t) v w marked d k l).baseChange ℝ →ₗ[ℝ]
      ℝ ⊗[ℚ] (markedShiftSubalgebra F v w marked t) :=
  ((markedShiftLayerPolynomialMap F v w marked hw hv t d k l).baseChange ℝ).comp
    (realificationSubmoduleEquiv (markedPolynomialLayer (σ := Fin t) v w marked d k l)).symm.toLinearMap

theorem realMarkedPolynomialLift_mem (t d k l : ℕ)
    (p : (markedPolynomialLayer (σ := Fin t) v w marked d k l).baseChange ℝ) :
    realMarkedPolynomialLift F v w marked hw hv t d k l p ∈
      (markedShiftBiLayer F v w marked t k d).baseChange ℝ := by
  obtain ⟨z, rfl⟩ := (realificationSubmoduleEquiv _).surjective p
  change (markedShiftLayerPolynomialMap F v w marked hw hv t d k l).baseChange ℝ
    ((realificationSubmoduleEquiv _).symm (realificationSubmoduleEquiv _ z)) ∈ _
  rw [LinearEquiv.symm_apply_apply]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a z =>
    rw [LinearMap.baseChange_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem a
      (markedShiftLayerPolynomialMap_mem F v w marked hw hv t d k l z)
  | add z z' hz hz' => simpa only [map_add] using Submodule.add_mem _ hz hz'

theorem realMarkedPolynomialLift_eval (t d k l : ℕ)
    (p : (markedPolynomialLayer (σ := Fin t) v w marked d k l).baseChange ℝ) (a : Fin t → ℚ) :
    (markedShiftEval F v w marked t a).baseChange ℝ
      (realMarkedPolynomialLift F v w marked hw hv t d k l p) =
        (eval a).baseChange ℝ p.val := by
  obtain ⟨z, rfl⟩ := (realificationSubmoduleEquiv _).surjective p
  change (markedShiftEval F v w marked t a).baseChange ℝ
    ((markedShiftLayerPolynomialMap F v w marked hw hv t d k l).baseChange ℝ
      ((realificationSubmoduleEquiv _).symm (realificationSubmoduleEquiv _ z))) = _
  rw [LinearEquiv.symm_apply_apply]
  rw [realificationSubmoduleEquiv_coe]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a z => rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

noncomputable def realMarkedQuotientCoefficient (t d k l : ℕ) :
    (markedPolynomialLayer (σ := Fin t) v w marked d k l).baseChange ℝ →ₗ[ℝ]
      ℝ ⊗[ℚ] (MarkedShiftQuotient F v w marked t) :=
  ((lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ).comp
    (realMarkedPolynomialLift F v w marked hw hv t d k l)

theorem realMarkedPolynomialLift_quotient_mem (t d k l : ℕ)
    (p : (markedPolynomialLayer (σ := Fin t) v w marked d k l).baseChange ℝ) :
    realMarkedQuotientCoefficient F v w marked hw hv t d k l p ∈
        (markedShiftMultidegree F v w marked hw hv t).realification.layer (correlationInput k d) := by
  change _ ∈ ((markedShiftBiLayer F v w marked t k d).map
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap).baseChange ℝ
  rw [realification_map]
  exact ⟨_, realMarkedPolynomialLift_mem F v w marked hw hv t d k l p, rfl⟩

variable (t l : ℕ)
  (c : ∀ j : Fin s, (markedPolynomialLayer (σ := Fin t) v w marked (j.val + 1) 0 l).baseChange ℝ)
  (d : ∀ j : Fin s, (markedPolynomialLayer (σ := Fin t) v w marked (j.val + 1) 1 l).baseChange ℝ)

noncomputable def realMarkedAffineMixedOrbit :
    (markedShiftMultidegree F v w marked hw hv t).realification.PolynomialOrbit :=
  (markedShiftMultidegree F v w marked hw hv t).realification.affineMixedOrbit
    (fun j => realMarkedQuotientCoefficient F v w marked hw hv t (j.val + 1) 0 l (c j))
    (fun j => realMarkedQuotientCoefficient F v w marked hw hv t (j.val + 1) 1 l (d j))
    (fun j => realMarkedPolynomialLift_quotient_mem F v w marked hw hv t (j.val + 1) 0 l (c j))
    (fun j => realMarkedPolynomialLift_quotient_mem F v w marked hw hv t (j.val + 1) 1 l (d j))

theorem realMarkedAffineMixedOrbit_eval (h n : ℤ) :
    ((markedShiftMultidegree F v w marked hw hv t).realification.polynomialOrbitEval
      (correlationInput h n) (realMarkedAffineMixedOrbit F v w marked hw hv t l c d)).coord =
        ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
          (realMarkedQuotientCoefficient F v w marked hw hv t (j.val + 1) 0 l (c j) +
          (h : ℚ) • realMarkedQuotientCoefficient F v w marked hw hv t (j.val + 1) 1 l (d j)) :=
  MultidegreeLieFiltration.affineMixedOrbit_eval _ _ _ _ _ (correlationInput h n)

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ) (u : Fin t → ℝ)

noncomputable def realAffineMarkedBase (j : Fin s) :
    (D.dependentPolynomialLayer (σ := Fin t) (j.val + 1) 0 1).baseChange ℝ :=
  ⟨realAffinePolynomial (x j).val (fun i => (y j i).val),
    realAffinePolynomial_mem_marked D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
      (Submodule.baseChange_mono ℝ (D.coefficientFreeSpan_le_dependentWordLayer j) (x j).property)
      (fun i => Submodule.baseChange_mono ℝ (D.dependentFreeSpan_le_dependentWordLayer j) (y j i).property)⟩

noncomputable def realAffineMarkedSlope (j : Fin s) :
    (D.dependentPolynomialLayer (σ := Fin t) (j.val + 1) 1 1).baseChange ℝ := by
  let z := ∑ i, u i • (y j i).val
  refine ⟨(monomialLinearMap (0 : Fin t →₀ ℕ)).baseChange ℝ z, ?_⟩
  apply realMonomial_mem_markedPolynomialLayer
  simp only [map_zero, Nat.add_zero]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact Submodule.baseChange_mono ℝ (D.dependentFreeSpan_le_dependentWordLayer j) (y j i).property

theorem realAffineMarkedBase_eval (j : Fin s) (a : Fin t → ℚ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t a).baseChange ℝ
        (realMarkedPolynomialLift D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
          D.coefficientFreeGenerator_mem_layer t (j.val + 1) 0 1 (D.realAffineMarkedBase t x y j)) =
            (x j).val + ∑ i, a i • (y j i).val := by
  exact (realMarkedPolynomialLift_eval D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t (j.val + 1) 0 1 (D.realAffineMarkedBase t x y j) a).trans
      (realAffinePolynomial_eval (x j).val (fun i => (y j i).val) a)

theorem realAffineMarkedSlope_eval (j : Fin s) (a : Fin t → ℚ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t a).baseChange ℝ
        (realMarkedPolynomialLift D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
          D.coefficientFreeGenerator_mem_layer t (j.val + 1) 1 1 (D.realAffineMarkedSlope t y u j)) =
            ∑ i, u i • (y j i).val := by
  apply (realMarkedPolynomialLift_eval D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t (j.val + 1) 1 1 (D.realAffineMarkedSlope t y u j) a).trans
  change (eval a).baseChange ℝ ((monomialLinearMap 0).baseChange ℝ (∑ i, u i • (y j i).val)) = _
  rw [realMonomial_eval, Finsupp.prod_zero_index, one_smul]

noncomputable def commonAffineMarkedOrbit : (D.markedQuotientMultidegree t).realification.PolynomialOrbit :=
  realMarkedAffineMixedOrbit D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t 1 (D.realAffineMarkedBase t x y) (D.realAffineMarkedSlope t y u)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ) (u : Fin t → ℝ)

noncomputable def commonAffineMarkedLift (h n : ℤ) :
    ℝ ⊗[ℚ] markedShiftSubalgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t :=
  ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
    (realMarkedPolynomialLift D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t (j.val + 1) 0 1 (D.realAffineMarkedBase t x y j) +
    (h : ℚ) • realMarkedPolynomialLift D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t (j.val + 1) 1 1 (D.realAffineMarkedSlope t y u j))

theorem commonAffineMarkedOrbit_eval (h n : ℤ) :
    ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval (correlationInput h n)
      (D.commonAffineMarkedOrbit t x y u)).coord =
        (lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
            (D.commonAffineMarkedLift t x y u h n) := by
  have he := realMarkedAffineMixedOrbit_eval D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t 1 (D.realAffineMarkedBase t x y) (D.realAffineMarkedSlope t y u) h n
  apply he.trans
  simp only [commonAffineMarkedLift, map_sum, LinearMap.map_smul_of_tower, map_add]
  rfl

theorem commonAffineMarkedLift_eval (a : Fin t → ℚ) (h n : ℤ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t a).baseChange ℝ
        (D.commonAffineMarkedLift t x y u h n) =
          ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
            ((x j).val + ∑ i, ((a i : ℝ) + (h : ℝ) * u i) • (y j i).val) := by
  simp only [commonAffineMarkedLift, map_sum, LinearMap.map_smul_of_tower, map_add]
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun z : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra => (n : ℚ) ^ (j.val + 1) • z)
  calc
    _ = ((x j).val + ∑ i, a i • (y j i).val) + (h : ℚ) • (∑ i, u i • (y j i).val) :=
      congrArg₂ (fun z z' : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra => z + (h : ℚ) • z')
        (D.realAffineMarkedBase_eval t x y j a) (D.realAffineMarkedSlope_eval t y u j a)
    _ = _ := by
      simp only [add_smul, Finset.sum_add_distrib, Finset.smul_sum,
        ← Rat.cast_smul_eq_qsmul ℝ, Rat.cast_intCast, smul_smul, add_assoc]

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedUnitOrbit
namespace OAI

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N)

noncomputable def localAffineMarkedBase (j : Fin s) : (D.coefficientFreeSpan j).baseChange ℝ :=
  ⟨(x j).val + ∑ i, (-(h₀.val : ℝ) * u i - c i) • (y j i).val,
    Submodule.add_mem _ (x j).property (Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ _ (Submodule.baseChange_mono ℝ
        (D.dependentFreeSpan_le_coefficientFreeSpan j) (y j i).property)))⟩

noncomputable def localAffineMarkedLift (h : ZMod N) (n : ℤ) :
    ℝ ⊗[ℚ] markedShiftSubalgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t :=
  D.commonAffineMarkedLift t (D.localAffineMarkedBase t x y u c h₀) y u h.val n

theorem localAffineMarkedLift_eval (h : ZMod N) (n : ℤ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t
        (fun i => (-affineCyclicTorusCarry u c h₀ h i : ℤ))).baseChange ℝ
          (D.localAffineMarkedLift t x y u c h₀ h n) =
            ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
              ((x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val) := by
  apply (D.commonAffineMarkedLift_eval t (D.localAffineMarkedBase t x y u c h₀) y u
    (fun i => (-affineCyclicTorusCarry u c h₀ h i : ℤ)) h.val n).trans
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun z : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra => (n : ℚ) ^ (j.val + 1) • z)
  change ((x j).val + ∑ i, (-(h₀.val : ℝ) * u i - c i) • (y j i).val) + _ = _
  rw [add_assoc, ← Finset.sum_add_distrib]
  apply congrArg ((x j).val + ·)
  apply Finset.sum_congr rfl
  intro i _
  rw [← add_smul]
  apply congrArg (fun a : ℝ => a • (y j i).val)
  simpa only [Int.cast_natCast, add_assoc] using affineCyclicTorusCarry_identity u c h₀ h i

theorem localAffineMarkedLift_eq_polynomial_eval
    (A : ZMod N → VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra))
    (h : ZMod N) (hA : A h = positiveUnivariate (fun j =>
      (x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val)) (n : ℤ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t
        (fun i => (-affineCyclicTorusCarry u c h₀ h i : ℤ))).baseChange ℝ
          (D.localAffineMarkedLift t x y u c h₀ h n) = eval (fun _ => (n : ℚ)) (A h) := by
  rw [D.localAffineMarkedLift_eval, hA]
  simp only [positiveUnivariate, map_sum, eval_monomial, Finsupp.prod_single_index, pow_zero]

end Erdos3.NativeRankRelation.CommonData

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial NilpotentLieBCHGroup
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N)

end Erdos3.NativeRankRelation.CommonData

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ)

end Erdos3.NativeRankRelation.CommonData

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial NilpotentLieBCHGroup
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ)

noncomputable def scaledLocalAffineCorrectingElement (h : ZMod N) :
    (D.markedQuotientMultidegree t).realification.Group :=
  ⟨realMarkedDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t ((m : ℚ) • fun i => ((-affineCyclicTorusCarry u c h₀ h i : ℤ) : ℚ))⟩

end Erdos3.NativeRankRelation.CommonData

namespace Erdos3.NativeRankRelation.CommonData

open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) {d : ℕ}
  (E : RationalFilteredNilmanifold
    (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t) (s + 1) d)
  (T : E.MultidegreeStructure (mixedCorrelationDegree s))
  (hT : T.filtration = D.markedQuotientMultidegree t)

variable [TopologicalSpace (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
  D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)]
  [T2Space (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)]

end Erdos3.NativeRankRelation.CommonData

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedParameterOrbit
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

noncomputable def realMarkedParameterOrbit (b a : Fin t → ℝ) :
    (markedShiftMultidegree F v w marked hw hv t).realification.PolynomialOrbit :=
  (markedShiftMultidegree F v w marked hw hv t).realification.polynomialOrbitOfLog
    (monomial 0 (realMarkedParameterDirection F v w marked t b) +
      monomial (correlationExponent 1 0) (realMarkedParameterDirection F v w marked t a)) (by
        apply (markedShiftMultidegree F v w marked hw hv t).realification.adaptedSubmodule.add_mem
        · apply MultidegreeLieFiltration.monomial_mem_adaptedSubmodule
          change _ ∈ (markedShiftMultidegree F v w marked hw hv t).realification.layer 0
          rw [MultidegreeLieFiltration.zero_eq_top]
          trivial
        · apply MultidegreeLieFiltration.monomial_mem_adaptedSubmodule
          simpa only [correlationExponent_apply] using
            realMarkedParameterDirection_mem_first F v w marked hw hv t a)

theorem realMarkedParameterOrbit_eval (b a : Fin t → ℝ) (h n : ℤ) :
    (markedShiftMultidegree F v w marked hw hv t).realification.polynomialOrbitEval
      (correlationInput h n) (realMarkedParameterOrbit F v w marked hw hv t b a) =
        realMarkedParameterElement F v w marked hw hv t (b + (h : ℝ) • a) := by
  apply NilpotentLieBCHGroup.ext
  change eval (fun i => ((correlationInput h n i : ℤ) : ℚ))
    (monomial 0 (realMarkedParameterDirection F v w marked t b) +
      monomial (correlationExponent 1 0) (realMarkedParameterDirection F v w marked t a)) =
        realMarkedParameterDirection F v w marked t (b + (h : ℝ) • a)
  rw [map_add, eval_correlation_monomial, eval_monomial]
  simp only [Finsupp.prod_zero_index, one_smul, pow_one, pow_zero, mul_one]
  change realMarkedParameterDirection F v w marked t b +
    (h : ℚ) • realMarkedParameterDirection F v w marked t a =
      realMarkedParameterDirection F v w marked t (b + (h : ℝ) • a)
  rw [map_add, map_smul]
  apply congrArg (realMarkedParameterDirection F v w marked t b + ·)
  simpa only [Rat.cast_intCast] using
    (Rat.cast_smul_eq_qsmul ℝ (h : ℚ) (realMarkedParameterDirection F v w marked t a)).symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RealMarkedAffineShift
namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped BigOperators TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

noncomputable def realMarkedAffineShift (a : Fin t → ℝ) :
    (ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) →ₗ[ℝ]
      (ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :=
  LinearMap.id + ∑ i, a i •
    ((markedShiftTranslate F v w marked hw hv t (Pi.single i 1)).baseChange ℝ - LinearMap.id)

theorem realMarkedAffineShift_apply (a : Fin t → ℝ)
    (p : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    realMarkedAffineShift F v w marked hw hv t a p =
      p + ∑ i, a i •
        ((markedShiftTranslate F v w marked hw hv t (Pi.single i 1)).baseChange ℝ p - p) := by
  simp only [realMarkedAffineShift, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply]

theorem realMarkedAffineShift_quotient (a : Fin t → ℝ)
    (p : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ
        (realMarkedAffineShift F v w marked hw hv t a p) =
      (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ p +
        ⁅realMarkedParameterDirection F v w marked t a,
          (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ p⁆ := by
  let q := (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ
  have hb : ⁅realMarkedParameterDirection F v w marked t a, q p⁆ =
      ∑ i, a i • ⁅realMarkedDirection F v w marked t (Pi.single i 1), q p⁆ := by
    apply (congrArg (fun z : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t => ⁅z, q p⁆)
      (realMarkedParameterDirection_apply F v w marked t a)).trans
    apply (sum_lie Finset.univ
      (fun i => a i • realMarkedDirection F v w marked t (Pi.single i 1)) (q p)).trans
    apply Finset.sum_congr rfl
    intro i _
    exact smul_lie (R := ℝ) (a i) (realMarkedDirection F v w marked t (Pi.single i 1)) (q p)
  calc
    q (realMarkedAffineShift F v w marked hw hv t a p) = q p +
        ∑ i, a i • (q ((markedShiftTranslate F v w marked hw hv t (Pi.single i 1)).baseChange ℝ p) - q p) := by
      rw [realMarkedAffineShift_apply F v w marked hw hv t a p]
      simp only [map_add, map_sum, map_smul, map_sub]
    _ = q p + ∑ i, a i • ⁅realMarkedDirection F v w marked t (Pi.single i 1), q p⁆ := by
      apply congrArg (q p + ·)
      apply Finset.sum_congr rfl
      intro i _
      have he := (realMarkedTranslate_quotient F v w marked hw hv t (Pi.single i 1) p).trans
        (realMarkedTranslate_first_order F v w marked hw hv t (Pi.single i 1) (q p))
      rw [he, add_sub_cancel_left]
    _ = _ := congrArg (q p + ·) hb.symm

theorem realMarkedAffineShift_conjugation (hs : 1 ≤ s) (a : Fin t → ℝ)
    (p : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    conjugationCoord (realMarkedParameterElement F v w marked hw hv t a)
        ((lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ p) =
      (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ
        (realMarkedAffineShift F v w marked hw hv t a p) :=
  (realMarkedParameterElement_conjugation F v w marked hw hv t hs a _).trans
    (realMarkedAffineShift_quotient F v w marked hw hv t a p).symm

theorem realMarkedAffineShift_eval (a : Fin t → ℝ)
    (p : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (markedShiftEval F v w marked t 0).baseChange ℝ
        (realMarkedAffineShift F v w marked hw hv t a p) =
      (markedShiftEval F v w marked t 0).baseChange ℝ p +
        ∑ i, a i • ((markedShiftEval F v w marked t (Pi.single i 1)).baseChange ℝ p -
          (markedShiftEval F v w marked t 0).baseChange ℝ p) := by
  rw [realMarkedAffineShift_apply, map_add, map_sum]
  apply congrArg ((markedShiftEval F v w marked t 0).baseChange ℝ p + ·)
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_sub, realMarkedShiftEval_translate, zero_add]

theorem realMarkedAffineShift_eval_affine (a : Fin t → ℝ)
    (p : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t)
    (x : ℝ ⊗[ℚ] L) (y : Fin t → ℝ ⊗[ℚ] L)
    (hp : ∀ b : Fin t → ℚ, (markedShiftEval F v w marked t b).baseChange ℝ p =
      x + ∑ i, (b i : ℝ) • y i) :
    (markedShiftEval F v w marked t 0).baseChange ℝ
        (realMarkedAffineShift F v w marked hw hv t a p) = x + ∑ i, a i • y i := by
  have h0 : (markedShiftEval F v w marked t 0).baseChange ℝ p = x := by
    simpa only [Pi.zero_apply, Rat.cast_zero, zero_smul, Finset.sum_const_zero, add_zero] using hp 0
  have hi (i : Fin t) : (markedShiftEval F v w marked t (Pi.single i 1)).baseChange ℝ p = x + y i := by
    simpa [Pi.single_apply, apply_ite] using hp (Pi.single i 1)
  rw [realMarkedAffineShift_eval, h0]
  simp only [hi, add_sub_cancel_left]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedMarkedChart
namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t m : ℕ)

theorem normalizedMarkedPhase_real_parameter (a : Fin t → ℝ) :
    torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
      (realMarkedParameterDirection F v w marked t a) = fun i => (m : ℝ)⁻¹ * a i := by
  classical
  have hsingle (j i : Fin t) :
      torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
        (realMarkedDirection F v w marked t (Pi.single j 1)) i =
          (m : ℝ)⁻¹ * (if j = i then 1 else 0) := by
    change torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
      ((1 : ℝ) ⊗ₜ[ℚ] markedQuotientDirection F v w marked t (Pi.single j 1)) i = _
    rw [torusPhaseLinear_tmul, _root_.one_mul, normalizedMarkedPhase_apply,
      markedQuotientPhase_direction]
    change (((m : ℚ)⁻¹ * (Pi.single j (1 : ℚ) : Fin t → ℚ) i : ℚ) : ℝ) = _
    by_cases hji : j = i
    · subst j
      simp
    · have hij : i ≠ j := Ne.symm hji
      simp [hji, hij]
  rw [realMarkedParameterDirection_apply, map_sum]
  funext i
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, hsingle]
  simp [mul_comm]

theorem normalizedMarkedPhase_real_scaled_parameter (hm : 0 < m) (a : Fin t → ℝ) :
    torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
      (realMarkedParameterDirection F v w marked t ((m : ℝ) • a)) = a := by
  rw [normalizedMarkedPhase_real_parameter]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hm.ne' : (m : ℝ) ≠ 0), _root_.one_mul]

theorem normalizedMarkedPhase_real_pure
    (z : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)
    (hz : z ∈ (markedQuotientPolynomialAlgebra F v w marked t).toSubmodule.baseChange ℝ) :
    torusPhaseLinear (normalizedMarkedPhase F v w marked t m) z = 0 := by
  have hker : (markedQuotientPolynomialAlgebra F v w marked t).toSubmodule ≤
      LinearMap.ker (normalizedMarkedPhase F v w marked t m).toLinearMap := by
    intro x hx
    change markedQuotientPhase F v w marked t x = 0 at hx
    change normalizedMarkedPhase F v w marked t m x = 0
    rw [normalizedMarkedPhase_apply, hx, smul_zero]
  have h := Submodule.baseChange_mono ℝ hker hz
  rw [realification_ker, LinearMap.mem_ker] at h
  change ((RationalTorus.basis t).baseChange ℝ).equivFun
    ((normalizedMarkedPhase F v w marked t m).toLinearMap.baseChange ℝ z) = 0
  rw [h, map_zero]

end Erdos3

namespace Erdos3.NativeRankRelation.CommonData

open NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedLocalCoefficientValue
namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t m : ℕ)
  (E : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)

theorem normalizedMarkedPhase_real_eq_zero_iff (hm : 0 < m)
    (z : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    torusPhaseLinear (normalizedMarkedPhase F v w marked t m) z = 0 ↔
      z ∈ (markedQuotientPolynomialAlgebra F v w marked t).toSubmodule.baseChange ℝ := by
  have hker : LinearMap.ker (normalizedMarkedPhase F v w marked t m).toLinearMap =
      LinearMap.ker (markedQuotientPhase F v w marked t).toLinearMap := by
    ext x
    change normalizedMarkedPhase F v w marked t m x = 0 ↔ markedQuotientPhase F v w marked t x = 0
    rw [normalizedMarkedPhase_apply]
    simp [show (m : ℚ) ≠ 0 by exact_mod_cast hm.ne']
  let e := ((RationalTorus.basis t).baseChange ℝ).equivFun
  change e ((normalizedMarkedPhase F v w marked t m).toLinearMap.baseChange ℝ z) = 0 ↔
    z ∈ (LinearMap.ker (markedQuotientPhase F v w marked t).toLinearMap).baseChange ℝ
  rw [← hker, realification_ker, LinearMap.mem_ker]
  constructor
  · intro hz
    exact e.injective (hz.trans (e.map_zero).symm)
  · intro hz
    rw [hz, map_zero]

noncomputable def normalizedMarkedRetraction (g : E.RealGroup) : E.RealGroup :=
  realMarkedParameterElement F v w marked hw hv t
    ((m : ℝ) • -(torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord)) * g

theorem normalizedMarkedRetraction_phase (hm : 0 < m) (g : E.RealGroup) :
    torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
      (normalizedMarkedRetraction F v w marked hw hv t m E g).coord = 0 := by
  unfold normalizedMarkedRetraction
  rw [torusPhaseLinear_mul E]
  change torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
    (realMarkedParameterDirection F v w marked t
      ((m : ℝ) • -(torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord))) +
        torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord = 0
  rw [normalizedMarkedPhase_real_scaled_parameter F v w marked t m hm]
  exact neg_add_cancel _

theorem normalizedMarkedRetraction_pure (hm : 0 < m) (g : E.RealGroup) :
    (normalizedMarkedRetraction F v w marked hw hv t m E g).coord ∈
      (markedQuotientPolynomialAlgebra F v w marked t).toSubmodule.baseChange ℝ :=
  (normalizedMarkedPhase_real_eq_zero_iff F v w marked t m hm _).mp
    (normalizedMarkedRetraction_phase F v w marked hw hv t m E hm g)

theorem normalizedMarkedRetraction_scaled_parameter (hm : 0 < m) (a : Fin t → ℝ) (g : E.RealGroup)
    (hg : torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord = 0) :
    normalizedMarkedRetraction F v w marked hw hv t m E
      (realMarkedParameterElement F v w marked hw hv t ((m : ℝ) • a) * g) = g := by
  have hphase : torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
      (realMarkedParameterElement F v w marked hw hv t ((m : ℝ) • a) * g).coord = a := by
    rw [torusPhaseLinear_mul E, hg, add_zero]
    exact normalizedMarkedPhase_real_scaled_parameter F v w marked t m hm a
  unfold normalizedMarkedRetraction
  rw [hphase, smul_neg, ← realMarkedParameterElement_inv]
  exact inv_mul_cancel_left _ _

end Erdos3

end

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d e u : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t m : ℕ) (hm : 0 < m)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)

noncomputable def normalizedMarkedPureRetraction (g : D.RealGroup) :
    realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (markedQuotientPolynomialAlgebra F v w marked t) :=
  ⟨normalizedMarkedRetraction F v w marked hw hv t m D g,
    normalizedMarkedRetraction_pure F v w marked hw hv t m D hm g⟩

variable (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
  (E : RationalFilteredNilmanifold (L ⧸ J) u e)
  (hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
    (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice)

noncomputable def markedLocalCoefficientValue (V : E.Space → ℂ) (g : D.RealGroup) : ℂ :=
  V (markedPureSpaceMap F v w marked t D J hJ E 0 hmap
    (QuotientGroup.mk (normalizedMarkedPureRetraction F v w marked hw hv t m hm D g)))

theorem markedLocalCoefficientValue_apply (V : E.Space → ℂ) (g : D.RealGroup) :
    markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V g =
      V (QuotientGroup.mk (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ
        (normalizedMarkedRetraction F v w marked hw hv t m D g).coord⟩ : E.RealGroup)) := rfl

theorem markedLocalCoefficientValue_scaled_parameter (V : E.Space → ℂ) (a : Fin t → ℝ) (g : D.RealGroup)
    (hg : torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord = 0) :
    markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V
      (realMarkedParameterElement F v w marked hw hv t ((m : ℝ) • a) * g) =
      V (QuotientGroup.mk (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ g.coord⟩ : E.RealGroup)) := by
  rw [markedLocalCoefficientValue_apply, normalizedMarkedRetraction_scaled_parameter F v w marked hw hv t m D hm a g hg]

theorem markedLocalCoefficientValue_eq_on_small_cosets
    (hphase : ∀ z : D.filtration.Group, z ∈ D.lattice →
      IntegralVector (normalizedMarkedPhase F v w marked t m z.coord))
    (V : E.Space → ℂ) (g h : D.RealGroup)
    (hg : ∀ i, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord i| ≤ 1 / 4)
    (hh : ∀ i, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) h.coord i| ≤ 1 / 4)
    (heq : (QuotientGroup.mk g : D.Space) = QuotientGroup.mk h) :
    markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V g =
      markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V h := by
  let φ := normalizedMarkedPhase F v w marked t m
  let R := normalizedMarkedPureRetraction F v w marked hw hv t m hm D
  have hph : torusPhaseLinear φ g.coord = torusPhaseLinear φ h.coord :=
    torusPhaseLinear_eq_of_small D φ hphase g h hg hh heq
  have hdiff : (R g)⁻¹ * R h ∈ D.realLattice.comap
      (realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (markedQuotientPolynomialAlgebra F v w marked t)).subtype := by
    change (normalizedMarkedRetraction F v w marked hw hv t m D g)⁻¹ *
      normalizedMarkedRetraction F v w marked hw hv t m D h ∈ D.realLattice
    have hcalc : (normalizedMarkedRetraction F v w marked hw hv t m D g)⁻¹ *
        normalizedMarkedRetraction F v w marked hw hv t m D h = g⁻¹ * h := by
      dsimp only [φ] at hph
      unfold normalizedMarkedRetraction
      rw [hph]
      group
    rw [hcalc]
    exact QuotientGroup.eq.mp heq
  have hq : (QuotientGroup.mk (R g) : _ ⧸ D.realLattice.comap
      (realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (markedQuotientPolynomialAlgebra F v w marked t)).subtype) = QuotientGroup.mk (R h) :=
    QuotientGroup.eq.mpr hdiff
  exact congrArg (fun x => V (markedPureSpaceMap F v w marked t D J hJ E 0 hmap x)) hq

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedMarkedLattice
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup

theorem exists_exact_source_lattice_cover {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
    (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hentries : ∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) :
    let Λ := D.lattice ⊓ E.lattice.comap (mapOfSteps
      (hL := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ)
    ∃ (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
      (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
      (N : ℝ) ≤ Real.exp ((p + 2) ^ 5) ∧
      (D.withLattice Λ N hN hin hout).GeometryComplexityLE ((p + 2) ^ 5) := by
  classical
  let A := LinearMap.toMatrix D.basis E.basis φ.toLinearMap
  let N := D.grid * (E.grid * matrixDenominator A)
  let Λ := D.lattice ⊓ E.lattice.comap (mapOfSteps
    (hL := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ)
  have hN : 0 < N := Nat.mul_pos D.grid_pos (Nat.mul_pos E.grid_pos (matrixDenominator_pos A))
  have hDN : D.grid ∣ N := dvd_mul_right _ _
  have hEN : E.grid * matrixDenominator A ∣ N := dvd_mul_left _ _
  have hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ := by
    intro x hx
    change (⟨D.basis.equivFun.symm x⟩ : D.filtration.Group) ∈ D.lattice ∧
      (⟨φ (D.basis.equivFun.symm x)⟩ : E.filtration.Group) ∈ E.lattice
    refine ⟨D.inner_grid (scaledIntegerGrid_subset_of_dvd hDN hx), ?_⟩
    apply (bchSubgroupCoordinates_repr E.basis E.lattice _).mp
    apply E.inner_grid
    apply linearMap_mem_scaledGrid D.basis E.basis φ.toLinearMap hEN
    simpa only [LinearEquiv.apply_symm_apply] using hx
  have hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N := by
    intro x hx
    exact denominatorGrid_subset_of_dvd hDN (D.outer_grid hx.1)
  have hA : (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    apply matrixDenominator_le_exp_power A hp 1
      (by simpa only [Fintype.card_fin] using hE.1)
      (by simpa only [Fintype.card_fin] using hD.1)
    intro i j
    dsimp only [A]
    rw [LinearMap.toMatrix_apply]
    exact ((rationalLogHeight_le_iff _ p).mp (hentries i j)).2.trans
      (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  have hNbound : (N : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
    have h := mul_le_mul hD.2.1 (mul_le_mul hE.2.1 hA (Nat.cast_nonneg _) (Real.exp_nonneg _))
      (by positivity) (Real.exp_nonneg _)
    have h' : (N : ℝ) ≤ Real.exp (p + (p + (p + 2) ^ 3)) := by
      simpa only [N, Nat.cast_mul, ← Real.exp_add] using h
    apply h'.trans (Real.exp_le_exp.mpr ?_)
    have hp3 : p ≤ (p + 2) ^ 3 := le_power_budget hp (by decide)
    calc
      p + (p + (p + 2) ^ 3) ≤ 3 * (p + 2) ^ 3 := by linarith
      _ ≤ (p + 2) ^ 2 * (p + 2) ^ 3 :=
        mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
      _ = (p + 2) ^ 5 := by ring
  exact ⟨N, hN, hin, hout, hNbound,
    D.withLattice_geometry Λ N hN hin hout hD (le_power_budget hp (by decide)) hNbound⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

namespace RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}

noncomputable def withLattice (M : D.MultidegreeStructure bound)
    (Λ : Subgroup D.filtration.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N) :
    (D.withLattice Λ N hN hin hout).MultidegreeStructure bound where
  filtration := M.filtration
  ordinary := M.ordinary
  basis := M.basis

theorem withLattice_complexity (M : D.MultidegreeStructure bound)
    (Λ : Subgroup D.filtration.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)
    {p P : ℝ} (hM : M.ComplexityLE p) (hpP : p ≤ P)
    (hD : (D.withLattice Λ N hN hin hout).GeometryComplexityLE P) :
    (M.withLattice Λ N hN hin hout).ComplexityLE P :=
  ⟨hD, fun a j k => (hM.2 a j k).trans hpP⟩

end RationalFilteredNilmanifold.MultidegreeStructure

theorem exists_marked_evaluation_lattice (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {r t d e u : ℕ}
      (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)
      (M : D.MultidegreeStructure (mixedCorrelationDegree s))
      (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
      (E : RationalFilteredNilmanifold (L ⧸ J) u e) {p : ℝ},
      0 ≤ p → M.ComplexityLE p → E.GeometryComplexityLE p → (t : ℝ) ≤ p →
      (∀ i j, rationalLogHeight
        (E.basis.repr (markedBaseEvaluation F v w marked t J hJ 0 (D.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (markedQuotientPhase F v w marked t (D.basis j) i) ≤ p) →
      ∃ (B : ℕ) (Λ : Subgroup D.filtration.Group) (hB : 0 < B)
        (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates D.basis Λ)
        (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid B),
        (B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ Λ ≤ D.lattice ∧
        bchSubgroupCoordinates D.basis Λ = scaledIntegerGrid B ∧
        (M.withLattice Λ B hB hin hout).ComplexityLE ((p + C) ^ C) ∧
        (∀ z : D.filtration.Group, z ∈ Λ →
          (⟨markedBaseEvaluation F v w marked t J hJ 0 z.coord⟩ : E.filtration.Group) ∈ E.lattice) ∧
        (∀ z : D.filtration.Group, z ∈ Λ →
          IntegralVector (markedQuotientPhase F v w marked t z.coord)) ∧
        ∀ z : D.RealGroup, z ∈ (D.withLattice Λ B hB hin hout).realLattice →
          (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈
            E.realLattice := by
  obtain ⟨C, hC, hcover⟩ := RationalFilteredNilmanifold.exists_native_linear_target_cover (s + 1)
  refine ⟨C, hC, ?_⟩
  intro I L _ _ r t d e u F v w marked D M J hJ E p hp hM hE ht hφ hψ
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast (show 1 ≤ C by omega)
  have hpC : p ≤ (p + C) ^ C := by
    calc
      p ≤ p + C := le_add_of_nonneg_right (Nat.cast_nonneg _)
      _ = (p + C) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega : 1 ≤ C)
  obtain ⟨B, Λ, hB, hin, hout, hbound, hΛ, hcoords, hgeom, hmap, hphase⟩ :=
    hcover D E (markedBaseEvaluation F v w marked t J hJ 0)
      (markedQuotientPhase F v w marked t).toLinearMap hp hM.1 hE ht hφ hψ
  refine ⟨B, Λ, hB, hin, hout, hbound, hΛ, hcoords,
    M.withLattice_complexity Λ B hB hin hout hM hpC hgeom, hmap, hphase, ?_⟩
  exact (D.withLattice Λ B hB hin hout).linearMap_real_lattice E
    (markedBaseEvaluation F v w marked t J hJ 0) hmap

end Erdos3

end

section

namespace Erdos3

open NilpotentLieBCHGroup

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t : ℕ)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d) (m : ℕ)

noncomputable def normalizedMarkedLattice : Subgroup D.filtration.Group :=
  D.lattice ⊓ (RationalTorus.nilmanifold t).lattice.comap
    (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
      (hM := (RationalTorus.nilmanifold t).filtration.lowerCentralSeries_eq_bot)
      (normalizedMarkedPhase F v w marked t m))

theorem normalizedMarkedLattice_le : normalizedMarkedLattice F v w marked t D m ≤ D.lattice :=
  inf_le_left

theorem normalizedMarkedLattice_integral (z : D.filtration.Group)
    (hz : z ∈ normalizedMarkedLattice F v w marked t D m) :
    IntegralVector (normalizedMarkedPhase F v w marked t m z.coord) := hz.2

theorem normalizedMarkedLattice_direction (hm : 0 < m) (a : Fin t → ℤ)
    (ha : (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
      D.filtration.Group) ∈ D.lattice) :
    (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
      D.filtration.Group) ∈ normalizedMarkedLattice F v w marked t D m := by
  refine ⟨ha, ?_⟩
  change IntegralVector (normalizedMarkedPhase F v w marked t m
    ((m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))))
  rw [normalizedMarkedPhase_scaled_direction F v w marked t m hm]
  exact ⟨a, fun _ => rfl⟩

theorem exists_normalizedMarkedLattice_model
    (M : D.MultidegreeStructure (mixedCorrelationDegree s)) {p : ℝ}
    (hp : 0 ≤ p) (hM : M.ComplexityLE p) (ht : (t : ℝ) ≤ p) (hm : 0 < m)
    (hmp : (m : ℝ) ≤ Real.exp p)
    (hcoords : ∀ i j, rationalLogHeight (markedQuotientPhase F v w marked t (D.basis j) i) ≤ p) :
    ∃ (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis (normalizedMarkedLattice F v w marked t D m))
      (hout : bchSubgroupCoordinates D.basis (normalizedMarkedLattice F v w marked t D m) ⊆ denominatorGrid N),
      (N : ℝ) ≤ Real.exp ((2 * p + 3) ^ 5) ∧
      (M.withLattice (normalizedMarkedLattice F v w marked t D m) N hN hin hout).ComplexityLE
        ((2 * p + 3) ^ 5) := by
  have hpP : p ≤ 2 * p + 1 := by linarith
  have hP : 0 ≤ 2 * p + 1 := hp.trans hpP
  have hentries (i j) : rationalLogHeight ((RationalTorus.nilmanifold t).basis.repr
      (normalizedMarkedPhase F v w marked t m (D.basis j)) i) ≤ 2 * p + 1 := by
    change rationalLogHeight ((RationalTorus.basis t).repr
      (normalizedMarkedPhase F v w marked t m (D.basis j)) i) ≤ _
    rw [RationalTorus.basis_repr]
    exact normalizedMarkedPhase_height F v w marked t m hm hp hmp (D.basis j) i (hcoords i j)
  obtain ⟨N, hN, hin, hout, hNbound, hgeom⟩ := D.exists_exact_source_lattice_cover
    (RationalTorus.nilmanifold t) (normalizedMarkedPhase F v w marked t m) hP
    (hM.1.mono D hpP) (RationalTorus.nilmanifold_geometry t hP (ht.trans hpP)) hentries
  have heq : 2 * p + 1 + 2 = 2 * p + 3 := by ring
  rw [heq] at hNbound hgeom
  have hpQ : p ≤ (2 * p + 3) ^ 5 := hpP.trans (by
    simpa only [heq] using le_power_budget hP (by decide : 1 ≤ 5))
  exact ⟨N, hN, hin, hout, hNbound,
    M.withLattice_complexity (normalizedMarkedLattice F v w marked t D m)
      N hN hin hout hM hpQ hgeom⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SharedFreeAffineBudget
namespace OAI

section

namespace Erdos3

open CyclicCrootSisask

noncomputable def affineRecoveryLogLoss (P : ℝ) (n : ℕ) : ℝ :=
  quarticBogolyubovProgressionConstant * (roundedModelLogBudget P n + 1) ^ 8 +
    (P + 13 * n) + 16 * ((n : ℝ) + 3)

theorem exp_neg_affineRecoveryLogLoss_card_le (P : ℝ) (n a b : ℕ)
    (h : Real.exp (-(quarticBogolyubovProgressionConstant *
        (roundedModelLogBudget P n + 1) ^ 8)) *
      ((2 ^ 4 : ℝ)⁻¹ * (Real.exp (P + 13 * n))⁻¹ * a) ≤
        16 ^ (n + 2) * (b : ℝ)) :
    Real.exp (-affineRecoveryLogLoss P n) * a ≤ (b : ℝ) := by
  let C := quarticBogolyubovProgressionConstant * (roundedModelLogBudget P n + 1) ^ 8
  let E := P + 13 * n
  let L := 16 * ((n : ℝ) + 3)
  have hmain : Real.exp (-(C + E)) * a ≤ (16 : ℝ) ^ (n + 3) * b := by
    calc
      _ = 16 * (Real.exp (-C) * ((2 ^ 4 : ℝ)⁻¹ * (Real.exp E)⁻¹ * a)) := by
        simp only [neg_add, Real.exp_add, Real.exp_neg]
        norm_num
        ring
      _ ≤ 16 * (16 ^ (n + 2) * (b : ℝ)) := mul_le_mul_of_nonneg_left h (by norm_num)
      _ = _ := by rw [show n + 3 = n + 2 + 1 by omega, pow_succ]; ring
  have h16 : (16 : ℝ) ^ (n + 3) ≤ Real.exp L := by
    calc
      _ ≤ (Real.exp 16) ^ (n + 3) :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (16 : ℝ)]) _
      _ = _ := by
        rw [← Real.exp_nat_mul]
        congr 1
        dsimp [L]
        push_cast
        ring
  calc
    _ = Real.exp (-L) * (Real.exp (-(C + E)) * a) := by
      change Real.exp (-(C + E + L)) * a = _
      rw [show -(C + E + L) = -L + -(C + E) by ring, Real.exp_add, mul_assoc]
    _ ≤ Real.exp (-L) * ((16 : ℝ) ^ (n + 3) * b) :=
      mul_le_mul_of_nonneg_left hmain (Real.exp_pos _).le
    _ ≤ Real.exp (-L) * (Real.exp L * b) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h16 (Nat.cast_nonneg _))
        (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

end Erdos3

end

section

namespace Erdos3

open CyclicCrootSisask

noncomputable def properAffineRankBound (P : ℝ) (n : ℕ) : ℝ :=
  2 + quarticBogolyubovConstant * (roundedModelLogBudget P n + 1) ^ 4

noncomputable def properAffineVolumeLog (P : ℝ) (n : ℕ) : ℝ :=
  2 + 16 * (44 + 6 * max P 0 + 94 * n)

noncomputable def properAffineScaleLog (P : ℝ) (n : ℕ) : ℝ :=
  2 * properAffineRankBound P n + properAffineVolumeLog P n + affineRecoveryLogLoss P n + 2

noncomputable def properAffineRecoveryLogLoss (P : ℝ) (n : ℕ) : ℝ :=
  affineRecoveryLogLoss P n + (4 + properAffineScaleLog P n) * properAffineRankBound P n

theorem affineBoxScale_le_exp {r V A B : ℕ} {R D S : ℝ}
    (hB : 0 < B) (hR : 0 ≤ R) (hD : 0 ≤ D) (hS : 0 ≤ S)
    (hr : (r : ℝ) ≤ R) (hV : (V : ℝ) ≤ Real.exp D * A)
    (hdense : Real.exp (-S) * A ≤ (B : ℝ)) :
    ((2 ^ r * V / B + 1 : ℕ) : ℝ) ≤ Real.exp (2 * R + D + S + 2) := by
  have hquot : ((2 ^ r * V / B + 1 : ℕ) : ℝ) * B ≤ (2 : ℝ) ^ r * V + B := by
    have h : (2 ^ r * V / B + 1) * B ≤ 2 ^ r * V + B := by
      calc
        _ = (2 ^ r * V / B) * B + B := by ring
        _ ≤ _ := Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
    exact_mod_cast h
  have htwo : (2 : ℝ) ^ r ≤ Real.exp (2 * R) := by
    calc
      _ ≤ (Real.exp 2) ^ r := pow_le_pow_left₀ (by norm_num)
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) _
      _ = Real.exp (2 * (r : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hr])
  have hA : (A : ℝ) ≤ Real.exp S * B := by
    calc
      _ = Real.exp S * (Real.exp (-S) * A) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hdense (Real.exp_pos _).le
  have hprod : (2 : ℝ) ^ r * V ≤ Real.exp (2 * R + D + S) * B := by
    calc
      _ ≤ Real.exp (2 * R) * (Real.exp D * A) := by gcongr
      _ ≤ Real.exp (2 * R) * (Real.exp D * (Real.exp S * B)) := by gcongr
      _ = _ := by simp only [Real.exp_add]; ring
  have hplus : Real.exp (2 * R + D + S) + 1 ≤ Real.exp (2 * R + D + S + 2) := by
    have hone : 1 ≤ Real.exp (2 * R + D + S) := Real.one_le_exp_iff.mpr (by linarith)
    calc
      _ ≤ 2 * Real.exp (2 * R + D + S) := by linarith only [hone]
      _ ≤ Real.exp 2 * Real.exp (2 * R + D + S) := by
        gcongr
        linarith [Real.add_one_le_exp (2 : ℝ)]
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply (mul_le_mul_iff_left₀ (by exact_mod_cast hB : (0 : ℝ) < B)).mp
  calc
    _ ≤ (2 : ℝ) ^ r * V + B := hquot
    _ ≤ Real.exp (2 * R + D + S) * B + B := add_le_add hprod (le_refl (B : ℝ))
    _ = (Real.exp (2 * R + D + S) + 1) * B := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hplus (Nat.cast_nonneg _)

theorem affineBoxCellCount_le_exp {r k : ℕ} {R T : ℝ}
    (hT : 0 ≤ T) (hr : (r : ℝ) ≤ R) (hk : (k : ℝ) ≤ Real.exp T) :
    ((4 * k) ^ r : ℕ) ≤ Real.exp ((4 + T) * R) := by
  have hbase : (4 : ℝ) * k ≤ Real.exp (4 + T) := by
    calc
      _ ≤ Real.exp 4 * Real.exp T := by
        gcongr
        linarith [Real.add_one_le_exp (4 : ℝ)]
      _ = _ := (Real.exp_add _ _).symm
  calc
    (((4 * k) ^ r : ℕ) : ℝ) = ((4 : ℝ) * k) ^ r := by push_cast; rfl
    _ ≤ (Real.exp (4 + T)) ^ r := pow_le_pow_left₀ (by positivity) hbase _
    _ = Real.exp ((4 + T) * (r : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr (by linarith))

theorem properAffineVolume_bound (P : ℝ) (n : ℕ) :
    2 * ((2 ^ 14 : ℝ) * (Real.exp (P + 13 * n)) ^ 6 * 16 ^ (n + 1)) ^ 16 ≤
      Real.exp (properAffineVolumeLog P n) := by
  calc
    _ ≤ Real.exp 2 * (Real.exp (44 + 6 * max P 0 + 94 * n)) ^ 16 := by
      gcongr
      · linarith [Real.add_one_le_exp (2 : ℝ)]
      · exact roundedModelScale_le_exp P n
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1

theorem properAffineSelection_bounds {P : ℝ} (hP : 0 ≤ P) (n r V A B C : ℕ)
    (hB : 0 < B) (hr : (r : ℝ) ≤ properAffineRankBound P n)
    (hV : (V : ℝ) ≤
      2 * ((2 ^ 14 : ℝ) * (Real.exp (P + 13 * n)) ^ 6 * 16 ^ (n + 1)) ^ 16 * A)
    (hdense : Real.exp (-affineRecoveryLogLoss P n) * A ≤ (B : ℝ))
    (hcell : B ≤ (4 * (2 ^ r * V / B + 1)) ^ r * C) :
    ((2 ^ r * V / B + 1 : ℕ) : ℝ) ≤ Real.exp (properAffineScaleLog P n) ∧
      Real.exp (-properAffineRecoveryLogLoss P n) * A ≤ (C : ℝ) := by
  have hR : 0 ≤ properAffineRankBound P n := by
    have hc := quarticBogolyubovConstant_pos.le
    unfold properAffineRankBound
    positivity
  have hD : 0 ≤ properAffineVolumeLog P n := by unfold properAffineVolumeLog; positivity
  have hS : 0 ≤ affineRecoveryLogLoss P n := by
    have hc := quarticBogolyubovProgressionConstant_pos.le
    unfold affineRecoveryLogLoss
    positivity
  have hT : 0 ≤ properAffineScaleLog P n := by unfold properAffineScaleLog; positivity
  have hV' : (V : ℝ) ≤ Real.exp (properAffineVolumeLog P n) * A :=
    hV.trans (mul_le_mul_of_nonneg_right (properAffineVolume_bound P n) (Nat.cast_nonneg _))
  have hk := affineBoxScale_le_exp hB hR hD hS hr hV' hdense
  have hcount := affineBoxCellCount_le_exp hT hr hk
  refine ⟨hk, ?_⟩
  have hcellR : (B : ℝ) ≤ ((4 * (2 ^ r * V / B + 1)) ^ r : ℕ) * (C : ℝ) := by
    exact_mod_cast hcell
  have hBC : (B : ℝ) ≤ Real.exp ((4 + properAffineScaleLog P n) * properAffineRankBound P n) * C :=
    hcellR.trans (mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg _))
  let T := (4 + properAffineScaleLog P n) * properAffineRankBound P n
  calc
    _ = Real.exp (-T) * (Real.exp (-affineRecoveryLogLoss P n) * A) := by
      unfold properAffineRecoveryLogLoss
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      congr 1
      dsimp [T]
      ring
    _ ≤ Real.exp (-T) * (Real.exp T * C) :=
      mul_le_mul_of_nonneg_left (hdense.trans hBC) (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

end Erdos3

end

section

namespace Erdos3

open CyclicCrootSisask

theorem exists_quadratic_affine_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let P := 1024 * (p + 1)
      P + properAffineRecoveryLogLoss P 1 ≤ (p + C) ^ C ∧
        properAffineRankBound P 1 ≤ (p + C) ^ C ∧ P ≤ (p + C) ^ C := by
  let c := ⌈max quarticBogolyubovProgressionConstant quarticBogolyubovConstant⌉₊
  have hc₀ : quarticBogolyubovProgressionConstant ≤ (c : ℝ) :=
    (le_max_left _ _).trans (Nat.le_ceil _)
  have hc₁ : quarticBogolyubovConstant ≤ (c : ℝ) :=
    (le_max_right _ _).trans (Nat.le_ceil _)
  let PB : Polynomial ℕ := 1024 * (Polynomial.X + 1)
  let PZ : Polynomial ℕ := 736 + 96 * PB + 1504
  let PR : Polynomial ℕ := 2 + Polynomial.C c * (PZ + 1) ^ 4
  let PA : Polynomial ℕ := Polynomial.C c * (PZ + 1) ^ 8 + (PB + 13) + 64
  let PV : Polynomial ℕ := 2 + 16 * (44 + 6 * PB + 94)
  let PT : Polynomial ℕ := 2 * PR + PV + PA + 2
  let PL : Polynomial ℕ := PA + (4 + PT) * PR
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (PB + PL + PR)
  refine ⟨C, hC, ?_⟩
  intro p hp B
  let Z := 736 + 96 * B + 1504
  let R := 2 + (c : ℝ) * (Z + 1) ^ 4
  let A := (c : ℝ) * (Z + 1) ^ 8 + (B + 13) + 64
  let V := 2 + 16 * (44 + 6 * B + 94)
  let T := 2 * R + V + A + 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hz : roundedModelLogBudget B 1 = Z := by
    simp [roundedModelLogBudget, max_eq_left hB, Z]
  have hrank : properAffineRankBound B 1 ≤ R := by
    unfold properAffineRankBound
    rw [hz]
    dsimp [R]
    gcongr
  have hloss : affineRecoveryLogLoss B 1 ≤ A := by
    unfold affineRecoveryLogLoss
    rw [hz]
    dsimp [A]
    norm_num
    gcongr
  have hvolume : properAffineVolumeLog B 1 = V := by
    simp [properAffineVolumeLog, max_eq_left hB, V]
  have hscale : properAffineScaleLog B 1 ≤ T := by
    unfold properAffineScaleLog
    rw [hvolume]
    dsimp [T]
    linarith
  have hrank0 : 0 ≤ properAffineRankBound B 1 := by
    have hc := quarticBogolyubovConstant_pos.le
    unfold properAffineRankBound
    positivity
  have hproper : properAffineRecoveryLogLoss B 1 ≤ A + (4 + T) * R := by
    unfold properAffineRecoveryLogLoss
    exact add_le_add hloss (mul_le_mul (by linarith) hrank hrank0 (by linarith))
  have htotal : B + (A + (4 + T) * R) + R ≤ (p + C) ^ C := by
    simpa [PB, PL, PR, PA, PZ, PV, PT, B, Z, R, A, V, T, Polynomial.eval₂_pow]
      using hbound p hp
  have hproper0 : 0 ≤ A + (4 + T) * R := by positivity
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3

end

section

namespace Erdos3

open CyclicCrootSisask

end Erdos3

end

section

namespace Erdos3

open CyclicCrootSisask

theorem exists_sharedFreeAffineSelection_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → ∀ n : ℕ, (n : ℝ) ≤ 4 * (s : ℝ) * p →
      affineRecoveryLogLoss ((p + 2) ^ 3 + 2 * p) n ≤ (p + C) ^ C ∧
      2 + quarticBogolyubovConstant *
        (roundedModelLogBudget ((p + 2) ^ 3 + 2 * p) n + 1) ^ 4 ≤ (p + C) ^ C := by
  let C₀ := ⌈max quarticBogolyubovProgressionConstant quarticBogolyubovConstant⌉₊
  have hC₀ : quarticBogolyubovProgressionConstant ≤ (C₀ : ℝ) :=
    (le_max_left _ _).trans (Nat.le_ceil _)
  have hC₁ : quarticBogolyubovConstant ≤ (C₀ : ℝ) :=
    (le_max_right _ _).trans (Nat.le_ceil _)
  let PB : Polynomial ℕ := (Polynomial.X + 2) ^ 3 + 2 * Polynomial.X
  let PD : Polynomial ℕ := 4 * Polynomial.C s * Polynomial.X
  let PZ : Polynomial ℕ := 736 + 96 * PB + 1504 * PD
  let T : Polynomial ℕ := Polynomial.C C₀ * (PZ + 1) ^ 8 +
    (PB + 13 * PD) + 16 * (PD + 3) + (2 + Polynomial.C C₀ * (PZ + 1) ^ 4)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro p hp n hn
  let B := (p + 2) ^ 3 + 2 * p
  let D := 4 * (s : ℝ) * p
  let U := 736 + 96 * B + 1504 * D
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hz : roundedModelLogBudget B n ≤ U := by
    unfold roundedModelLogBudget
    rw [max_eq_left hB]
    dsimp [U]
    gcongr
  have hz0 : 0 ≤ roundedModelLogBudget B n + 1 := by
    linarith [roundedModelLogBudget_nonneg B n]
  have hcost : affineRecoveryLogLoss B n ≤
      (C₀ : ℝ) * (U + 1) ^ 8 + (B + 13 * D) + 16 * (D + 3) := by
    unfold affineRecoveryLogLoss
    gcongr
  have hrank : 2 + quarticBogolyubovConstant * (roundedModelLogBudget B n + 1) ^ 4 ≤
      2 + (C₀ : ℝ) * (U + 1) ^ 4 := by gcongr
  have heval : T.eval₂ (Nat.castRingHom ℝ) p =
      (C₀ : ℝ) * (U + 1) ^ 8 + (B + 13 * D) + 16 * (D + 3) +
        (2 + (C₀ : ℝ) * (U + 1) ^ 4) := by
    simp [T, PZ, PD, PB, B, D, U, Polynomial.eval₂_pow]
  have htotal := hbound p hp
  rw [heval] at htotal
  have hcost0 : 0 ≤ (C₀ : ℝ) * (U + 1) ^ 8 + (B + 13 * D) + 16 * (D + 3) := by
    positivity
  have hrank0 : 0 ≤ 2 + (C₀ : ℝ) * (U + 1) ^ 4 := by positivity
  constructor <;> linarith

theorem exists_sharedFreeAffineUniform_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      ∀ n : ℕ, (n : ℝ) ≤ 4 * (s : ℝ) * p →
        sharedFreeRecoveryThreshold s q p ≤ (p + C) ^ C ∧
        affineRecoveryLogLoss ((p + 2) ^ 3 + 2 * p) n ≤ (p + C) ^ C ∧
        2 + quarticBogolyubovConstant *
          (roundedModelLogBudget ((p + 2) ^ 3 + 2 * p) n + 1) ^ 4 ≤ (p + C) ^ C := by
  obtain ⟨C₁, hC₁, hthreshold⟩ := exists_sharedFreeRecoveryThreshold_bound s
  obtain ⟨C₂, hC₂, hselection⟩ := exists_sharedFreeAffineSelection_bound s
  let C := C₁ + C₂
  have hC : 2 ≤ C := by dsimp [C]; omega
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp n hn
  have hshift (c : ℕ) (hc : c ≤ C) : (p + c) ^ c ≤ (p + C) ^ C := by
    have hcR : (c : ℝ) ≤ C := by exact_mod_cast hc
    have hCR : (2 : ℝ) ≤ C := by exact_mod_cast hC
    exact (pow_le_pow_left₀ (by positivity) (by linarith : p + c ≤ p + C) c).trans
      (pow_le_pow_right₀ (by linarith : 1 ≤ p + C) hc)
  have h₁ := hshift C₁ (by dsimp [C]; omega)
  have h₂ := hshift C₂ (by dsimp [C]; omega)
  have hs := hselection p hp n hn
  exact ⟨(hthreshold q p hq hqp hp).trans h₁, hs.1.trans h₂, hs.2.trans h₂⟩

theorem sharedFreeRecoveryThreshold_coefficient_bounds (s : ℕ) {q p : ℝ}
    (hq : 0 ≤ q) (hp : 0 ≤ p) :
    let A := sharedFreeEquationInputBudget s q p
    let z := 8 * sharedRefinementInputBudget s p + 1
    (A + 2) ^ 4 ≤ sharedFreeRecoveryThreshold s q p ∧
      2 * (Real.exp ((A + 2) ^ 3) *
        (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z))) ≤
          Real.exp (sharedFreeRecoveryThreshold s q p) := by
  intro A z
  have hb := sharedFreeEquationInputBudget_bounds s hq hp
  have hA : 0 ≤ A := hb.1
  have hz : 0 ≤ z := by
    have hi := (sharedRefinementInputBudget_bounds s hp).2.2.1
    dsimp [z]
    linarith
  have hbudget : z + ((z + 2) ^ 3 + (z + 2) ^ 36) ≤ A := hb.2.2.2
  have hT : (A + 2) ^ 5 ≤ sharedFreeRecoveryThreshold s q p := le_max_right _ _
  refine ⟨(pow_le_pow_right₀ (by linarith : 1 ≤ A + 2) (by decide : 4 ≤ 5)).trans hT, ?_⟩
  have hzA : z ≤ A := by
    have h3 : 0 ≤ (z + 2) ^ 3 := by positivity
    have h36 : 0 ≤ (z + 2) ^ 36 := by positivity
    linarith
  have h18 : (z + 2) ^ 18 ≤ (z + 2) ^ 36 :=
    pow_le_pow_right₀ (by linarith) (by decide)
  have hwA : (z + 2) ^ 3 + (z + 2) ^ 18 + z ≤ A := by linarith
  have hsum : Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z) ≤
      2 * Real.exp A := by
    linarith [Real.exp_le_exp.mpr hzA, Real.exp_le_exp.mpr hwA]
  have hpoly : (A + 2) ^ 3 + A + 4 ≤ (A + 2) ^ 5 := by
    have hh : 0 ≤ A ^ 5 + 10 * A ^ 4 + 39 * A ^ 3 + 74 * A ^ 2 + 67 * A + 20 := by
      positivity
    nlinarith
  calc
    _ ≤ 2 * (Real.exp ((A + 2) ^ 3) * (2 * Real.exp A)) := by gcongr
    _ = 4 * Real.exp ((A + 2) ^ 3 + A) := by rw [Real.exp_add]; ring
    _ ≤ Real.exp 4 * Real.exp ((A + 2) ^ 3 + A) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      linarith [Real.add_one_le_exp (4 : ℝ)]
    _ = Real.exp ((A + 2) ^ 3 + A + 4) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp ((A + 2) ^ 5) := Real.exp_le_exp.mpr hpoly
    _ ≤ _ := Real.exp_le_exp.mpr hT

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SharedFreeComparisonBasis
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module

theorem exists_layer_basis_of_eq
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n : ℕ}
    {E : RationalFilteredNilmanifold L s n} (T : E.DegreeRankStructure r)
    {p : ℝ} (hT : T.ComplexityLE p) (i j : Fin (s + 1))
    (K : Submodule ℚ L) (hK : T.filtration.layer i.val j.val = K) :
    ∃ k : Basis (Fin (finrank ℚ K)) ℚ K,
      ∀ a b, rationalLogHeight (E.basis.repr (k a : L) b) ≤ p := by
  subst K
  exact ⟨T.basis i j, hT.2 i j⟩

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3

open Module

variable {V μ : Type*} [AddCommGroup V] [Module ℚ V] [Fintype μ]

theorem exists_firstProjection_basis_logHeight
    (e : Basis μ ℚ V) (K : Submodule ℚ (Fin 4 → V))
    (k : Basis (Fin (finrank ℚ K)) ℚ K) {p : ℝ}
    (hk : ∀ a i, rationalLogHeight ((Pi.basis (fun _ : Fin 4 => e)).repr (k a : Fin 4 → V) i) ≤ p) :
    ∃ c : Basis (Fin (finrank ℚ (K.map (LinearMap.proj 0)))) ℚ (K.map (LinearMap.proj 0)),
      ∀ a i, rationalLogHeight (e.repr (c a : V) i) ≤ p := by
  have hspan : Submodule.span ℚ (Set.range (fun a => (k a : Fin 4 → V))) = K := by
    change Submodule.span ℚ (Set.range (K.subtype ∘ k)) = K
    rw [Set.range_comp, ← Submodule.map_span, k.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hproj : Submodule.span ℚ (Set.range (fun a => (k a : Fin 4 → V) 0)) =
      K.map (LinearMap.proj 0) := by
    change Submodule.span ℚ (Set.range
      ((LinearMap.proj (0 : Fin 4) : (Fin 4 → V) →ₗ[ℚ] V) ∘ fun a => (k a : Fin 4 → V))) = _
    rw [Set.range_comp, ← Submodule.map_span, hspan]
  apply exists_submodule_basis_of_spanning_logHeight e _ (fun a => (k a : Fin 4 → V) 0) hproj
  intro a i
  simpa only [Pi.basis_repr] using hk a ⟨0, i⟩

theorem exists_fourPetalSpace_basis_logHeight
    (e : Basis μ ℚ V) (D : Submodule ℚ V) (K : Submodule ℚ (Fin 4 → V))
    (b : Basis (Fin (finrank ℚ D)) ℚ D) (k : Basis (Fin (finrank ℚ K)) ℚ K)
    {p : ℝ} (hp : 0 ≤ p) (hdim : (Fintype.card μ : ℝ) ≤ p)
    (hb : ∀ a i, rationalLogHeight (e.repr (b a : V) i) ≤ p)
    (hk : ∀ a i, rationalLogHeight ((Pi.basis (fun _ : Fin 4 => e)).repr (k a : Fin 4 → V) i) ≤ p) :
    ∃ c : Basis (Fin (finrank ℚ (fourPetalSpace D K))) ℚ (fourPetalSpace D K),
      ∀ a i, rationalLogHeight (e.repr (c a : V) i) ≤ preimageBasisBudget (4 * p) := by
  let : FiniteDimensional ℚ V := e.finiteDimensional_of_finite
  have hp4 : p ≤ 4 * p := by linarith only [hp]
  have hspan (U : Submodule ℚ V) (a : Basis (Fin (finrank ℚ U)) ℚ U) :
      Submodule.span ℚ (Set.range (fun j => (a j : V))) = U := by
    change Submodule.span ℚ (Set.range (U.subtype ∘ a)) = U
    rw [Set.range_comp, ← Submodule.map_span, a.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hkspan : Submodule.span ℚ (Set.range (fun j => (k j : Fin 4 → V))) = K := by
    change Submodule.span ℚ (Set.range (K.subtype ∘ k)) = K
    rw [Set.range_comp, ← Submodule.map_span, k.span_eq, Submodule.map_top, Submodule.range_subtype]
  apply exists_preimage_basis_logHeight e (Pi.basis (fun _ : Fin 4 => e)) D K
    (LinearMap.single ℚ (fun _ : Fin 4 => V) 0)
    (fun j => (b j : V)) (fun j => (k j : Fin 4 → V)) (hspan D b) hkspan
    (mul_nonneg (by norm_num) hp)
  · simpa using mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 4)
  · have hD : (finrank ℚ D : ℝ) ≤ Fintype.card μ := by
      exact_mod_cast D.finrank_le.trans_eq (finrank_eq_card_basis e)
    simpa only [Fintype.card_fin] using (hD.trans hdim).trans hp4
  · have hK : (finrank ℚ K : ℝ) ≤ 4 * Fintype.card μ := by
      exact_mod_cast four_submodule_finrank_le e K
    simpa only [Fintype.card_fin] using hK.trans
      (mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 4))
  · exact fun a i => (hb a i).trans hp4
  · exact fun a i => (hk a i).trans hp4
  · rintro a ⟨j, i⟩
    by_cases hj : j = 0
    · subst j
      simpa [Pi.basis_repr, LinearMap.single_apply] using (hb a i).trans hp4
    · simpa [Pi.basis_repr, LinearMap.single_apply, hj, Ne.symm hj, rationalLogHeight] using
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hp)

end Erdos3

end

section

namespace Erdos3

theorem preimageBasisBudget_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    preimageBasisBudget p ≤ preimageBasisBudget q := by
  have hq : 0 ≤ q := hp.trans hpq
  unfold preimageBasisBudget sparseGeneratorBudget
  gcongr

theorem fourRefinementBasisBudget_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    fourRefinementBasisBudget p ≤ fourRefinementBasisBudget q :=
  add_le_add hpq (preimageBasisBudget_mono (by positivity)
    (mul_le_mul_of_nonneg_left hpq (by norm_num)))

noncomputable def sharedFreeComparisonBasisBudget (q p : ℝ) : ℝ :=
  let A := q + fourRefinementBasisBudget (q + coefficientFourHeightBudget p)
  A + preimageBasisBudget (4 * A)

theorem exists_sharedFreeComparisonBasisBudget_bound :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      sharedFreeComparisonBasisBudget q p ≤ (p + C) ^ C := by
  let R (X : Polynomial ℕ) := ((X + 1 + (X + 3) ^ 7 + 2) ^ 9 + X + 4) ^ 4
  let H (X : Polynomial ℕ) := X + R X + 2
  let G (X : Polynomial ℕ) := X + X * ((X + 2) ^ 7 + X)
  let V (X : Polynomial ℕ) := G (X + (X + (X + 3) ^ 7 + 2) ^ 4 + 1)
  let F (X : Polynomial ℕ) := X + V (4 * X)
  let A : Polynomial ℕ := Polynomial.X + F (Polynomial.X + H Polynomial.X)
  let T : Polynomial ℕ := A + V (4 * A)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp
  have hheight : 0 ≤ coefficientFourHeightBudget p := coefficientFourHeightBudget_nonneg hp
  have hupper : sharedFreeComparisonBasisBudget q p ≤ sharedFreeComparisonBasisBudget p p := by
    have hA := add_le_add hqp (fourRefinementBasisBudget_mono (add_nonneg hq hheight)
      (add_le_add hqp (le_refl (coefficientFourHeightBudget p))))
    have hA0 : 0 ≤ q + fourRefinementBasisBudget (q + coefficientFourHeightBudget p) :=
      add_nonneg hq (fourRefinementBasisBudget_nonneg (add_nonneg hq hheight))
    dsimp only [sharedFreeComparisonBasisBudget]
    exact add_le_add hA (preimageBasisBudget_mono (mul_nonneg (by norm_num) hA0)
      (mul_le_mul_of_nonneg_left hA (by norm_num)))
  apply hupper.trans
  simpa [T, A, F, V, G, H, R, sharedFreeComparisonBasisBudget, coefficientFourHeightBudget,
    refiltrationCoordinateBudget, fourRefinementBasisBudget, preimageBasisBudget,
    sparseGeneratorBudget, Polynomial.eval₂_pow] using hbound p hp

end Erdos3

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_sharedFreeComparisonSpace_basis
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P') (d : Fin s) :
    let C := (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
      (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)
    let P := fourPetalSpace (D.dependentFreeSpan d)
      (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))
    let K := D.coefficientFreeFiltration.layer (d.val + 1) 2
    ∃ b : Basis (Fin (finrank ℚ (petalComparisonSpace C P K))) ℚ (petalComparisonSpace C P K),
      ∀ a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => E.basis)).repr
        (b a : Fin 2 → D.CoefficientFreeLieAlgebra) i) ≤ sharedFreeComparisonBasisBudget Q P' := by
  intro C P K
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  let H := fourRefinementBasisBudget (Q + coefficientFourHeightBudget P')
  let A := Q + H
  have hH : 0 ≤ H := fourRefinementBasisBudget_nonneg
    (add_nonneg hQ (coefficientFourHeightBudget_nonneg hP'))
  have hA : 0 ≤ A := add_nonneg hQ hH
  have hQA : Q ≤ A := le_add_of_nonneg_right hH
  have hHA : H ≤ A := le_add_of_nonneg_left hQ
  obtain ⟨k, hk⟩ := D.exists_correlation_refined_basis E T hbQ hT F V g hg D' hs hP' hQP' d
  obtain ⟨b, hb⟩ := D.exists_dependentFreeSpan_basis E.basis F (by omega) d
  obtain ⟨c, hc⟩ := exists_firstProjection_basis_logHeight E.basis _ k
    (fun a i => (hk a i).trans hHA)
  obtain ⟨p, hp⟩ := exists_fourPetalSpace_basis_logHeight E.basis _ _ b k hA
    (by simpa only [Fintype.card_fin] using hT.1.1.trans hQA)
    (fun a i => (hb a i).trans hQA) (fun a i => (hk a i).trans hHA)
  have hK : ∃ k : Basis (Fin (finrank ℚ K)) ℚ K,
      ∀ a i, rationalLogHeight (E.basis.repr (k a : D.CoefficientFreeLieAlgebra) i) ≤ Q := by
    exact T.exists_layer_basis_of_eq hT ⟨d.val + 1, by omega⟩ ⟨2, by omega⟩ K
      (congrArg (fun T => T.layer (d.val + 1) 2) hTfil)
  obtain ⟨k₂, hk₂⟩ := hK
  have hpre : 0 ≤ preimageBasisBudget (4 * A) := preimageBasisBudget_nonneg (by positivity)
  have hAL : A ≤ sharedFreeComparisonBasisBudget Q P' := le_add_of_nonneg_right hpre
  have hPL : preimageBasisBudget (4 * A) ≤ sharedFreeComparisonBasisBudget Q P' :=
    le_add_of_nonneg_left hA
  exact exists_petalComparisonSpace_basis_logHeight E.basis C P K c p k₂
    (add_nonneg hA hpre) (fun a i => (hc a i).trans hAL) (fun a i => (hp a i).trans hPL)
    (fun a i => (hk₂ a i).trans (hQA.trans hAL))

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialOrbitLogSum
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {F : NilpotentLieFiltration L s} {w : σ → ℕ}

noncomputable def PolynomialOrbit.logSum (g h : F.PolynomialOrbit w) : F.PolynomialOrbit w :=
  ⟨⟨g.log + h.log⟩, (F.adaptedLieSubalgebra w).add_mem g.property h.property⟩

@[simp] theorem PolynomialOrbit.logSum_log (g h : F.PolynomialOrbit w) :
    (g.logSum h).log = g.log + h.log := rfl

theorem PolynomialOrbit.logSum_normalized (g h : F.PolynomialOrbit w)
    (hg : F.polynomialOrbitEval w 0 g = 1) (hh : F.polynomialOrbitEval w 0 h = 1) :
    F.polynomialOrbitEval w 0 (g.logSum h) = 1 := by
  rw [F.polynomialOrbitEval_zero_iff_coefficient_zero] at hg hh ⊢
  simp only [logSum_log, map_add, Finsupp.add_apply, hg, hh, add_zero]

end Erdos3.NilpotentLieFiltration

end

end OAI

end


