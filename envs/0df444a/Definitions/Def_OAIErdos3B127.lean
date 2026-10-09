-- Prove2me | Definitions.Def_OAIErdos3B127
-- name    : OAIErdos3B127
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T07:10:38.270415+00:00
-- url     : https://prove2.me/theorems/4977aeda-70bf-4cc4-94e1-a4a312bb140f
-- title:
--   OpenAI Erdős-3 split, definitions bundle 128 of 132
-- statement:
--   Definitions bundle 128 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B126`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 128 available.
--
--   Modules: `OAI.Erdos3.BinaryTensorIndex`, `OAI.Erdos3.BinaryTensorIndex.fintype`, `OAI.Erdos3.MultidegreeLieFiltration.polynomialOrbitEval_eq_on_active_coordinates`, `OAI.Erdos3.NativeCoordinateSplit`, `OAI.Erdos3.NativeCoordinateSplit.exists_fixed_correlating_term`, `OAI.Erdos3.NativeCoordinateSplit.exists_second_expansion_budget`, `OAI.Erdos3.NativeCoordinateSplit.firstFactor`, `OAI.Erdos3.NativeCoordinateSplit.firstFactor_norm`, `OAI.Erdos3.NativeCoordinateSplit.first_eval_eq`, `OAI.Erdos3.NativeCoordinateSplit.first_eval_firstFactor`, `OAI.Erdos3.NativeIntegerVectorEquivalence.conjugationPower`, `OAI.Erdos3.NativeIntegerVectorEquivalence.exists_fin_product_budget`, `OAI.Erdos3.NativeIntegerVectorEquivalence.exists_finite_product_budget`, `OAI.Erdos3.NativeIntegerVectorEquivalence.of_addition_family`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_addition_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_addition_family`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_coordinate_parallelogram_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_coordinate_sum_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_coordinate_translation_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_frozen_affine_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_integer_self_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_multilinearity_equivalence`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonVerticalProduct_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_addition_niltest_of_data`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_controlled_addition_family`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_controlled_addition_model`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_prepared_addition_niltest`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.niltest_eval_eq_of_zero_coordinate`, `OAI.Erdos3.TernaryTensorIndex`, `OAI.Erdos3.TernaryTensorIndex.fintype`, `OAI.Erdos3.VectorPolynomial.eval_eq_of_support_agreement`, `OAI.Erdos3.coordinateAdditionProduct_eq`, `OAI.Erdos3.coordinateReplaceIndex`, `OAI.Erdos3.coordinateReplaceInput`, `OAI.Erdos3.coordinateSplitBound`, `OAI.Erdos3.coordinateSplitBound_le`, `OAI.Erdos3.coordinateSplitDownset`, `OAI.Erdos3.coordinateSplitDownset_covers`, `OAI.Erdos3.coordinateSplitDownset_lower`, `OAI.Erdos3.coordinateSplitDownset_terminal`, `OAI.Erdos3.coordinateSumVector`, `OAI.Erdos3.coordinateTensorVector`, `OAI.Erdos3.coordinateTensorVector_unit`, `OAI.Erdos3.coordinateTranslatedInput`, `OAI.Erdos3.coordinateTranslationExpansion`, `OAI.Erdos3.coordinateTranslationExpansion_unit`, `OAI.Erdos3.coordinateTranslationHom`, `OAI.Erdos3.coordinateTranslation_left`, `OAI.Erdos3.coordinateTranslation_right`, `OAI.Erdos3.coordinateTranslation_sum`, `OAI.Erdos3.derivative_covolume_budget_le_exp`, `OAI.Erdos3.derivative_extended_budget_le_exp`, `OAI.Erdos3.derivative_output_budgets_le_exp`, `OAI.Erdos3.derivative_output_exponent_le`, `OAI.Erdos3.derivative_projection_budget_le_exp`, `OAI.Erdos3.euclideanDerivative_lattice_extraction`, `OAI.Erdos3.euclideanDerivative_uniform_lattice_extraction`, `OAI.Erdos3.exists_coordinate_niltest_splitting`, `OAI.Erdos3.exists_missing_coordinate_niltest_approximation`, `OAI.Erdos3.exists_totalDegree_niltest_splitting`, `OAI.Erdos3.lattice_subspace_budgets_le_exp`, `OAI.Erdos3.mem_mixedEvaluationCoordinates`, `OAI.Erdos3.mixedEvaluationCoordinates`, `OAI.Erdos3.mixedEvaluationCoordinates_card`, `OAI.Erdos3.mixedEvaluationCoordinates_erase_card`, `OAI.Erdos3.mixedEvaluationEmbedding`, `OAI.Erdos3.mixedShiftCoordinate`, `OAI.Erdos3.mixedShiftCoordinate_unique`, `OAI.Erdos3.mixed_input_eq_coordinateConstant`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B122
import Definitions.Def_OAIErdos3B128

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.TotalDegreeNiltestSplitting
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial RationalFilteredNilmanifold
open RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators NNReal

theorem exists_totalDegree_niltest_splitting (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {D : RationalFilteredNilmanifold L s d} {p : ℝ}
      (T : D.Niltest (fun _ : Fin 2 => 1)), T.ComplexityLE p → T.normBound ≤ 1 →
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      Nonempty (NativeTwoVariableSplit s d ((p + C) ^ C) epsilon T.eval) := by
  obtain ⟨C, hC, hsplit⟩ := exists_two_downset_splitting s (2 * s) a
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p T hT hnorm epsilon hepsilon hscale
  classical
  let M := D.totalDegreeMultidegree (Fin 2) hT.1
  let J := totalDegreeSplitDownset s
  have hJ : ∀ b, IsLowerSet (J b) := totalDegreeSplitDownset_lower s
  let K := fun b => M.filtration.positivePolynomialAlgebra ⧸
    restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J b) (hJ b)
  let : ∀ b, TopologicalSpace (ℝ ⊗[ℚ] K b) := fun _ => moduleTopology ℝ _
  let : ∀ b, IsTopologicalAddGroup (ℝ ⊗[ℚ] K b) :=
    fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ b, T2Space (ℝ ⊗[ℚ] K b) :=
    fun b => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J b) (hJ b) p)
  let g := D.filtration.realTotalDegreeOrbit T.orbit
  have hsum : (∑ _ : Fin 2, s) = 2 * s := by simp
  have hM : M.ComplexityLE p := D.totalDegreeMultidegree_complexity (Fin 2) hT.1
  have hcover : ∀ c, c ≠ 0 → c ∉ J false ∪ J true →
      M.filtration.layer (fun i => c i) = ⊥ :=
    fun c _ hc => totalDegreeSplitDownset_terminal D.filtration c hc
  obtain ⟨r, _, _, B, hB, hstable, hresult⟩ :=
    hsplit M J hJ p hsum hM hcover g epsilon hepsilon hscale
  obtain ⟨hE, hdim, hterminal, h, _, happrox⟩ := hresult
  have hlip : (T.lipBound : ℝ) ≤ Real.exp p := by
    have hb := T.observable_budget hT
    have hn := T.normBound.coe_nonneg
    linarith
  have hub : ∀ x, ‖T.observable x‖ ≤ 1 := fun x =>
    (T.norm_le x).trans (show (T.normBound : ℝ) ≤ 1 from hnorm)
  obtain ⟨N, hN, hNbound, A, B', hAnorm, hBnorm, hA, hB', hAg, hBg, herr⟩ :=
    happrox T.observable T.lipBound hlip T.lipschitz hub
  let E := fun b => M.positivePolynomialDownsetModel (J b) (hJ b) r B hB hstable
  let F := fun b => M.positivePolynomialDownsetModelMultidegree (J b) (hJ b) r B hB hstable
  have hzero (b : Bool) (v : Fin 2 → ℕ) (hv : ¬v ≤ totalDegreeSplitBound s b) :
      (F b).filtration.layer v = ⊥ := by
    let c : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm v
    exact hterminal b c hv
  let R := fun b => (F b).restrictBound (totalDegreeSplitBound s b)
    (totalDegreeSplitBound_le s b) (hzero b)
  let tests : ∀ b, Fin N → (E b).Niltest (fun _ : Fin 2 => 1) :=
    fun b => match b with
      | false => A
      | true => B'
  refine ⟨{
    count := N
    count_pos := hN
    count_bound := hNbound
    L := K
    dim := fun b => Fintype.card (M.PositivePolynomialDownsetIndex (J b))
    model := E
    multi := R
    complexity := fun b => (F b).restrictBound_complexity (totalDegreeSplitBound s b)
      (totalDegreeSplitBound_le s b) (hzero b) (hE b)
    dimension_bound := hdim
    orbit := fun b => (F b).filtration.restrictBoundRealOrbit (totalDegreeSplitBound s b)
      (hzero b) (M.filtration.positivePolynomialDownsetOrbit (J b) (hJ b) h)
    test := tests
    test_norm := ?_
    test_complexity := ?_
    test_orbit := ?_
    approximation := ?_ }⟩
  · intro b j
    cases b
    · exact hAnorm j
    · exact hBnorm j
  · intro b j
    cases b
    · exact hA j
    · exact hB' j
  · intro b j
    cases b
    · exact hAg j
    · exact hBg j
  · intro x
    change ‖T.eval x - ∑ j, (A j).eval x * (B' j).eval x‖ ≤ epsilon
    have heval : T.observable (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)) =
        T.eval x := by
      change T.observable (QuotientGroup.mk
        ((D.filtration.totalDegreeMultifiltration (Fin 2)).realification.polynomialOrbitEval x
          (D.filtration.realTotalDegreeOrbit T.orbit))) = _
      rw [D.filtration.realTotalDegreeOrbit_eval]
      rfl
    simpa only [heval] using herr x

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PreparedAdditionNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {σ L I : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [Fintype I] {s d r n : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) (i : σ) (hi : bound i = 1) (hs : ∑ j, bound j = s + 1)
  (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) (s + 1) r)
  (hEF : E.filtration = M.filtration.additiveTripleFiltration i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
  (hEL : E.lattice = M.additiveTripleLattice i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  (Q : RationalFilteredNilmanifold ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  (hQF : Q.filtration = E.filtration.quotientTop)
  (hQL : Q.lattice = E.lattice.map (E.filtration.quotientStepHom
    (E.filtration.layerIdeal (s + 1)) (t := s) le_rfl))
  [TopologicalSpace (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]

include hs hEF hQF hQL

theorem exists_addition_niltest_of_data {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ j k, RationalHeightLE
      (Q.basis.repr (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis k)) j) H)
    (hstructure : ∀ a b c, RationalHeightLE (lieStructureConstants Q.basis a b c) H)
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ)
    (a : Fin 3 → I) (A : ℝ≥0)
    (hLip : letI := E.metricSpace
      LipschitzWith A (M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
        E hEL ε (fun j => V.observable (a j)))) :
    ∃ T : Q.Niltest (fun _ : Option σ => 1), T.normBound = 1 ∧
      T.lipBound = rationalReconstructionLipschitzBound s r n H A 1 ∧
      Q.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
      ∀ x, T.eval x = coordinateAdditionProduct
        (fun j y => V.observable j (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval y g)))
        a i x := by
  obtain ⟨q, hq0, hq⟩ := M.exists_native_addition_orbit i hi.le E hEF g ε γ hγ hfactor
  obtain ⟨T, hTnorm, hTlip, hTorbit, hTval⟩ := M.exists_unitVertical_triple_quotient_niltest
    i hi hs E hEF hEL Q hQL hQF hH hentries hstructure V ε a A hLip q
  refine ⟨T, hTnorm, hTlip, ?_, ?_⟩
  · rw [hTorbit, E.topQuotientOrbit_eval Q hQF, hq0, map_one]
  · intro x
    rw [hTval]
    exact M.tripleObservable_of_addition_values i hi.le E hEL g ε q hq
      (fun j => V.observable (a j)) x

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {σ L I : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [Fintype I] {s d r n : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) (i : σ) (hi : bound i = 1) (hs : ∑ j, bound j = s + 1)
  (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) (s + 1) r)
  (hEF : E.filtration = M.filtration.additiveTripleFiltration i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
  (hEL : E.lattice = M.additiveTripleLattice i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  (Q : RationalFilteredNilmanifold ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  (hQF : Q.filtration = E.filtration.quotientTop)
  (hQL : Q.lattice = E.lattice.map (E.filtration.quotientStepHom
    (E.filtration.layerIdeal (s + 1)) (t := s) le_rfl))
  [TopologicalSpace (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]

include hs hEF hEL hQF hQL

theorem exists_prepared_addition_niltest
    {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE (MultilinearityBudget.ambient p))
    (hE : E.GeometryComplexityLE (MultilinearityBudget.ambient p))
    (he : ∀ j a k, rationalLogHeight (D.basis.repr
      (M.filtration.additiveTripleProjection i hi.le _ (omittedCoordinateWeight_le_one i) j (E.basis a)) k) ≤
        MultilinearityBudget.ambient p)
    (hQ : Q.GeometryComplexityLE (MultilinearityBudget.quotient p))
    (hq : ∀ j k, rationalLogHeight
      (Q.basis.repr (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis k)) j) ≤
        MultilinearityBudget.quotient p)
    (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (g : M.filtration.realification.PolynomialOrbit) (C : ℕ) (ε γ : D.RealGroup)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ)
    (A : ℝ≥0) (hA : (A : ℝ) ≤ Real.exp ((p + C) ^ C))
    (hε : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x))
    (a : Fin 3 → I) :
    ∃ T : Q.Niltest (fun _ : Option σ => 1), T.normBound = 1 ∧
      T.ComplexityLE (MultilinearityBudget.total C (MultilinearityBudget.reconstructionExponent s) p) ∧
      Q.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
      ∀ x, T.eval x = coordinateAdditionProduct
        (fun j y => V.observable j (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval y g)))
        a i x := by
  let H := ⌈Real.exp (MultilinearityBudget.quotient p)⌉₊
  let A₃ : ℝ≥0 := 3 * (V.lipBound * (A *
    ⟨Real.exp ((MultilinearityBudget.ambient p + 3) ^ 2), (Real.exp_pos _).le⟩))
  have hLip : letI := E.metricSpace
      LipschitzWith A₃ (M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
        E hEL ε (fun j => V.observable (a j))) :=
    M.tripleObservable_lipschitz i hi.le _ (omittedCoordinateWeight_le_one i) E hEL
      (MultilinearityBudget.ambient_bounds hp).1 hD hE he ε (fun j => V.observable (a j))
      V.lipBound A (fun j x => V.norm (a j) x) (fun j => V.lipschitz (a j)) hε
  obtain ⟨T, hTnorm, hTlip, hTzero, hTeval⟩ := M.exists_addition_niltest_of_data
    i hi hs E hEF hEL Q hQF hQL (one_le_ceil_exp _)
    (fun j k => rationalHeightLE_ceil_exp (hq j k))
    (fun j k l => rationalHeightLE_ceil_exp (hQ.2.2.1 j k l))
    V g ε γ hγ hfactor a A₃ hLip
  have hR := MultilinearityBudget.reconstruction_bounds C hp
  have hHb : (H : ℝ) ≤ Real.exp (MultilinearityBudget.reconstruction C p) :=
    (ceil_exp_le_exp_add_one (MultilinearityBudget.quotient_bounds hp).1).trans
      (Real.exp_le_exp.mpr hR.2.2.1)
  have hA₃ : (A₃ : ℝ) ≤ Real.exp (MultilinearityBudget.reconstruction C p) := by
    change (3 : ℝ) * (V.lipBound * (A * Real.exp ((MultilinearityBudget.ambient p + 3) ^ 2))) ≤ _
    exact (MultilinearityBudget.observable_bound C p V.lipBound A V.lip_bound hA).trans
      (Real.exp_le_exp.mpr hR.2.2.2)
  exact ⟨T, hTnorm, MultilinearityBudget.niltest_complexity Q T C r H A₃ hp hQ
    (hE.1.trans hR.2.1) hHb hA₃ hTnorm hTlip, hTzero, hTeval⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMultilinearityCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ I : Type*} [DecidableEq σ]

noncomputable def coordinateSumVector (f : I → (σ → ℤ) → ℂ)
    (i : σ) (a : I) (x : Option σ → ℤ) : ℂ :=
  f a (coordinateAdditionInputs i x 0)

noncomputable def coordinateTensorVector (f : I → (σ → ℤ) → ℂ)
    (i : σ) (a : I × I) (x : Option σ → ℤ) : ℂ :=
  f a.1 (coordinateAdditionInputs i x 1) * f a.2 (coordinateAdditionInputs i x 2)

theorem coordinateAdditionProduct_eq (f : I → (σ → ℤ) → ℂ)
    (i : σ) (a : I) (b : I × I) (x : Option σ → ℤ) :
    coordinateAdditionProduct f ![a, b.1, b.2] i x =
      coordinateSumVector f i a x * star (coordinateTensorVector f i b x) := by
  simp [coordinateAdditionProduct, coordinateSumVector, coordinateTensorVector, mul_assoc]

theorem coordinateTensorVector_unit [Fintype I] (f : I → (σ → ℤ) → ℂ)
    (hf : ∀ x, ∑ a, ‖f a x‖ ^ 2 = 1) (i : σ) (x : Option σ → ℤ) :
    ∑ a, ‖coordinateTensorVector f i a x‖ ^ 2 = 1 := by
  simp only [coordinateTensorVector, norm_mul, mul_pow, Fintype.sum_prod_type,
    ← Finset.mul_sum, hf, mul_one]

end Erdos3

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

theorem of_addition_family {σ I : Type*} [DecidableEq σ] [Fintype I]
    {s : ℕ} {p q r : ℝ} (f : I → (σ → ℤ) → ℂ) (i : σ)
    (R : NativeIntegerModelFamily (fun _ : Option σ => 1) s q
      (fun a => coordinateAdditionProduct f a i))
    (hcard : (Fintype.card I : ℝ) ≤ Real.exp p)
    (hpr : p ≤ r) (h2pr : 2 * p ≤ r) (hqr : q ≤ r) :
    NativeIntegerVectorEquivalence s r (coordinateSumVector f i) (coordinateTensorVector f i) := by
  refine {
    left_dimension := hcard.trans (Real.exp_le_exp.mpr hpr)
    right_dimension := ?_
    expansion := ?_ }
  · simp only [Fintype.card_prod, Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p :=
        mul_le_mul hcard hcard (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add, two_mul]
      _ ≤ Real.exp r := Real.exp_le_exp.mpr h2pr
  · intro a b
    have heq : (fun x => coordinateAdditionProduct f ![a, b.1, b.2] i x) =
        (fun x => coordinateSumVector f i a x * star (coordinateTensorVector f i b x)) :=
      funext (coordinateAdditionProduct_eq f i a b)
    exact ⟨heq ▸ (NativeIntegerExpansion.ofModelFamily R ![a, b.1, b.2]).mono hqr⟩

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_controlled_addition_model (i : σ) (hi : bound i = 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi.le
        c hc) s
        (finrank ℚ (M.filtration.additiveTripleSubalgebra i hi.le
          c hc)),
      E.filtration = M.filtration.additiveTripleFiltration i hi.le
        c hc ∧
      E.lattice = M.additiveTripleLattice i hi.le
        c hc ∧
      E.GeometryComplexityLE (MultilinearityBudget.ambient p) ∧
      (∀ j a k, rationalLogHeight (D.basis.repr (M.filtration.additiveTripleProjection i hi.le
        c hc j (E.basis a)) k) ≤
          MultilinearityBudget.ambient p) ∧
      finrank ℚ (M.filtration.additiveTripleSubalgebra i hi.le c hc) ≤ 3 * d := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  obtain ⟨E, hEF, hEL, hE, hdim, he⟩ :=
    M.exists_additiveTriple_model i hi c hc hM
  have hR := MultilinearityBudget.ambient_bounds hp
  have hE' := hE.mono E hR.2.2.1
  have he' (j : Fin 3) (a) (k) :
      rationalLogHeight (D.basis.repr (M.filtration.additiveTripleProjection i hi.le
        c hc j (E.basis a)) k) ≤
          MultilinearityBudget.ambient p := by
    fin_cases j
    · exact (he a k).1.trans hR.2.2.2
    · exact (he a k).2.1.trans hR.2.2.2
    · exact (he a k).2.2.trans hR.2.2.2
  exact ⟨E, hEF, hEL, hE', he', hdim⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped TensorProduct BigOperators NNReal

theorem exists_controlled_addition_family (s : ℕ) :
    ∃ Z : ℕ, 2 ≤ Z ∧ ∀ {σ I : Type*} {L : Type}
      [Fintype σ] [DecidableEq σ] [Fintype I] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {t d : ℕ} {bound : σ → ℕ} (D : RationalFilteredNilmanifold L t d)
      (M : D.MultidegreeStructure bound) (i : σ) (_hi : bound i = 1)
      (_hs : ∑ j, bound j = t) (_ht : t = s + 1) {p : ℝ}, M.ComplexityLE p →
      ∀ (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
        (g : M.filtration.realification.PolynomialOrbit),
      ∃ R : NativeIntegerModelFamily (fun _ : Option σ => 1) s ((p + Z) ^ Z)
        (fun a => coordinateAdditionProduct
          (fun j y => V.observable j
            (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval y g))) a i),
        R.dim ≤ 3 * d := by
  obtain ⟨C, _, hnormal⟩ := exists_controlled_group_normalization (s + 1)
  obtain ⟨Z, hZ, hbudget⟩ := MultilinearityBudget.exists_total_bound C
    (MultilinearityBudget.reconstructionExponent s)
  refine ⟨Z, hZ, ?_⟩
  intro σ I L _ _ _ _ _ _ _ _ _ t d bound D M i hi hs ht p hM V g
  subst ht
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  have hR := MultilinearityBudget.ambient_bounds hp
  obtain ⟨E, hEF, hEL, hE, he, hdim⟩ := M.exists_controlled_addition_model
    i hi (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i) hM
  obtain ⟨n, hn, Q, hQF, hQL, hQ, hq, _⟩ := E.exists_controlled_top_quotient hR.1 hE
  obtain ⟨ε, γ, A, hγ, hfactor, _, hA, hε⟩ := hnormal D p hp hM.1
    (M.filtration.realification.polynomialOrbitEval 0 g)
  let K := M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)
  let J := K ⧸ E.filtration.layerIdeal (s + 1)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 E.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] J)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] J) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] J) := realification_moduleTopology_t2 Q.basis
  have hall (a : Fin 3 → I) := M.exists_prepared_addition_niltest i hi hs
    E hEF hEL Q hQF hQL hp (hM.1.mono D hR.2.1) hE he hQ
    (fun j k => (hq k j).trans (MultilinearityBudget.quotient_bounds hp).2.2)
    V g C ε γ hγ hfactor A hA hε a
  choose T hnorm hcomplex hzero heval using hall
  refine ⟨{
    L := J
    dim := n
    model := Q
    test := T
    norm := fun a => (hnorm a).le
    complexity := fun a => (hcomplex a).mono (hbudget p hp)
    normalized := hzero
    eval := heval }, hn.trans hdim⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_addition_family {σ : Type*} [Fintype σ] [DecidableEq σ] (bound : σ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (i : σ), bound i = 1 →
      ∃ R : NativeIntegerModelFamily (fun _ : Option σ => 1) ((∑ j, bound j) - 1)
        ((p + C) ^ C) (fun a => coordinateAdditionProduct W.eval a i),
        R.dim ≤ 3 * W.dim := by
  obtain ⟨C, hC, hcontrol⟩ := exists_controlled_addition_family ((∑ j, bound j) - 1)
  refine ⟨C, hC, ?_⟩
  intro p W i hi
  have hle : bound i ≤ ∑ j, bound j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hpos : 1 ≤ ∑ j, bound j := by simpa only [hi] using hle
  exact hcontrol W.model W.multi i hi rfl (Nat.sub_add_cancel hpos).symm
    W.complexity W.vertical W.orbit

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_addition_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ] (bound : σ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (i : σ), bound i = 1 →
      NativeIntegerVectorEquivalence ((∑ j, bound j) - 1) ((p + C) ^ C)
        (coordinateSumVector W.eval i) (coordinateTensorVector W.eval i) := by
  obtain ⟨a, _, hadd⟩ := exists_addition_family bound
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + 2 * X + 2)
  refine ⟨C, hC, ?_⟩
  intro p W i hi
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hpow : 0 ≤ (p + a) ^ a := pow_nonneg (add_nonneg hp (Nat.cast_nonneg a)) a
  have hb : (p + a) ^ a + 2 * p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hpr : p ≤ (p + C) ^ C := by linarith only [hp, hpow, hb]
  have h2pr : 2 * p ≤ (p + C) ^ C := by linarith only [hpow, hb]
  have hqr : (p + a) ^ a ≤ (p + C) ^ C := by linarith only [hp, hb]
  obtain ⟨R, _⟩ := hadd W i hi
  exact NativeIntegerVectorEquivalence.of_addition_family W.eval i R
    (by simpa only [Fintype.card_fin] using W.output_bound) hpr h2pr hqr

theorem exists_multilinearity_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p)
      (i : σ), NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C)
        (coordinateSumVector W.eval i) (coordinateTensorVector W.eval i) := by
  obtain ⟨C, hC, h⟩ := exists_addition_equivalence (fun _ : σ => 1)
  exact ⟨C, hC, fun W i => by simpa using h W i rfl⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ComparisonProductMetric
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct NNReal

variable {σ : Type} {L I : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] [Fintype I]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) {p q v : ℝ}
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  (V : D.UnitVerticalObservable (D.filtration.realification.subgroup s) I v)
  (U : M.SymmetricSquarefreeUnitData p V.frequency q)
  (E : RationalFilteredNilmanifold
    (M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))
    (max s (Fintype.card (ReplicatedIndex bound))) r)
  (hEL : E.lattice = M.comparisonLattice p U.grid U.grid_pos U.stable)
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]

theorem comparisonVerticalProduct_lipschitz {R : ℝ} (hR : 0 ≤ R)
    (hD : D.GeometryComplexityLE R)
    (hQ : (M.squarefreeModel p U.grid U.grid_pos U.stable).GeometryComplexityLE R)
    (hE : E.GeometryComplexityLE R)
    (hfirst : ∀ j k, rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ R)
    (hsecond : ∀ j k, rationalLogHeight ((M.squarefreeFinBasis p).repr (E.basis j).val.2 k) ≤ R)
    (ε : D.RealGroup) (A : ℝ≥0)
    (hε : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x))
    (a : Fin (multidegreeFactorial bound) → I)
    (k : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin U.coordinateCount)) :
    letI := E.metricSpace
    let P : ℝ≥0 := ⟨Real.exp ((R + 3) ^ 2), (Real.exp_pos _).le⟩
    LipschitzWith ((V.tensorPower (multidegreeFactorial bound)).lipBound * (A * P) +
      U.observable.lipBound * P) (M.comparisonVerticalProduct V U E hEL ε a k) := by
  let := D.metricSpace
  let := (M.squarefreeModel p U.grid U.grid_pos U.stable).metricSpace
  let := E.metricSpace
  have h₁ := ((V.tensorPower (multidegreeFactorial bound)).lipschitz a).comp
    (hε.comp (M.comparisonFirstSpace_lipschitz p U.grid U.grid_pos U.stable E hEL hR hD hE hfirst))
  have h₂ := (U.observable.lipschitz k).comp
    (M.comparisonSecondSpace_lipschitz p U.grid U.grid_pos U.stable E hEL hR hQ hE hsecond)
  have h := lipschitz_mul_star_of_bounds
      (fun x => (V.tensorPower (multidegreeFactorial bound)).observable a
        (ε • M.comparisonFirstSpace p U.grid U.grid_pos U.stable E hEL x))
      (fun x => U.observable.observable k (M.comparisonSecondSpace p U.grid U.grid_pos U.stable E hEL x))
      (Bf := 1) (Bg := 1) h₁ h₂
      (fun x => (V.tensorPower (multidegreeFactorial bound)).norm a _) (fun x => U.observable.norm k _)
  simp only [one_mul] at h
  rw [add_comm] at h
  convert h using 1
  all_goals rfl

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerSelfEquivalence
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_integer_self_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ] [Nonempty σ] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p),
      NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C) W.eval W.eval := by
  obtain ⟨a, _, hadd⟩ := exists_multilinearity_equivalence (σ := σ)
  obtain ⟨c, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C a) ^ a + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p W
  classical
  let i : σ := Classical.arbitrary σ
  let A : Option σ → ((σ → ℤ) →+ ℤ) := fun j => match j with
    | none => 0
    | some k => ⟨⟨fun x => x k, rfl⟩, fun _ _ => rfl⟩
  let E := (hadd W i).linearPullbackHom A
  have hleft (k : Fin W.outputDim) (x : σ → ℤ) :
      coordinateSumVector W.eval i k (fun j => A j x) = W.eval k x := by
    simp [coordinateSumVector, coordinateAdditionInputs, A]
  have hunit (x : σ → ℤ) :
      ∑ k, ‖coordinateTensorVector W.eval i k (fun j => A j x)‖ ^ 2 = 1 :=
    coordinateTensorVector_unit W.eval W.unit_eval i _
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ (p + a) ^ a := by positivity
  have F := htrans hq E E.symm hunit
  have hcost : ((p + a) ^ a + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  simpa only [hleft] using F.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeTernaryCoordinate
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def BinaryTensorIndex (I : Type*) : ℕ → Type _
  | 0 => I
  | n + 1 => BinaryTensorIndex I n × BinaryTensorIndex I n

instance BinaryTensorIndex.fintype (I : Type*) [Fintype I] (n : ℕ) : Fintype (BinaryTensorIndex I n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype I)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (BinaryTensorIndex I n × BinaryTensorIndex I n))

variable {σ I : Type*} [DecidableEq σ]

def coordinateTranslatedInput (l : List σ) (x : Option σ → ℤ) (i : σ) : ℤ :=
  x (some i) + if i ∈ l then x none else 0

def coordinateTranslationHom (l : List σ) (j : Option σ) : ((Option σ → ℤ) →+ ℤ) where
  toFun x := match j with
    | none => x none
    | some i => coordinateTranslatedInput l x i
  map_zero' := by cases j <;> simp [coordinateTranslatedInput]
  map_add' x y := by
    cases j with
    | none => rfl
    | some i =>
      simp only [coordinateTranslatedInput, Pi.add_apply]
      split_ifs <;> ring

def coordinateReplaceIndex (i : σ) (j : Option σ) : Option σ :=
  if j = some i then none else j

def coordinateReplaceInput (i : σ) (x : Option σ → ℤ) : Option σ → ℤ :=
  fun j => x (coordinateReplaceIndex i j)

theorem coordinateTranslation_sum (l : List σ) (i : σ) (hi : i ∉ l) (x : Option σ → ℤ) :
    coordinateAdditionInputs i (fun j => coordinateTranslationHom l j x) 0 =
      coordinateTranslatedInput (i :: l) x := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [coordinateAdditionInputs, coordinateTranslationHom, coordinateTranslatedInput, hi]
  · simp [coordinateAdditionInputs, coordinateTranslationHom, coordinateTranslatedInput, hj]

theorem coordinateTranslation_left (l : List σ) (i : σ) (x : Option σ → ℤ) :
    coordinateAdditionInputs i (fun j => coordinateTranslationHom l j x) 1 =
      coordinateTranslatedInput l x := rfl

theorem coordinateTranslation_right (l : List σ) (i : σ) (hi : i ∉ l) (x : Option σ → ℤ) :
    coordinateAdditionInputs i (fun j => coordinateTranslationHom l j x) 2 =
      coordinateTranslatedInput l (coordinateReplaceInput i x) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [coordinateAdditionInputs, coordinateTranslationHom, coordinateTranslatedInput,
      coordinateReplaceInput, coordinateReplaceIndex, hi]
  · simp [coordinateAdditionInputs, coordinateTranslationHom, coordinateTranslatedInput,
      coordinateReplaceInput, coordinateReplaceIndex, hj]

noncomputable def coordinateTranslationExpansion (f : I → (σ → ℤ) → ℂ) :
    (l : List σ) → BinaryTensorIndex I l.length → (Option σ → ℤ) → ℂ
  | [], a, x => f a (fun j => x (some j))
  | i :: l, a, x => coordinateTranslationExpansion f l a.1 x *
      coordinateTranslationExpansion f l a.2 (coordinateReplaceInput i x)

theorem coordinateTranslationExpansion_unit [Fintype I] (f : I → (σ → ℤ) → ℂ)
    (hunit : ∀ x, ∑ i, ‖f i x‖ ^ 2 = 1) (l : List σ) (x : Option σ → ℤ) :
    ∑ a : BinaryTensorIndex I l.length, ‖coordinateTranslationExpansion f l a x‖ ^ 2 = 1 := by
  induction l generalizing x with
  | nil => exact hunit _
  | cons i l ih =>
    change (∑ a : BinaryTensorIndex I l.length × BinaryTensorIndex I l.length,
      ‖coordinateTranslationExpansion f l a.1 x *
        coordinateTranslationExpansion f l a.2 (coordinateReplaceInput i x)‖ ^ 2) = 1
    simp only [Fintype.sum_prod_type, norm_mul, mul_pow, ← Finset.mul_sum, ih, mul_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def TernaryTensorIndex (I : Type*) : ℕ → Type _
  | 0 => I
  | n + 1 => TernaryTensorIndex I n × (TernaryTensorIndex I n × TernaryTensorIndex I n)

instance TernaryTensorIndex.fintype (I : Type*) [Fintype I] (n : ℕ) : Fintype (TernaryTensorIndex I n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype I)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (TernaryTensorIndex I n ×
      (TernaryTensorIndex I n × TernaryTensorIndex I n)))

variable {σ I : Type*} [DecidableEq σ]

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

theorem exists_coordinate_translation_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p)
      (l : List σ) (i : σ), i ∉ l →
      NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C)
        (fun k x => W.eval k (coordinateTranslatedInput (i :: l) x))
        (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
          W.eval k.1 (coordinateTranslatedInput l x) *
            W.eval k.2 (coordinateTranslatedInput l (coordinateReplaceInput i x))) := by
  obtain ⟨C, hC, hadd⟩ := exists_multilinearity_equivalence (σ := σ)
  refine ⟨C, hC, ?_⟩
  intro p W l i hi
  have E := (hadd W i).linearPullbackHom (coordinateTranslationHom l)
  simpa only [coordinateSumVector, coordinateTensorVector,
    coordinateTranslation_sum l i hi, coordinateTranslation_left,
    coordinateTranslation_right l i hi] using E

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerEquivalenceFiniteFamily
namespace OAI

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped BigOperators

theorem exists_fin_product_budget (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ I J : Type*} [Fintype I] [Fintype J] {s : ℕ} {p : ℝ}
      (f : Fin n → I → (σ → ℤ) → ℂ) (g : Fin n → J → (σ → ℤ) → ℂ),
      0 ≤ p → (Fintype.card I : ℝ) ≤ Real.exp p → (Fintype.card J : ℝ) ≤ Real.exp p →
      (∀ i, NativeIntegerVectorEquivalence s p (f i) (g i)) →
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun a : Fin n → I => fun x => ∏ i, f i (a i) x)
        (fun b : Fin n → J => fun x => ∏ i, g i (b i) x) := by
  obtain ⟨A, _, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget n
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + Polynomial.C n * X)
  refine ⟨C, hC, ?_⟩
  intro σ I J _ _ s p f g hp hI hJ E
  have hsum : (p + A) ^ A + n * p ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (p + A) ^ A ≤ (p + C) ^ C := by
    have hn : 0 ≤ (n : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
    linarith
  have hnp : (n : ℝ) * p ≤ (p + C) ^ C := by
    have ha : 0 ≤ (p + A) ^ A := by positivity
    linarith
  have hIn : (Fintype.card (Fin n → I) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp p) ^ n := pow_le_pow_left₀ (Nat.cast_nonneg _) hI n
      _ = Real.exp ((n : ℝ) * p) := (Real.exp_nat_mul p n).symm
      _ ≤ _ := Real.exp_le_exp.mpr hnp
  have hJn : (Fintype.card (Fin n → J) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp p) ^ n := pow_le_pow_left₀ (Nat.cast_nonneg _) hJ n
      _ = Real.exp ((n : ℝ) * p) := (Real.exp_nat_mul p n).symm
      _ ≤ _ := Real.exp_le_exp.mpr hnp
  refine ⟨hIn, hJn, ?_⟩
  intro a b
  obtain ⟨F⟩ := hprod (σ := σ) (w := fun _ : σ => 1) (s := s)
    (fun k x => f k (a k) x * star (g k (b k) x)) hp
    (fun k => (E k).expansion (a k) (b k))
  have heq : (fun x => ∏ k, f k (a k) x * star (g k (b k) x)) =
      (fun x => (∏ k, f k (a k) x) * star (∏ k, g k (b k) x)) := by
    funext x
    simp only [Finset.prod_mul_distrib, star_prod]
  exact ⟨heq ▸ F.mono hcost⟩

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped BigOperators

theorem conjugationPower {σ I J : Type*} [Fintype I] [Fintype J] {s : ℕ} {p : ℝ}
    {f : I → (σ → ℤ) → ℂ} {g : J → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p f g) (n : ℕ) :
    NativeIntegerVectorEquivalence s p
      (fun i x => Erdos3.conjugationPower n (f i x))
      (fun j x => Erdos3.conjugationPower n (g j x)) := by
  induction n with
  | zero => exact E
  | succ n ih => exact ih.conjugate

theorem exists_finite_product_budget (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ I J : Type*} [Fintype I] [Fintype J] {s : ℕ} {p : ℝ}
      (f : ι → I → (σ → ℤ) → ℂ) (g : ι → J → (σ → ℤ) → ℂ),
      0 ≤ p → (Fintype.card I : ℝ) ≤ Real.exp p → (Fintype.card J : ℝ) ≤ Real.exp p →
      (∀ i, NativeIntegerVectorEquivalence s p (f i) (g i)) →
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun a : ι → I => fun x => ∏ i, f i (a i) x)
        (fun b : ι → J => fun x => ∏ i, g i (b i) x) := by
  obtain ⟨C, hC, hprod⟩ := exists_fin_product_budget (Fintype.card ι)
  refine ⟨C, hC, ?_⟩
  intro σ I J _ _ s p f g hp hI hJ E
  classical
  let e := (Fintype.equivFin ι).symm
  have F := hprod (fun j => f (e j)) (fun j => g (e j)) hp hI hJ (fun j => E (e j))
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Fintype.card_fun, Fintype.card_fin] using F.left_dimension
  · simpa only [Fintype.card_fun, Fintype.card_fin] using F.right_dimension
  · intro a b
    have h := F.expansion (fun j => a (e j)) (fun j => b (e j))
    have hf (x : σ → ℤ) : (∏ j, f (e j) (a (e j)) x) = ∏ i, f i (a i) x :=
      e.prod_comp (fun i => f i (a i) x)
    have hg (x : σ → ℤ) : (∏ j, g (e j) (b (e j)) x) = ∏ i, g i (b i) x :=
      e.prod_comp (fun i => g i (b i) x)
    simpa only [hf, hg] using h

end Erdos3.NativeIntegerVectorEquivalence

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedEvaluationCoordinates
namespace OAI

section

namespace Erdos3

def mixedEvaluationEmbedding (s : ℕ) : Fin s ↪ ReplicatedIndex (mixedCorrelationDegree s) where
  toFun k := ⟨1, k⟩
  inj' := by
    intro i j hij
    exact Fin.ext (congrArg (fun z : ReplicatedIndex (mixedCorrelationDegree s) => z.2.val) hij)

def mixedEvaluationCoordinates (s : ℕ) : Finset (ReplicatedIndex (mixedCorrelationDegree s)) :=
  Finset.univ.map (mixedEvaluationEmbedding s)

@[simp] theorem mem_mixedEvaluationCoordinates (s : ℕ) (j : ReplicatedIndex (mixedCorrelationDegree s)) :
    j ∈ mixedEvaluationCoordinates s ↔ j.1 = 1 := by
  constructor
  · intro hj
    obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hj
    rfl
  · intro hj
    rcases j with ⟨j, k⟩
    dsimp only at hj
    subst j
    exact Finset.mem_map.mpr ⟨k, Finset.mem_univ _, rfl⟩

@[simp] theorem mixedEvaluationCoordinates_card (s : ℕ) :
    (mixedEvaluationCoordinates s).card = s := by
  simp only [mixedEvaluationCoordinates, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem mixedEvaluationCoordinates_erase_card (s : ℕ)
    (i : ReplicatedIndex (mixedCorrelationDegree s)) (hi : i.1 = 1) :
    ((mixedEvaluationCoordinates s).erase i).card = s - 1 := by
  rw [Finset.card_erase_of_mem ((mem_mixedEvaluationCoordinates s i).mpr hi),
    mixedEvaluationCoordinates_card]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedShiftCoordinate
namespace OAI

section

namespace Erdos3

def mixedShiftCoordinate (s : ℕ) : ReplicatedIndex (mixedCorrelationDegree s) :=
  ⟨0, ⟨0, by change 0 < 1; omega⟩⟩

theorem mixedShiftCoordinate_unique (s : ℕ) (j : ReplicatedIndex (mixedCorrelationDegree s))
    (hj : j.1 = 0) : j = mixedShiftCoordinate s := by
  rcases j with ⟨j, k⟩
  dsimp only at hj
  subst j
  dsimp only [mixedShiftCoordinate]
  apply congrArg (fun t : Fin (mixedCorrelationDegree s 0) =>
    (⟨0, t⟩ : ReplicatedIndex (mixedCorrelationDegree s)))
  apply Fin.ext
  have hk := k.isLt
  change k.val < 1 at hk
  change k.val = 0
  omega

theorem mixed_input_eq_coordinateConstant (s : ℕ) (h n : ℤ) :
    (fun j : ReplicatedIndex (mixedCorrelationDegree s) => correlationInput h n j.1) =
      coordinateConstantInput (mixedShiftCoordinate s) h n := by
  funext j
  by_cases hj : j = mixedShiftCoordinate s
  · subst j
    simp [coordinateConstantInput, mixedShiftCoordinate, correlationInput]
  · have hj₀ : j.1 ≠ 0 := fun h => hj (mixedShiftCoordinate_unique s j h)
    have hj₁ : j.1 = 1 := by
      apply Fin.ext
      have hlt := j.1.isLt
      have hne : j.1.val ≠ 0 := fun h => hj₀ (Fin.ext h)
      change j.1.val = 1
      omega
    rw [hj₁, coordinateConstantInput, Function.update_of_ne hj]
    rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinatePairs
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_coordinate_sum_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ]
    (bound : σ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (i : σ), bound i = 1 → ∀ {τ : Type*} [Fintype τ] (a b n : (τ → ℤ) →+ ℤ),
      NativeIntegerVectorEquivalence ((∑ j, bound j) - 1) ((p + C) ^ C)
        (fun k x => W.eval k (coordinateConstantInput i (a x + b x) (n x)))
        (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
          W.eval k.1 (coordinateConstantInput i (a x) (n x)) *
            W.eval k.2 (coordinateConstantInput i (b x) (n x))) := by
  obtain ⟨C, hC, hadd⟩ := exists_addition_equivalence bound
  refine ⟨C, hC, ?_⟩
  intro p W i hi τ _ a b n
  let A : Option σ → ((τ → ℤ) →+ ℤ) := fun j => match j with
    | none => b
    | some j => if j = i then a else n
  have hinput (x : τ → ℤ) : (fun j => A j x) = coordinatePairInput i (a x) (b x) (n x) := by
    funext j
    cases j with
    | none => rfl
    | some j =>
      by_cases hji : j = i <;> simp [A, coordinatePairInput, coordinateConstantInput, hji]
  have E := (hadd W i hi).linearPullbackHom A
  simpa only [coordinateSumVector, coordinateTensorVector, hinput,
    coordinatePairInput_sum, coordinatePairInput_left, coordinatePairInput_right] using E

theorem exists_coordinate_parallelogram_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ]
    (bound : σ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (i : σ), bound i = 1 → ∀ {τ : Type*} [Fintype τ] (u v w n : (τ → ℤ) →+ ℤ),
      NativeIntegerVectorEquivalence ((∑ j, bound j) - 1) ((p + C) ^ C)
        (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
          W.eval k.1 (coordinateConstantInput i (v x) (n x)) *
            W.eval k.2 (coordinateConstantInput i (w x) (n x)))
        (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
          W.eval k.1 (coordinateConstantInput i (u x) (n x)) *
            W.eval k.2 (coordinateConstantInput i (v x + w x - u x) (n x))) := by
  obtain ⟨a, _, hadd⟩ := exists_coordinate_sum_equivalence bound
  obtain ⟨c, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C a) ^ a + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p W i hi τ _ u v w n
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  let u₄ := v + w - u
  have hu₄ (x : τ → ℤ) : u₄ x = v x + w x - u x := rfl
  have hsum (x : τ → ℤ) : u x + u₄ x = v x + w x := by rw [hu₄]; ring
  have E₁ := hadd W i hi u u₄ n
  have E₂ := hadd W i hi v w n
  have E₁' : NativeIntegerVectorEquivalence ((∑ j, bound j) - 1) q
      (fun k x => W.eval k (coordinateConstantInput i (v x + w x) (n x)))
      (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
        W.eval k.1 (coordinateConstantInput i (u x) (n x)) *
          W.eval k.2 (coordinateConstantInput i (u₄ x) (n x))) := by
    simpa only [hsum] using E₁
  have R := htrans hq E₂.symm E₁' (fun x => W.unit_eval _)
  have hcost : (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  simpa only [hu₄] using R.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinateSplitFreezing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace VectorPolynomial

theorem eval_eq_of_support_agreement {σ R V : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] (p : VectorPolynomial σ R V) (x y : σ → R)
    (hxy : ∀ a, coefficients p a ≠ 0 → ∀ i, a i ≠ 0 → x i = y i) :
    eval x p = eval y p := by
  classical
  conv_lhs => rw [← sum_monomial_coefficients p]
  conv_rhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, eval_monomial, Finsupp.prod]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [hxy a (Finsupp.mem_support_iff.mp ha) i (Finsupp.mem_support_iff.mp hi)]

end VectorPolynomial

namespace MultidegreeLieFiltration

open VectorPolynomial

theorem polynomialOrbitEval_eq_on_active_coordinates {σ L : Type*} [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ} {bound : σ → ℕ}
    (F : MultidegreeLieFiltration σ L s bound) (g : F.PolynomialOrbit)
    (x y : σ → ℤ) (hxy : ∀ i, bound i ≠ 0 → x i = y i) :
    F.polynomialOrbitEval x g = F.polynomialOrbitEval y g := by
  apply NilpotentLieBCHGroup.ext
  apply VectorPolynomial.eval_eq_of_support_agreement (g.log F)
  intro a ha i hi
  have hle : (fun j => a j) ≤ bound := by
    by_contra hn
    have hc := g.adapted F a
    exact ha (by simpa only [F.terminal _ hn, Submodule.mem_bot] using hc)
  have hb : bound i ≠ 0 := by
    intro hz
    exact hi (Nat.eq_zero_of_le_zero (by simpa only [hz] using hle i))
  exact congrArg (fun z : ℤ => (z : ℚ)) (hxy i hb)

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [DecidableEq σ]

def coordinateSplitBound (s : ℕ) (i : σ) (b : Bool) (j : σ) : ℕ :=
  if b then (if j = i then s - 1 else s) else (if j = i then s else 0)

def coordinateSplitDownset (s : ℕ) (i : σ) (b : Bool) : Set (σ →₀ ℕ) :=
  {a | ∀ j, a j ≤ coordinateSplitBound s i b j}

theorem coordinateSplitBound_le (s : ℕ) (i : σ) (b : Bool) :
    coordinateSplitBound s i b ≤ fun _ => s := by
  intro j
  cases b <;> by_cases h : j = i <;> simp [coordinateSplitBound, h]

theorem coordinateSplitDownset_lower (s : ℕ) (i : σ) (b : Bool) :
    IsLowerSet (coordinateSplitDownset s i b) :=
  fun _ _ hab hb j => (hab j).trans (hb j)

theorem coordinateSplitDownset_covers [Fintype σ] (s : ℕ) (i : σ) (a : σ →₀ ℕ)
    (ha : (∑ j, a j) ≤ s) :
    a ∈ coordinateSplitDownset s i false ∪ coordinateSplitDownset s i true := by
  have hall (j : σ) : a j ≤ s :=
    (Finset.single_le_sum (fun k _ => Nat.zero_le (a k)) (Finset.mem_univ j)).trans ha
  by_cases hi : a i ≤ s - 1
  · right
    intro j
    by_cases hj : j = i
    · subst j
      simpa [coordinateSplitBound] using hi
    · simpa [coordinateSplitBound, hj] using hall j
  · left
    intro j
    by_cases hj : j = i
    · subst j
      simpa [coordinateSplitBound] using hall i
    · have htwo : a i + a j ≤ ∑ k, a k := by
        calc
          a i + a j = ∑ k ∈ ({i, j} : Finset σ), a k := by simp [Ne.symm hj]
          _ ≤ ∑ k, a k := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      have hz : a j = 0 := by omega
      simp [coordinateSplitBound, hj, hz]

theorem coordinateSplitDownset_terminal [Fintype σ] [Nonempty σ]
    {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s) (i : σ) (a : σ →₀ ℕ)
    (ha : a ∉ coordinateSplitDownset s i false ∪ coordinateSplitDownset s i true) :
    (F.totalDegreeMultifiltration σ).layer (fun j => a j) = ⊥ := by
  apply F.layer_eq_bot_above_step
  exact Nat.lt_of_not_ge (fun h => ha (coordinateSplitDownset_covers s i a h))

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeCoordinateSplit {σ : Type} [Fintype σ] [DecidableEq σ] [Nonempty σ]
    (i : σ) (s d : ℕ) (p epsilon : ℝ) (f : (σ → ℤ) → ℂ) where
  count : ℕ
  count_pos : 0 < count
  count_bound : (count : ℝ) ≤ Real.exp p
  L : Bool → Type
  [lie : ∀ b, LieRing (L b)]
  [algebra : ∀ b, LieAlgebra ℚ (L b)]
  dim : Bool → ℕ
  [topology : ∀ b, TopologicalSpace (ℝ ⊗[ℚ] L b)]
  [topologicalAdd : ∀ b, IsTopologicalAddGroup (ℝ ⊗[ℚ] L b)]
  [continuousSMul : ∀ b, ContinuousSMul ℝ (ℝ ⊗[ℚ] L b)]
  [hausdorff : ∀ b, T2Space (ℝ ⊗[ℚ] L b)]
  model : ∀ b, RationalFilteredNilmanifold (L b) (∑ _ : σ, s) (dim b)
  multi : ∀ b, (model b).MultidegreeStructure (coordinateSplitBound s i b)
  complexity : ∀ b, (multi b).ComplexityLE p
  dimension_bound : ∀ b, dim b ≤ 2 ^ (Fintype.card σ * s) * d
  orbit : ∀ b, (multi b).filtration.realification.PolynomialOrbit
  test : ∀ b, Fin count → (model b).Niltest (fun _ : σ => 1)
  test_norm : ∀ b j, (test b j).normBound ≤ 1
  test_complexity : ∀ b j, (test b j).ComplexityLE p
  test_orbit : ∀ b j, (test b j).orbit = (multi b).orbitToOrdinary (orbit b)
  approximation : ∀ x, ‖f x - ∑ j, (test false j).eval x * (test true j).eval x‖ ≤ epsilon

end Erdos3

end

section

namespace Erdos3.NativeCoordinateSplit

open scoped TensorProduct BigOperators

attribute [local instance] NativeCoordinateSplit.lie NativeCoordinateSplit.algebra NativeCoordinateSplit.topology NativeCoordinateSplit.topologicalAdd NativeCoordinateSplit.continuousSMul NativeCoordinateSplit.hausdorff

theorem exists_fixed_correlating_term {σ : Type} [Fintype σ] [DecidableEq σ] [Nonempty σ]
    {i : σ} {G X : Type*} {s d : ℕ} {p epsilon rho : ℝ} {u : (σ → ℤ) → ℂ}
    (R : NativeCoordinateSplit i s d p epsilon u) (H : Finset G) (hH : H.Nonempty)
    (S : G → Finset X) (hS : ∀ h ∈ H, (S h).Nonempty)
    (sample : G → X → σ → ℤ) (f : G → X → ℂ)
    (hrho : 0 < rho) (hepsilon : epsilon ≤ rho / 2)
    (hf : ∀ h ∈ H, ∀ x ∈ S h, ‖f h x‖ ≤ 1)
    (hcorr : ∀ h ∈ H, rho ≤ ‖𝔼 x ∈ S h, f h x * star (u (sample h x))‖) :
    ∃ (j : Fin R.count) (Q : Finset G), Q ⊆ H ∧ Q.Nonempty ∧
      Real.exp (-p) * (H.card : ℝ) ≤ (Q.card : ℝ) ∧
      ∀ h ∈ Q, rho / (2 * Real.exp p) ≤
        ‖𝔼 x ∈ S h, f h x * star ((R.test false j).eval (sample h x) *
          (R.test true j).eval (sample h x))‖ := by
  classical
  let rel (h : G) (_ : Unit) (j : Fin R.count) : Prop :=
    rho / (2 * Real.exp p) ≤
      ‖𝔼 x ∈ S h, f h x * star ((R.test false j).eval (sample h x) *
        (R.test true j).eval (sample h x))‖
  have hcount : (Fintype.card (Fin R.count) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using R.count_bound
  have hchoice : ∀ h ∈ H, ∀ b, ∃ j, rel h b j := by
    intro h hh _
    apply exists_correlating_summand (J := Fin R.count) (hS h hh)
      (f h) (fun x => u (sample h x))
      (fun j x => (R.test false j).eval (sample h x) * (R.test true j).eval (sample h x))
      hrho (Real.exp_pos p) hcount (hf h hh) _ (hcorr h hh)
    intro x _
    rw [norm_sub_rev]
    exact (R.approximation (sample h x)).trans hepsilon
  obtain ⟨j, Q, hsub, hQ, hsize, hfixed⟩ :=
    exists_large_fixed_choices H hH rel hchoice hcount
  refine ⟨j (), Q, hsub, hQ, ?_, fun h hh => hfixed h hh ()⟩
  simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hsize

end Erdos3.NativeCoordinateSplit

end

section

namespace Erdos3.NativeCoordinateSplit

open scoped TensorProduct

attribute [local instance] NativeCoordinateSplit.lie NativeCoordinateSplit.algebra NativeCoordinateSplit.topology NativeCoordinateSplit.topologicalAdd NativeCoordinateSplit.continuousSMul NativeCoordinateSplit.hausdorff

variable {σ : Type} [Fintype σ] [DecidableEq σ] [Nonempty σ] {i : σ} {s d : ℕ}
  {p epsilon : ℝ} {f : (σ → ℤ) → ℂ} (R : NativeCoordinateSplit i s d p epsilon f)

theorem first_eval_eq (j : Fin R.count) (x y : σ → ℤ) (hxy : x i = y i) :
    (R.test false j).eval x = (R.test false j).eval y := by
  unfold RationalFilteredNilmanifold.Niltest.eval
  rw [R.test_orbit false j, (R.multi false).orbitToOrdinary_eval,
    (R.multi false).orbitToOrdinary_eval]
  apply congrArg (R.test false j).observable
  apply congrArg QuotientGroup.mk
  apply (R.multi false).filtration.realification.polynomialOrbitEval_eq_on_active_coordinates
  intro k hk
  have hki : k = i := by
    by_contra hn
    exact hk (by simp [coordinateSplitBound, hn])
  subst k
  exact hxy

noncomputable def firstFactor (j : Fin R.count) (n : ℤ) : ℂ :=
  (R.test false j).eval (fun _ => n)

theorem first_eval_firstFactor (j : Fin R.count) (x : σ → ℤ) :
    (R.test false j).eval x = R.firstFactor j (x i) :=
  R.first_eval_eq j x (fun _ => x i) rfl

theorem firstFactor_norm (j : Fin R.count) (n : ℤ) : ‖R.firstFactor j n‖ ≤ 1 :=
  ((R.test false j).norm_eval_le _).trans
    (show ((R.test false j).normBound : ℝ) ≤ 1 from R.test_norm false j)

end Erdos3.NativeCoordinateSplit

end

section

namespace Erdos3.NativeCoordinateSplit

open Module RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators

attribute [local instance] NativeCoordinateSplit.lie NativeCoordinateSplit.algebra NativeCoordinateSplit.topology NativeCoordinateSplit.topologicalAdd NativeCoordinateSplit.continuousSMul NativeCoordinateSplit.hausdorff

theorem exists_second_expansion_budget (σ : Type) [Fintype σ] [DecidableEq σ] [Nonempty σ]
    (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {i : σ} {d : ℕ} {p epsilon : ℝ} {f : (σ → ℤ) → ℂ}
      (R : NativeCoordinateSplit i s d p epsilon f) (j : Fin R.count) (b : σ → ℤ),
      ∃ E : NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) ((p + C) ^ C)
          (fun x => (R.test true j).eval (Function.update b i (x ()))), E.count = 1 := by
  obtain ⟨C, hC, hfreeze⟩ := exists_controlled_frozen_niltest (∑ _ : σ, s)
  refine ⟨C, hC, ?_⟩
  intro i d p epsilon f R j b
  classical
  let S : Finset σ := {i}
  have hp : 0 ≤ p := (Nat.cast_nonneg (R.dim true)).trans (R.complexity true).1.1
  have hlip : ((R.test true j).lipBound : ℝ) ≤ Real.exp p := by
    have hb := (R.test true j).observable_budget (R.test_complexity true j)
    have hn := (R.test true j).normBound.coe_nonneg
    linarith
  have hub : ∀ x, ‖(R.test true j).observable x‖ ≤ (1 : ℝ) := fun x =>
    ((R.test true j).norm_le x).trans
      (show ((R.test true j).normBound : ℝ) ≤ 1 from R.test_norm true j)
  obtain ⟨E, _, _, hE⟩ := hfreeze (R.model true) (R.multi true) S b
    (R.orbit true) (R.test true j).observable (R.test true j).lipBound 1
    (R.test true j).lipschitz hub (R.complexity true) hlip
    (by simpa only [NNReal.coe_one] using Real.one_le_exp hp)
  let K := (R.multi true).filtration.weightedSubalgebra (retainedCoordinateWeight S)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 E.basis
  obtain ⟨T, _, hT, _, hTeval⟩ := hE
  let U := T.affinePullback (fun _ (_ : Unit) => (1 : ℤ)) 0
  have hU : U.ComplexityLE ((p + C) ^ C) := hT
  have hval (x : Unit → ℤ) : U.eval x = (R.test true j).eval (Function.update b i (x ())) := by
    rw [RationalFilteredNilmanifold.Niltest.eval_affinePullback, hTeval]
    unfold RationalFilteredNilmanifold.Niltest.eval
    rw [R.test_orbit true j, (R.multi true).orbitToOrdinary_eval]
    congr 2
    apply congrArg (fun z => (R.multi true).filtration.realification.polynomialOrbitEval z
      (R.orbit true))
    funext k
    by_cases hk : k = i
    · subst k
      simp [S, freezeCoordinates, integerAffineMap]
    · simp [S, freezeCoordinates, hk]
  have hdegree : multidegreeWeight (retainedCoordinateWeight S) (coordinateSplitBound s i true) =
      s - 1 := by
    rw [retainedCoordinate_degree]
    simp [S, coordinateSplitBound]
  have hresult : ∃ Q : NativeIntegerExpansion (fun _ : Unit => 1)
      (multidegreeWeight (retainedCoordinateWeight S) (coordinateSplitBound s i true))
      ((p + C) ^ C) (fun x => (R.test true j).eval (Function.update b i (x ()))), Q.count = 1 :=
    ⟨NativeIntegerExpansion.ofTest U hU (fun x => (hval x).symm), rfl⟩
  exact hdegree ▸ hresult

end Erdos3.NativeCoordinateSplit

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeFrozenAffineExpansion
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open Module
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_frozen_affine_expansion {σ : Type*} [Fintype σ] [DecidableEq σ]
    (bound : σ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (S : Finset σ) (A b : σ → ℤ) (k : Fin W.outputDim),
      (∀ i, i ∉ S → A i = 0) →
      ∃ E : NativeIntegerExpansion (fun _ : Unit => 1) (∑ i ∈ S, bound i) ((p + C) ^ C)
          (fun x => W.eval k (fun i => b i + A i * x ())), E.count = 1 := by
  obtain ⟨C, hC, hfreeze⟩ := exists_freezing_niltest bound
  refine ⟨C, hC, ?_⟩
  intro p W S A b k hA
  classical
  obtain ⟨t, n, ht, _, D, hD⟩ := hfreeze W S b k
  subst t
  let K := W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 D.basis
  obtain ⟨T, _, hT, _, heval⟩ := hD
  let U := T.affinePullback (fun i (_ : Unit) => A i.val) (fun i => b i.val)
  have hU : U.ComplexityLE ((p + C) ^ C) := hT
  have hval (x : Unit → ℤ) : U.eval x = W.eval k (fun i => b i + A i * x ()) := by
    rw [RationalFilteredNilmanifold.Niltest.eval_affinePullback, heval]
    congr 1
    funext i
    by_cases hi : i ∈ S
    · simp [freezeCoordinates, hi, integerAffineMap]
    · simp [freezeCoordinates, hi, hA i hi]
  exact ⟨NativeIntegerExpansion.ofTest U hU (fun x => (hval x).symm), rfl⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformDerivativeLatticeExtraction
namespace OAI

section

namespace Erdos3

theorem derivative_covolume_budget_le_exp (d n : ℕ) (R δ p : ℝ)
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hn : (n : ℝ) ≤ p)
    (hR0 : 0 ≤ R) (hR : R ≤ Real.exp p) (hδ : 0 < δ)
    (hδinv : δ⁻¹ ≤ Real.exp p) :
    (((d : ℝ) + 2) * ((n : ℝ) * R)) ^ d / δ ≤ Real.exp (3 * p ^ 2 + 2 * p) := by
  have hd2 : (d : ℝ) + 2 ≤ Real.exp (p + 1) := by
    exact (by linarith : (d : ℝ) + 2 ≤ (p + 1) + 1).trans (Real.add_one_le_exp (p + 1))
  have hnexp : (n : ℝ) ≤ Real.exp p :=
    hn.trans ((show p ≤ p + 1 by linarith).trans (Real.add_one_le_exp p))
  have hbase : ((d : ℝ) + 2) * ((n : ℝ) * R) ≤ Real.exp (3 * p + 1) := by
    calc
      _ ≤ Real.exp (p + 1) * (Real.exp p * Real.exp p) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc
    _ ≤ Real.exp (3 * p + 1) ^ d * Real.exp p := by
      rw [div_eq_mul_inv]
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) hbase d) hδinv
        (inv_nonneg.mpr hδ.le) (by positivity)
    _ = Real.exp ((d : ℝ) * (3 * p + 1) + p) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (3 * p ^ 2 + 2 * p) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hd (by positivity : 0 ≤ 3 * p + 1)]

theorem derivative_extended_budget_le_exp (k l : ℕ) (C p : ℝ)
    (hp : 0 ≤ p) (hk : (k : ℝ) ≤ p) (hl : (l : ℝ) ≤ Real.exp p)
    (hC : C ≤ Real.exp (3 * p ^ 2 + 2 * p)) :
    C * (l : ℝ) ^ k ≤ Real.exp (4 * p ^ 2 + 2 * p) := by
  calc
    _ ≤ Real.exp (3 * p ^ 2 + 2 * p) * Real.exp p ^ k := by
      exact mul_le_mul hC (pow_le_pow_left₀ (Nat.cast_nonneg l) hl k)
        (pow_nonneg (Nat.cast_nonneg l) k) (Real.exp_nonneg _)
    _ = Real.exp (3 * p ^ 2 + 2 * p + (k : ℝ) * p) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (4 * p ^ 2 + 2 * p) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hk hp]

theorem derivative_output_exponent_le {p : ℝ} (hp : 0 ≤ p) :
    4 * p ^ 2 + 4 * p + 1 ≤ (p + 2) ^ 3 := by
  nlinarith [pow_nonneg hp 3]

theorem derivative_output_budgets_le_exp (n k l : ℕ) (B p : ℝ)
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hk : (k : ℝ) ≤ p)
    (hl : (l : ℝ) ≤ Real.exp p) (hB : B ≤ Real.exp (4 * p ^ 2 + 2 * p)) :
    B ≤ Real.exp ((p + 2) ^ 3) ∧
      (n : ℝ) * k * B ≤ Real.exp ((p + 2) ^ 3) ∧
      (l : ℝ) * B ≤ Real.exp ((p + 2) ^ 3) ∧
      (Nat.ceil B : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
  have hne : (n : ℝ) ≤ Real.exp p :=
    hn.trans ((show p ≤ p + 1 by linarith).trans (Real.add_one_le_exp p))
  have hke : (k : ℝ) ≤ Real.exp p :=
    hk.trans ((show p ≤ p + 1 by linarith).trans (Real.add_one_le_exp p))
  have hpoly := derivative_output_exponent_le hp
  have h0 : 4 * p ^ 2 + 2 * p ≤ (p + 2) ^ 3 := by linarith
  have h1 : 4 * p ^ 2 + 3 * p ≤ (p + 2) ^ 3 := by linarith
  have h2 : 4 * p ^ 2 + 4 * p ≤ (p + 2) ^ 3 := by linarith
  have h3 : 4 * p ^ 2 + 2 * p + 1 ≤ (p + 2) ^ 3 := by linarith
  refine ⟨hB.trans (Real.exp_le_exp.mpr h0), ?_, ?_, ?_⟩
  · calc
      _ ≤ (n : ℝ) * k * Real.exp (4 * p ^ 2 + 2 * p) := by gcongr
      _ ≤ Real.exp p * Real.exp p * Real.exp (4 * p ^ 2 + 2 * p) := by gcongr
      _ = Real.exp (4 * p ^ 2 + 4 * p) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr h2
  · calc
      _ ≤ (l : ℝ) * Real.exp (4 * p ^ 2 + 2 * p) := by gcongr
      _ ≤ Real.exp p * Real.exp (4 * p ^ 2 + 2 * p) := by gcongr
      _ = Real.exp (4 * p ^ 2 + 3 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr h1
  · calc
      (Nat.ceil B : ℝ) ≤ Nat.ceil (Real.exp (4 * p ^ 2 + 2 * p)) := by
        exact_mod_cast Nat.ceil_mono hB
      _ ≤ Real.exp (4 * p ^ 2 + 2 * p + 1) := ceil_exp_le_exp_add_one (by positivity)
      _ ≤ _ := Real.exp_le_exp.mpr h3

theorem derivative_projection_budget_le_exp (n : ℕ) (R δ p : ℝ)
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hR0 : 0 ≤ R) (hR : R ≤ Real.exp p)
    (hδ : 0 < δ) (hδinv : δ⁻¹ ≤ Real.exp p) :
    (3 * R) ^ (n - 1) / δ ≤ Real.exp ((p + 2) ^ 3) := by
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hbase : 3 * R ≤ Real.exp (p + 2) := by
    calc
      _ ≤ Real.exp 2 * Real.exp p := mul_le_mul hthree hR hR0 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hn' : ((n - 1 : ℕ) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (Nat.sub_le n 1)).trans hn
  calc
    _ ≤ Real.exp (p + 2) ^ (n - 1) * Real.exp p := by
      rw [div_eq_mul_inv]
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) hbase _) hδinv
        (inv_nonneg.mpr hδ.le) (by positivity)
    _ = Real.exp (((n - 1 : ℕ) : ℝ) * (p + 2) + p) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (p ^ 2 + 3 * p) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hn' (by positivity : 0 ≤ p + 2)]
    _ ≤ Real.exp ((p + 2) ^ 3) := by
      apply Real.exp_le_exp.mpr
      nlinarith [derivative_output_exponent_le hp, sq_nonneg p]

end Erdos3

end

section

namespace Erdos3

theorem lattice_subspace_budgets_le_exp
    {σ : Type*} [Fintype σ] {m : ℕ}
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ Fin m))) (V : Submodule ℝ Z)
    (l : ℕ) (R δ p : ℝ) (hp : 0 ≤ p)
    (hdim : ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) ≤ p)
    (hl : (l : ℝ) ≤ Real.exp p) (hR0 : 0 ≤ R) (hR : R ≤ Real.exp p)
    (hδ : 0 < δ) (hδinv : δ⁻¹ ≤ Real.exp p) :
    let n := Fintype.card σ + Fintype.card (Fin m)
    let d := Module.finrank ℝ Z
    let k := Module.finrank ℝ V
    let C := (((d : ℝ) + 2) * ((n : ℝ) * R)) ^ d / δ
    let B := C * (l : ℝ) ^ k
    C * (l : ℝ) ^ m ≤ Real.exp ((p + 2) ^ 3) ∧
      B ≤ Real.exp ((p + 2) ^ 3) ∧
      (n : ℝ) * k * B ≤ Real.exp ((p + 2) ^ 3) ∧
      (l : ℝ) * B ≤ Real.exp ((p + 2) ^ 3) ∧
      (Nat.ceil B : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
  let n := Fintype.card σ + Fintype.card (Fin m)
  let d := Module.finrank ℝ Z
  let k := Module.finrank ℝ V
  let C := (((d : ℝ) + 2) * ((n : ℝ) * R)) ^ d / δ
  let B := C * (l : ℝ) ^ k
  have hdn : d ≤ n := by
    simpa only [finrank_euclideanSpace, Fintype.card_sum] using Z.finrank_le
  have hdp : (d : ℝ) ≤ p := (Nat.cast_le.mpr hdn).trans hdim
  have hkp : (k : ℝ) ≤ p := (Nat.cast_le.mpr V.finrank_le).trans hdp
  have hmp : (m : ℝ) ≤ p := by
    have hmn : m ≤ n := by simp [n]
    exact (Nat.cast_le.mpr hmn).trans hdim
  have hC : C ≤ Real.exp (3 * p ^ 2 + 2 * p) :=
    derivative_covolume_budget_le_exp d n R δ p hp hdp hdim hR0 hR hδ hδinv
  have hB : B ≤ Real.exp (4 * p ^ 2 + 2 * p) :=
    derivative_extended_budget_le_exp k l C p hp hkp hl hC
  have hthreshold : C * (l : ℝ) ^ m ≤ Real.exp ((p + 2) ^ 3) := by
    apply (derivative_extended_budget_le_exp m l C p hp hmp hl hC).trans
    apply Real.exp_le_exp.mpr
    have he := derivative_output_exponent_le hp
    linarith
  exact ⟨hthreshold, derivative_output_budgets_le_exp n k l B p hp hdim hkp hl hB⟩

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_lattice_extraction
    {σ : Type*} [Fintype σ] [DecidableEq σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 1 ≤ R) (hδ : 0 < δ)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → Fin m → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (hlarge : ∀ i, (3 * R) ^ (Fintype.card σ - 1) < δ * T i)
    (a : ℕ) (ha : a ≤ m) (Tmin : ℝ)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i) :
    let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let ρ := ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T hT0 scale hs0 Y A l hl
    let Z := shortVectorSpan Λ ρ
    let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
    let V := LinearMap.ker π
    let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
    let k := Module.finrank ℝ V
    let C := (((Module.finrank ℝ Z : ℝ) + 2) * ρ) ^ Module.finrank ℝ Z / δ
    let B := C * (l : ℝ) ^ k
    let N := (Fintype.card (σ ⊕ Fin m) : ℝ) * k * B
    C * (l : ℝ) ^ m < Tmin →
      ∃ lifts : RationalHorizontalLift k P ha A scale N (Nat.ceil B),
        ∃ I : ℕ, 0 < I ∧ (I : ℝ) ≤ B ∧
          ∀ i, ∃ (s r' : Fin m → ℝ) (q : LinearMap.range P),
            Y (Pi.basisFun ℝ σ i) = s + A r' + lifts.geometricLift q ∧
            r' ∈ realDenominatorGrid (l * I) ∧
            ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * s j)‖ ≤ B / T i := by
  let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
  let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
  let ρ := ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) * R
  let Λ := euclideanDerivativeLattice T hT0 scale hs0 Y A l hl
  let Z := shortVectorSpan Λ ρ
  let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
  let V := LinearMap.ker π
  let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
  let k := Module.finrank ℝ V
  let C := (((Module.finrank ℝ Z : ℝ) + 2) * ρ) ^ Module.finrank ℝ Z / δ
  let B := C * (l : ℝ) ^ k
  let N := (Fintype.card (σ ⊕ Fin m) : ℝ) * k * B
  let I := (latticeImage (shortVectorLattice Λ ρ) π).toAddSubgroup.relIndex
    integerCoordinateLattice.toAddSubgroup
  change C * (l : ℝ) ^ m < Tmin →
    ∃ lifts : RationalHorizontalLift k P ha A scale N (Nat.ceil B),
      ∃ I : ℕ, 0 < I ∧ (I : ℝ) ≤ B ∧
        ∀ i, ∃ (s r' : Fin m → ℝ) (q : LinearMap.range P),
          Y (Pi.basisFun ℝ σ i) = s + A r' + lifts.geometricLift q ∧
          r' ∈ realDenominatorGrid (l * I) ∧
          ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * s j)‖ ≤ B / T i
  intro hvertical
  obtain ⟨hI, G, hG, _, hcov, hIB, hGB⟩ := euclideanDerivative_index_graph_bounds
    T hT scale hscale Y A hA hdiag l hl R δ hR hδ H r hr hnorm hdense hlarge
  obtain ⟨lifts, hrecovers⟩ := euclideanDerivative_horizontal_lifts T hT0 scale hscale
    Y A hA hdiag l hl ρ a ha Tmin C hscalehor hblock hfar hvertical hcov
  refine ⟨lifts, I, hI, hIB, ?_⟩
  have hGbasis (i) : ‖G (Pi.basisFun ℝ σ i)‖ ≤ B :=
    (euclidean_section_basis_norm_le_gram_sqrt Z G hG i).trans hGB
  have hI_lifts (i) : ∃ v : Z, v.val ∈ Λ ∧
      euclideanDerivativeShiftMap T hT0 v.val = (I : ℝ) • Pi.basisFun ℝ σ i := by
    obtain ⟨v, hv, hπv⟩ := latticeImage_basis_lifts (shortVectorLattice Λ ρ) π i
    exact ⟨v, hv, hπv⟩
  exact indexed_derivative_decomposition (σ := σ) (m := m) (a := a) (k := k)
    T hT0 (fun i => lt_of_lt_of_le zero_lt_one (hT i)) scale hs0 Y A l hl Z ha N B
    (Nat.ceil B) lifts hrecovers G hG hGbasis I hI hI_lifts

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_uniform_lattice_extraction
    {σ : Type*} [Fintype σ] [DecidableEq σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 1 ≤ R) (hδ : 0 < δ)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → Fin m → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (a : ℕ) (ha : a ≤ m) (Tmin : ℝ)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i)
    (p : ℝ) (hp : 0 ≤ p)
    (hdim : ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) ≤ p)
    (hlcap : (l : ℝ) ≤ Real.exp p) (hRcap : R ≤ Real.exp p)
    (hδcap : δ⁻¹ ≤ Real.exp p)
    (hmin : Real.exp ((p + 2) ^ 3) < Tmin) (hside : ∀ i, Tmin ≤ T i) :
    let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let ρ := ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T hT0 scale hs0 Y A l hl
    let Z := shortVectorSpan Λ ρ
    let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
    let V := LinearMap.ker π
    let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
    let k := Module.finrank ℝ V
    let C := (((Module.finrank ℝ Z : ℝ) + 2) * ρ) ^ Module.finrank ℝ Z / δ
    let B := C * (l : ℝ) ^ k
    let N := (Fintype.card (σ ⊕ Fin m) : ℝ) * k * B
    let E := Real.exp ((p + 2) ^ 3)
    ∃ lifts : RationalHorizontalLift k P ha A scale N (Nat.ceil B),
      N ≤ E ∧ (Nat.ceil B : ℝ) ≤ E ∧
        ∃ I : ℕ, 0 < I ∧ ((l * I : ℕ) : ℝ) ≤ E ∧
          ∀ i, ∃ (s r' : Fin m → ℝ) (q : LinearMap.range P),
            Y (Pi.basisFun ℝ σ i) = s + A r' + lifts.geometricLift q ∧
            r' ∈ realDenominatorGrid (l * I) ∧
            ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * s j)‖ ≤ E / T i := by
  let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
  let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
  let ρ := ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) * R
  let Λ := euclideanDerivativeLattice T hT0 scale hs0 Y A l hl
  let Z := shortVectorSpan Λ ρ
  let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
  let V := LinearMap.ker π
  let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
  let k := Module.finrank ℝ V
  let C := (((Module.finrank ℝ Z : ℝ) + 2) * ρ) ^ Module.finrank ℝ Z / δ
  let B := C * (l : ℝ) ^ k
  let N := (Fintype.card (σ ⊕ Fin m) : ℝ) * k * B
  let E := Real.exp ((p + 2) ^ 3)
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  obtain ⟨hthreshold, hBE, hNE, hlBE, hheight⟩ :=
    lattice_subspace_budgets_le_exp Z V l R δ p hp hdim hlcap hR0 hRcap hδ hδcap
  have hN : N ≤ E := by
    simpa only [N, Fintype.card_sum] using hNE
  have hσ : (Fintype.card σ : ℝ) ≤ p := by
    have hd : (Fintype.card σ : ℝ) + Fintype.card (Fin m) ≤ p := by exact_mod_cast hdim
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Fin m))]
  have hprojection := derivative_projection_budget_le_exp (Fintype.card σ) R δ p
    hp hσ hR0 hRcap hδ hδcap
  have hlarge : ∀ i, (3 * R) ^ (Fintype.card σ - 1) < δ * T i := by
    intro i
    have hi := (div_lt_iff₀ hδ).mp (hprojection.trans_lt (hmin.trans_le (hside i)))
    simpa only [mul_comm] using hi
  have hvertical : C * (l : ℝ) ^ m < Tmin := hthreshold.trans_lt hmin
  obtain ⟨lifts, I, hI, hIB, hdecomp⟩ := euclideanDerivative_lattice_extraction
    T hT scale hscale Y A hA hdiag l hl R δ hR hδ H r hr hnorm hdense hlarge
    a ha Tmin hscalehor hblock hfar hvertical
  refine ⟨lifts, hN, hheight, I, hI, ?_, ?_⟩
  · rw [Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_left hIB (Nat.cast_nonneg l)).trans hlBE
  · intro i
    obtain ⟨s, r', q, heq, hr', hs⟩ := hdecomp i
    refine ⟨s, r', q, heq, hr', ?_⟩
    exact hs.trans (div_le_div_of_nonneg_right hBE (zero_le_one.trans (hT i)))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CoordinateNiltestSplitting
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial RationalFilteredNilmanifold
open RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators NNReal

theorem exists_coordinate_niltest_splitting (σ : Type) [Fintype σ] [DecidableEq σ] [Nonempty σ]
    (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (i : σ) {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {D : RationalFilteredNilmanifold L s d} {p : ℝ}
      (T : D.Niltest (fun _ : σ => 1)), T.ComplexityLE p → T.normBound ≤ 1 →
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      Nonempty (NativeCoordinateSplit i s d ((p + C) ^ C) epsilon T.eval) := by
  obtain ⟨C, hC, hsplit⟩ := exists_two_downset_splitting s (Fintype.card σ * s) a
  refine ⟨C, hC, ?_⟩
  intro i L _ _ _ _ _ _ d D p T hT hnorm epsilon hepsilon hscale
  classical
  let M := D.totalDegreeMultidegree σ hT.1
  let J := coordinateSplitDownset s i
  have hJ : ∀ b, IsLowerSet (J b) := coordinateSplitDownset_lower s i
  let K := fun b => M.filtration.positivePolynomialAlgebra ⧸
    restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J b) (hJ b)
  let : ∀ b, TopologicalSpace (ℝ ⊗[ℚ] K b) := fun _ => moduleTopology ℝ _
  let : ∀ b, IsTopologicalAddGroup (ℝ ⊗[ℚ] K b) :=
    fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ b, T2Space (ℝ ⊗[ℚ] K b) :=
    fun b => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J b) (hJ b) p)
  let g := D.filtration.realTotalDegreeOrbit T.orbit
  have hsum : (∑ _ : σ, s) = Fintype.card σ * s := by simp
  have hM : M.ComplexityLE p := D.totalDegreeMultidegree_complexity σ hT.1
  have hcover : ∀ c, c ≠ 0 → c ∉ J false ∪ J true →
      M.filtration.layer (fun j => c j) = ⊥ :=
    fun c _ hc => coordinateSplitDownset_terminal D.filtration i c hc
  obtain ⟨r, _, _, B, hB, hstable, hresult⟩ :=
    hsplit M J hJ p hsum hM hcover g epsilon hepsilon hscale
  obtain ⟨hE, hdim, hterminal, h, _, happrox⟩ := hresult
  have hlip : (T.lipBound : ℝ) ≤ Real.exp p := by
    have hb := T.observable_budget hT
    have hn := T.normBound.coe_nonneg
    linarith
  have hub : ∀ x, ‖T.observable x‖ ≤ 1 := fun x =>
    (T.norm_le x).trans (show (T.normBound : ℝ) ≤ 1 from hnorm)
  obtain ⟨N, hN, hNbound, A, B', hAnorm, hBnorm, hA, hB', hAg, hBg, herr⟩ :=
    happrox T.observable T.lipBound hlip T.lipschitz hub
  let E := fun b => M.positivePolynomialDownsetModel (J b) (hJ b) r B hB hstable
  let F := fun b => M.positivePolynomialDownsetModelMultidegree (J b) (hJ b) r B hB hstable
  have hzero (b : Bool) (v : σ → ℕ) (hv : ¬v ≤ coordinateSplitBound s i b) :
      (F b).filtration.layer v = ⊥ := by
    let c : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm v
    exact hterminal b c hv
  let R := fun b => (F b).restrictBound (coordinateSplitBound s i b)
    (coordinateSplitBound_le s i b) (hzero b)
  let tests : ∀ b, Fin N → (E b).Niltest (fun _ : σ => 1) :=
    fun b => match b with
      | false => A
      | true => B'
  refine ⟨{
    count := N
    count_pos := hN
    count_bound := hNbound
    L := K
    dim := fun b => Fintype.card (M.PositivePolynomialDownsetIndex (J b))
    model := E
    multi := R
    complexity := fun b => (F b).restrictBound_complexity (coordinateSplitBound s i b)
      (coordinateSplitBound_le s i b) (hzero b) (hE b)
    dimension_bound := hdim
    orbit := fun b => (F b).filtration.restrictBoundRealOrbit (coordinateSplitBound s i b)
      (hzero b) (M.filtration.positivePolynomialDownsetOrbit (J b) (hJ b) h)
    test := tests
    test_norm := ?_
    test_complexity := ?_
    test_orbit := ?_
    approximation := ?_ }⟩
  · intro b j
    cases b
    · exact hAnorm j
    · exact hBnorm j
  · intro b j
    cases b
    · exact hA j
    · exact hB' j
  · intro b j
    cases b
    · exact hAg j
    · exact hBg j
  · intro x
    change ‖T.eval x - ∑ j, (A j).eval x * (B' j).eval x‖ ≤ epsilon
    have heval : T.observable (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)) =
        T.eval x := by
      change T.observable (QuotientGroup.mk
        ((D.filtration.totalDegreeMultifiltration σ).realification.polynomialOrbitEval x
          (D.filtration.realTotalDegreeOrbit T.orbit))) = _
      rw [D.filtration.realTotalDegreeOrbit_eval]
      rfl
    simpa only [heval] using herr x

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.MissingCoordinateNiltestApproximation
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct

theorem niltest_eval_eq_of_zero_coordinate {σ L : Type*} [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
    (M : D.MultidegreeStructure bound) (i : σ) (hi : bound i = 0)
    (T : D.Niltest (fun _ : σ => 1)) (g : M.filtration.realification.PolynomialOrbit)
    (hT : T.orbit = M.orbitToOrdinary g) (x y : σ → ℤ)
    (hxy : ∀ j, j ≠ i → x j = y j) : T.eval x = T.eval y := by
  unfold RationalFilteredNilmanifold.Niltest.eval
  rw [hT, M.orbitToOrdinary_eval, M.orbitToOrdinary_eval]
  apply congrArg T.observable
  apply congrArg QuotientGroup.mk
  exact M.filtration.realification.polynomialOrbitEval_eq_of_zero_coordinate i hi g x y hxy

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3

open Module VectorPolynomial RationalFilteredNilmanifold
open RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators NNReal

theorem exists_missing_coordinate_niltest_approximation (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {D : RationalFilteredNilmanifold L s d} {p : ℝ}
      (T : D.Niltest (fun _ : Fin (s + 1) => 1)), T.ComplexityLE p → T.normBound ≤ 1 →
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (c : Fin m → ℂ) (F : Fin (s + 1) → Fin m → (Fin (s + 1) → ℤ) → ℂ),
          (∀ j, ‖c j‖ ≤ 2) ∧ (∀ i j x, ‖F i j x‖ ≤ 1) ∧
          (∀ i j x y, (∀ k, k ≠ i → x k = y k) → F i j x = F i j y) ∧
          ∀ x, ‖T.eval x - ∑ j, c j * ∏ i, F i j x‖ ≤ epsilon := by
  obtain ⟨B, _, hsplit⟩ := exists_multidegree_downset_splitting s ((s + 1) * s) a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C (s + 1) + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p T hT hnorm epsilon hepsilon hscale
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hT.1.1
  let q := p + (s + 1 : ℕ)
  have hpq : p ≤ q := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hq : 0 ≤ q := hp.trans hpq
  have hcost : (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  let M := D.totalDegreeMultidegree (Fin (s + 1)) hT.1
  let J := missingCoordinateDownset s
  have hJ : ∀ i, IsLowerSet (J i) := missingCoordinateDownset_lower s
  let K := fun i => M.filtration.positivePolynomialAlgebra ⧸
    restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] K i) := fun _ => moduleTopology ℝ _
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] K i) :=
    fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ i, T2Space (ℝ ⊗[ℚ] K i) :=
    fun i => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J i) (hJ i) q)
  have hM : M.ComplexityLE q := (D.totalDegreeMultidegree_complexity (Fin (s + 1)) hT.1).mono M hpq
  have hfamily : (Fintype.card (Fin (s + 1)) : ℝ) ≤ q + 2 := by
    simp only [Fintype.card_fin]
    dsimp [q]
    linarith only [hp]
  have hcover : ∀ b, b ≠ 0 → (∀ i, b ∉ J i) → M.filtration.layer (fun k => b k) = ⊥ :=
    fun b _ hb => missingCoordinateDownset_terminal D.filtration b hb
  have hscaleq : 1 / epsilon ≤ Real.exp ((q + 2) ^ a) :=
    hscale.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith only [hpq]) a))
  obtain ⟨r, _, _, b, hb, hstable, hE, _, h, _, n, hn, _, hcount, U,
    hUnorm, _, _, hUorbit, happrox⟩ :=
    hsplit (I := Unit) (α := Fin (s + 1)) M J hJ q (by simp) hM hfamily hcover
      (D.filtration.realTotalDegreeOrbit T.orbit) epsilon hepsilon hscaleq
      (by simpa using Real.one_le_exp hq)
  let V := fun i => M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) r b hb hstable
  have hzero (i : Fin (s + 1)) (v : Fin (s + 1) → ℕ)
      (hv : ¬v ≤ missingCoordinateBound s i) : (V i).filtration.layer v = ⊥ := by
    let c : Fin (s + 1) →₀ ℕ := Finsupp.equivFunOnFinite.symm v
    exact M.filtration.positivePolynomialDownsetQuotient_terminal (J i) (hJ i) c hv
  let V' := fun i => (V i).restrictBound (missingCoordinateBound s i)
    (missingCoordinateBound_le s i) (hzero i)
  have hindependent (i : Fin (s + 1)) (j : Fin (n i)) (x y : Fin (s + 1) → ℤ)
      (hxy : ∀ k, k ≠ i → x k = y k) : (U i j).eval x = (U i j).eval y := by
    let g : (V i).filtration.realification.PolynomialOrbit :=
      M.filtration.positivePolynomialDownsetOrbit (J i) (hJ i) h
    let g' := (V i).filtration.restrictBoundRealOrbit (missingCoordinateBound s i) (hzero i) g
    exact (V' i).niltest_eval_eq_of_zero_coordinate i (by simp [missingCoordinateBound])
      (U i j) g' (hUorbit i j) x y hxy
  have hlip : (T.lipBound : ℝ) ≤ Real.exp q := by
    have hobs := T.observable_budget hT
    have hnonneg := T.normBound.coe_nonneg
    exact (by linarith only [hobs, hnonneg] : (T.lipBound : ℝ) ≤ Real.exp p).trans
      (Real.exp_le_exp.mpr hpq)
  have hub : ∀ x, ‖T.observable x‖ ≤ 1 := fun x =>
    (T.norm_le x).trans (show (T.normBound : ℝ) ≤ 1 from hnorm)
  obtain ⟨coeff, hcoeff, _, herr⟩ := happrox (fun _ : Unit => T.observable) T.lipBound hlip
    (fun _ => T.lipschitz) (fun _ => hub)
  have hscalar := scalar_error_le_of_vector_error (I := Unit) (J := ∀ i, Fin (n i))
    (S := (Fin (s + 1) → ℤ)) (epsilon := epsilon)
    (fun _ : Unit => fun x => T.observable (QuotientGroup.mk
      (M.filtration.realification.polynomialOrbitEval x (D.filtration.realTotalDegreeOrbit T.orbit))))
    (fun j x => ∏ i, (U i (j i)).eval x) coeff herr ()
  let W := ∀ i, Fin (n i)
  let : Nonempty W := ⟨fun i => ⟨0, hn i⟩⟩
  let e : Fin (Fintype.card W) ≃ W := (Fintype.equivFin W).symm
  refine ⟨Fintype.card W, Fintype.card_pos, hcount.trans (Real.exp_le_exp.mpr hcost),
    (fun j => coeff (e j) ()), (fun i j x => (U i (e j i)).eval x),
    (fun j => hcoeff (e j) ()), ?_, ?_, ?_⟩
  · intro i j x
    exact ((U i (e j i)).norm_eval_le x).trans (by rw [hUnorm]; rfl)
  · intro i j x y hxy
    exact hindependent i (e j i) x y hxy
  · intro x
    have hval : T.observable (QuotientGroup.mk
        (M.filtration.realification.polynomialOrbitEval x
          (D.filtration.realTotalDegreeOrbit T.orbit))) = T.eval x := by
      exact congrArg (fun z => T.observable (QuotientGroup.mk z))
        (D.filtration.realTotalDegreeOrbit_eval T.orbit x)
    have hs := hscalar x
    rw [hval] at hs
    have hsum := e.sum_comp (fun j => coeff j () * ∏ i, (U i (j i)).eval x)
    rw [hsum]
    simpa only [mul_comm] using hs

end Erdos3

end

end OAI

end


