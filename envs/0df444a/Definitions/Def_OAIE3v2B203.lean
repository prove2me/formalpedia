-- Prove2me | Definitions.Def_OAIE3v2B203
-- name    : OAIE3v2B203
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:05:36.962408+00:00
-- url     : https://prove2.me/theorems/4d41eb8d-09df-42ae-bcbf-24303c083086
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 207 of 311
-- statement:
--   Definitions bundle 207 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B299`, `OAIE3v2B180`, `OAIE3v2B181`, `OAIE3v2B185`, `OAIE3v2B186`, `OAIE3v2B187` of this split.
--
--   Modules: `Dynamics/IntervalSplitBudget.lean`, `Estimates/BoundedNativeDependentApproximations.lean`, `Estimates/CubicAntisymmetricTransfer.lean`, `Estimates/MarkedShiftGeneratorBounds.lean`, `Estimates/NativeAbsorbedIntervals.lean`, `Estimates/NativeDilationOrbit.lean`, `Estimates/NativeSubspaceFreeModel.lean`, `Estimates/NativeTwoVariableSplitFreezing.lean`, `Estimates/NativeWeightPairRemoval.lean`, `Estimates/SymmetricSquarefreeMonotonicity.lean`, `Fourier/ControlledReplicatedFrequency.lean`, `Geometry/CommonNativeCoordinateCorrections.lean`, `Linear/NativeCoefficientKernel.lean`, `Linear/RankRelationBudget.lean`, `Polynomial/ControlledPositivePolynomialDownsets.lean`, `Polynomial/IntervalSplitPolynomialBudget.lean`, `Polynomial/PositivePolynomialVectorOrbit.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B299
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B181
import Definitions.Def_OAIE3v2B185
import Definitions.Def_OAIE3v2B186
import Definitions.Def_OAIE3v2B187

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ControlledReplicatedFrequency
namespace OAI

section

namespace Erdos3

namespace RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem replicatedFrequency_basis_height {p : ℝ} (hM : M.ComplexityLE p) (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p) (j : M.SquarefreeBasisIndex) :
    RationalHeightLE (M.filtration.replicatedFrequency η (M.squarefreeBasis p j))
      (replicatedFrequencyHeight d ⌈Real.exp p⌉₊) := by
  rcases j with ⟨a, k⟩
  by_cases ha : a = SquarefreeIndex.full (ReplicatedIndex bound)
  · subst a
    change RationalHeightLE (M.filtration.replicatedFrequency η
      (M.filtration.squarefreeBasis _ (M.squarefreeCoefficientBasis p) ⟨_, k⟩)) _
    rw [M.filtration.replicatedFrequency_basis_full]
    have h := linearFunctional_coordinate_height D.basis η
      (fun i => rationalHeightLE_ceil_exp (hη i)) _ (M.squarefreeCoefficientBasis_height hM _ k)
    simp only [Fintype.card_fin] at h
    exact h
  · change RationalHeightLE (M.filtration.replicatedFrequency η
      (M.filtration.squarefreeBasis _ (M.squarefreeCoefficientBasis p) ⟨a, k⟩)) _
    rw [M.filtration.replicatedFrequency_basis_ne (M.squarefreeCoefficientBasis p) η a ha k]
    exact rationalHeightLE_zero (replicatedFrequencyHeight_pos d (one_le_ceil_exp p))

theorem replicatedFrequency_finBasis_height {p : ℝ} (hM : M.ComplexityLE p) (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p) (j) :
    RationalHeightLE (M.filtration.replicatedFrequency η (M.squarefreeFinBasis p j))
      (replicatedFrequencyHeight d ⌈Real.exp p⌉₊) := by
  rw [squarefreeFinBasis, Module.Basis.reindex_apply]
  exact M.replicatedFrequency_basis_height hM η hη _

theorem exists_replicatedFrequency_denominator {p : ℝ} (hM : M.ComplexityLE p) (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p) :
    ∃ l : ℕ, 0 < l ∧
      l ≤ replicatedFrequencyHeight d ⌈Real.exp p⌉₊ ^ Fintype.card M.SquarefreeBasisIndex ∧
      ∀ j : M.SquarefreeBasisIndex, ∃ n : ℤ,
        (l : ℚ) * M.filtration.replicatedFrequency η (M.squarefreeBasis p j) = n := by
  obtain ⟨l, hl, hbound, z, hz, _⟩ := exists_bounded_integer_array
    (fun j => M.filtration.replicatedFrequency η (M.squarefreeBasis p j))
    (M.replicatedFrequency_basis_height hM η hη)
  exact ⟨l, hl, hbound, fun j => ⟨z j, (hz j).symm⟩⟩

end RationalFilteredNilmanifold.MultidegreeStructure

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_controlled_replicated_frequency {p : ℝ} (hM : M.ComplexityLE p)
    (η : L →ₗ[ℚ] ℚ) (hη : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p) :
    ∃ (B : ℕ) (hB : 0 < B) (hstable : M.SquarefreeGridStable p B),
      (M.squarefreeModelMultidegree p B hB hstable).ComplexityLE
        (squarefreeFrequencyModelBudget (∑ i, bound i) p) ∧
      (∀ i, rationalLogHeight (M.filtration.replicatedFrequency η
        ((M.squarefreeModel p B hB hstable).basis i)) ≤
          squarefreeFrequencyModelBudget (∑ i, bound i) p) ∧
      ∀ z : (M.squarefreeModel p B hB hstable).RealGroup,
        z ∈ (M.squarefreeModel p B hB hstable).realLattice →
          ∃ n : ℤ, realifyFunctional (M.filtration.replicatedFrequency η) z.coord = n := by
  let t := ∑ i, bound i
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  obtain ⟨l, hl, hlraw, hclear⟩ := M.exists_replicatedFrequency_denominator hM η hη
  have hN := M.squarefreeBasisIndex_card_le p
  have hlexp := replicatedFrequencyDenominator_le_exp t _ d l hp hM.1.1 hN hlraw
  obtain ⟨B, hB, hdiv, hBraw, hstable⟩ := M.exists_squarefree_stable_grid hM l hl
  rw [replicatedIndex_card] at hBraw
  have hbase : squarefreeInputBudget t p ≤ squarefreeFrequencyModelBudget t p :=
    (squarefreeInputBudget_le_frequency t hp).trans (squarefreeFrequencyInputBudget_le_model t hp)
  have hq : 0 ≤ squarefreeFrequencyModelBudget t p := (squarefreeInputBudget_nonneg t hp).trans hbase
  have hdq : (Fintype.card M.SquarefreeBasisIndex : ℝ) ≤ squarefreeFrequencyModelBudget t p := by
    apply le_trans _ hbase
    calc
      _ ≤ (2 : ℝ) ^ t * d := by exact_mod_cast hN
      _ ≤ (2 : ℝ) ^ t * p := mul_le_mul_of_nonneg_left hM.1.1 (by positivity)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  have h8 : (p + 3) ^ 8 ≤ squarefreeFrequencyModelBudget t p :=
    (le_add_of_nonneg_left (mul_nonneg (by positivity) hp)).trans hbase
  have hHq : (squarefreeStructureHeight d ⌈Real.exp p⌉₊ : ℝ) ≤
      Real.exp (squarefreeFrequencyModelBudget t p) :=
    (squarefreeStructureHeight_ceil_exp d hp hM.1.1).trans (Real.exp_le_exp.mpr h8)
  have hGq : (replicatedFrequencyHeight d ⌈Real.exp p⌉₊ : ℝ) ≤
      Real.exp (squarefreeFrequencyModelBudget t p) :=
    (replicatedFrequencyHeight_ceil_exp d hp hM.1.1).trans (Real.exp_le_exp.mpr
      ((pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 3) (by decide : 4 ≤ 8)).trans h8))
  refine ⟨B, hB, hstable, ?_, ?_, ?_⟩
  · exact M.squarefreeModel_complexity hM B hB hstable hq hdq
      (squarefree_frequency_grid_budget t _ d l B hp hM.1.1 hN hlexp hBraw) hHq
  · intro i
    exact rationalLogHeight_le_of_height (M.replicatedFrequency_finBasis_height hM η hη i) hGq
  · intro z hz
    exact M.squarefreeRealLattice_frequency_integral p η l B hB hstable hdiv hclear z hz

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeTwoVariableSplitFreezing
namespace OAI

section

namespace Erdos3.NativeTwoVariableSplit

open Module RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators

attribute [local instance] NativeTwoVariableSplit.lie NativeTwoVariableSplit.algebra
  NativeTwoVariableSplit.topology NativeTwoVariableSplit.topologicalAdd
  NativeTwoVariableSplit.continuousSMul NativeTwoVariableSplit.hausdorff

theorem exists_second_expansion_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {d : ℕ} {p epsilon : ℝ} {f : (Fin 2 → ℤ) → ℂ}
      (R : NativeTwoVariableSplit s d p epsilon f) (j : Fin R.count) (h : ℤ),
      ∃ E : NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) ((p + C) ^ C)
          (fun x => (R.test true j).eval ![h, x ()]), E.count = 1 := by
  obtain ⟨C, hC, hfreeze⟩ := exists_controlled_frozen_niltest (∑ _ : Fin 2, s)
  refine ⟨C, hC, ?_⟩
  intro d p epsilon f R j h
  classical
  let S : Finset (Fin 2) := {1}
  have hp : 0 ≤ p := (Nat.cast_nonneg (R.dim true)).trans (R.complexity true).1.1
  have hlip : ((R.test true j).lipBound : ℝ) ≤ Real.exp p := by
    have hb := (R.test true j).observable_budget (R.test_complexity true j)
    have hn := (R.test true j).normBound.coe_nonneg
    linarith
  have hub : ∀ x, ‖(R.test true j).observable x‖ ≤ (1 : ℝ) := fun x =>
    ((R.test true j).norm_le x).trans
      (show ((R.test true j).normBound : ℝ) ≤ 1 from R.test_norm true j)
  obtain ⟨E, _, _, hE⟩ := hfreeze (R.model true) (R.multi true) S ![h, 0]
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
  have hval (x : Unit → ℤ) : U.eval x = (R.test true j).eval ![h, x ()] := by
    rw [RationalFilteredNilmanifold.Niltest.eval_affinePullback, hTeval]
    unfold RationalFilteredNilmanifold.Niltest.eval
    rw [R.test_orbit true j, (R.multi true).orbitToOrdinary_eval]
    congr 2
    apply congrArg (fun z => (R.multi true).filtration.realification.polynomialOrbitEval z
      (R.orbit true))
    funext i
    fin_cases i <;> simp [S, freezeCoordinates, integerAffineMap]
  have hdegree : multidegreeWeight (retainedCoordinateWeight S) (totalDegreeSplitBound s true) =
      s - 1 := by
    rw [retainedCoordinate_degree]
    simp [S, totalDegreeSplitBound]
  have hresult : ∃ Q : NativeIntegerExpansion (fun _ : Unit => 1)
      (multidegreeWeight (retainedCoordinateWeight S) (totalDegreeSplitBound s true))
      ((p + C) ^ C) (fun x => (R.test true j).eval ![h, x ()]), Q.count = 1 :=
    ⟨NativeIntegerExpansion.ofTest U hU (fun x => (hval x).symm), rfl⟩
  exact hdegree ▸ hresult

end Erdos3.NativeTwoVariableSplit

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymmetricSquarefreeMonotonicity
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct BigOperators

theorem exists_controlled_symmetric_squarefree_unit (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      {s d : ℕ} (D : RationalFilteredNilmanifold L s d) {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound), (∑ i, bound i) = t →
      ∀ [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
        [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
        [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
        {p : ℝ}, M.ComplexityLE p → ∀ η : L →ₗ[ℚ] ℚ,
      (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
      Nonempty (M.SymmetricSquarefreeUnitData (p + t.factorial + 1) η ((p + C) ^ C)) := by
  obtain ⟨a, _, hinvariant⟩ := exists_prescribed_invariant_unit t t.factorial
  obtain ⟨b, _, hfrequency⟩ := exists_squarefreeFrequency_cost t
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + Polynomial.C t.factorial + 1
  let R := (Q + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + R + (R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ s d D bound M ht _ _ _ _ p hM η hη
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let q := p + t.factorial + 1
  let m := Fintype.card (ReplicatedPermutation bound)
  have hm : 0 < m := Fintype.card_pos_iff.mpr ⟨1⟩
  have hmle : m ≤ t.factorial := by
    simpa only [ht] using replicatedPermutation_card_le bound
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith [Nat.cast_nonneg (α := ℝ) t.factorial]
  have hηdiv (i) : rationalLogHeight (dividedFrequency m η (D.basis i)) ≤ q := by
    apply (dividedFrequency_height m hm η (D.basis i) (hη i)).trans
    have hmr : (m : ℝ) ≤ t.factorial := by exact_mod_cast hmle
    dsimp [q]
    linarith
  obtain ⟨B, hB, hstable, hE, hηE, hint⟩ :=
    M.exists_controlled_replicated_frequency (hM.mono M hpq) (dividedFrequency m η) hηdiv
  rw [ht] at hE hηE
  let r := (q + b) ^ b
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hqr : squarefreeFrequencyModelBudget t q ≤ r := hfrequency q hq
  have hEr := hE.mono (M.squarefreeModelMultidegree q B hB hstable) hqr
  let E := M.squarefreeModel q B hB hstable
  let := M.squarefreeSpaceAction q B hB hstable
  have hstep : Fintype.card (ReplicatedIndex bound) = t := (replicatedIndex_card bound).trans ht
  rw [← hstep] at hinvariant
  obtain ⟨n, hn, hdim, W, hW, hWinv⟩ := hinvariant (Γ := ReplicatedPermutation bound) E
    (by simpa only [hstep] using hmle) hr hEr.1
    (fun e => M.squarefreeSpacePermute_lipschitz q B hB hstable hr hEr.1 e)
    (fun e z hz x => M.squarefreeSpacePermute_commutes_top q B hB hstable e z hz x)
    (M.filtration.replicatedFrequency (dividedFrequency m η)) (fun i => (hηE i).trans hqr) hint
  have htotal : q + r + (r + a) ^ a ≤ (p + C) ^ C := by
    simpa [Q, R, X, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hra : 0 ≤ (r + a) ^ a := by positivity
  have hrC : r ≤ (p + C) ^ C := by linarith
  have hWC : (r + a) ^ a ≤ (p + C) ^ C := by linarith
  refine ⟨{
    grid := B
    grid_pos := hB
    stable := hstable
    complexity := hEr.mono (M.squarefreeModelMultidegree q B hB hstable) hrC
    coordinateCount := n
    coordinateCount_pos := hn
    observable := W.mono hWC
    frequency := ?_
    invariant := hWinv
    dimension := hdim.trans (Real.exp_le_exp.mpr hWC) }⟩
  change W.frequency = M.filtration.replicatedFrequency η
  rw [hW]
  ext x
  simp only [LinearMap.smul_apply, nsmul_eq_mul, MultidegreeLieFiltration.replicatedFrequency_apply,
    dividedFrequency, smul_eq_mul]
  change (m : ℚ) * ((m : ℚ)⁻¹ * η _) = _
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hm.ne' : (m : ℚ) ≠ 0), one_mul]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData

open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  {M : D.MultidegreeStructure bound} {p q : ℝ} {η : L →ₗ[ℚ] ℚ}
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  (U : M.SymmetricSquarefreeUnitData p η q)

theorem eval_permute (g : M.filtration.realification.PolynomialOrbit)
    (e : ReplicatedPermutation bound)
    (k : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin U.coordinateCount))
    (x : ReplicatedIndex bound → ℤ) :
    U.eval g k (fun j => x ((replicatedPermutation bound e).symm j)) = U.eval g k x := by
  unfold eval
  rw [← M.filtration.polarizeRealOrbit_permute (fun j : ReplicatedIndex bound => j.1)
    g (replicatedPermutation bound e) (replicatedPermutation_block bound e) x]
  change U.observable.observable k (QuotientGroup.mk
    (M.squarefreeRealPermute p U.grid U.grid_pos U.stable e _)) = _
  rw [← M.squarefreeSpacePermute_mk]
  exact U.invariant e k _

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledPositivePolynomialDownsets
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (J : Set (σ →₀ ℕ)) [DecidablePred (· ∈ J)]
  (hJ : IsLowerSet J)

theorem positivePolynomialDownsetModel_complexity (p q : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (hE : (M.positivePolynomialModel p B hB hstable).GeometryComplexityLE q) :
    (M.positivePolynomialDownsetModelMultidegree J hJ p B hB hstable).ComplexityLE q := by
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans hE.1
  have hone : ((1 : ℕ) : ℝ) ≤ Real.exp q := by simpa only [Nat.cast_one] using Real.one_le_exp hq
  have hc (i j k : M.PositivePolynomialBasisIndex) :
      rationalLogHeight (lieStructureConstants (M.positivePolynomialBasis p) i j k) ≤ q := by
    have h := hE.2.2.1 ((Fintype.equivFin _) i) ((Fintype.equivFin _) j) ((Fintype.equivFin _) k)
    simpa only [positivePolynomialModel, positivePolynomialFinBasis, lieStructureConstants_reindex,
      Equiv.symm_apply_apply] using h
  refine ⟨⟨(Nat.cast_le.mpr (M.positivePolynomialDownsetIndex_card_le J)).trans hE.1,
    hE.2.1, ?_, ?_⟩, ?_⟩
  · intro i j k
    change rationalLogHeight (lieStructureConstants (M.positivePolynomialDownsetFinBasis J hJ p) i j k) ≤ q
    rw [positivePolynomialDownsetFinBasis, lieStructureConstants_reindex,
      M.positivePolynomialDownsetBasis_structure]
    exact hc _ _ _
  · intro i j k
    exact rationalLogHeight_le_of_height
      (M.positivePolynomialDownsetFinBasis_degree_height J hJ p (i.val + 1) j k) hone
  · intro a j k
    exact rationalLogHeight_le_of_height
      (M.positivePolynomialDownsetFinBasis_multidegree_height J hJ p (fun i => (a i).val) j k) hone

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PositivePolynomialVectorOrbit
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration VectorPolynomial NilpotentLieBCHGroup

variable {α σ L : Type*} [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
  {bound : σ → ℕ} (M : D.MultidegreeStructure bound)
  (J : α → Set (σ →₀ ℕ)) [∀ a, DecidablePred (· ∈ J a)] (hJ : ∀ a, IsLowerSet (J a))

omit [DecidableEq α] in
theorem positivePolynomialQuotientProductModel_geometry (p q : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (hα : (Fintype.card α : ℝ) ≤ q)
    (hE : (M.positivePolynomialModel p B hB hstable).GeometryComplexityLE q) :
    (M.positivePolynomialQuotientProductModel J hJ p B hB hstable).GeometryComplexityLE ((q + 2) ^ 2) :=
  pi_geometry _ ((Nat.cast_nonneg _).trans hE.1) hα
    (fun a => (M.positivePolynomialDownsetModel_complexity (J a) (hJ a) p q B hB hstable hE).1)

omit [DecidableEq α] in
theorem positivePolynomialQuotientProductModel_map_height (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B) (i j) :
    RationalHeightLE ((M.positivePolynomialQuotientProductModel J hJ p B hB hstable).basis.repr
      (M.filtration.positivePolynomialQuotientProductMap J hJ (M.positivePolynomialFinBasis p j)) i) 1 := by
  change RationalHeightLE ((pi (fun a => M.positivePolynomialDownsetModel (J a) (hJ a) p B hB hstable)).basis.repr _ i) 1
  rw [productFinBasis_repr]
  exact M.positivePolynomialDownset_projection_height _ _ p _ j

theorem positivePolynomialQuotientProductModel_lattice_cover (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (hcover : ∀ c, c ≠ 0 → (∀ a, c ∉ J a) → M.filtration.layer (fun i => c i) = ⊥) :
    (M.positivePolynomialQuotientProductModel J hJ p B hB hstable).realLattice ⊓
      (M.filtration.positivePolynomialQuotientProductRealMap J hJ).range ≤
        (M.positivePolynomialModel p B hB hstable).realLattice.map
          (M.filtration.positivePolynomialQuotientProductRealMap J hJ) := by
  exact M.filtration.positivePolynomialQuotientProduct_lattice_cover J hJ
    (M.positiveCoefficientBasis p) hcover (M.positivePolynomialLattice p B hstable) B
    (M.positivePolynomialLattice_coordinates p B hstable)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

theorem exists_positivePolynomial_product_reconstruction (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {α σ L : Type*} [Fintype α] [DecidableEq α]
      [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : α → Set (σ →₀ ℕ))
      [∀ a, DecidablePred (· ∈ J a)] (hJ : ∀ a, IsLowerSet (J a))
      [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [T2Space (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      [T2Space (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      (p q : ℝ) (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
      (∑ i, bound i) = t → (Fintype.card α : ℝ) ≤ q →
      (M.positivePolynomialModel p B hB hstable).GeometryComplexityLE q →
      (∀ c, c ≠ 0 → (∀ a, c ∉ J a) → M.filtration.layer (fun i => c i) = ⊥) →
      ∀ (u : (M.positivePolynomialModel p B hB hstable).Space → ℂ) (ℓ : ℝ≥0),
        (ℓ : ℝ) ≤ Real.exp q →
        (letI := (M.positivePolynomialModel p B hB hstable).metricSpace; LipschitzWith ℓ u) →
        (∀ x, ‖u x‖ ≤ 1) →
        ∃ (v : (M.positivePolynomialQuotientProductModel J hJ p B hB hstable).Space → ℂ) (K : ℝ≥0),
          (K : ℝ) ≤ Real.exp ((q + C) ^ C) ∧
          (letI := (M.positivePolynomialQuotientProductModel J hJ p B hB hstable).metricSpace;
            LipschitzWith K v) ∧ (∀ y, ‖v y‖ ≤ 2) ∧
          ∀ x, v (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ x)) =
            u (QuotientGroup.mk x) := by
  obtain ⟨a, _, hrec⟩ := exists_native_complex_reconstruction t
  let P : Polynomial ℕ := (Polynomial.X + (Polynomial.X + 2) ^ 2 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro α σ L _ _ _ _ _ _ s d D bound M J _ hJ _ _ _ _ _ _ _ _ p q B hB hstable ht hα hX hcover u ℓ hℓ hu hub
  subst t
  let X := M.positivePolynomialModel p B hB hstable
  let Y := M.positivePolynomialQuotientProductModel J hJ p B hB hstable
  let r := q + (q + 2) ^ 2
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans hX.1
  have hqr : q ≤ r := le_add_of_nonneg_right (sq_nonneg _)
  have hrr : (q + 2) ^ 2 ≤ r := le_add_of_nonneg_left hq
  have hr : 0 ≤ r := hq.trans hqr
  have hY := M.positivePolynomialQuotientProductModel_geometry J hJ p q B hB hstable hα hX
  have hmap : ∀ i j, rationalLogHeight
      (Y.basis.repr (M.filtration.positivePolynomialQuotientProductMap J hJ (X.basis j)) i) ≤ r := by
    intro i j
    exact rationalLogHeight_le_of_height
      (M.positivePolynomialQuotientProductModel_map_height J hJ p B hB hstable i j)
      (by simpa only [Nat.cast_one] using Real.one_le_exp hr)
  have hker : ∀ k ∈ (M.filtration.positivePolynomialQuotientProductRealMap J hJ).ker, ∀ x,
      u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x) := by
    intro k hk x
    have hk1 : k = 1 := M.positivePolynomialQuotientProductModel_map_injective J hJ p hcover
      ((MonoidHom.mem_ker.mp hk).trans (map_one _).symm)
    rw [hk1, one_mul]
  obtain ⟨v, K, hK, hv, hb, heval⟩ := hrec X Y
    (M.filtration.positivePolynomialQuotientProductMap J hJ) hr
    (hX.mono X hqr) (hY.mono Y hrr) hmap
    (M.positivePolynomialQuotientProductModel_lattice_cover J hJ p B hB hstable hcover)
    u ℓ (hℓ.trans (Real.exp_le_exp.mpr hqr)) hu hub hker
  have hcost : (r + a) ^ a ≤ (q + C) ^ C := by
    simpa [P, r, Polynomial.eval₂_pow] using hbudget q hq
  exact ⟨v, K, hK.trans (Real.exp_le_exp.mpr hcost), hv, hb, heval⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDilationOrbit
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_native_dilation_orbit (q : ℤ)
    (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) s r)
    (hEF : E.filtration = M.filtration.ordinary.dilationPairFiltration (q : ℚ))
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ) :
    ∃ h : E.filtration.realification.PolynomialOrbit (fun _ : σ => 1),
      E.filtration.realification.polynomialOrbitEval _ 0 h = 1 ∧
      ∀ x : σ → ℤ,
        (QuotientGroup.mk (ε * M.filtration.ordinary.realDilationPairProjection (q : ℚ) 0
          (E.filtration.realification.polynomialOrbitEval _ x h)) : D.Space) =
            QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval (fun i => q * x i) g) ∧
        (QuotientGroup.mk (ε * M.filtration.ordinary.realDilationPairProjection (q : ℚ) 1
          (E.filtration.realification.polynomialOrbitEval _ x h)) : D.Space) =
            QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g) := by
  let F := M.filtration.ordinary.dilationPairFiltration (q : ℚ)
  obtain ⟨h, hh0, hh⟩ := M.filtration.exists_real_normalized_dilationPair_orbit q g ε γ hfactor
  have hF : F.realification = E.filtration.realification := by rw [hEF]
  let hE := F.realification.orbitEquivOfEq hF (fun _ : σ => 1)
    ((M.filtration.dilationPairMultidegree (q : ℚ)).realification.toOrdinaryOrbit h)
  have hhE (x : σ → ℤ) : E.filtration.realification.polynomialOrbitEval _ x hE =
      (M.filtration.dilationPairMultidegree (q : ℚ)).realification.polynomialOrbitEval x h :=
    F.realification.orbitEquivOfEq_eval hF _ _ x
  refine ⟨hE, (hhE 0).trans hh0, fun x => ?_⟩
  rw [hhE]
  constructor
  · rw [(hh x).1]
    simp only [← mul_assoc, mul_inv_cancel, one_mul]
    exact QuotientGroup.mk_mul_of_mem _ (D.realLattice.inv_mem hγ)
  · rw [(hh x).2]
    simp only [← mul_assoc, mul_inv_cancel, one_mul]
    exact QuotientGroup.mk_mul_of_mem _ (D.realLattice.inv_mem hγ)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeWeightPairRemoval
namespace OAI

section

namespace Erdos3.NativeMixedReductionData

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

noncomputable def translationTermExpansion (k : Fin V.outputDim) (a : MixedExpansionIndex V)
    (b : Fin (D.translation.selectedExpansion k a).count) :
    NativeIntegerExpansion (fun _ : Fin 3 => 1) s P (D.translationTerm k a b) :=
  NativeIntegerExpansion.ofTest ((D.translation.selectedExpansion k a).test b)
    ((D.translation.selectedExpansion k a).complexity b) (fun _ => rfl)

noncomputable def translationGlobalExpansion (k : Fin 4 → Fin V.outputDim)
    (t : D.TranslationCode k) :
    NativeIntegerExpansion (fun _ : Fin 5 => 1) s (productNiltestBudget P + 2 * P)
      (D.translationGlobal k t) :=
  ((D.translationTermExpansion (k 1) t.second t.secondTerm).linearPullbackHom secondInput).mul
    (((D.translationTermExpansion (k 3) t.fourth t.fourthTerm).linearPullbackHom fourthInput).conjugate)
    D.budget_two

noncomputable def lowerTermExpansion (h δ : ℤ) (a : MixedExpansionIndex V)
    (c : Fin (D.lower h δ a).count) :
    NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) P
      (fun x => D.lowerTerm h δ a c (x ())) :=
  NativeIntegerExpansion.ofTest ((D.lower h δ a).test c) ((D.lower h δ a).complexity c)
    (fun _ => rfl)

noncomputable def translationLowerExpansion {k : Fin 4 → Fin V.outputDim}
    (t : D.TranslationCode k) (h₂ h₄ δ : ℤ) (c : D.LowerCode t h₂ h₄ δ) :
    NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) (productNiltestBudget P + 2 * P)
      (fun x => D.translationLower t h₂ h₄ δ c (x ())) :=
  (D.lowerTermExpansion h₂ δ t.second c.second).mul
    (D.lowerTermExpansion h₄ δ t.fourth c.fourth).conjugate D.budget_two

noncomputable def parallelogramTermExpansion (k : Fin 4 → Fin V.outputDim)
    (a : D.ReductionCode k) :
    NativeIntegerExpansion (fun _ : Fin 5 => 1) s P
      (fun x => ((D.parallelogram (D.translationCoordinates k a.translations)).test a.term).eval
        ![x 0, x 1, x 2, x 3]) :=
  (NativeIntegerExpansion.ofTest
    ((D.parallelogram (D.translationCoordinates k a.translations)).test a.term)
    ((D.parallelogram (D.translationCoordinates k a.translations)).complexity a.term)
    (fun _ => rfl)).linearPullbackHom parallelogramInput

end Erdos3.NativeMixedReductionData

end

section

namespace Erdos3

namespace NativeMixedReductionData

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

noncomputable def globalErrorExpansion (k : Fin 4 → Fin V.outputDim)
    (a : D.ReductionCode k) :
    NativeIntegerExpansion (fun _ : Fin 5 => 1) s (mixedErrorBudget P) (D.globalError k a) := by
  have hp : 0 ≤ P := le_trans (by norm_num) D.budget_two
  have hP : P ≤ mixedErrorPairBudget P := le_mixedErrorPairBudget hp
  exact (D.translationGlobalExpansion k a.translations).mul
    ((D.parallelogramTermExpansion k a).mono hP) (D.budget_two.trans hP)

end NativeMixedReductionData

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.IntervalSplitBudget
namespace OAI

section

namespace Erdos3

theorem exists_interval_error_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → intervalErrorBudget p ≤ (p + C) ^ C := by
  obtain ⟨a, _, ha⟩ := exists_mixed_error_budget
  let X : Polynomial ℕ := Polynomial.X
  let Y := (X + 2 + Polynomial.C a) ^ a + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Y + Polynomial.C a) ^ a)
  refine ⟨C, hC, fun p hp => ?_⟩
  have hbase := intervalErrorBaseBudget_bounds hp
  have hbase0 : 0 ≤ intervalErrorBaseBudget p := le_trans (by norm_num) hbase.1
  have hbound : intervalErrorBaseBudget p ≤ (p + 2 + a) ^ a + p + 2 := by
    unfold intervalErrorBaseBudget
    gcongr
    exact (ha (p + 2) (by linarith)).2
  have hpoly : ((p + 2 + a) ^ a + p + 2 + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Y, Polynomial.eval₂_pow] using hbudget p hp
  have hmono : (intervalErrorBaseBudget p + a) ^ a ≤
      ((p + 2 + a) ^ a + p + 2 + a) ^ a := by gcongr
  exact (ha _ hbase0).1.trans (hmono.trans hpoly)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubicAntisymmetricTransfer
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

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

theorem comparisonVerticalProduct_top_invariant (hstep : s = ∑ i, bound i)
    (hEF : E.filtration = M.filtration.comparisonFiltration (fun j : ReplicatedIndex bound => j.1))
    (ε : D.RealGroup) (a : Fin (multidegreeFactorial bound) → I)
    (k : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin U.coordinateCount))
    (z : E.RealGroup) (hz : z ∈ E.filtration.realification.subgroup
      (max s (Fintype.card (ReplicatedIndex bound)))) (x : E.Space) :
    M.comparisonVerticalProduct V U E hEL ε a k (z • x) =
      M.comparisonVerticalProduct V U E hEL ε a k x := by
  let π := fun j : ReplicatedIndex bound => j.1
  have hcard : Fintype.card (ReplicatedIndex bound) = s := (replicatedIndex_card bound).trans hstep.symm
  have hzF : z.coord ∈ (M.filtration.comparisonFiltration π).realification.layer s := by
    have hh : z.coord ∈ E.filtration.realification.layer s :=
      E.filtration.realification.antitone (le_max_left s _) hz
    simpa only [hEF] using hh
  let z₁ : D.RealGroup := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := D.filtration.lowerCentralSeries_eq_bot) (M.filtration.comparisonFirst π) z
  let z₂ : (M.squarefreeModel p U.grid U.grid_pos U.stable).RealGroup :=
    realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := (M.squarefreeModel p U.grid U.grid_pos U.stable).filtration.lowerCentralSeries_eq_bot)
      (M.filtration.comparisonSecond π) z
  have hz₁ : z₁ ∈ D.filtration.realification.subgroup s := by
    change realificationLieHom (M.filtration.comparisonFirst π) z.coord ∈ D.filtration.realification.layer s
    rw [← M.ordinary]
    exact M.filtration.comparisonFirst_real_mem_layer π s z.coord hzF
  have hz₂ : z₂ ∈ (M.squarefreeModel p U.grid U.grid_pos U.stable).filtration.realification.subgroup
      (Fintype.card (ReplicatedIndex bound)) := by
    change realificationLieHom (M.filtration.comparisonSecond π) z.coord ∈
      (M.filtration.squarefreeOrdinaryFiltration π).realification.layer (Fintype.card (ReplicatedIndex bound))
    rw [congrArg (fun n => (M.filtration.squarefreeOrdinaryFiltration π).realification.layer n) hcard]
    exact M.filtration.comparisonSecond_real_mem_layer π s z.coord hzF
  have hfreq : realifyFunctional (V.tensorPower (multidegreeFactorial bound)).frequency z₁.coord =
      realifyFunctional U.observable.frequency z₂.coord := by
    change realifyFunctional (multidegreeFactorial bound • V.frequency)
      (realificationLieHom (M.filtration.comparisonFirst π) z.coord) =
      realifyFunctional U.observable.frequency (realificationLieHom (M.filtration.comparisonSecond π) z.coord)
    rw [realifyFunctional_nsmul, U.frequency, nsmul_eq_mul]
    exact M.filtration.realComparisonTop_frequency hstep V.frequency hzF
  have hcomm : Commute z₁ ε := commute_of_lie_eq_zero z₁ ε
    (D.filtration.realification.top_layer_central hz₁ ε.coord)
  have hswap (y : D.Space) : ε • (z₁ • y) = z₁ • (ε • y) := by
    rw [← mul_smul, ← hcomm.eq, mul_smul]
  let c := CircleFourier.character ((realifyFunctional U.observable.frequency z₂.coord : ℝ) : CircleFourier.Circle)
  have hc : c * star c = 1 := by
    change CircleFourier.character ((realifyFunctional U.observable.frequency z₂.coord : ℝ) : CircleFourier.Circle) *
      star (CircleFourier.character ((realifyFunctional U.observable.frequency z₂.coord : ℝ) : CircleFourier.Circle)) = 1
    rw [← CircleFourier.character_neg, ← CircleFourier.character_add,
      add_neg_cancel, CircleFourier.character_zero]
  unfold comparisonVerticalProduct
  rw [M.comparisonFirstSpace_smul, M.comparisonSecondSpace_smul]
  change (V.tensorPower (multidegreeFactorial bound)).observable a
    (ε • (z₁ • M.comparisonFirstSpace p U.grid U.grid_pos U.stable E hEL x)) *
    star (U.observable.observable k (z₂ • M.comparisonSecondSpace p U.grid U.grid_pos U.stable E hEL x)) = _
  rw [hswap, (V.tensorPower (multidegreeFactorial bound)).vertical a z₁ hz₁,
    U.observable.vertical k z₂ hz₂, hfreq, star_mul]
  let u := (V.tensorPower (multidegreeFactorial bound)).observable a
    (ε • M.comparisonFirstSpace p U.grid U.grid_pos U.stable E hEL x)
  let w := U.observable.observable k (M.comparisonSecondSpace p U.grid U.grid_pos U.stable E hEL x)
  change (c * u) * (star w * star c) = u * star w
  calc
    _ = (c * star c) * (u * star w) := by ring
    _ = _ := by rw [hc, one_mul]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData

open scoped TensorProduct

theorem exists_nilcharacter {σ L : Type} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
    {M : D.MultidegreeStructure bound} {p q : ℝ} {η : L →ₗ[ℚ] ℚ}
    [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
    [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
    (U : M.SymmetricSquarefreeUnitData p η q)
    (g : M.filtration.realification.PolynomialOrbit) :
    ∃ W : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex bound => 1) q,
    ∃ e : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound))
        (Fin U.coordinateCount) ≃ Fin W.outputDim,
      W.dim = Fintype.card M.SquarefreeBasisIndex ∧
      (∀ k x, W.eval (e k) x = U.eval g k x) ∧
      ∀ (a : ReplicatedPermutation bound) k x,
        W.eval k (fun j => x ((replicatedPermutation bound a).symm j)) = W.eval k x := by
  classical
  obtain ⟨W, e, hdim, heval⟩ := NativeMultidegreeNilcharacter.exists_of_unit_data
    (M.squarefreeModel p U.grid U.grid_pos U.stable)
    (M.squarefreeModelMultidegree p U.grid U.grid_pos U.stable)
    (by simp) U.complexity
    (M.filtration.polarizeRealOrbit (fun j : ReplicatedIndex bound => j.1) g)
    U.observable U.dimension
  change ∀ k x, W.eval (e k) x = U.eval g k x at heval
  refine ⟨W, e, hdim, heval, ?_⟩
  intro a k x
  have h (y : ReplicatedIndex bound → ℤ) : W.eval k y = U.eval g (e.symm k) y := by
    simpa only [Equiv.apply_symm_apply] using heval (e.symm k) y
  rw [h, h, U.eval_permute]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct BigOperators NNReal

variable {σ L : Type} {I : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] [Fintype I]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) {p q v : ℝ}
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  (V : D.UnitVerticalObservable (D.filtration.realification.subgroup (s + 1)) I v)
  (U : M.SymmetricSquarefreeUnitData p V.frequency q)
  (E : RationalFilteredNilmanifold
    (M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))
    (max (s + 1) (Fintype.card (ReplicatedIndex bound))) r)
  (hEL : E.lattice = M.comparisonLattice p U.grid U.grid_pos U.stable)
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]

include hEL in
theorem comparison_diagonal_expansion
    (hstep : s + 1 = ∑ i, bound i)
    (hEF : E.filtration = M.filtration.comparisonFiltration (fun j : ReplicatedIndex bound => j.1))
    {R : ℝ} (hR : 0 ≤ R) (hD : D.GeometryComplexityLE R) (hE : E.GeometryComplexityLE R)
    (hv : v ≤ R) (hq : q ≤ R)
    (hfirst : ∀ j k, rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ R)
    (hsecond : ∀ j k, rationalLogHeight ((M.squarefreeFinBasis p).repr (E.basis j).val.2 k) ≤ R)
    (hc : (multidegreeFactorial bound : ℝ) ≤ Real.exp R)
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup) (A : ℝ≥0)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ)
    (hA : (A : ℝ) ≤ Real.exp R)
    (hε : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x))
    (a : Fin (multidegreeFactorial bound) → I)
    (k : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin U.coordinateCount)) :
    Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s (comparisonDescentBudget s R)
      (fun x => (∏ j, V.observable (a j) (QuotientGroup.mk
          (M.filtration.realification.polynomialOrbitEval x g))) *
        star (U.eval (M.filtration.realification.normalizeMultidegreeOrbit g ε γ) k (fun j => x j.1)))) := by
  let := E.metricSpace
  obtain ⟨h, _, hdiag⟩ := M.exists_normalized_comparison_orbit p U.grid U.grid_pos U.stable
    E hEF hEL g ε γ hγ hfactor
  let K := comparisonProductLip (multidegreeFactorial bound) V.lipBound U.observable.lipBound A R
  have hLip : LipschitzWith K (M.comparisonVerticalProduct V U E hEL ε a k) :=
    M.comparisonVerticalProduct_lipschitz V U E hEL hR hD
      (U.complexity.1.mono _ hq) hE hfirst hsecond ε A hε a k
  let T : E.Niltest (fun _ : σ => 1) := {
    orbit := h
    observable := M.comparisonVerticalProduct V U E hEL ε a k
    normBound := 1
    lipBound := K
    norm_le := M.comparisonVerticalProduct_norm V U E hEL ε a k
    lipschitz := hLip }
  have hK : (K : ℝ) ≤ Real.exp ((R + 3) ^ 2 + 3 * R + 1) :=
    comparisonProductLip_le_exp _ _ _ _ hR hc
      (V.lip_bound.trans (Real.exp_le_exp.mpr hv))
      (U.observable.lip_bound.trans (Real.exp_le_exp.mpr hq)) hA
  have hcost : 0 ≤ comparisonProductCost R := by dsimp [comparisonProductCost]; positivity
  have hT : T.ComplexityLE (comparisonProductCost R) := by
    refine ⟨hE.mono E ?_, ?_⟩
    · dsimp [comparisonProductCost]
      nlinarith [sq_nonneg (R + 3)]
    · have hh := niltest_log_bound_of_exp (1 : ℝ≥0) K (a := 0)
        (b := (R + 3) ^ 2 + 3 * R + 1) (by norm_num) (by positivity) (by simp) hK
      simp only [NNReal.coe_one, zero_add] at hh
      change Real.log (2 + (1 : ℝ) + K) ≤ comparisonProductCost R
      dsimp [comparisonProductCost]
      linarith
  have heq : max (s + 1) (Fintype.card (ReplicatedIndex bound)) = s + 1 := by
    rw [replicatedIndex_card, ← hstep, max_self]
  have hexp : Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s
      (comparisonDescentBudget s R) T.eval) :=
    topInvariant_integer_expansion_of_step heq E T hcost hT
      (fun z hz x => M.comparisonVerticalProduct_top_invariant V U E hEL hstep hEF ε a k z hz x)
  have heval : T.eval = (fun x => (∏ j, V.observable (a j) (QuotientGroup.mk
        (M.filtration.realification.polynomialOrbitEval x g))) *
      star (U.eval (M.filtration.realification.normalizeMultidegreeOrbit g ε γ) k (fun j => x j.1))) := by
    funext x
    change M.comparisonVerticalProduct V U E hEL ε a k
      (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval _ x h)) = _
    unfold comparisonVerticalProduct
    rw [(hdiag x).1, (hdiag x).2]
    rfl
  exact heval ▸ hexp

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct BigOperators NNReal

variable {σ L : Type} {I : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] [Fintype I]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) {p q v : ℝ}
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  (V : D.UnitVerticalObservable (D.filtration.realification.subgroup (s + 1)) I v)
  (U : M.SymmetricSquarefreeUnitData p V.frequency q)
  (E : RationalFilteredNilmanifold
    (M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))
    (max (s + 1) (Fintype.card (ReplicatedIndex bound))) r)
  (hEL : E.lattice = M.comparisonLattice p U.grid U.grid_pos U.stable)
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]

include hEL in
theorem comparison_diagonal_equivalence
    (hstep : s + 1 = ∑ i, bound i)
    (hEF : E.filtration = M.filtration.comparisonFiltration (fun j : ReplicatedIndex bound => j.1))
    {R : ℝ} (hR : 0 ≤ R) (hD : D.GeometryComplexityLE R) (hE : E.GeometryComplexityLE R)
    (hv : v ≤ R) (hq : q ≤ R)
    (hfirst : ∀ j k, rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ R)
    (hsecond : ∀ j k, rationalLogHeight ((M.squarefreeFinBasis p).repr (E.basis j).val.2 k) ≤ R)
    (hc : (multidegreeFactorial bound : ℝ) ≤ Real.exp R)
    (hI : (Fintype.card I : ℝ) ≤ Real.exp R)
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup) (A : ℝ≥0)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ)
    (hA : (A : ℝ) ≤ Real.exp R)
    (hε : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x)) :
    NativeIntegerVectorEquivalence s (comparisonEquivalenceBudget s R)
      (fun (a : Fin (multidegreeFactorial bound) → I) x =>
        ∏ j, V.observable (a j) (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)))
      (fun k x => U.eval (M.filtration.realification.normalizeMultidegreeOrbit g ε γ) k (fun j => x j.1)) := by
  obtain ⟨hdesc, hbase, htensor⟩ := comparisonEquivalenceBudget_bounds s hR
  refine ⟨?_, U.dimension.trans ((Real.exp_le_exp.mpr hq).trans (Real.exp_le_exp.mpr hbase)), ?_⟩
  · have hfac : multidegreeFactorial bound ≤ (s + 1).factorial := by
      simpa only [← hstep] using multidegreeFactorial_le_total bound
    have hfacR : (multidegreeFactorial bound : ℝ) ≤ (s + 1).factorial := by exact_mod_cast hfac
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp R) ^ multidegreeFactorial bound :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hI _
      _ = Real.exp ((multidegreeFactorial bound : ℝ) * R) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (((s + 1).factorial : ℝ) * R) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hfacR hR)
      _ ≤ _ := Real.exp_le_exp.mpr htensor
  · intro a k
    obtain ⟨F⟩ := M.comparison_diagonal_expansion V U E hEL hstep hEF hR hD hE hv hq
      hfirst hsecond hc g ε γ A hγ hfactor hA hε a k
    exact ⟨F.mono hdesc⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped TensorProduct BigOperators

theorem exists_controlled_diagonal_comparison (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type} {I : Type*}
      [Fintype σ] [Fintype I] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {t d : ℕ} {bound : σ → ℕ} (D : RationalFilteredNilmanifold L t d)
      (M : D.MultidegreeStructure bound), (∑ i, bound i) = t → t = s + 1 →
      ∀ {p : ℝ}, M.ComplexityLE p →
      ∀ (V : D.UnitVerticalObservable (D.filtration.realification.subgroup t) I p),
      (Fintype.card I : ℝ) ≤ Real.exp p → ∀ g : M.filtration.realification.PolynomialOrbit,
      let P := p + (s + 1).factorial + 1
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))
      letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :=
        IsModuleTopology.topologicalAddGroup ℝ _
      letI : T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :=
        realification_moduleTopology_t2 (M.squarefreeFinBasis P)
      ∃ U : M.SymmetricSquarefreeUnitData P V.frequency ((p + C) ^ C),
      ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
        M.filtration.realification.polynomialOrbitEval 0 g = ε * γ ∧
        NativeIntegerVectorEquivalence s ((p + C) ^ C)
          (fun (a : Fin (multidegreeFactorial bound) → I) x =>
            ∏ j, V.observable (a j) (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)))
          (fun k x => U.eval (M.filtration.realification.normalizeMultidegreeOrbit g ε γ) k (fun j => x j.1)) := by
  obtain ⟨a, _, hsymm⟩ := exists_controlled_symmetric_squarefree_unit (s + 1)
  obtain ⟨b, _, hnormal⟩ := exists_controlled_group_normalization (s + 1)
  obtain ⟨c, _, hequivalence⟩ := exists_comparisonEquivalence_cost s
  let X : Polynomial ℕ := Polynomial.X
  let P₀ := X + Polynomial.C (s + 1).factorial + 1
  let Q₀ := (X + Polynomial.C a) ^ a
  let H₀ := P₀ + 1 + Polynomial.C ((s + 1) ^ 2)
  let G₀ := ((P₀ + Q₀ + 4) ^ 2 + H₀ + 6) ^ 11
  let N₀ := (X + Polynomial.C b) ^ b
  let R₀ := X + P₀ + Q₀ + H₀ + G₀ + N₀ + Polynomial.C (s + 1).factorial + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R₀ + Q₀ + (R₀ + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro σ L I _ _ _ _ _ _ _ _ t d bound D M hs ht p hM V hI g
  subst ht
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let P := p + (s + 1).factorial + 1
  let Q := (p + a) ^ a
  let H := comparisonBasisBudget (s + 1) P
  let G := comparisonGeometryBudget (s + 1) P Q
  let N := (p + b) ^ b
  let R := p + P + Q + H + G + N + (s + 1).factorial + 1
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hH : 0 ≤ H := by dsimp [H, comparisonBasisBudget]; positivity
  have hG : 0 ≤ G := by dsimp [G, comparisonGeometryBudget]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hF : 0 ≤ ((s + 1).factorial : ℝ) := Nat.cast_nonneg _
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hpP : p ≤ P := by dsimp [P]; linarith
  have hpR : p ≤ R := by dsimp [R]; linarith
  have hQR : Q ≤ R := by dsimp [R]; linarith
  have hHR : H ≤ R := by dsimp [R]; linarith
  have hGR : G ≤ R := by dsimp [R]; linarith
  have hNR : N ≤ R := by dsimp [R]; linarith
  have hFR : ((s + 1).factorial : ℝ) ≤ R := by dsimp [R]; linarith
  let := moduleTopology ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :=
    realification_moduleTopology_t2 (M.squarefreeFinBasis P)
  obtain ⟨U⟩ := hsymm D M hs hM V.frequency V.height
  obtain ⟨E, hEF, hEL, hE, he⟩ := M.exists_comparison_model (hM.mono M hpP)
    U.grid U.grid_pos U.stable U.complexity.1
  rw [hs] at hE he
  let K := M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 E.basis
  obtain ⟨ε, γ, A, hγ, hfactor, _, hA, hε⟩ := hnormal D p hp hM.1
    (M.filtration.realification.polynomialOrbitEval 0 g)
  have hfirst (j k) : rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ R := by
    have hh := (he j (Sum.inl k)).trans hHR
    simpa only [Basis.prod_repr_inl] using hh
  have hsecond (j k) : rationalLogHeight ((M.squarefreeFinBasis P).repr (E.basis j).val.2 k) ≤ R := by
    have hh := (he j (Sum.inr k)).trans hHR
    simpa only [Basis.prod_repr_inr] using hh
  have hc : (multidegreeFactorial bound : ℝ) ≤ Real.exp R := by
    have hh : multidegreeFactorial bound ≤ (s + 1).factorial := by
      simpa only [hs] using multidegreeFactorial_le_total bound
    exact (Nat.cast_le.mpr hh).trans (hFR.trans (by linarith [Real.add_one_le_exp R]))
  have hcompare := M.comparison_diagonal_equivalence V U E hEL hs.symm hEF hR
    (hM.1.mono D hpR) (hE.mono E hGR) hpR hQR hfirst hsecond hc
    (hI.trans (Real.exp_le_exp.mpr hpR)) g ε γ A hγ hfactor
    (hA.trans (Real.exp_le_exp.mpr hNR)) hε
  have htotal : R + Q + (R + c) ^ c ≤ (p + C) ^ C := by
    simpa [R₀, G₀, H₀, N₀, P₀, Q₀, X, R, G, H, N, P, Q,
      comparisonGeometryBudget, comparisonBasisBudget, Polynomial.eval₂_pow] using hbudget p hp
  have hRc : 0 ≤ (R + c) ^ c := by positivity
  have hQC : Q ≤ (p + C) ^ C := by linarith
  have hcompareC : comparisonEquivalenceBudget s R ≤ (p + C) ^ C :=
    (hequivalence R hR).trans (by linarith)
  exact ⟨U.mono hQC, ε, γ, hγ, hfactor, hcompare.mono hcompareC⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open Module
open RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_factorial_diagonal (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type} [Fintype σ] (bound : σ → ℕ),
      (∑ i, bound i) = s + 1 → ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p),
      ∃ V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex bound => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.dim ∧
        (∀ (e : ReplicatedPermutation bound) k x,
          V.eval k (fun j => x ((replicatedPermutation bound e).symm j)) = V.eval k x) ∧
        NativeIntegerVectorEquivalence s ((p + C) ^ C)
          (tensorVector W.eval (multidegreeFactorial bound))
          (fun k x => V.eval k (fun j => x j.1)) := by
  obtain ⟨C, hC, hcompare⟩ := exists_controlled_diagonal_comparison s
  refine ⟨C, hC, ?_⟩
  intro σ _ bound hs p W
  classical
  let T : W.model.UnitVerticalObservable
      (W.model.filtration.realification.subgroup (∑ i, bound i)) (Fin W.outputDim) p :=
    { W.vertical with
      vertical := fun i z hz x => W.vertical.vertical i z (W.multi.realSubgroup_top.symm ▸ hz) x
      integral := fun z hz hL => W.vertical.integral z (W.multi.realSubgroup_top.symm ▸ hz) hL }
  let P := p + (s + 1).factorial + 1
  let := moduleTopology ℝ (ℝ ⊗[ℚ] W.multi.filtration.SquarefreeAlgebra
    (fun j : ReplicatedIndex bound => j.1))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] W.multi.filtration.SquarefreeAlgebra
      (fun j : ReplicatedIndex bound => j.1)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] W.multi.filtration.SquarefreeAlgebra
      (fun j : ReplicatedIndex bound => j.1)) :=
    realification_moduleTopology_t2 (W.multi.squarefreeFinBasis P)
  obtain ⟨U, ε, γ, _, _, hE⟩ := hcompare W.model W.multi rfl hs W.complexity T
    (by simpa only [Fintype.card_fin] using W.output_bound) W.orbit
  obtain ⟨V, e, hdim, heval, hsymm⟩ := U.exists_nilcharacter
    (W.multi.filtration.realification.normalizeMultidegreeOrbit W.orbit ε γ)
  refine ⟨V, ?_, hsymm, ?_⟩
  · rw [hdim]
    simpa only [hs] using W.multi.squarefreeBasisIndex_card_le P
  refine hE.of_coordinate_maps _ _ id e.symm (fun _ _ => rfl) ?_ hE.left_dimension ?_ le_rfl
  · intro k x
    simpa only [Equiv.apply_symm_apply] using heval (e.symm k) (fun j => x j.1)
  · simpa only [Fintype.card_fin] using V.output_bound

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntervalSplitPolynomialBudget
namespace OAI

section

namespace Erdos3

theorem exists_interval_split_budget (c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ K : ℝ, 0 ≤ K →
      2 * K + intervalSplitTermBudget c K ≤ (K + C) ^ C ∧
      intervalSplitLocalBudget c K ≤ (K + C) ^ C := by
  obtain ⟨a, _, ha⟩ := exists_interval_error_budget
  obtain ⟨b, _, hb⟩ := exists_mixed_error_budget
  let X : Polynomial ℕ := Polynomial.X
  let Y := (X + Polynomial.C a) ^ a
  let V := (2 * X + 2 * Y + 2 + Polynomial.C c) ^ c
  let Z := (Y + V + 2 + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * X + V + Z)
  refine ⟨C, hC, fun K hK => ?_⟩
  have hL : 0 ≤ intervalErrorBudget K := intervalErrorBudget_nonneg hK
  have hI : 0 ≤ intervalSplitInput K := le_trans (by norm_num) (intervalSplitInput_bounds hK).1
  have hF : 0 ≤ intervalSplitTermBudget c K := by unfold intervalSplitTermBudget; positivity
  have hi : intervalSplitInput K ≤ 2 * K + 2 * (K + a) ^ a + 2 := by
    unfold intervalSplitInput
    gcongr
    exact ha K hK
  have hv : intervalSplitTermBudget c K ≤ (2 * K + 2 * (K + a) ^ a + 2 + c) ^ c := by
    unfold intervalSplitTermBudget
    gcongr
  have hm : 0 ≤ intervalErrorBudget K + intervalSplitTermBudget c K + 2 := by positivity
  have hz : intervalSplitLocalBudget c K ≤
      ((K + a) ^ a + (2 * K + 2 * (K + a) ^ a + 2 + c) ^ c + 2 + b) ^ b := by
    apply (hb _ hm).1.trans
    gcongr
    exact ha K hK
  have hZ : 0 ≤ ((K + a) ^ a + (2 * K + 2 * (K + a) ^ a + 2 + c) ^ c + 2 + b) ^ b := by
    positivity
  have hbound : 2 * K + (2 * K + 2 * (K + a) ^ a + 2 + c) ^ c +
      ((K + a) ^ a + (2 * K + 2 * (K + a) ^ a + 2 + c) ^ c + 2 + b) ^ b ≤ (K + C) ^ C := by
    simpa [X, Y, V, Z, Polynomial.eval₂_pow] using hbudget K hK
  constructor
  · linarith only [hv, hZ, hbound]
  · have hv0 : 0 ≤ (2 * K + 2 * (K + a) ^ a + 2 + c) ^ c := by positivity
    linarith only [hz, hK, hv0, hbound]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeAbsorbedIntervals
namespace OAI

section

namespace Erdos3.NativeMultilinearIntervalFamily

variable {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N p f} (B : NativeMultilinearIntervalFamily W q)

theorem sample_update (t : B.quadruples) (n : ℤ) :
    B.sample t n = Function.update (B.sample t 0) (3 : Fin 5) n := by
  funext k
  fin_cases k <;> rfl

end Erdos3.NativeMultilinearIntervalFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankRelationBudget
namespace OAI

section

namespace Erdos3

theorem exists_rank_relation_budget (a c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let K := (p + a) ^ a
      let q := K + (K + c) ^ c + 2
      11 * q + 7 ≤ (p + C) ^ C ∧ mixedErrorPairBudget q ≤ (p + C) ^ C := by
  obtain ⟨b, _, hpair⟩ := exists_mixed_error_budget
  let X : Polynomial ℕ := Polynomial.X
  let Y := (X + Polynomial.C a) ^ a
  let Z := Y + (Y + Polynomial.C c) ^ c + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (11 * Z + 7 + (Z + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p hp K q
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hterm : 0 ≤ (q + b) ^ b := by positivity
  have hbound : 11 * q + 7 + (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, Y, Z, K, q, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith only [hterm, hbound],
    (hpair q hq).1.trans (by linarith only [hq, hbound])⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeCoefficientKernel
namespace OAI

section

namespace Erdos3.NativeRankInterval

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)

theorem real_rankProjection_coordinates
    (x : ℝ ⊗[ℚ] (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))
    (j : Σ _ : Fin 4, Fin W.dim) :
    (W.fourRankBasis.baseChange ℝ).repr ((I.rankProjection i).toLinearMap.baseChange ℝ x) j =
      ((pi (I.productModels i)).basis.baseChange ℝ).repr x
        ((Fintype.equivFin (Σ k : Option (Fin 4),
          Fin (optionDimension (I.expansion.dim i) (fun _ : Fin 4 => W.dim) k)))
          ⟨some ((![1, 2, 0, 3] : Fin 4 → Fin 4) j.1), j.2⟩) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul]
    exact congrArg (fun q : ℚ => q • a) (I.rankProjection_coordinates i x j)
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

end Erdos3.NativeRankInterval

end

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} (D : I.SunflowerWitness P)

theorem projectedDenominator_pos : 0 < D.projectedDenominator :=
  Nat.mul_pos (matrixDenominator_pos _) D.denominator_pos

end Erdos3.NativeRankInterval.SunflowerWitness

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CommonNativeCoordinateCorrections
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} [Fintype κ] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem spaces_le_fourHorizontalLayer (d : Fin (s + 1)) :
    D.spaces d ≤ W.rank.filtration.fourHorizontalLayer d.val := by
  obtain ⟨t, ht⟩ := D.nonempty
  rw [← D.projection t ht d]
  let I := R.interval ⟨t, D.subset ht⟩
  let V : I.SunflowerWitness P := D.witness t ht
  change I.refilteredProjectionImage V.index V.subalgebra d.val ≤ _
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact (W.rank.filtration.mem_fourHorizontalLayer d.val _).mpr
    (I.rankProjection_mem_refiltered V.index V.subalgebra d.val y hy)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedNativeDependentApproximations
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

structure SparseAnchors (D : R.CommonData P) where
  anchors12 : ZMod N × ZMod N
  anchors13 : ZMod N × ZMod N
  shifts : Finset (ZMod N)
  nonempty : shifts.Nonempty
  density : Real.exp (-(2 * P)) * Fintype.card (ZMod N) ≤ (shifts.card : ℝ)
  relations : ∀ h ∈ shifts,
    (anchors12.2 - h, anchors12.2, anchors12.1) ∈ D.quadruples ∧
      (anchors13.1 - anchors13.2, h + (anchors13.1 - anchors13.2), anchors13.1) ∈ D.quadruples

namespace SparseAnchors

variable {D : R.CommonData P} (A : D.SparseAnchors)

theorem shifts_subset : A.shifts ⊆ H := by
  intro h hh
  have hmem := (A.relations h hh).1
  have hsecond := (R.interval ⟨_, D.subset hmem⟩).second_mem
  simpa using hsecond

end SparseAnchors

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSubspaceFreeModel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

theorem exists_positiveUnivariate_orbit_lift
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (π : L →ₗ[ℚ] M) (g : G.PolynomialOrbit (fun _ : Unit => 1))
    (hg : G.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    (v : Fin s → L) (hv : ∀ d, v d ∈ F.layer (d.val + 1))
    (hπ : ∀ d, π (v d) = coefficients g.log (Finsupp.single () (d.val + 1))) :
    ∃ q : F.PolynomialOrbit (fun _ : Unit => 1),
      q.log = positiveUnivariate v ∧ F.polynomialOrbitEval (fun _ : Unit => 1) 0 q = 1 ∧
      VectorPolynomial.map π q.log = g.log ∧
      ∀ x : Unit → ℤ, π (F.polynomialOrbitEval (fun _ : Unit => 1) x q).coord =
        (G.polynomialOrbitEval (fun _ : Unit => 1) x g).coord := by
  have hadapt : F.Adapted (fun _ : Unit => 1) (positiveUnivariate v) := by
    apply (F.adapted_iff_coefficients _ _).mpr
    apply positiveUnivariate_coefficients_mem
    intro d
    simpa only [Finsupp.weight_single, smul_eq_mul, mul_one] using hv d
  let q := polynomialOrbitOfLog (positiveUnivariate v) hadapt
  have hzero : coefficients g.log 0 = 0 := by
    have h := congrArg NilpotentLieBCHGroup.coord hg
    simpa only [G.polynomialOrbitEval_coord, Pi.zero_apply, Int.cast_zero,
      eval_zero_eq_coefficient, NilpotentLieBCHGroup.coord_one] using h
  have hmap : VectorPolynomial.map π q.log = g.log := by
    change VectorPolynomial.map π (positiveUnivariate v) = g.log
    rw [map_positiveUnivariate, show (fun d => π (v d)) =
      (fun d : Fin s => coefficients g.log (Finsupp.single () (d.val + 1))) from funext hπ]
    exact positiveUnivariate_reconstruct g.log g.degreeLE hzero
  refine ⟨q, rfl, ?_, hmap, ?_⟩
  · apply NilpotentLieBCHGroup.ext
    change eval (fun _ : Unit => (0 : ℚ)) (positiveUnivariate v) = 0
    rw [eval_zero_eq_coefficient, positiveUnivariate_zero]
  · intro x
    rw [F.polynomialOrbitEval_coord, G.polynomialOrbitEval_coord, ← eval_map, hmap]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedShiftGeneratorBounds
namespace OAI

section

namespace Erdos3

open VectorPolynomial NilpotentLieBCHGroup

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ)

theorem markedShiftDirection_lie_right (h : Fin t → ℚ) (x : markedShiftSubalgebra F v w marked t) :
    (⁅markedShiftDirection F v w marked t h, x⁆).val.right = 0 := rfl

noncomputable def markedQuotientDirection (h : Fin t → ℚ) : MarkedShiftQuotient F v w marked t :=
  lieQuotientMap (markedShiftSecondIdeal F v w marked t) (markedShiftDirection F v w marked t h)

end Erdos3

end

end OAI
end


