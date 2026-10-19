-- Prove2me | Definitions.Def_OAIE3v2B164
-- name    : OAIE3v2B164
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:21:12.008981+00:00
-- url     : https://prove2.me/theorems/d95b0455-0659-4ea1-afa3-c76b3459b2be
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 166 of 311
-- statement:
--   Definitions bundle 166 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B151`, `OAIE3v2B152`, `OAIE3v2B153` of this split.
--
--   Modules: `Dynamics/ComparisonEquivalenceBudget.lean`, `Estimates/GradedUnitEvaluation.lean`, `Estimates/NativeCorrelatedFactorFamily.lean`, `Estimates/NativeCrossFactorization.lean`, `Estimates/NativeDilationDescent.lean`, `Estimates/NativeOrbitFreezing.lean`, `Estimates/NativePartitionFreezing.lean`, `Estimates/NativePositiveCorrelation.lean`, `Estimates/NativeSharedFrozenCorrelations.lean`, `Estimates/NativeTwoVariableSplitFreezing.lean`, `Estimates/NativeWeightPairRemoval.lean`, `Estimates/SampledNativeModel.lean`, `Estimates/SourceUnitCover.lean`, `Estimates/TranslatedShiftTesting.lean`, `Estimates/UniformControlledNativeExternalNetsOfRecovery.lean`, `Estimates/UniformFrozenDescent.lean`, `Fourier/BohrNiltestBudget.lean`, `Geometry/NativeCoordinateSplitFreezing.lean`, `Geometry/NativeIntervalCoordinate.lean`, `Lattices/NativeIntegerHalving.lean`, `Lattices/NativeIntervalResiduePartition.lean`, `Linear/FixedAdaptedSymbolFactorizationBasis.lean`, `Linear/NativeCoefficientKernel.lean`, `Linear/NativeRankQuotientOrbit.lean`, `Linear/RefiltrationLayerBasis.lean`, `Nilpotent/NativeFrozenMultidegreeNiltest.lean`, `Nilpotent/NativeResidueNiltests.lean`, `Polynomial/FreeDegreeRankAdaptedBounds.lean`, `Polynomial/NativeDegreeRankFamily.lean`, `Polynomial/PolynomialGridValues.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B151
import Definitions.Def_OAIE3v2B152
import Definitions.Def_OAIE3v2B153

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FreeDegreeRankAdaptedBounds
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_adapted_free_degree_rank_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : Type*) [Fintype X] (r : ℕ) (hr : r ≤ s)
      (w : X → ℕ) (hw : ∀ x, 0 < w x) (p : ℝ), 0 ≤ p → (Fintype.card X : ℝ) ≤ p →
      (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw) : ℝ) ≤ (p + C) ^ C ∧
      ∃ b : Basis (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ
          (FreeDegreeRankLieAlgebra X s r w hw),
        IsCentralLieBasis b ∧
        (∀ i j, ∃ c ≤ finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw),
          (FreeDegreeRankLieAlgebra.filtration X s r w hw hr).layer i j = basisTail b c) ∧
        (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + C) ^ C) ∧
        (∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
          rationalLogHeight (b.repr (FreeDegreeRankLieAlgebra.projection X s r w hw x) i) ≤ (p + C) ^ C) ∧
        ∃ e : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s),
          (∀ i, e i ∈ FreeNilpotentLieAlgebra.treeGenerators X s) ∧
          (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ (p + C) ^ C ∧
          ∃ S : Matrix (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s)))
              (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ,
            LinearMap.toMatrix e b (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap * S = 1 ∧
            ∀ i j, rationalLogHeight (S i j) ≤ (p + C) ^ C := by
  obtain ⟨a, _, hmodel⟩ := exists_bounded_free_degree_rank_model s
  let B₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let P₀ := (B₀ + 3) ^ (6 * s + 2)
  let Q₀ := P₀ + (P₀ + 3) ^ 5
  let R₀ := (Q₀ + 2) ^ 4 + (P₀ + 3) ^ 11 + B₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R₀ + (R₀ + 3) ^ 5)
  refine ⟨C, hC, ?_⟩
  intro X _ r hr w hw p hp hX
  classical
  let B := (p + a) ^ a
  let P := (B + 3) ^ (6 * s + 2)
  let Q := P + (P + 3) ^ 5
  let R := (Q + 2) ^ 4 + (P + 3) ^ 11 + B
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hBP : B ≤ P :=
    (le_power_budget hB (by omega : 1 ≤ 6 * s + 2)).trans
      (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl B) (by norm_num : (2 : ℝ) ≤ 3)) _)
  have hPQ : P ≤ Q := le_add_of_nonneg_right (by positivity)
  have hIQ : (P + 3) ^ 5 ≤ Q := le_add_of_nonneg_left hP
  have hQ : 0 ≤ Q := hP.trans hPQ
  have hBR : B ≤ R := le_add_of_nonneg_left (by positivity)
  have hR : 0 ≤ R := hB.trans hBR
  have hprojectionR : (Q + 2) ^ 4 ≤ R :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (P + 3) ^ 11)).trans (le_add_of_nonneg_right hB)
  have hstructureR : (P + 3) ^ 11 ≤ R :=
    (le_add_of_nonneg_left (by positivity : 0 ≤ (Q + 2) ^ 4)).trans (le_add_of_nonneg_right hB)
  have hsum : R + (R + 3) ^ 5 ≤ (p + C) ^ C := by
    simpa [B₀, P₀, Q₀, R₀, B, P, Q, R, Polynomial.eval₂_pow] using hbudget p hp
  have hRC : R ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (R + 3) ^ 5)).trans hsum
  have hSC : (R + 3) ^ 5 ≤ (p + C) ^ C := (le_add_of_nonneg_left hR).trans hsum
  obtain ⟨hdim, q, hc, hgen, e, he, hdim₀, _⟩ := hmodel X r w hw p hp hX
  let F := FreeDegreeRankLieAlgebra.filtration X s r w hw hr
  let v (i j : Fin (s + 1)) := FreeDegreeRankLieAlgebra.layerFamily X s r w hw hr i.val j.val
  have hv (i j : Fin (s + 1)) (x : FreeDegreeRankLieAlgebra.layerGenerators X s r w hw i.val j.val) (k) :
      rationalLogHeight (q.repr (v i j x : FreeDegreeRankLieAlgebra X s r w hw) k) ≤ P := by
    exact FreeDegreeRankLieAlgebra.layerGenerators_logHeight X s r w hw q hB
      (by simpa only [Fintype.card_fin] using hdim) hc hgen i.val j.val
      (Nat.le_of_lt_succ i.isLt) x.val x.property k
  obtain ⟨b, hcentral, hlayer, _, hinverse, hstructure⟩ := F.exists_rank_adapted_basis_logHeight q v
    (fun i j => FreeDegreeRankLieAlgebra.layerFamily_span X s r w hw hr i.val j.val) hP
    (by simpa only [Fintype.card_fin] using hdim.trans hBP) hv
    (fun i j k => (hc i j k).trans hBP)
  have htree (x : FreeNilpotentLieAlgebra X s)
      (hx : x ∈ FreeNilpotentLieAlgebra.treeGenerators X s) (j) :
      rationalLogHeight (b.repr (FreeDegreeRankLieAlgebra.projection X s r w hw x) j) ≤ R := by
    apply le_trans _ hprojectionR
    exact linearMap_coordinate_logHeight q b LinearMap.id hQ
      (by simpa only [Fintype.card_fin] using hdim.trans (hBP.trans hPQ))
      (fun i k => (hinverse i k).trans hIQ) (FreeDegreeRankLieAlgebra.projection X s r w hw x)
      (fun i => (hgen x hx i).trans (hBP.trans hPQ)) j
  let A := LinearMap.toMatrix e b (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap
  have hA (i j) : rationalLogHeight (A i j) ≤ R := by
    dsimp only [A]
    rw [LinearMap.toMatrix_apply]
    exact htree (e j) (he j) i
  obtain ⟨S, hAS, hS⟩ := exists_rational_section_exp_height A
    (basisMatrix_surjective e b (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap
      (FreeDegreeRankLieAlgebra.projection_surjective X s r w hw))
    (one_le_ceil_exp R) (fun i j => rationalHeightLE_ceil_exp (hA i j))
    (hR.trans (le_add_of_nonneg_right zero_le_one))
    (by simpa only [Fintype.card_fin] using
      (hdim.trans (hBR.trans (le_add_of_nonneg_right zero_le_one))))
    (ceil_exp_le_exp_add_one hR)
  refine ⟨hdim.trans (hBR.trans hRC), b, hcentral, hlayer,
    fun i j k => (hstructure i j k).trans (hstructureR.trans hRC),
    fun x hx i => (htree x hx i).trans hRC, e, he, hdim₀.trans (hBR.trans hRC), S, hAS, ?_⟩
  intro i j
  apply le_trans ((rationalLogHeight_le_iff _ _).mpr (hS i j))
  simpa only [show R + 1 + 2 = R + 3 from
    (add_assoc R 1 2).trans (congrArg (fun z : ℝ => R + z) (by norm_num))] using hSC

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrNiltestBudget
namespace OAI

section

namespace Erdos3.RationalTorus

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable (d : ℕ)
  [TopologicalSpace (ℝ ⊗[ℚ] Algebra d)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra d)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] Algebra d)] [T2Space (ℝ ⊗[ℚ] Algebra d)]

theorem phaseCoordinates_lipschitz :
    letI := rightMetricSpace
      (hnil := (nilmanifold d).filtration.realification.lowerCentralSeries_eq_bot)
      ((basis d).baseChange ℝ)
    LipschitzWith 1 (phaseCoordinates d) := by
  let := rightMetricSpace
    (hnil := (nilmanifold d).filtration.realification.lowerCentralSeries_eq_bot)
    ((basis d).baseChange ℝ)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hc := ((nilmanifold d).filtration.realification.stepOne_coordinates_lipschitz
    ((basis d).baseChange ℝ)).dist_le_mul x y
  simp only [NNReal.coe_one, one_mul, basisHomeomorph_apply] at hc
  have hphase : dist (phaseCoordinates d x) (phaseCoordinates d y) ≤
      dist (((basis d).baseChange ℝ).equivFun x.coord)
        (((basis d).baseChange ℝ).equivFun y.coord) := by
    change dist
      (fun i : Fin d => (((basis d).baseChange ℝ).repr x.coord i : CircleFourier.Circle))
      (fun i : Fin d => (((basis d).baseChange ℝ).repr y.coord i : CircleFourier.Circle)) ≤ _
    simpa only [NNReal.coe_one, one_mul, Basis.equivFun_apply] using
      CircleFourier.real_phase_map_lipschitz.dist_le_mul
        (((basis d).baseChange ℝ).equivFun x.coord)
        (((basis d).baseChange ℝ).equivFun y.coord)
  simpa only [NNReal.coe_one, one_mul] using hphase.trans hc

theorem phaseProjection_lipschitz :
    letI := (nilmanifold d).metricSpace
    LipschitzWith 1 (phaseProjection d) := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] Algebra d) :=
    ((basis d).baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace
    (hnil := (nilmanifold d).filtration.realification.lowerCentralSeries_eq_bot)
    ((basis d).baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul
    (hnil := (nilmanifold d).filtration.realification.lowerCentralSeries_eq_bot)
    ((basis d).baseChange ℝ)
  exact rightCosetMetricSpace_lipschitz_lift (nilmanifold d).realLattice
    (nilmanifold d).realLattice_closed_discrete.1 (phaseProjection d)
    (phaseCoordinates_lipschitz d)

end Erdos3.RationalTorus

end

section

namespace Erdos3.RationalTorus

open scoped BigOperators TensorProduct NNReal

variable {σ : Type*} [Fintype σ] (d : ℕ)

variable [TopologicalSpace (ℝ ⊗[ℚ] Algebra d)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra d)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] Algebra d)] [T2Space (ℝ ⊗[ℚ] Algebra d)]
  (b : Fin d → ℝ) (a : σ → Fin d → ℝ)
  (Ψ : (Fin d → CircleFourier.Circle) → ℂ) (M K : ℝ≥0)
  (hΨ : ∀ v, ‖Ψ v‖ ≤ M) (hLip : LipschitzWith K Ψ)

noncomputable def affineNiltest : (nilmanifold d).Niltest (fun _ : σ => 1) where
  orbit := affineOrbit d b a
  observable := Ψ ∘ phaseProjection d
  normBound := M
  lipBound := K
  norm_le x := hΨ (phaseProjection d x)
  lipschitz := by
    let := (nilmanifold d).metricSpace
    simpa only [mul_one] using hLip.comp (phaseProjection_lipschitz d)

theorem affineNiltest_eval (x : σ → ℤ) :
    (affineNiltest d b a Ψ M K hΨ hLip).eval x =
      Ψ (fun i => ((b + ∑ j, (x j : ℝ) • a j) i : CircleFourier.Circle)) := by
  change Ψ (phaseCoordinates d
    ((nilmanifold d).filtration.realification.polynomialOrbitEval (fun _ => 1) x
      (affineOrbit d b a))) = _
  rw [affineOrbit_phases]

theorem affineNiltest_evalCyclic (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    (affineNiltest d b a Ψ M K hΨ hLip).evalCyclic N x =
      Ψ (fun i => ((b + ∑ j, ((x j).val : ℝ) • a j) i : CircleFourier.Circle)) := by
  rw [RationalFilteredNilmanifold.Niltest.evalCyclic, affineNiltest_eval]
  simp only [Int.cast_natCast]

theorem affineNiltest_complexity {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p)
    (hbudget : Real.log (2 + (M : ℝ) + (K : ℝ)) ≤ p) :
    (affineNiltest d b a Ψ M K hΨ hLip).ComplexityLE p :=
  ⟨nilmanifold_geometry d hp hd, hbudget⟩

end Erdos3.RationalTorus

end

section

namespace Erdos3

open scoped TensorProduct NNReal

namespace RationalTorus

variable {ι : Type*} [Fintype ι] {d : ℕ} (e : ι ≃ Fin d)
  (Ψ : (ι → CircleFourier.Circle) → ℝ)

omit [Fintype ι] in
theorem reindexedRealObservable_norm (hΨ : ∀ v, 0 ≤ Ψ v ∧ Ψ v ≤ 1)
    (v : Fin d → CircleFourier.Circle) : ‖reindexedRealObservable e Ψ v‖ ≤ (1 : ℝ≥0) := by
  change ‖(Ψ (fun i => v (e i)) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hΨ _).1]
  exact (hΨ _).2

theorem reindexedRealObservable_lipschitz {K : ℝ≥0} (hLip : LipschitzWith K Ψ) :
    LipschitzWith K (reindexedRealObservable e Ψ) := by
  change LipschitzWith K (fun v : Fin d → CircleFourier.Circle => (Ψ (fun i => v (e i)) : ℂ))
  simpa only [one_mul, mul_one, Function.comp_def] using
    Complex.isometry_ofReal.lipschitz.comp (hLip.comp (torus_reindex_lipschitz e))

variable [TopologicalSpace (ℝ ⊗[ℚ] Algebra d)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra d)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] Algebra d)] [T2Space (ℝ ⊗[ℚ] Algebra d)]
  (b a : ι → ℝ) (K : ℝ≥0)
  (hΨ : ∀ v, 0 ≤ Ψ v ∧ Ψ v ≤ 1) (hLip : LipschitzWith K Ψ)

noncomputable def realAffineNiltest : (nilmanifold d).Niltest (fun _ : Unit => 1) :=
  affineNiltest d (fun i => b (e.symm i)) (fun _ : Unit => fun i => a (e.symm i))
    (reindexedRealObservable e Ψ) 1 K (reindexedRealObservable_norm e Ψ hΨ)
    (reindexedRealObservable_lipschitz e Ψ hLip)

theorem realAffineNiltest_unitInterval :
    (realAffineNiltest e Ψ b a K hΨ hLip).UnitIntervalValued := by
  intro z
  change 0 = 0 ∧ 0 ≤ Ψ (fun i => phaseProjection d z (e i)) ∧
    Ψ (fun i => phaseProjection d z (e i)) ≤ 1
  exact ⟨rfl, hΨ _⟩

theorem realAffineNiltest_evalCyclic (N : ℕ) [NeZero N] (x : ZMod N) :
    (realAffineNiltest e Ψ b a K hΨ hLip).evalCyclic N (fun _ => x) =
      (Ψ (fun i => ((b i + (x.val : ℝ) * a i : ℝ) : CircleFourier.Circle)) : ℂ) := by
  unfold realAffineNiltest
  rw [affineNiltest_evalCyclic]
  simp [reindexedRealObservable]

theorem realAffineNiltest_complexity {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p)
    (hbudget : Real.log (3 + (K : ℝ)) ≤ p) :
    (realAffineNiltest e Ψ b a K hΨ hLip).ComplexityLE p := by
  apply affineNiltest_complexity _ _ _ _ _ _ _ _ hp hd
  simpa only [NNReal.coe_one, show (2 : ℝ) + 1 = 3 by norm_num] using hbudget

end RationalTorus
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformControlledNativeExternalNetsOfRecovery
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem observable_freeze_factors (T : D.Niltest w) (a a₀ b r r₀ : D.RealGroup)
    (hr : (QuotientGroup.mk r : D.Space) = QuotientGroup.mk r₀) :
    letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
    ‖T.observable (QuotientGroup.mk (a * b * r)) -
      T.observable (QuotientGroup.mk (a₀ * b * r₀))‖ ≤ (T.lipBound : ℝ) * dist a a₀ := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  have heq : T.observable (QuotientGroup.mk (a * b * r)) =
      T.observable (QuotientGroup.mk (a * b * r₀)) :=
    congrArg (fun x : D.Space => T.observable ((a * b) • x)) hr
  rw [heq, mul_assoc a b r₀, mul_assoc a₀ b r₀]
  exact T.observable_change_left a a₀ (QuotientGroup.mk (b * r₀))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SampledNativeModel
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeSampleCorrelation

variable {σ X : Type*} {w : σ → ℕ} {s : ℕ} {p q : ℝ}
  {S : Finset X} {sample : X → σ → ℤ} {f : X → ℂ}

noncomputable def mono (V : NativeSampleCorrelation w s p S sample f) (hpq : p ≤ q) :
    NativeSampleCorrelation w s q S sample f :=
  { V with
    complexity := V.complexity.mono hpq
    correlation := (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans V.correlation }

end NativeSampleCorrelation

end Erdos3

end

section

namespace Erdos3.NativeSampleModel

open CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [instance] VerticalExpansion.finite

end Erdos3.NativeSampleModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCrossFactorization
namespace OAI

section

namespace Erdos3.NativeVectorCorrelation

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_of_mean_approx {I : Type*} {degree N : ℕ} [NeZero N] {p : ℝ}
    {f : I → ZMod N → ℂ} (W : NativeVectorCorrelation degree N p f)
    (g : I → ZMod N → ℂ)
    (herr : (𝔼 x, ‖f W.coordinate x - g W.coordinate x‖) ≤ Real.exp (-(2 * p)) / 2) :
    Nonempty (NativeVectorCorrelation degree N (p + 1) g) := by
  let b (x : ZMod N) := star (W.test.evalCyclic N (fun _ => x))
  have hb (x : ZMod N) : ‖b x‖ ≤ Real.exp p := by
    simpa only [b, norm_star, RationalFilteredNilmanifold.Niltest.evalCyclic] using W.test.eval_budget W.complexity
      (fun _ : Unit => (x.val : ℤ))
  have he := mean_error_mul_bounded (f W.coordinate) (g W.coordinate) b
    (Real.exp_pos p).le hb herr
  have hexp : Real.exp p * (Real.exp (-(2 * p)) / 2) = Real.exp (-p) / 2 := by
    rw [← mul_div_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hexp] at he
  have hdiff : ‖(𝔼 x, f W.coordinate x * b x) -
      (𝔼 x, g W.coordinate x * b x)‖ ≤ Real.exp (-p) / 2 := by
    rw [← Finset.expect_sub_distrib]
    exact (RCLike.norm_expect_le (K := ℂ)).trans he
  have hretain : Real.exp (-p) / 2 ≤ ‖𝔼 x, g W.coordinate x * b x‖ := by
    have htri := norm_le_norm_add_norm_sub
      (𝔼 x, g W.coordinate x * b x) (𝔼 x, f W.coordinate x * b x)
    rw [norm_sub_rev] at htri
    have hc : Real.exp (-p) ≤ ‖𝔼 x, f W.coordinate x * b x‖ := W.correlation
    linarith
  refine ⟨{ W with complexity := W.complexity.mono (by linarith), correlation := ?_ }⟩
  have ht : Real.exp (-(p + 1)) ≤ Real.exp (-p) / 2 := by
    simpa only [neg_add, sub_eq_add_neg] using exp_sub_one_le_half_exp (-p)
  exact ht.trans hretain

theorem exists_of_uniform_approx {I : Type*} {degree N : ℕ} [NeZero N] {p : ℝ}
    {f : I → ZMod N → ℂ} (W : NativeVectorCorrelation degree N p f)
    (g : I → ZMod N → ℂ)
    (herr : ∀ i x, ‖f i x - g i x‖ ≤ Real.exp (-(2 * p)) / 2) :
    Nonempty (NativeVectorCorrelation degree N (p + 1) g) := by
  apply W.exists_of_mean_approx g
  calc
    _ ≤ 𝔼 _x : ZMod N, Real.exp (-(2 * p)) / 2 :=
      Finset.expect_le_expect (fun x _ => herr W.coordinate x)
    _ = _ := by simp

end Erdos3.NativeVectorCorrelation

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace NativeVectorCorrelation

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_absorb {I J : Type*} {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d N : ℕ} [NeZero N] {p : ℝ} (D : RationalFilteredNilmanifold L s d)
    (T : J → D.Niltest (fun _ : Unit => 1)) (f : I → ZMod N → ℂ) (hp : 2 ≤ p)
    (hT : ∀ j, (T j).ComplexityLE p)
    (W : NativeVectorCorrelation s N p
      (fun ij : I × J => fun x => f ij.1 x * star ((T ij.2).evalCyclic N (fun _ => x)))) :
    Nonempty (NativeVectorCorrelation s N (productNiltestBudget p) f) := by
  have hp0 : 0 ≤ p := by linarith
  let K : Bool → Type := BoolLieFamily L W.L
  let dims : Bool → ℕ := fun b => Bool.rec W.dim d b
  let models : ∀ b, RationalFilteredNilmanifold (K b) s (dims b) := fun b => by
    cases b
    · exact W.model
    · exact D
  let tests : ∀ b, (models b).Niltest (fun _ : Unit => 1) := fun b => by
    cases b
    · exact W.test
    · exact T W.coordinate.2
  have htests : ∀ b, (tests b).ComplexityLE p := by
    intro b
    cases b
    · exact W.complexity
    · exact hT _
  have hcard : (Fintype.card Bool : ℝ) ≤ p := by
    simpa only [Fintype.card_bool, Nat.cast_ofNat] using hp
  let : FiniteDimensional ℚ (∀ b, K b) :=
    (RationalFilteredNilmanifold.productFinBasis models).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ b, K b))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ b, K b)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ b, K b)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis models)
  let S := RationalFilteredNilmanifold.piNiltest models tests hp0 hcard htests
  have heval (x : ZMod N) : S.evalCyclic N (fun _ => x) =
      (T W.coordinate.2).evalCyclic N (fun _ => x) * W.test.evalCyclic N (fun _ => x) := by
    change (RationalFilteredNilmanifold.piNiltest models tests hp0 hcard htests).eval
      (fun _ : Unit => (x.val : ℤ)) = _
    rw [RationalFilteredNilmanifold.piNiltest_eval, Fintype.prod_bool]
    rfl
  refine ⟨{
    L := ∀ b, K b
    dim := _
    model := RationalFilteredNilmanifold.pi models
    test := S
    complexity := RationalFilteredNilmanifold.piNiltest_complexity models tests hp0 hcard htests
    coordinate := W.coordinate.1
    correlation := ?_
  }⟩
  have hcorr := (Real.exp_le_exp.mpr (neg_le_neg (le_productNiltestBudget hp0))).trans W.correlation
  simpa only [heval, star_mul, mul_assoc, mul_left_comm, mul_comm] using hcorr

end NativeVectorCorrelation

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SourceUnitCover
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

namespace RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
  {D : RationalFilteredNilmanifold L s d}

namespace DegreeRankStructure

noncomputable def withLattice (R : D.DegreeRankStructure r)
    (Λ : Subgroup D.filtration.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N) :
    (D.withLattice Λ N hN hin hout).DegreeRankStructure r where
  filtration := R.filtration
  associated := R.associated
  basis := R.basis

theorem withLattice_complexity (R : D.DegreeRankStructure r)
    (Λ : Subgroup D.filtration.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)
    {p P : ℝ} (hR : R.ComplexityLE p) (hpP : p ≤ P)
    (hQ : (D.withLattice Λ N hN hin hout).GeometryComplexityLE P) :
    (R.withLattice Λ N hN hin hout).ComplexityLE P :=
  ⟨hQ, fun i j a k => (hR.2 i j a k).trans hpP⟩

theorem top_realSubgroup_commute (R : D.DegreeRankStructure r)
    {z : D.RealGroup} (hz : z ∈ R.realSubgroup s r) (x : D.RealGroup) : Commute z x := by
  apply commute_of_lie_eq_zero
  exact D.filtration.realification.top_layer_central (R.realSubgroup_le_degree s r hz) x.coord

end DegreeRankStructure

variable {I : Type*} [Fintype I]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

namespace UnitVerticalObservable

noncomputable def frozenCover (R : D.DegreeRankStructure r) {p P : ℝ}
    (V : D.UnitVerticalObservable (R.realSubgroup s r) I p)
    (Λ : Subgroup D.filtration.Group) (hΛ : Λ ≤ D.lattice)
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)
    (a u : D.RealGroup) (f : (D.withLattice Λ N hN hin hout).Space → D.Space)
    (hf : ∀ x : D.RealGroup, f (QuotientGroup.mk x) = QuotientGroup.mk (a * x * u))
    (K : ℝ≥0)
    (hLip : letI := (D.withLattice Λ N hN hin hout).metricSpace;
      letI := D.metricSpace; LipschitzWith K f)
    (hpP : p ≤ P) (hK : (V.lipBound * K : ℝ≥0) ≤ Real.exp P) :
    (D.withLattice Λ N hN hin hout).UnitVerticalObservable
      ((R.withLattice Λ N hN hin hout).realSubgroup s r) I P where
  observable i x := V.observable i (f x)
  unit x := V.unit (f x)
  norm i x := V.norm i (f x)
  lipBound := V.lipBound * K
  lip_bound := hK
  lipschitz := by
    let := (D.withLattice Λ N hN hin hout).metricSpace
    let := D.metricSpace
    exact fun i => (V.lipschitz i).comp hLip
  frequency := V.frequency
  height i := (V.height i).trans hpP
  vertical i z hz x := by
    rw [frozen_quotient_map_smul _ _ a u f hf z (R.top_realSubgroup_commute hz a)]
    exact V.vertical i z hz (f x)
  integral z hz hlat := by
    have hsub : (D.withLattice Λ N hN hin hout).realLattice ≤ D.realLattice := Subgroup.map_mono hΛ
    exact V.integral z hz (hsub hlat)

end UnitVerticalObservable
end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M I : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [Fintype I] {s t d e : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {D : RationalFilteredNilmanifold L s d} {E : RationalFilteredNilmanifold M t e}
  {T : Subgroup E.RealGroup} {p q : ℝ} (V : E.UnitVerticalObservable T I p)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : D.lattice ≤ E.lattice.comap (mapOfSteps
    (hL := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
  (S : Subgroup D.RealGroup)
  (hS : S ≤ T.comap (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
  (K : ℝ≥0)
  (hLip : letI := D.metricSpace; letI := E.metricSpace;
    LipschitzWith K (D.nativeSpaceMap E φ hφ))
  (hK : ((V.lipBound * K : ℝ≥0) : ℝ) ≤ Real.exp q)
  (hfreq : ∀ i, rationalLogHeight (V.frequency (φ (D.basis i))) ≤ q)

noncomputable def pullback : D.UnitVerticalObservable S I q where
  observable i x := V.observable i (D.nativeSpaceMap E φ hφ x)
  unit x := V.unit (D.nativeSpaceMap E φ hφ x)
  norm i x := V.norm i (D.nativeSpaceMap E φ hφ x)
  lipBound := V.lipBound * K
  lip_bound := hK
  lipschitz := by
    let := D.metricSpace
    let := E.metricSpace
    exact fun i => (V.lipschitz i).comp hLip
  frequency := V.frequency.comp φ.toLinearMap
  height := hfreq
  vertical i z hz x := by
    rw [D.nativeSpaceMap_smul E φ hφ z x, realifyFunctional_comp]
    exact V.vertical i
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ z) (hS hz) _
  integral z hz hlat := by
    obtain ⟨n, hn⟩ := V.integral
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ z)
      (hS hz) ((realificationMap_subgroup φ D.lattice E.lattice hφ) hlat)
    refine ⟨n, ?_⟩
    rw [realifyFunctional_comp]
    exact hn

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeDegreeRankFamily
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

namespace NativeDegreeRankFamily

variable {s r : ℕ} {A : Type*} {p q : ℝ} (W : NativeDegreeRankFamily s r A p)

noncomputable def mono (hpq : p ≤ q) : NativeDegreeRankFamily s r A q :=
  { W with
    complexity := W.complexity.mono W.rank hpq
    output_bound := W.output_bound.trans (Real.exp_le_exp.mpr hpq)
    vertical := W.vertical.mono hpq }

end NativeDegreeRankFamily

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialGridValues
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

theorem polynomialSlowBound_value [Fintype σ] (hw : ∀ i, 0 < w i)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T M g) (v : σ → ℝ) (hv : ∀ i, |v i| ≤ T i) (i : ι) :
    |(b.baseChange ℝ).repr (F.adaptedPolynomialRealValueHom w v g).coord i| ≤
      ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * M := by
  let P := coordinate (((b.baseChange ℝ).coord i).toAddMonoidHom)
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
  have hdegree : P.totalDegree ≤ s := F.adaptedPolynomial_coordinate_totalDegree b w hw g i
  have hcoeff (α : σ →₀ ℕ) : |P.coeff α| ≤ M / monomialScale T α := by
    dsimp only [P]
    rw [coeff_coordinate]
    exact hg α i
  have hcard : (P.support.card : ℝ) ≤ ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s := by
    exact_mod_cast polynomial_support_card_le P hdegree
  change |((b.baseChange ℝ).coord i) (eval₂ v (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)))| ≤ _
  rw [coordinate_eval₂]
  exact (abs_eval_le_scaled_box_bound P T v hT hM hcoeff hv).trans
    (mul_le_mul_of_nonneg_right hcard hM)

theorem polynomialSlowBound_difference [Fintype σ] (hw : ∀ i, 0 < w i)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T M g) (v z : σ → ℝ)
    (hv : ∀ i, |v i| ≤ T i) (hz : ∀ i, |z i| ≤ T i)
    (hvz : ∀ i, |v i - z i| ≤ T i * δ) (i : ι) :
    |(b.baseChange ℝ).repr (F.adaptedPolynomialRealValueHom w v g).coord i -
      (b.baseChange ℝ).repr (F.adaptedPolynomialRealValueHom w z g).coord i| ≤
      ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * M * Fintype.card σ * s * δ := by
  let P := coordinate (((b.baseChange ℝ).coord i).toAddMonoidHom)
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
  have hdegree : P.totalDegree ≤ s := F.adaptedPolynomial_coordinate_totalDegree b w hw g i
  have hcoeff (α : σ →₀ ℕ) : |P.coeff α| ≤ M / monomialScale T α := by
    dsimp only [P]
    rw [coeff_coordinate]
    exact hg α i
  have hcard : (P.support.card : ℝ) ≤ ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s := by
    exact_mod_cast polynomial_support_card_le P hdegree
  change |((b.baseChange ℝ).coord i) (eval₂ v (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) -
    ((b.baseChange ℝ).coord i) (eval₂ z (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)))| ≤ _
  rw [coordinate_eval₂, coordinate_eval₂]
  apply (abs_eval_sub_eval_scaled_box_bound P T v z hT hM hδ hcoeff hv hz hvz hdegree).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hM) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)) hδ

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module _root_.MvPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

open VectorPolynomial

theorem polynomialRationalGrid_exists_coordinates {σ ι L : Type*} [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)
    (hw : ∀ i, 0 < w i) (q : ℕ) (hq : 0 < q)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w q g) :
    ∃ P : ι → MvPolynomial σ ℚ,
      (∀ i, (P i).totalDegree ≤ s) ∧ (∀ i α, ((P i).coeff α).den ∣ q) ∧
      ∀ x : σ → ℝ,
        realPolynomialBCHMap (hnil := F.realification.lowerCentralSeries_eq_bot)
          (b.baseChange ℝ) P x = F.adaptedPolynomialRealValueHom w x g := by
  classical
  let R := fun i => coordinate (((b.baseChange ℝ).coord i).toAddMonoidHom)
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
  obtain ⟨a, ha⟩ := hg
  have hR (i : ι) : ∀ α, ∃ z : ℤ, (z : ℝ) = (q : ℝ) * (R i).coeff α := by
    intro α
    refine ⟨a (α, i), ?_⟩
    dsimp only [R]
    rw [coeff_coordinate]
    exact congrFun ha (α, i)
  choose P hmap hdeg hden using fun i => exists_rational_polynomial_of_grid (R i) q hq (hR i)
  refine ⟨P, fun i => (hdeg i).le.trans (F.adaptedPolynomial_coordinate_totalDegree b w hw g i), hden, ?_⟩
  intro x
  apply NilpotentLieBCHGroup.ext
  apply (b.baseChange ℝ).equivFun.injective
  rw [realPolynomialBCHMap_coordinates]
  funext i
  change aeval x (P i) = ((b.baseChange ℝ).coord i)
    (VectorPolynomial.eval₂ x (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)))
  rw [coordinate_eval₂]
  change aeval x (P i) = MvPolynomial.eval x (R i)
  rw [← hmap i, MvPolynomial.eval_map]
  rfl

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

theorem polynomialSlowBound_dist_le (hw : ∀ i, 0 < w i)
    (H : ℕ) (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (B : ℝ≥0) (hB : 1 ≤ B)
    (hMB : ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * M ≤ B)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T M g) (v z : σ → ℝ)
    (hv : ∀ i, |v i| ≤ T i) (hz : ∀ i, |z i| ≤ T i)
    (hvz : ∀ i, |v i - z i| ≤ T i * δ) :
    letI := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
    dist (F.adaptedPolynomialRealValueHom w v g) (F.adaptedPolynomialRealValueHom w z g) ≤
      (bchBoxMetricConstant s (Fintype.card ι) H B : ℝ) *
        (((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * M * Fintype.card σ * s) * δ := by
  let := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
  have h := dist_le_bchBoxMetricConstant (b.baseChange ℝ) (lieStructureConstants b)
    (fun i j k => (realLieBasis_structure b i j k).symm) hc B hB
    (show 0 ≤ ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * M * Fintype.card σ * s * δ by positivity)
    (F.adaptedPolynomialRealValueHom w v g) (F.adaptedPolynomialRealValueHom w z g)
    (fun i => (F.polynomialSlowBound_value b w hw T hT hM g hg v hv i).trans hMB)
    (fun i => (F.polynomialSlowBound_value b w hw T hT hM g hg z hz i).trans hMB)
    (fun i => F.polynomialSlowBound_difference b w hw T hT hM hδ g hg v z hv hz hvz i)
  simpa only [mul_assoc] using h

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_polynomialSlowBound_dist_exp (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ g : (D.filtration.realification.adaptedPolynomialFiltration w).Group,
        D.filtration.PolynomialSlowBound D.basis w T (Real.exp ((p + 2) ^ r)) g →
        ∀ (v z : σ → ℝ) (δ : ℝ), 0 ≤ δ →
          (∀ i, |v i| ≤ T i) → (∀ i, |z i| ≤ T i) →
          (∀ i, |v i - z i| ≤ T i * δ) →
          letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
          dist (D.filtration.adaptedPolynomialRealValueHom w v g)
            (D.filtration.adaptedPolynomialRealValueHom w z g) ≤ Real.exp ((p + C) ^ C) * δ := by
  obtain ⟨a, _, hbound⟩ := exists_slow_polynomial_metric_budget s r
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + 1 + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D w hw p hp hD hσ T hT g hg v z δ hδ hv hz hvz
  let H := ⌈Real.exp p⌉₊
  have hpp : p ≤ p + 1 := le_add_of_nonneg_right zero_le_one
  obtain ⟨B, hB, hMB, hK⟩ := hbound d (Fintype.card σ) H (p + 1)
    (Real.exp ((p + 2) ^ r)) (by linarith) (hD.1.trans hpp) (hσ.trans hpp)
    (ceil_exp_le_exp_add_one hp) (Real.exp_pos _).le
    (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) _))
  have hdist := D.filtration.polynomialSlowBound_dist_le D.basis w hw H
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)) T hT (Real.exp_pos _).le
    hδ B hB hMB g hg v z hv hz hvz
  have hK' : (bchBoxMetricConstant s (Fintype.card (Fin d)) H B : ℝ) *
      (((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * Real.exp ((p + 2) ^ r) * Fintype.card σ * s) ≤
        Real.exp ((p + C) ^ C) := by
    rw [Fintype.card_fin]
    apply hK.trans (Real.exp_le_exp.mpr _)
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  exact hdist.trans (mul_le_mul_of_nonneg_right hK' hδ)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module _root_.MvPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

open VectorPolynomial

theorem polynomialRationalGrid_value {σ ι L : Type*} [Fintype σ] [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ) (q : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w q g) (x : σ → ℤ) :
    (b.baseChange ℝ).equivFun
      (F.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) g).coord ∈ realDenominatorGrid q := by
  classical
  let P := fun i => coordinate (((b.baseChange ℝ).coord i).toAddMonoidHom)
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
  obtain ⟨a, ha⟩ := hg
  have hP (i : ι) : ∀ α, ∃ z : ℤ, (z : ℝ) = (q : ℝ) * (P i).coeff α := by
    intro α
    refine ⟨a (α, i), ?_⟩
    dsimp only [P]
    rw [coeff_coordinate]
    exact congrFun ha (α, i)
  choose z hz using fun i => polynomial_integer_value_common_denominator (P i) q (hP i) x
  refine ⟨z, funext fun i => ?_⟩
  change (z i : ℝ) = (q : ℝ) * ((b.baseChange ℝ).coord i)
    (eval₂ (fun j => (x j : ℝ)) (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)))
  rw [coordinate_eval₂]
  exact hz i

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOrbitFreezing
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

theorem polynomialOrbitCoordinates_realValue {σ L : Type*}
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ} (F : NilpotentLieFiltration L s)
    (w : σ → ℕ) (g : F.realification.PolynomialOrbit w) (x : σ → ℤ) :
    F.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ))
        (F.realification.polynomialOrbitCoordinates w g) =
      F.realification.polynomialOrbitEval w x g := by
  apply NilpotentLieBCHGroup.ext
  change eval₂ (fun i => (x i : ℝ)) g.log = eval (fun i => (x i : ℚ)) g.log
  simpa only [map_intCast] using
    (eval₂_algebraMap (S := ℝ) (fun i => (x i : ℚ)) g.log)

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_orbit_factor_freezing (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p →
      ∀ (Φ : D.Space → ℂ) (K : ℝ≥0), (∀ x, ‖Φ x‖ ≤ 1) →
      (letI := D.metricSpace; LipschitzWith K Φ) → (K : ℝ) ≤ Real.exp p →
      ∀ ε b γ g : D.filtration.realification.PolynomialOrbit w,
        ε * b * γ = g → ∀ T : σ → ℝ, (∀ i, 0 < T i) →
        CoefficientBound (D.basis.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) ε.log →
        ∀ (x y : σ → ℤ) (δ : ℝ), 0 ≤ δ →
        (∀ i, |(x i : ℝ)| ≤ T i) → (∀ i, |(y i : ℝ)| ≤ T i) →
        (∀ i, |(x i : ℝ) - y i| ≤ T i * δ) →
        (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x γ) : D.Space) =
          QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w y γ) →
        ‖Φ (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g)) -
          Φ (QuotientGroup.mk
            (D.filtration.realification.polynomialOrbitEval w y ε *
             D.filtration.realification.polynomialOrbitEval w x b *
             D.filtration.realification.polynomialOrbitEval w y γ))‖ ≤
          Real.exp ((p + C) ^ C) * δ := by
  obtain ⟨c, _, hmove⟩ := exists_polynomialSlowBound_dist_exp s a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Polynomial.X + (Polynomial.X + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D w hw p hp hD hσ Φ K hΦ hLip hK ε b γ g hprod T hT hε x y δ hδ hx hy hxy hγ
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let S : D.Niltest w := {
    orbit := g
    observable := Φ
    normBound := 1
    lipBound := K
    norm_le := hΦ
    lipschitz := hLip }
  have hslow := (D.filtration.polynomialSlowBound_iff_formal D.basis w T _
    (D.filtration.realification.polynomialOrbitCoordinates w ε)).mpr hε
  have hdist := hmove D w hw p hp hD hσ T hT
    (D.filtration.realification.polynomialOrbitCoordinates w ε) hslow
    (fun i => (x i : ℝ)) (fun i => (y i : ℝ)) δ hδ hx hy hxy
  simp only [D.filtration.polynomialOrbitCoordinates_realValue] at hdist
  have hfreeze := S.observable_freeze_factors
    (D.filtration.realification.polynomialOrbitEval w x ε)
    (D.filtration.realification.polynomialOrbitEval w y ε)
    (D.filtration.realification.polynomialOrbitEval w x b)
    (D.filtration.realification.polynomialOrbitEval w x γ)
    (D.filtration.realification.polynomialOrbitEval w y γ) hγ
  have hg : D.filtration.realification.polynomialOrbitEval w x g =
      D.filtration.realification.polynomialOrbitEval w x ε *
      D.filtration.realification.polynomialOrbitEval w x b *
      D.filtration.realification.polynomialOrbitEval w x γ := by
    rw [← hprod, map_mul, map_mul]
  rw [hg]
  apply hfreeze.trans
  have hcost : p + (p + c) ^ c ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  calc
    _ ≤ Real.exp p * (Real.exp ((p + c) ^ c) * δ) :=
      mul_le_mul hK hdist dist_nonneg (Real.exp_pos p).le
    _ = Real.exp (p + (p + c) ^ c) * δ := by rw [← mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcost) hδ

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativePartitionFreezing
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial
open scoped TensorProduct BigOperators NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d N : ℕ} [NeZero N]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

noncomputable def frozenCyclicOrbitValue (D : RationalFilteredNilmanifold L s d)
    (Φ : D.Space → ℂ) (ε b γ : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (y x : ZMod N) : ℂ :=
  Φ (QuotientGroup.mk
    (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (y.val : ℤ)) ε *
     D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) b *
     D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (y.val : ℤ)) γ))

theorem exists_partition_orbit_freezing (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I L : Type*} [Fintype I] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d N M : ℕ} [NeZero N] (D : RationalFilteredNilmanifold L s d)
      {p ρ : ℝ}, 1 ≤ p → D.GeometryComplexityLE p → 0 < ρ →
      ∀ (A : I → ZMod N → ℝ), (∀ j x, 0 ≤ A j x) → (∀ x, ∑ j, A j x = 1) →
      (∀ j x y, x ∉ cyclicWrapExceptional 0 ρ → y ∉ cyclicWrapExceptional 0 ρ →
        0 < A j x → 0 < A j y →
        |(x.val : ℝ) - y.val| ≤ N * ρ ∧ (M : ℤ) ∣ (x.val : ℤ) - y.val) →
      ∀ (Φ : D.Space → ℂ) (K : ℝ≥0), (∀ x, ‖Φ x‖ ≤ 1) →
      (letI := D.metricSpace; LipschitzWith K Φ) → (K : ℝ) ≤ Real.exp p →
      ∀ ε b γ g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      ε * b * γ = g →
      CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
        (Real.exp ((p + 2) ^ a)) ε.log →
      (∀ x y : Unit → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
        (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x γ) : D.Space) =
          QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) y γ)) →
      ∃ y : I → ZMod N,
        (∀ j x, ‖D.frozenCyclicOrbitValue Φ ε b γ (y j) x‖ ≤ 1) ∧
        (𝔼 x, ‖Φ (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
            (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) g)) -
          ∑ j, (A j x : ℂ) * D.frozenCyclicOrbitValue Φ ε b γ (y j) x‖) ≤
            Real.exp ((p + C) ^ C) * ρ + 12 * ρ + 6 / N := by
  obtain ⟨C, hC, hfreeze⟩ := exists_orbit_factor_freezing s a
  refine ⟨C, hC, ?_⟩
  intro I L _ _ _ _ _ _ _ d N M _ D p ρ hp hD hρ A hA hsum hcells Φ K hΦ hLip hK ε b γ g hprod hε hperiod
  classical
  let E := cyclicWrapExceptional (0 : ZMod N) ρ
  have hchoose (j : I) : ∃ y : ZMod N, ∀ x, x ∉ E → 0 < A j x → y ∉ E ∧ 0 < A j y := by
    by_cases h : ∃ y, y ∉ E ∧ 0 < A j y
    · obtain ⟨y, hy⟩ := h
      exact ⟨y, fun _ _ _ => hy⟩
    · exact ⟨0, fun x hx hAx => False.elim (h ⟨x, hx, hAx⟩)⟩
  choose y hy using hchoose
  refine ⟨y, fun _ _ => hΦ _, ?_⟩
  have hpoint (j : I) (x : ZMod N) (hx : x ∉ E) (hAx : 0 < A j x) :
      ‖Φ (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) g)) -
        D.frozenCyclicOrbitValue Φ ε b γ (y j) x‖ ≤ Real.exp ((p + C) ^ C) * ρ := by
    obtain ⟨hyE, hAy⟩ := hy j x hx hAx
    obtain ⟨hnear, hres⟩ := hcells j x (y j) hx hyE hAx hAy
    apply hfreeze D (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) p (by linarith) hD
      (by simpa only [Fintype.card_unit, Nat.cast_one] using hp)
      Φ K hΦ hLip hK ε b γ g hprod (fun _ : Unit => (N : ℝ))
      (fun _ => Nat.cast_pos.mpr (NeZero.pos N)) hε
      (fun _ => (x.val : ℤ)) (fun _ => ((y j).val : ℤ)) ρ hρ.le
      (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (hperiod _ _ (fun _ => hres))
    · simpa only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ x.val from Nat.cast_nonneg _)] using
        (Nat.cast_le.mpr x.val_lt.le : (x.val : ℝ) ≤ N)
    · simpa only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ (y j).val from Nat.cast_nonneg _)] using
        (Nat.cast_le.mpr (y j).val_lt.le : ((y j).val : ℝ) ≤ N)
    · simpa only [Int.cast_natCast] using hnear
  have hm := complex_partition_approximation_mean_error E A
    (fun j x => D.frozenCyclicOrbitValue Φ ε b γ (y j) x)
    (fun x : ZMod N => Φ (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
      (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) g)))
    (mul_nonneg (Real.exp_pos _).le hρ.le) hA hsum (fun _ _ => hΦ _) (fun _ => hΦ _) hpoint
  apply hm.trans
  have hE := cyclicWrapExceptional_density_le (0 : ZMod N) hρ.le
  rw [ZMod.card]
  calc
    _ = Real.exp ((p + C) ^ C) * ρ + 2 * ((E.card : ℝ) / N) := by ring
    _ ≤ Real.exp ((p + C) ^ C) * ρ + 2 * (6 * ρ + 3 / N) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hE (by norm_num : (0 : ℝ) ≤ 2))
    _ = _ := by ring

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativePositiveCorrelation
namespace OAI

section

namespace Erdos3.NativeVectorCorrelation

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_absorb_positive {I : Type*} {degree N : ℕ} [NeZero N] {p : ℝ}
    (f : I → ZMod N → ℂ) (A : ZMod N → ℝ) (hp : 2 ≤ p)
    (hA : PositiveCyclicNiltest.{0} degree N p A)
    (W : NativeVectorCorrelation degree N p (fun i x => (A x : ℂ) * f i x)) :
    Nonempty (NativeVectorCorrelation degree N (productNiltestBudget (raisedNiltestBudget p)) f) := by
  rcases hA with @⟨L, lie, alg, s, dim, top, add, smul, t2, D, hs, T, hT, hTc, heval⟩
  let U := T.raiseStep hs
  have hpq : p ≤ raisedNiltestBudget p := le_raisedNiltestBudget p
  have hU : U.ComplexityLE (raisedNiltestBudget p) :=
    T.raiseStep_complexity hs (by linarith) hTc
  have hval (x : ZMod N) : (A x : ℂ) = star (U.evalCyclic N (fun _ => x)) := by
    rw [RationalFilteredNilmanifold.Niltest.raiseStep_evalCyclic]
    apply Complex.ext
    · simp only [Complex.ofReal_re, Complex.star_def, Complex.conj_re, heval]
    · simp only [Complex.ofReal_im, Complex.star_def, Complex.conj_im,
        (T.unit_interval_evalCyclic hT N (fun _ => x)).1, neg_zero]
  let W' : NativeVectorCorrelation degree N (raisedNiltestBudget p)
      (fun iu : I × Unit => fun x => f iu.1 x * star (U.evalCyclic N (fun _ => x))) := {
    L := W.L
    dim := W.dim
    model := W.model
    test := W.test
    complexity := W.complexity.mono hpq
    coordinate := (W.coordinate, ())
    correlation := by
      have h := (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans W.correlation
      simpa only [hval, mul_comm] using h }
  exact exists_absorb (D.raiseStep hs) (fun _ : Unit => U) f (hp.trans hpq) (fun _ => hU) W'

end Erdos3.NativeVectorCorrelation

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeResidueNiltests
namespace OAI

section

namespace Erdos3.RationalTorus

open CircleFourier
open scoped TensorProduct NNReal

variable [TopologicalSpace (ℝ ⊗[ℚ] Algebra 1)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra 1)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] Algebra 1)] [T2Space (ℝ ⊗[ℚ] Algebra 1)]

noncomputable def residueNiltest {q : ℕ} [NeZero q] (j : ZMod q) :
    (nilmanifold 1).Niltest (fun _ : Unit => 1) :=
  realAffineNiltest (Equiv.refl (Fin 1)) (fun v => residueCutoff j (v 0))
    (fun _ => 0) (fun _ => 1 / (q : ℝ)) (q : ℝ≥0)
    (fun v => residueCutoff_unit_interval j (v 0)) (residueObservable_lipschitz j)

theorem residueNiltest_unit_interval {q : ℕ} [NeZero q] (j : ZMod q) :
    (residueNiltest j).UnitIntervalValued := by
  unfold residueNiltest
  apply realAffineNiltest_unitInterval

theorem residueNiltest_complexity {q : ℕ} [NeZero q] (j : ZMod q) {p : ℝ}
    (hp : 0 ≤ p) (hq : (q : ℝ) ≤ Real.exp p) :
    (residueNiltest j).ComplexityLE (p + 2) := by
  unfold residueNiltest
  apply realAffineNiltest_complexity _ _ _ _ _ _ _ (by linarith) (by norm_num; linarith)
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  have h1 := Real.one_le_exp hp
  have h2 : (4 : ℝ) ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  rw [Real.exp_add]
  change 3 + (q : ℝ) ≤ Real.exp p * Real.exp 2
  nlinarith [mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg p)]

theorem residueNiltest_evalCyclic {q : ℕ} [NeZero q] (j : ZMod q)
    (N : ℕ) [NeZero N] (x : ZMod N) :
    (residueNiltest j).evalCyclic N (fun _ : Unit => x) =
      if (x.val : ZMod q) = j then 1 else 0 := by
  classical
  unfold residueNiltest
  rw [realAffineNiltest_evalCyclic]
  simp only [zero_add, mul_one_div]
  rw [← ZMod.toAddCircle_natCast, residueCutoff_at_grid]
  split_ifs <;> rfl

end Erdos3.RationalTorus

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeIntervalCoordinate
namespace OAI

section

namespace Erdos3.RationalTorus

open scoped TensorProduct NNReal

theorem intervalCoordinate_lipschitz :
    letI := (nilmanifold 1).metricSpace
    LipschitzWith 1 (fun z => phaseProjection 1 z 0) := by
  let := (nilmanifold 1).metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (dist_le_pi_dist (phaseProjection 1 x) (phaseProjection 1 y) 0).trans
    ((phaseProjection_lipschitz 1).dist_le_mul x y)

end Erdos3.RationalTorus

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslatedShiftTesting
namespace OAI

universe u

section

namespace Erdos3.PositiveCyclicNiltest

open scoped TensorProduct BigOperators

theorem mul {degree N : ℕ} [NeZero N] {p : ℝ} {f g : ZMod N → ℝ}
    (hf : PositiveCyclicNiltest.{u} degree N p f)
    (hg : PositiveCyclicNiltest.{u} degree N p g) (hp : 0 ≤ p) :
    PositiveCyclicNiltest.{u} degree N (productNiltestBudget (raisedNiltestBudget p))
      (fun x => f x * g x) := by
  rcases hf with @⟨L₁, lie₁, alg₁, s₁, dim₁, top₁, add₁, smul₁, t2₁, D₁, hs₁, A, hA, hAc, hevalA⟩
  rcases hg with @⟨L₂, lie₂, alg₂, s₂, dim₂, top₂, add₂, smul₂, t2₂, D₂, hs₂, B, hB, hBc, hevalB⟩
  let K : Bool → Type u := BoolLieFamily L₁ L₂
  let dims : Bool → ℕ := fun b => Bool.rec dim₂ dim₁ b
  let D : ∀ b, RationalFilteredNilmanifold (K b) degree (dims b) := fun b => by
    cases b
    · exact D₂.raiseStep hs₂
    · exact D₁.raiseStep hs₁
  let U : ∀ b, (D b).Niltest (fun _ : Unit => 1) := fun b => by
    cases b
    · exact B.raiseStep hs₂
    · exact A.raiseStep hs₁
  have hUc : ∀ b, (U b).ComplexityLE (raisedNiltestBudget p) := by
    intro b
    cases b
    · exact B.raiseStep_complexity hs₂ hp hBc
    · exact A.raiseStep_complexity hs₁ hp hAc
  have hU : ∀ b, (U b).UnitIntervalValued := by
    intro b
    cases b
    · exact B.raiseStep_unit_interval hs₂ hB
    · exact A.raiseStep_unit_interval hs₁ hA
  have hp' : 0 ≤ raisedNiltestBudget p := hp.trans (le_raisedNiltestBudget p)
  have hcard : (Fintype.card Bool : ℝ) ≤ raisedNiltestBudget p := by
    norm_num only [Fintype.card_bool, Nat.cast_ofNat]
    unfold raisedNiltestBudget
    nlinarith [sq_nonneg (p + 2)]
  let : FiniteDimensional ℚ (∀ b, K b) :=
    (RationalFilteredNilmanifold.productFinBasis D).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ b, K b))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ b, K b)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ b, K b)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis D)
  let S := RationalFilteredNilmanifold.piNiltest D U hp' hcard hUc
  have hSc := RationalFilteredNilmanifold.piNiltest_complexity D U hp' hcard hUc
  have hSu := RationalFilteredNilmanifold.piNiltest_unit_interval D U hp' hcard hUc hU
  have heval (x : ZMod N) : S.evalCyclic N (fun _ : Unit => x) =
      A.evalCyclic N (fun _ : Unit => x) * B.evalCyclic N (fun _ : Unit => x) := by
    change (RationalFilteredNilmanifold.piNiltest D U hp' hcard hUc).eval
      (fun _ : Unit => (x.val : ℤ)) = _
    rw [RationalFilteredNilmanifold.piNiltest_eval, Fintype.prod_bool]
    change (A.raiseStep hs₁).eval (fun _ : Unit => (x.val : ℤ)) *
      (B.raiseStep hs₂).eval (fun _ : Unit => (x.val : ℤ)) = _
    rw [RationalFilteredNilmanifold.Niltest.raiseStep_eval,
      RationalFilteredNilmanifold.Niltest.raiseStep_eval]
    rfl
  refine .of_test (RationalFilteredNilmanifold.pi D) le_rfl S hSu hSc ?_
  intro x
  rw [heval, Complex.mul_re, (A.unit_interval_evalCyclic hA N (fun _ => x)).1,
    (B.unit_interval_evalCyclic hB N (fun _ => x)).1, zero_mul, sub_zero, hevalA x, hevalB x]

end Erdos3.PositiveCyclicNiltest

end

section

namespace Erdos3

open scoped TensorProduct

theorem exists_interval_circle_partition (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (N : ℕ) [NeZero N] {p ρ : ℝ},
      0 ≤ p → 0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A : Fin n → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} 1 N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          ∀ j x y, 0 < A j x → 0 < A j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ := by
  obtain ⟨B, _, hpartition⟩ := RationalFilteredNilmanifold.exists_native_niltest_partition 1 a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + 1 + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p ρ hp hρ hρinv
  let D := RationalTorus.nilmanifold 1
  let G := RationalTorus.intervalOrbit N
  have hD : D.GeometryComplexityLE (p + 1) :=
    RationalTorus.nilmanifold_geometry 1 (by linarith) (by norm_num; linarith)
  have hρinv' : 1 / ρ ≤ Real.exp (((p + 1) + 2) ^ a) :=
    hρinv.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) _))
  obtain ⟨n, hn, hnb, tests, horbit, hunit, hcomplexity, hsum, hdiam⟩ :=
    hpartition D (fun _ : Unit => 1) (by linarith) hD hρ hρinv' G
  have hcost : (p + 1 + B) ^ B ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  let A : Fin n → ZMod N → ℝ := fun j x => ((tests j).evalCyclic N (fun _ : Unit => x)).re
  have heval (j : Fin n) (x : ZMod N) :
      A j x = ((tests j).observable (D.cyclicOrbitPoint G N (fun _ : Unit => x))).re := by
    change ((tests j).observable (QuotientGroup.mk
      (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (tests j).orbit))).re = _
    rw [horbit j]
    rfl
  refine ⟨n, hn, hnb.trans (Real.exp_le_exp.mpr hcost), A, ?_, ?_, ?_⟩
  · intro j
    exact .of_test D le_rfl (tests j) (hunit j) ((hcomplexity j).mono hcost) (fun _ => rfl)
  · intro x
    simpa only [heval] using hsum (D.cyclicOrbitPoint G N (fun _ : Unit => x))
  · let := D.metricSpace
    intro j x y hx hy
    have hd := hdiam j _ _ ((heval j x) ▸ hx) ((heval j y) ▸ hy)
    have hp := RationalTorus.intervalCoordinate_lipschitz.dist_le_mul
      (D.cyclicOrbitPoint G N (fun _ : Unit => x)) (D.cyclicOrbitPoint G N (fun _ : Unit => y))
    change dist (RationalTorus.phaseProjection 1 (D.cyclicOrbitPoint G N (fun _ : Unit => x)) 0)
      (RationalTorus.phaseProjection 1 (D.cyclicOrbitPoint G N (fun _ : Unit => y)) 0) ≤
      (1 : ℝ) * dist (D.cyclicOrbitPoint G N (fun _ : Unit => x))
        (D.cyclicOrbitPoint G N (fun _ : Unit => y)) at hp
    rw [RationalTorus.intervalOrbit_phase, RationalTorus.intervalOrbit_phase, one_mul] at hp
    exact hp.trans hd

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntervalResiduePartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residue_indicator_positiveCyclicNiltest {q N : ℕ} [NeZero q] [NeZero N]
    (j : ZMod q) {p : ℝ} (hp : 0 ≤ p) (hq : (q : ℝ) ≤ Real.exp p) :
    PositiveCyclicNiltest.{0} 1 N (p + 2)
      (fun x => if (x.val : ZMod q) = j then 1 else 0) := by
  classical
  refine .of_test (RationalTorus.nilmanifold 1) le_rfl (RationalTorus.residueNiltest j)
    (RationalTorus.residueNiltest_unit_interval j) (RationalTorus.residueNiltest_complexity j hp hq) ?_
  intro x
  rw [RationalTorus.residueNiltest_evalCyclic]
  split_ifs <;> rfl

theorem refine_positive_partition_by_residue {I : Type*} [Fintype I]
    {degree q N : ℕ} [NeZero q] [NeZero N] (A : I → ZMod N → ℝ) {p : ℝ}
    (hp : 0 ≤ p) (hdegree : 1 ≤ degree) (hq : (q : ℝ) ≤ Real.exp p)
    (hA : ∀ i, PositiveCyclicNiltest.{0} degree N p (A i)) (hsum : ∀ x, ∑ i, A i x = 1) :
    ∃ B : (I × ZMod q) → ZMod N → ℝ,
      (∀ j, PositiveCyclicNiltest.{0} degree N
        (productNiltestBudget (raisedNiltestBudget (p + 2))) (B j)) ∧
      (∀ x, ∑ j, B j x = 1) ∧
      (∀ j x, 0 < B j x → 0 < A j.1 x ∧ (x.val : ZMod q) = j.2) := by
  classical
  let B : (I × ZMod q) → ZMod N → ℝ := fun j x =>
    A j.1 x * if (x.val : ZMod q) = j.2 then 1 else 0
  refine ⟨B, ?_, ?_, ?_⟩
  · intro j
    exact ((hA j.1).mono le_rfl (by linarith)).mul
      ((residue_indicator_positiveCyclicNiltest j.2 hp hq).mono hdegree le_rfl) (by linarith)
  · intro x
    simpa [B, Fintype.sum_prod_type, mul_ite] using hsum x
  · intro j x hx
    by_cases h : (x.val : ZMod q) = j.2
    · exact ⟨by simpa only [B, h, ↓reduceIte, mul_one] using hx, h⟩
    · simp only [B, h, ↓reduceIte, mul_zero, lt_self_iff_false] at hx

theorem exists_controlled_residue_refinement :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type*} [Fintype I]
      {degree q N : ℕ} [NeZero q] [NeZero N] (A : I → ZMod N → ℝ) {p : ℝ},
      0 ≤ p → 1 ≤ degree → (Fintype.card I : ℝ) ≤ Real.exp p → (q : ℝ) ≤ Real.exp p →
      (∀ i, PositiveCyclicNiltest.{0} degree N p (A i)) → (∀ x, ∑ i, A i x = 1) →
      ∃ B : (I × ZMod q) → ZMod N → ℝ,
        (Fintype.card (I × ZMod q) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (∀ j, PositiveCyclicNiltest.{0} degree N ((p + C) ^ C) (B j)) ∧
        (∀ x, ∑ j, B j x = 1) ∧
        ∀ j x, 0 < B j x → 0 < A j.1 x ∧ (x.val : ZMod q) = j.2 := by
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + 2) + (X + 4) ^ 2 + 3
  let Q := (R + 2) ^ 2 + R + (R + (R ^ 2 + R + 3) ^ 2) + R ^ 2 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * X + Q)
  refine ⟨C, hC, ?_⟩
  intro I _ degree q N _ _ A p hp hdegree hcard hq hA hsum
  obtain ⟨B, hB, hBsum, hsupport⟩ := refine_positive_partition_by_residue A hp hdegree hq hA hsum
  have hcost : 2 * p + productNiltestBudget (raisedNiltestBudget (p + 2)) ≤ (p + C) ^ C := by
    simpa [X, Q, R, Polynomial.eval₂_pow, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, show p + 2 + 2 = p + 4 by ring] using hbudget p hp
  have hnonneg : 0 ≤ productNiltestBudget (raisedNiltestBudget (p + 2)) := by
    unfold productNiltestBudget productObservableLipBudget raisedNiltestBudget
    positivity
  refine ⟨B, ?_, fun j => (hB j).mono le_rfl (by linarith), hBsum, hsupport⟩
  calc
    _ = (Fintype.card I : ℝ) * q := by rw [Fintype.card_prod, ZMod.card, Nat.cast_mul]
    _ ≤ Real.exp p * Real.exp p := mul_le_mul hcard hq (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (2 * p) := by rw [← Real.exp_add, two_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_interval_residue_partition (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (N M : ℕ) [NeZero N] [NeZero M] {p ρ : ℝ},
      0 ≤ p → (M : ℝ) ≤ Real.exp p → 0 < ρ →
      1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧ (Fintype.card (Fin n × ZMod M) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A : (Fin n × ZMod M) → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} 1 N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          ∀ j x y, x ∉ cyclicWrapExceptional 0 ρ → y ∉ cyclicWrapExceptional 0 ρ →
            0 < A j x → 0 < A j y →
            |(x.val : ℝ) - y.val| ≤ N * ρ ∧ (M : ℤ) ∣ (x.val : ℤ) - y.val := by
  obtain ⟨b, _, hpart⟩ := exists_interval_circle_partition a
  obtain ⟨c, _, hrefine⟩ := exists_controlled_residue_refinement
  let B : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((B + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro N M _ _ p ρ hp hM hρ hprec
  classical
  obtain ⟨n, hn, hnb, V, hV, hsum, hdiam⟩ := hpart N hp hρ hprec
  let t := p + (p + b) ^ b
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hbt : (p + b) ^ b ≤ t := le_add_of_nonneg_left hp
  have hcost : (t + c) ^ c ≤ (p + C) ^ C := by
    simpa [B, t, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨A, hcard, hA, hAsum, hsupport⟩ := hrefine V (hp.trans hpt) le_rfl
    (by simpa only [Fintype.card_fin] using hnb.trans (Real.exp_le_exp.mpr hbt))
    (hM.trans (Real.exp_le_exp.mpr hpt)) (fun j => (hV j).mono le_rfl hbt) hsum
  refine ⟨n, hn, hcard.trans (Real.exp_le_exp.mpr hcost), A,
    fun j => (hA j).mono le_rfl hcost, hAsum, ?_⟩
  intro j x y hx hy hAx hAy
  obtain ⟨hVx, hMx⟩ := hsupport j x hAx
  obtain ⟨hVy, hMy⟩ := hsupport j y hAy
  have hnear := good_circle_observations_control_representatives 0 x y hρ hx hy
    (hdiam j.1 x y hVx hVy)
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  rw [← sub_div, abs_div, abs_of_pos hN] at hnear
  refine ⟨by simpa only [mul_comm] using (div_le_iff₀ hN).mp hnear, ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd ((x.val : ℤ) - y.val) M).mp
  push_cast
  rw [hMx, hMy, sub_self]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSharedFrozenCorrelations
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
  (φ : L →ₗ⁅ℚ⁆ M) (a r : E.RealGroup)
  (h : ∀ γ ∈ D.realLattice,
    r⁻¹ * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ γ * r ∈ E.realLattice)

theorem lipschitz_native_frozenCosetMap {A C : ℝ≥0}
    (hφ : letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
      LipschitzWith C (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
    (ha : letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
      LipschitzWith A (fun x => a * x)) :
    letI := D.metricSpace
    letI := E.metricSpace
    LipschitzWith (A * C) (frozenCosetMap D.realLattice E.realLattice
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ) a r h) := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (D.basis.baseChange ℝ).finiteDimensional_of_finite
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] M) := (E.basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  exact lipschitz_frozenCosetMap D.realLattice E.realLattice D.realLattice_closed_discrete.1
    E.realLattice_closed_discrete.1 _ a r h hφ ha

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup

noncomputable def conjugationPullback {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (φ : L →ₗ⁅ℚ⁆ M) (q : ℕ) : Subgroup D.filtration.Group :=
  ⨅ z : {z : E.filtration.Group // E.basis.equivFun z.coord ∈ denominatorGrid q},
    (E.lattice.map (MulAut.conj z.val).toMonoidHom).comap
      (NilpotentLieBCHGroup.map (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem real_conjugationPullback_property {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (φ : L →ₗ⁅ℚ⁆ M) (q : ℕ) (hq : 0 < q) (Λ : Subgroup D.filtration.Group)
    (hΛ : Λ ≤ D.conjugationPullback E φ q)
    (r : E.RealGroup) (hr : (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q) :
    ∀ γ ∈ Λ.map realificationHom,
      r⁻¹ * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ γ * r ∈ E.realLattice := by
  obtain ⟨z, hz, rfl⟩ := (realification_grid_iff
    (hnil := E.filtration.lowerCentralSeries_eq_bot) E.basis q hq r).mp hr
  intro γ hγ
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hγ
  have h := Subgroup.mem_iInf.mp (hΛ hc) ⟨z, hz⟩
  change NilpotentLieBCHGroup.map (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ c ∈
      E.lattice.map (MulAut.conj z).toMonoidHom at h
  obtain ⟨v, hv, heq⟩ := Subgroup.mem_map.mp h
  have hconj : z⁻¹ * NilpotentLieBCHGroup.map (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ c * z = v := by
    rw [← heq]
    change z⁻¹ * (z * v * z⁻¹) * z = v
    group
  rw [realificationMap_realificationHom, ← map_inv, ← map_mul, ← map_mul, hconj]
  exact Subgroup.mem_map.mpr ⟨v, hv, rfl⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem realificationMap_id_apply {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (x : D.RealGroup) :
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L) x = x := by
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom (LieHom.id : L →ₗ⁅ℚ⁆ L) x.coord = x.coord
  generalize x.coord = y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rfl
  | add y z hy hz => simp only [map_add, hy, hz]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformFrozenDescent
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem quotientFinBasis_repr_mk {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι]
    (b : Basis ι ℚ L) (I : LieIdeal ℚ L) (S : Set ι) [DecidablePred (· ∈ S)]
    (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))
    (x : L) (k : Fin (Fintype.card {i // i ∉ S})) :
    (quotientFinBasis b I S hspan).repr (lieQuotientMap I x) k =
      b.repr x ((Fintype.equivFin {i // i ∉ S}).symm k) := by
  rw [quotientFinBasis, Basis.repr_reindex_apply]
  exact supportedQuotientBasis_repr_mk b I.toSubmodule S hspan x _

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ComparisonEquivalenceBudget
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_bounded_normalization_left_lipschitz (s a : ℕ) :
    ∃ b : ℕ, 2 ≤ b ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p →
      ∃ A : ℝ≥0, 0 < A ∧ (A : ℝ) ≤ Real.exp (normalizedSquareLeftBudget a b p) ∧
        ∀ ε : D.RealGroup,
          (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 1 + a) ^ a)) →
          letI := D.metricSpace
          LipschitzWith A (fun x : D.Space => ε • x) := by
  obtain ⟨b, hb, hleft⟩ := exists_uniform_quotient_left_lipschitz_exp_bound s a
  refine ⟨b, hb, ?_⟩
  intro L _ _ d _ _ _ _ D p hp hD
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  let q := p + a + 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hH : (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr (by dsimp [q]; linarith))
  obtain ⟨A, hA, hAp, hLip⟩ := hleft (D.basis.baseChange ℝ)
    (lieStructureConstants D.basis) ⌈Real.exp p⌉₊ q
    D.filtration.realification.lowerCentralSeries_eq_bot
    (fun i j k => (realLieBasis_structure D.basis i j k).symm) hq
    (by simpa only [Fintype.card_fin] using hD.1.trans hpq) hH
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
  refine ⟨A, hA, hAp, ?_⟩
  intro ε hε
  apply hLip D.realLattice (D.realLattice_closed_discrete).1 ε
  intro i
  apply (hε i).trans (Real.exp_le_exp.mpr _)
  apply pow_le_pow_left₀ (by positivity)
  dsimp [q]
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GradedUnitEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

section Projection

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem gradedPieceProjection_basis (j : ℕ) (i : ι) :
    F.gradedPieceProjection e ω hF j (e i) =
      if ω i = j then F.associatedGradedBasis e ω hF i else 0 := by
  classical
  apply (F.associatedGradedBasis e ω hF).repr.injective
  ext k
  rw [F.gradedPieceProjection_coordinate]
  by_cases hi : i = k <;> by_cases hj : ω i = j <;>
    simp_all only [Basis.repr_self, Finsupp.single_apply, ite_true, ite_false,
      map_zero, Finsupp.zero_apply, ite_self]

end Projection

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCorrelatedFactorFamily
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

theorem polynomialOrbit_coefficient_grid_value (q : ℕ)
    (g : F.realification.PolynomialOrbit w) (hg : CoefficientGrid (b.baseChange ℝ) q g.log)
    (x : σ → ℤ) :
    (b.baseChange ℝ).equivFun (F.realification.polynomialOrbitEval w x g).coord ∈ realDenominatorGrid q := by
  have h := F.polynomialRationalGrid_value b w q (F.realification.polynomialOrbitCoordinates w g)
    ((F.polynomialRationalGrid_iff_formal b w q _).mpr hg) x
  simpa only [F.polynomialOrbitCoordinates_realValue] using h

omit [Fintype ι] in
theorem polynomialOrbit_coefficient_bound_value
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (hw : ∀ i, 0 < w i) (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : F.realification.PolynomialOrbit w) (hg : CoefficientBound (b.baseChange ℝ) T M g.log)
    (x : σ → ℤ) (hx : ∀ i, |(x i : ℝ)| ≤ T i) (i : ι) :
    |(b.baseChange ℝ).repr (F.realification.polynomialOrbitEval w x g).coord i| ≤
      ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * M := by
  have h := F.polynomialSlowBound_value b w hw T hT hM (F.realification.polynomialOrbitCoordinates w g)
    ((F.polynomialSlowBound_iff_formal b w T M _).mpr hg) (fun j => (x j : ℝ)) hx i
  simpa only [F.polynomialOrbitCoordinates_realValue] using h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial
open scoped TensorProduct

theorem exists_bounded_frozen_constants (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d N : ℕ} [NeZero N] (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ ε γ : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
          CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
            (Real.exp ((p + 2) ^ a)) ε.log →
          CoefficientGrid (D.basis.baseChange ℝ) q γ.log → ∀ y : ZMod N,
          (∀ i, |(D.basis.baseChange ℝ).repr
            (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
              (fun _ => (y.val : ℤ)) ε).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
          ∃ r : D.RealGroup,
            (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m ∧
            ∃ δ ∈ D.realLattice,
              D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                (fun _ => (y.val : ℤ)) γ = r * δ := by
  obtain ⟨b, _, hrep⟩ := exists_native_rational_representatives s
  let k := (s + 1) * 2 ^ s
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ a + Polynomial.C k
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Polynomial.X + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d N _ D p hp hD q hq hqp
  have htotal : (p + 2) ^ a + (k : ℝ) + (p + b) ^ b ≤ (p + C) ^ C := by
    simpa [Q, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (p + b) ^ b := by positivity
  have hsmall : (p + 2) ^ a + (k : ℝ) ≤ (p + C) ^ C := by linarith
  have hrepC : (p + b) ^ b ≤ (p + C) ^ C := by
    have hpowa : 0 ≤ (p + 2) ^ a := by positivity
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  obtain ⟨m, hm, hmp, hsolve⟩ := hrep D p hp hD q hq hqp
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hrepC), ?_⟩
  intro ε γ hε hγ y
  refine ⟨?_, ?_⟩
  · intro i
    have hv := D.filtration.polynomialOrbit_coefficient_bound_value D.basis (fun _ : Unit => 1)
      (fun _ => Nat.zero_lt_one) (fun _ : Unit => (N : ℝ))
      (fun _ => Nat.cast_pos.mpr (NeZero.pos N)) (Real.exp_pos _).le ε hε
      (fun _ => (y.val : ℤ)) (fun _ => by
        simpa only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ y.val from Nat.cast_nonneg _)]
          using (Nat.cast_le.mpr y.val_lt.le : (y.val : ℝ) ≤ N)) i
    have hke : (k : ℝ) ≤ Real.exp k := by linarith [Real.add_one_le_exp (k : ℝ)]
    have hk : ((s : ℝ) + 1) * ((Fintype.card Unit : ℝ) + 1) ^ s = (k : ℝ) := by
      simp only [k, Fintype.card_unit, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
      norm_num
    rw [hk] at hv
    exact hv.trans ((mul_le_mul_of_nonneg_right hke (Real.exp_pos _).le).trans
      (by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)))
  · obtain ⟨⟨r, hr, hrgrid, δ, hδ, heq⟩, _⟩ := hsolve
      (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (y.val : ℤ)) γ)
      (D.filtration.polynomialOrbit_coefficient_grid_value D.basis (fun _ : Unit => 1) q γ hγ _)
    exact ⟨r, fun i => (hr i).trans (Real.exp_le_exp.mpr hrepC), hrgrid, δ, hδ, heq⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDilationDescent
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem real_top_frequency_mul {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (η : L →ₗ[ℚ] ℚ)
    (z w : F.realification.Group) (hz : z ∈ F.realification.subgroup s) :
    ((realifyFunctional η (z * w).coord : ℝ) : CircleFourier.Circle) =
      (realifyFunctional η z.coord : CircleFourier.Circle) +
        (realifyFunctional η w.coord : CircleFourier.Circle) := by
  change ((realifyFunctional η (lieBCH s z.coord w.coord) : ℝ) : CircleFourier.Circle) = _
  rw [lieBCH_eq_add_of_lie_eq_zero F.realification.lowerCentralSeries_eq_bot
    (F.realification.top_layer_central hz w.coord), map_add, AddCircle.coe_add]

theorem MultidegreeLieFiltration.realAdditiveTriple_frequency_phase
    {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
    (i : σ) (hi : bound i ≤ 1) (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (htop : F.realification.weightedLayer c s = ⊥) (η : L →ₗ[ℚ] ℚ)
    (g : (F.additiveTripleFiltration i hi c hc).realification.Group)
    (hg : g ∈ (F.additiveTripleFiltration i hi c hc).realification.subgroup s) :
    (realifyFunctional η (F.realAdditiveTripleProjection i hi c hc 0 g).coord : CircleFourier.Circle) =
      (realifyFunctional η (F.realAdditiveTripleProjection i hi c hc 1 g).coord : CircleFourier.Circle) +
        (realifyFunctional η (F.realAdditiveTripleProjection i hi c hc 2 g).coord : CircleFourier.Circle) := by
  apply F.realAdditiveTriple_top_phase i hi c hc htop
    (fun z => (realifyFunctional η z.coord : CircleFourier.Circle)) ?_ g hg
  intro z w hz _
  exact real_top_frequency_mul F.ordinary η z w hz

theorem MultidegreeLieFiltration.realAdditiveTriple_omitted_frequency_phase
    {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
    (i : σ) (hi : bound i = 1) (hs : ∑ j, bound j = s) (η : L →ₗ[ℚ] ℚ)
    (g : (F.additiveTripleFiltration i hi.le (omittedCoordinateWeight i)
      (omittedCoordinateWeight_le_one i)).realification.Group)
    (hg : g ∈ (F.additiveTripleFiltration i hi.le (omittedCoordinateWeight i)
      (omittedCoordinateWeight_le_one i)).realification.subgroup s) :
    (realifyFunctional η (F.realAdditiveTripleProjection i hi.le _
      (omittedCoordinateWeight_le_one i) 0 g).coord : CircleFourier.Circle) =
      (realifyFunctional η (F.realAdditiveTripleProjection i hi.le _
        (omittedCoordinateWeight_le_one i) 1 g).coord : CircleFourier.Circle) +
      (realifyFunctional η (F.realAdditiveTripleProjection i hi.le _
        (omittedCoordinateWeight_le_one i) 2 g).coord : CircleFourier.Circle) :=
  F.realAdditiveTriple_frequency_phase i hi.le _ (omittedCoordinateWeight_le_one i)
    (F.realification.omitted_weighted_top i hi hs) η g hg

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeFrozenMultidegreeNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (S : Finset σ)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S))]

theorem exists_frozen_niltest {n : ℕ}
    (E : RationalFilteredNilmanifold (M.filtration.weightedSubalgebra (retainedCoordinateWeight S))
      (multidegreeWeight (retainedCoordinateWeight S) bound) n)
    (hEF : E.filtration = M.filtration.weightedFiltration (retainedCoordinateWeight S))
    (hEL : E.lattice = D.lattice.comap
      (mapOfSteps (M.filtration.weightedSubalgebra (retainedCoordinateWeight S)).incl))
    (b : σ → ℤ) (p : M.filtration.realification.PolynomialOrbit)
    (u : D.Space → ℂ) (ℓ B : ℝ≥0)
    (hu : letI := D.metricSpace; LipschitzWith ℓ u) (hub : ∀ x, ‖u x‖ ≤ B)
    (a γ : D.RealGroup) (hγ : γ ∈ D.realLattice)
    (hfactor : M.filtration.realification.polynomialOrbitEval (freezeCoordinates S b 0) p = a * γ)
    (A : ℝ≥0) (hA : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => a • x))
    (H : ℕ) (he : ∀ i k, RationalHeightLE (D.basis.repr (E.basis i : L) k) H) :
    ∃ T : E.Niltest (fun _ : S => 1), T.normBound = B ∧
      T.lipBound = ℓ * (A * coordinateLipschitzBound d n H) ∧
      E.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
      ∀ x, T.eval x = u (QuotientGroup.mk
        (M.filtration.realification.polynomialOrbitEval (freezeCoordinates S b x) p)) := by
  let c := retainedCoordinateWeight S
  let K := M.filtration.weightedSubalgebra c
  let F := M.filtration.weightedFiltration c
  have hΓ : E.lattice ≤ D.lattice.comap (mapOfSteps K.incl) := by rw [hEL]
  let φ : E.RealGroup →* D.RealGroup := realificationMap
    (hnil := E.filtration.lowerCentralSeries_eq_bot) (hM := D.filtration.lowerCentralSeries_eq_bot) K.incl
  have hφ : E.realLattice ≤ D.realLattice.comap φ :=
    realificationMap_subgroup K.incl E.lattice D.lattice hΓ
  let π : E.Space → D.Space := cosetMap E.realLattice D.realLattice φ hφ
  have hπ : letI := E.metricSpace; letI := D.metricSpace
      LipschitzWith (coordinateLipschitzBound d n H) π := by
    let : MetricSpace (E.RealGroup ⧸ E.lattice.map realificationHom) :=
      realificationQuotientMetricSpace E.basis E.lattice E.grid E.grid_pos E.outer_grid
    let : MetricSpace (D.RealGroup ⧸ D.lattice.map realificationHom) :=
      realificationQuotientMetricSpace D.basis D.lattice D.grid D.grid_pos D.outer_grid
    exact (lipschitz_realificationMap_quotient E.basis D.basis K.incl E.lattice D.lattice hΓ
      E.grid D.grid E.grid_pos D.grid_pos E.outer_grid D.outer_grid H
      (fun k i => he i k)).weaken (by simp only [Fintype.card_fin]; exact le_rfl)
  obtain ⟨q, hq, hval⟩ := M.filtration.exists_real_normalized_frozen_orbit S b p a γ hfactor
  have hF : F.realification = E.filtration.realification := by rw [hEF]
  let qE := F.realification.orbitEquivOfEq hF (fun _ : S => 1) q
  have hqE (x : S → ℤ) : E.filtration.realification.polynomialOrbitEval _ x qE =
      F.realification.polynomialOrbitEval _ x q :=
    F.realification.orbitEquivOfEq_eval hF _ q x
  have hvalE (x : S → ℤ) : φ (E.filtration.realification.polynomialOrbitEval _ x qE) =
      a⁻¹ * M.filtration.realification.polynomialOrbitEval (freezeCoordinates S b x) p * γ⁻¹ := by
    rw [hqE]
    exact hval x
  let T : E.Niltest (fun _ : S => 1) :=
    { orbit := qE
      observable := fun x => u (a • π x)
      normBound := B
      lipBound := ℓ * (A * coordinateLipschitzBound d n H)
      norm_le := fun _ => hub _
      lipschitz := by
        let := E.metricSpace
        let := D.metricSpace
        exact hu.comp (hA.comp hπ) }
  refine ⟨T, rfl, rfl, (hqE 0).trans hq, ?_⟩
  intro x
  change u (a • π (QuotientGroup.mk
    (E.filtration.realification.polynomialOrbitEval _ x qE))) = _
  rw [show π (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval _ x qE)) =
      QuotientGroup.mk (φ (E.filtration.realification.polynomialOrbitEval _ x qE)) from rfl, hvalE]
  simp only [MulAction.Quotient.smul_mk, smul_eq_mul, ← mul_assoc, mul_inv_cancel, one_mul]
  exact congrArg u (QuotientGroup.mk_mul_of_mem _ (D.realLattice.inv_mem hγ))

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeTwoVariableSplitFreezing
namespace OAI

section

namespace Erdos3.NativeTwoVariableSplit

open scoped TensorProduct

attribute [local instance] NativeTwoVariableSplit.lie NativeTwoVariableSplit.algebra
  NativeTwoVariableSplit.topology NativeTwoVariableSplit.topologicalAdd
  NativeTwoVariableSplit.continuousSMul NativeTwoVariableSplit.hausdorff

theorem first_eval_eq {s d : ℕ} {p epsilon : ℝ} {f : (Fin 2 → ℤ) → ℂ}
    (R : NativeTwoVariableSplit s d p epsilon f) (j : Fin R.count)
    (x y : Fin 2 → ℤ) (hxy : x 1 = y 1) :
    (R.test false j).eval x = (R.test false j).eval y := by
  unfold RationalFilteredNilmanifold.Niltest.eval
  rw [R.test_orbit false j, (R.multi false).orbitToOrdinary_eval,
    (R.multi false).orbitToOrdinary_eval]
  apply congrArg (R.test false j).observable
  apply congrArg QuotientGroup.mk
  apply (R.multi false).filtration.realification.polynomialOrbitEval_eq_of_zero_coordinate
    0 (show totalDegreeSplitBound s false 0 = 0 from rfl) (R.orbit false) x y
  intro i hi
  fin_cases i
  · exact (hi rfl).elim
  · exact hxy

end Erdos3.NativeTwoVariableSplit

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerHalving
namespace OAI

section

namespace Erdos3.NativeIntegerExpansion

noncomputable def constOne {σ : Type*} (w : σ → ℕ) (s : ℕ) {p : ℝ} (hp : 2 ≤ p) :
    NativeIntegerExpansion w s p (fun _ => 1) :=
  ofTest (RationalFilteredNilmanifold.Niltest.const (RationalTorus.trivialNilmanifold s) w 1)
    (RationalTorus.trivialNilmanifold_const_one_complexity s w hp) (fun _ => rfl)

end Erdos3.NativeIntegerExpansion

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeWeightPairRemoval
namespace OAI

section

namespace Erdos3.NativeIntegerExpansion

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem select_sample_product_correlation {σ X : Type*} {w : σ → ℕ} {s : ℕ} {p q : ℝ}
    {eta : (σ → ℤ) → ℂ} (E : NativeIntegerExpansion w s p eta)
    (S : Finset X) (sample : X → σ → ℤ) (f : X → ℂ)
    (hcorr : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u * eta (sample u)‖) :
    ∃ i : Fin E.count, Real.exp (-(q + p)) ≤
      ‖𝔼 u ∈ S, f u * (E.test i).eval (sample u)‖ := by
  have hpoint (u : X) : f u * eta (sample u) =
      ∑ i, E.coefficient i * (f u * (E.test i).eval (sample u)) := by
    rw [E.eval, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hmean : (𝔼 u ∈ S, f u * eta (sample u)) =
      ∑ i, E.coefficient i * (𝔼 u ∈ S, f u * (E.test i).eval (sample u)) := by
    calc
      _ = 𝔼 u ∈ S, ∑ i, E.coefficient i * (f u * (E.test i).eval (sample u)) :=
        Finset.expect_congr rfl (fun u _ => hpoint u)
      _ = _ := by simp_rw [Finset.expect_sum_comm, ← Finset.mul_expect]
  obtain ⟨i, hi⟩ := exists_large_weighted_term E.coefficient
    (fun i => 𝔼 u ∈ S, f u * (E.test i).eval (sample u))
    (Real.exp_pos (-q)) (Real.exp_pos p) E.cost (by rwa [← hmean])
  refine ⟨i, ?_⟩
  have heq : Real.exp (-q) / Real.exp p = Real.exp (-(q + p)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rwa [heq] at hi

end Erdos3.NativeIntegerExpansion

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedAdaptedSymbolFactorizationBasis
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix NNReal

def ControlledSymbolBasisChangeSpec (s C : ℕ) : Prop :=
  ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ L) (ν : κ → ℕ)
    (hC : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hκ : (Fintype.card κ : ℝ) ≤ p)
    (_hσ : (Fintype.card σ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hb : ∀ i j, RationalHeightLE (c.repr (b i) j) H)
    (T : σ → ℝ) (_hT : ∀ i, 0 < T i) (η : L →ₗ[ℚ] ℚ)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)),
    F.ControlledSymbolFactorization b ω hF η T X p →
      F.ControlledSymbolFactorization c ν hC η T X ((p + C) ^ C)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankQuotientOrbit
namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}

theorem NilpotentLieFiltration.exists_weights_of_tails {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis (Fin d) ℚ L)
    (htail : ∀ i, ∃ c, F.layer i = basisTail b c) :
    ∃ w : Fin d → ℕ, ∀ i, F.layer i = Submodule.span ℚ (b '' {j | i ≤ w j}) := by
  let S : Fin (s + 1) → Set (Fin d) := fun i => {j | b j ∈ F.layer (i.val + 1)}
  have hS : Antitone S := fun _ _ h _ hx => F.antitone (Nat.add_le_add_right h 1) hx
  let w := nestedSupportWeight S
  refine ⟨w, F.layer_eq_span_of_weighted_flag b w (fun j => nestedSupportWeight_le S j) ?_⟩
  intro i
  obtain ⟨c, hc⟩ := htail (i.val + 1)
  rw [tail_span_basis_members b _ c hc]
  apply congrArg (Submodule.span ℚ)
  apply congrArg (fun A : Set (Fin d) => b '' A)
  ext j
  exact mem_nestedSupport_iff S hS i j

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration

theorem exists_coordinate_quotient_layer_basis
    {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι]
    (b : Basis ι ℚ L) (I : LieIdeal ℚ L) (S : Set ι) [DecidablePred (· ∈ S)]
    (hI : I.toSubmodule = Submodule.span ℚ (b '' S))
    (P : Submodule ℚ L) (T : Set ι) (hP : P = Submodule.span ℚ (b '' T)) :
    ∃ a : Basis (Fin (finrank ℚ (P.map (lieQuotientMap I).toLinearMap))) ℚ
        (P.map (lieQuotientMap I).toLinearMap),
      ∀ i j, rationalLogHeight ((quotientFinBasis b I S hI).repr (a i : L ⧸ I) j) ≤ 0 := by
  classical
  let q := supportedQuotientBasis b I.toSubmodule S hI
  have hspan : P.map (lieQuotientMap I).toLinearMap =
      Submodule.span ℚ (q '' {i : {i // i ∉ S} | i.val ∈ T}) := by
    rw [hP]
    exact supportedQuotientBasis_map_span b I.toSubmodule S hI T
  let a := supportedSubmoduleBasis q (P.map (lieQuotientMap I).toLinearMap)
    {i : {i // i ∉ S} | i.val ∈ T} hspan
  let e := Fintype.equivFinOfCardEq (finrank_eq_card_basis a).symm
  refine ⟨a.reindex e, ?_⟩
  intro i j
  rw [Basis.reindex_apply, supportedSubmoduleBasis_coe,
    quotientFinBasis, Basis.repr_reindex_apply]
  change rationalLogHeight (q.repr (q (e.symm i).val)
    ((Fintype.equivFin {i // i ∉ S}).symm j)) ≤ 0
  rw [Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> norm_num [rationalLogHeight]

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

variable [Fintype κ]

theorem quotientFinBasis_projection_height (b : Basis κ ℚ L) (I : LieIdeal ℚ L)
    (S : Set κ) [DecidablePred (· ∈ S)]
    (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))
    (i : κ) (j : Fin (Fintype.card {i // i ∉ S})) :
    RationalHeightLE ((quotientFinBasis b I S hspan).repr (lieQuotientMap I (b i)) j) 1 := by
  rw [quotientFinBasis, Basis.repr_reindex_apply]
  exact supportedQuotientBasis_projection_height b I S hspan i _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
  {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure r)

theorem rankFlag_span_height {H : ℕ}
    (hR : ∀ i j a k, RationalHeightLE (D.basis.repr (R.basis i j a : L) k) H)
    (n : Fin ((s + 1) * (s + 1) + 1)) :
    Submodule.span ℚ ({x : L | ∀ k, RationalHeightLE (D.basis.repr x k) H} ∩
      (R.filtration.rankFlag n.val : Set L)) = R.filtration.rankFlag n.val := by
  by_cases hn : n.val < (s + 1) * (s + 1)
  · obtain ⟨hi, hj⟩ := DegreeRankLieFiltration.rankFlag_decode_lt hn
    let i : Fin (s + 1) := ⟨n.val / (s + 1), by omega⟩
    let j : Fin (s + 1) := ⟨n.val % (s + 1), by omega⟩
    exact span_inter_eq_of_spanning_family _ (R.basis i j) (R.basis i j).span_eq _
      (fun a => hR i j a)
  · have heq : n.val = (s + 1) * (s + 1) := by omega
    rw [heq, R.filtration.rankFlag_terminal]
    exact le_antisymm (Submodule.span_le.mpr (fun _ hx => hx.2)) bot_le

theorem exists_bounded_rank_adapted_basis {H : ℕ}
    (hR : ∀ i j a k, RationalHeightLE (D.basis.repr (R.basis i j a : L) k) H) :
    ∃ b : Basis (Fin (finrank ℚ L)) ℚ L,
      IsCentralLieBasis b ∧ (∀ a k, RationalHeightLE (D.basis.repr (b a) k) H) ∧
      ∀ i j, ∃ c ≤ finrank ℚ L, R.filtration.layer i j = basisTail b c := by
  let := D.basis.finiteDimensional_of_finite
  let N := (s + 1) * (s + 1)
  let S : Set L := {x | ∀ k, RationalHeightLE (D.basis.repr x k) H}
  let P : Fin (N + 1) → Submodule ℚ L := fun n => R.filtration.rankFlag n.val
  have hP : Antitone P := fun _ _ h => R.filtration.rankFlag_antitone h
  have hspan : ∀ n, Submodule.span ℚ (S ∩ (P n : Set L)) = P n := R.rankFlag_span_height hR
  have hS : Submodule.span ℚ S = ⊤ := by
    apply top_unique
    calc
      ⊤ = P 0 := R.filtration.rankFlag_zero.symm
      _ = Submodule.span ℚ (S ∩ (P 0 : Set L)) := (hspan 0).symm
      _ ≤ Submodule.span ℚ S := Submodule.span_mono Set.inter_subset_left
  obtain ⟨b, w, hw, _, hb, hflag⟩ := exists_sorted_flag_basis_from_spanning_set P hP S hS hspan
  have hcentral : IsCentralLieBasis b := centralLieBasis_of_finite_flag R.filtration.rankFlag b w
    R.filtration.rankFlag_zero R.filtration.rankFlag_terminal
    (fun _ {_ _} hy => R.filtration.rankFlag_lie_mem hy) hw hflag
  refine ⟨b, hcentral, hb, ?_⟩
  intro i j
  obtain ⟨k, hk⟩ := R.filtration.layer_eq_rankFlag i j
  exact ⟨weightCut w k.val, weightCut_le w k.val,
    hk.trans ((hflag k).trans (span_weight_gt_eq_basisTail b w hw k.val))⟩

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure (r + 1))

theorem terminal_le_topRankIdeal :
    D.filtration.layer (s + 1) ≤ (R.filtration.layerIdeal s (r + 1)).toSubmodule := by
  rw [D.filtration.terminal]
  exact bot_le

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d n : ℕ}
  {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure (r + 1))
  (Q : RationalFilteredNilmanifold (L ⧸ R.filtration.layerIdeal s (r + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientLie
    (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal) {w : σ → ℕ}

noncomputable def rankQuotientOrbit (g : D.filtration.realification.PolynomialOrbit w) :
    Q.filtration.realification.PolynomialOrbit w :=
  let q := D.filtration.realQuotientPolynomialOrbit
    (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal g
  NilpotentLieFiltration.polynomialOrbitOfLog q.log (by rw [hQ]; exact q.adapted)

theorem rankQuotientOrbit_eval (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    Q.filtration.realification.polynomialOrbitEval w x (R.rankQuotientOrbit Q hQ g) =
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot)
        (lieQuotientMap (R.filtration.layerIdeal s (r + 1)))
        (D.filtration.realification.polynomialOrbitEval w x g) :=
  D.filtration.realQuotientPolynomialOrbit_eval
    (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal g x

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RefiltrationLayerBasis
namespace OAI

section

namespace Erdos3

open Module

namespace NilpotentLieFiltration

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

theorem exists_refiltration_layer_basis_of_quotient
    {κ : Type*} [Fintype κ] (W : LieSubalgebra ℚ F.AssociatedGraded)
    (f : Basis κ ℚ (F.AssociatedGraded ⧸ W.toSubmodule)) {H : ℕ} (hH : 1 ≤ H)
    (hf : ∀ i k, RationalHeightLE
      (f.repr (W.toSubmodule.mkQ (F.associatedGradedBasis b w hlayers i)) k) H) (j : ℕ) :
    ∃ r : ℕ, r ≤ Fintype.card κ ∧
      ∃ e : Basis (Fin (finrank ℚ (F.gradedRefiltrationLayer W j))) ℚ (F.gradedRefiltrationLayer W j),
        ∀ i k, RationalHeightLE (b.repr (e i : L) k)
          ((Fintype.card ι + 1) * rationalKernelHeight r H ^ Fintype.card ι) := by
  classical
  let v : ι → L := fun i => if j ≤ w i then b i else 0
  let P := W.toSubmodule.mkQ.comp (F.gradedPieceProjection b w hlayers j)
  have hv : ∀ i k, RationalHeightLE (b.repr (v i) k) 1 := by
    intro i k
    dsimp [v]
    split_ifs
    · exact basis_repr_height_one b i k
    · simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero (by decide : 1 ≤ 1)
  have hPv : ∀ i k, RationalHeightLE (f.repr (P (v i)) k) H := by
    intro i k
    dsimp only [P, v, LinearMap.comp_apply]
    split_ifs
    · rw [F.gradedPieceProjection_basis]
      split_ifs
      · exact hf i k
      · simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
    · simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
  have hspan : Submodule.span ℚ (Set.range v) = F.layer j := by
    rw [hlayers j]
    exact span_selected_basis b {i | j ≤ w i}
  have hker : F.layer j ⊓ LinearMap.ker P = F.gradedRefiltrationLayer W j := by
    rw [F.gradedRefiltrationLayer_eq_inf_comap b w hlayers W j]
    dsimp only [P]
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  obtain ⟨r, hr, z, hz, hheight⟩ := exists_bounded_span_kernel_generators b f P v hH hv hPv
  rw [hspan, hker] at hz
  have hh : ∀ i k, RationalHeightLE (b.repr (z i) k)
      ((Fintype.card ι + 1) * rationalKernelHeight r H ^ Fintype.card ι) := by
    simpa only [mul_one] using hheight
  obtain ⟨e, he⟩ := exists_bounded_submodule_basis_from_spanning b _ z hz hh
  exact ⟨r, hr, e, he⟩

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeCoefficientKernel
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realifyFunctional_lieTreeEval_rational (η : L →ₗ[ℚ] ℚ) (v : I → L) (a : FreeMagma I) :
    realifyFunctional η (lieTreeEval (fun i => rationalLieInclusion (v i)) a) =
      (η (lieTreeEval v a) : ℝ) := by
  rw [lieTreeEval_hom rationalLieInclusion v a]
  simp only [rationalLieInclusion_apply, realifyFunctional_tmul, one_mul]

theorem rational_lieTree_kernel_of_real (A : I → Submodule ℚ L)
    (η : L →ₗ[ℚ] ℚ) (a : FreeMagma I)
    (hker : ∀ z : I → ℝ ⊗[ℚ] L, (∀ i, z i ∈ (A i).baseChange ℝ) →
      realifyFunctional η (lieTreeEval z a) = 0)
    (v : I → L) (hv : ∀ i, v i ∈ A i) : η (lieTreeEval v a) = 0 := by
  have h := hker (fun i => rationalLieInclusion (v i))
    (fun i => Submodule.tmul_mem_baseChange_of_mem (1 : ℝ) (hv i))
  rw [realifyFunctional_lieTreeEval_rational] at h
  exact_mod_cast h

end Erdos3

end

end OAI
end


