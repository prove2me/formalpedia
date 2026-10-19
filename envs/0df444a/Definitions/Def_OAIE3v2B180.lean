-- Prove2me | Definitions.Def_OAIE3v2B180
-- name    : OAIE3v2B180
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:30:34.426393+00:00
-- url     : https://prove2.me/theorems/3574b2e8-caff-4994-910c-abcd758773a7
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 183 of 311
-- statement:
--   Definitions bundle 183 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B161`, `OAIE3v2B162`, `OAIE3v2B163`, `OAIE3v2B164` of this split.
--
--   Modules: `Estimates/AllocatedFixedScaleJointMarginal.lean`, `Estimates/AllocatedProfileDimensions.lean`, `Estimates/AllocatedSourceNormalization.lean`, `Estimates/AntisymmetricPartitionApproximation.lean`, `Estimates/CanonicalEmptyLayerGeometry.lean`, `Estimates/CommonRefilteredFactorization.lean`, `Estimates/DilationCost.lean`, `Estimates/MarkedShiftGeneratorBounds.lean`, `Estimates/MultidegreeIntegralModel.lean`, `Estimates/NativeDilationObservable.lean`, `Estimates/NativeDilationOrbit.lean`, `Estimates/NativeIntervalWeightPairs.lean`, `Estimates/NativeTwoVariableSplitFreezing.lean`, `Estimates/NativeWeightPairRemoval.lean`, `Estimates/NormalizedComparisonOrbit.lean`, `Estimates/PhysicalSingleSiteCommonCover.lean`, `Estimates/QuadraticPairCorrelator.lean`, `Fourier/ControlledReplicatedFrequency.lean`, `Fourier/DilationFrequencyPhase.lean`, `Geometry/AllocatedFullSiteSupport.lean`, `Geometry/MixedCoordinateTransfer.lean`, `Geometry/NativeCoordinateSplitFreezing.lean`, `Lattices/CommonAffineOrbitEvaluation.lean`, `Lattices/ForecastInactiveAffineIntervalFixedResidueSite.lean`, `Linear/NativeRankPairs.lean`, `Linear/NativeRankRelationExistence.lean`, `Linear/RankIntervalFactorization.lean`, `Nilpotent/NativeRankZeroNiltest.lean`, `Polynomial/BufferedSampledCurrentGradePhase.lean`, `Polynomial/MarkedPolynomialGenerators.lean`, `Polynomial/NativeDegreeRankFamily.lean`, `Sampling/AllocatedSlicedGridGeometryBudget.lean`, `Sampling/ForecastInactiveSlicedCappedContinuousSource.lean`, `Sampling/ForecastNativePullbackBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B162
import Definitions.Def_OAIE3v2B163
import Definitions.Def_OAIE3v2B164

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ControlledReplicatedFrequency
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

variable {κ : SquarefreeIndex (ReplicatedIndex bound) → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a))

theorem replicatedFrequency_basis_ne (η : L →ₗ[ℚ] ℚ) (a : SquarefreeIndex (ReplicatedIndex bound))
    (ha : a ≠ SquarefreeIndex.full (ReplicatedIndex bound)) (j : κ a) :
    F.replicatedFrequency η (F.squarefreeBasis (fun j : ReplicatedIndex bound => j.1) b ⟨a, j⟩) = 0 := by
  rw [F.replicatedFrequency_apply, F.squarefreeBasis_coefficient_ne _ b a _ ha, map_zero]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realComparisonTop_frequency (hstep : s = ∑ i, bound i) (η : L →ₗ[ℚ] ℚ)
    {z : ℝ ⊗[ℚ] F.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1)}
    (hz : z ∈ (F.comparisonFiltration (fun j : ReplicatedIndex bound => j.1)).realification.layer s) :
    (multidegreeFactorial bound : ℝ) * realifyFunctional η
        (realificationLieHom (F.comparisonFirst (fun j : ReplicatedIndex bound => j.1)) z) =
      realifyFunctional (F.replicatedFrequency η)
        (realificationLieHom (F.comparisonSecond (fun j : ReplicatedIndex bound => j.1)) z) := by
  change z ∈ ((F.comparisonFiltration (fun j : ReplicatedIndex bound => j.1)).layer s).baseChange ℝ at hz
  obtain ⟨y, rfl⟩ := hz
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    simp only [LinearMap.baseChange_tmul, realificationLieHom_tmul, realifyFunctional_tmul]
    change (multidegreeFactorial bound : ℝ) *
      (r * (η (F.comparisonFirst (fun j : ReplicatedIndex bound => j.1) y.val) : ℝ)) =
      r * (F.replicatedFrequency η
        (F.comparisonSecond (fun j : ReplicatedIndex bound => j.1) y.val) : ℝ)
    have h := F.comparisonTop_frequency hstep η y.property
    have hr : (multidegreeFactorial bound : ℝ) *
        (η (F.comparisonFirst (fun j : ReplicatedIndex bound => j.1) y.val) : ℝ) =
        (F.replicatedFrequency η
          (F.comparisonSecond (fun j : ReplicatedIndex bound => j.1) y.val) : ℝ) := by
      exact_mod_cast h
    rw [← hr]
    ring
  | add y w hy hw => simp only [map_add, mul_add, hy, hw]

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDilationObservable
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem realDilationPair_top_group_relation (q : ℤ)
    (g : (F.dilationPairFiltration (q : ℚ)).realification.Group)
    (hg : g ∈ (F.dilationPairFiltration (q : ℚ)).realification.subgroup s) :
    F.realDilationPairProjection (q : ℚ) 0 g =
      (F.realDilationPairProjection (q : ℚ) 1 g) ^ (q ^ s) := by
  let h : (F.realification.dilationPairFiltration (q : ℚ)).Group :=
    ⟨F.realifiedDilationPairEquiv (q : ℚ) g.coord⟩
  have hh : h ∈ (F.realification.dilationPairFiltration (q : ℚ)).subgroup s :=
    (F.realifiedDilationPairEquiv_mem_layer (q : ℚ) s g.coord).mp hg
  have he (j : Fin 2) : F.realDilationPairProjection (q : ℚ) j g =
      (NilpotentLieBCHGroup.map (F.realification.dilationPairProjection (q : ℚ) j) h :
        F.realification.Group) := by
    apply NilpotentLieBCHGroup.ext
    exact F.realDilationPairProjection_coord (q : ℚ) j g
  rw [he 0, he 1]
  exact F.realification.dilationPair_top_group_relation q h hh

end NilpotentLieFiltration

namespace MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realDilationPairProjection_mem (q : ℚ) (j : Fin 2) (a : σ → ℕ)
    {g : (F.dilationPairMultidegree q).realification.Group}
    (hg : g ∈ (F.dilationPairMultidegree q).realification.subgroup a) :
    F.ordinary.realDilationPairProjection q j g ∈ F.realification.subgroup a := by
  have hm := (F.realifiedDilationPairEquiv_mem_multidegree q a g.coord).mp hg
  change (F.ordinary.realDilationPairProjection q j g).coord ∈ F.realification.layer a
  rw [F.ordinary.realDilationPairProjection_coord]
  fin_cases j
  · exact hm.1
  · exact hm.2.1

theorem realDilationPair_top_group_relation (q : ℤ)
    (g : (F.dilationPairMultidegree (q : ℚ)).realification.Group)
    (hg : g ∈ (F.dilationPairMultidegree (q : ℚ)).realification.subgroup bound) :
    F.ordinary.realDilationPairProjection (q : ℚ) 0 g =
      (F.ordinary.realDilationPairProjection (q : ℚ) 1 g) ^ (q ^ ∑ i, bound i) := by
  let h : (F.realification.dilationPairMultidegree (q : ℚ)).Group :=
    ⟨F.ordinary.realifiedDilationPairEquiv (q : ℚ) g.coord⟩
  have hh : h ∈ (F.realification.dilationPairMultidegree (q : ℚ)).subgroup bound :=
    (F.realifiedDilationPairEquiv_mem_multidegree (q : ℚ) bound g.coord).mp hg
  have he (j : Fin 2) : F.ordinary.realDilationPairProjection (q : ℚ) j g =
      (NilpotentLieBCHGroup.map (F.ordinary.realification.dilationPairProjection (q : ℚ) j) h :
        F.realification.Group) := by
    apply NilpotentLieBCHGroup.ext
    exact F.ordinary.realDilationPairProjection_coord (q : ℚ) j g
  rw [he 0, he 1]
  exact F.realification.dilationPair_top_group_relation q h hh

end MultidegreeLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedComparisonOrbit
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem realPolarizedLog_eval_permute (p : F.realification.adaptedLieSubalgebra)
    (e : Equiv.Perm ι) (he : ∀ i, π (e i) = π i) (x : ι → ℚ) :
    (F.squarefreeBlockPermute π e he).toLinearMap.baseChange ℝ (eval x (F.realPolarizedLog π p)) =
      eval (fun i => x (e.symm i)) (F.realPolarizedLog π p) := by
  rw [F.realPolarizedLog_eval, F.realPolarizedLog_eval]
  simp only [map_sum, LinearMap.map_smul_of_tower, F.realPolarizedCoefficient_permute π p e he]
  symm
  calc
    (∑ a : SquarefreeIndex ι, (a.val.prod fun i n => x (e.symm i) ^ n) •
        F.realPolarizedCoefficient π p a) =
      ∑ a : SquarefreeIndex ι,
        ((SquarefreeIndex.permute e a).val.prod fun i n => x (e.symm i) ^ n) •
        F.realPolarizedCoefficient π p (SquarefreeIndex.permute e a) :=
      (Equiv.sum_comp (SquarefreeIndex.permute e) _).symm
    _ = _ := by simp only [SquarefreeIndex.permute_weight]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem polarizeRealOrbit_permute (p : F.realification.PolynomialOrbit)
    (e : Equiv.Perm ι) (he : ∀ i, π (e i) = π i) (x : ι → ℤ) :
    NilpotentLieBCHGroup.mapReal (realificationLieHom (F.squarefreeBlockPermute π e he).toLieHom)
        ((F.squarefreeMultidegreeFiltration π).realification.polynomialOrbitEval x
          (F.polarizeRealOrbit π p)) =
      (F.squarefreeMultidegreeFiltration π).realification.polynomialOrbitEval
        (fun i => x (e.symm i)) (F.polarizeRealOrbit π p) := by
  apply NilpotentLieBCHGroup.ext
  exact F.realPolarizedLog_eval_permute π
    ⟨PolynomialOrbit.log F.realification p, PolynomialOrbit.adapted F.realification p⟩
    e he (fun i => (x i : ℚ))

end Erdos3.MultidegreeLieFiltration

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

theorem norm_eval (i : Fin W.outputDim) (a : A) (n : ℤ) : ‖W.eval i a n‖ ≤ 1 := W.vertical.norm i _

end NativeDegreeRankFamily

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonRefilteredFactorization
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_weighted_model_of_bases (c : σ → ℕ)
    (b : Basis (Fin (finrank ℚ (M.filtration.weightedSubalgebra c))) ℚ
      (M.filtration.weightedSubalgebra c))
    {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i k, RationalHeightLE (D.basis.repr (b i : L) k) H)
    (hlayers : ∀ n, 1 ≤ n →
      ∃ a : Basis (Fin (finrank ℚ (M.filtration.weightedLayer c n))) ℚ
        (M.filtration.weightedLayer c n),
        ∀ i k, RationalHeightLE (D.basis.repr (a i : L) k) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hgrid : (D.grid : ℝ) ≤ Real.exp p) :
    ∃ E : RationalFilteredNilmanifold (M.filtration.weightedSubalgebra c)
        (multidegreeWeight c bound) (finrank ℚ (M.filtration.weightedSubalgebra c)),
      E.filtration = M.filtration.weightedFiltration c ∧ E.basis = b ∧
      E.lattice = D.lattice.comap
        (NilpotentLieBCHGroup.mapOfSteps (M.filtration.weightedSubalgebra c).incl) ∧
      E.GeometryComplexityLE ((p + 2) ^ 11) := by
  classical
  let K := M.filtration.weightedSubalgebra c
  let F := M.filtration.weightedFiltration c
  have hr : (finrank ℚ K : ℝ) ≤ p :=
    (Nat.cast_le.mpr (lie_subalgebra_finrank_le D.basis K)).trans
      (by simpa only [Fintype.card_fin] using hd)
  have hd' : (Fintype.card (Fin d) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hd
  have hr' : (Fintype.card (Fin (finrank ℚ K)) : ℝ) ≤ p := by
    simpa only [Fintype.card_fin] using hr
  have hmatrix : ∀ i j, RationalHeightLE (LinearMap.toMatrix b D.basis K.incl.toLinearMap i j) H := by
    intro i j
    rw [LinearMap.toMatrix_apply]
    change RationalHeightLE (D.basis.repr (b j : L) i) H
    exact hb j i
  obtain ⟨N, hN, hNb, hin, hout⟩ := exists_bchSubgroup_comap_grid_of_steps
    (hM := F.lowerCentralSeries_eq_bot) b D.basis K.incl
    (fun _ _ h => Subtype.ext h) D.lattice hH D.grid_pos hmatrix D.inner_grid D.outer_grid
    hp hd' hr' hHp hgrid
  obtain ⟨_, _, _, hbracket⟩ := exists_bounded_lie_embedding_retraction b D.basis K.incl
    (fun _ _ h => Subtype.ext h) hH hc hmatrix
  have hbracketBudget := rationalLieStructureHeight_inverse_budget d (finrank ℚ K) H hp hd hr hHp
  have hLayer : ∀ i : Fin (multidegreeWeight c bound + 1),
      ∃ a : Basis (Fin (finrank ℚ (F.layer (i.val + 1)))) ℚ (F.layer (i.val + 1)),
        ∀ j k, rationalLogHeight (b.repr (a j : K) k) ≤ (p + 2) ^ 8 := by
    intro i
    obtain ⟨a, ha⟩ := hlayers (i.val + 1) (Nat.le_add_left 1 _)
    exact M.filtration.exists_weighted_layer_coordinate_basis c D.basis b (i.val + 1)
      (Nat.le_add_left 1 _) a hH hb ha hp hd' hr' hHp
  choose a ha using hLayer
  let E : RationalFilteredNilmanifold K (multidegreeWeight c bound) (finrank ℚ K) :=
    { filtration := F
      basis := b
      layerBasis := a
      lattice := D.lattice.comap (NilpotentLieBCHGroup.mapOfSteps K.incl)
      grid := N
      grid_pos := hN
      inner_grid := hin
      outer_grid := hout }
  have hp1 : 1 ≤ p + 2 := by linarith
  have h9 : (p + 2) ^ 9 ≤ (p + 2) ^ 11 := pow_le_pow_right₀ hp1 (by decide)
  have h8 : (p + 2) ^ 8 ≤ (p + 2) ^ 11 := pow_le_pow_right₀ hp1 (by decide)
  refine ⟨E, rfl, rfl, rfl, hr.trans (le_power_budget hp (by decide)),
    hNb.trans (Real.exp_le_exp.mpr h9), ?_, ?_⟩
  · intro i j k
    apply rationalLogHeight_le_of_height (hbracket i j k)
    simpa only [Fintype.card_fin] using hbracketBudget
  · intro i j k
    exact (ha i j k).trans h8

theorem exists_weighted_model (c : σ → ℕ) {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ E : RationalFilteredNilmanifold (M.filtration.weightedSubalgebra c)
        (multidegreeWeight c bound) (finrank ℚ (M.filtration.weightedSubalgebra c)),
      E.filtration = M.filtration.weightedFiltration c ∧
      E.lattice = D.lattice.comap
        (NilpotentLieBCHGroup.mapOfSteps (M.filtration.weightedSubalgebra c).incl) ∧
      E.GeometryComplexityLE ((p + 3) ^ 11) ∧
      ∀ i k, rationalLogHeight (D.basis.repr (E.basis i : L) k) ≤ p + 1 := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hheight : ∀ a i k, RationalHeightLE (D.basis.repr (M.basis a i : L) k) H :=
    fun a i k => rationalHeightLE_ceil_exp (hM.2 a i k)
  obtain ⟨b, hb⟩ := M.exists_weighted_layer_basis c 1 hheight
  obtain ⟨E, hEF, hEb, hElattice, hEgeom⟩ := M.exists_weighted_model_of_bases c b hH hb
    (fun n _ => M.exists_weighted_layer_basis c n hheight)
    (fun i j k => rationalHeightLE_ceil_exp (hM.1.2.2.1 i j k))
    (by linarith : 0 ≤ p + 1) (hM.1.1.trans (by linarith)) hHp
    (hM.1.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
  refine ⟨E, hEF, hElattice, ?_, ?_⟩
  · convert hEgeom using 1
    ring
  · intro i k
    rw [hEb]
    exact rationalLogHeight_le_of_height (hb i k) hHp

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

structure AllocatedComparisonDimensions (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] (D : ℝ) : Prop where
  nonneg : 0 ≤ D
  degree : (m : ℝ) ≤ D
  kernel_variables : (Fintype.card G : ℝ) ≤ D
  cube : (Fintype.card α : ℝ) ≤ D
  axes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D
  tuples : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ D
  parameters : (Fintype.card (JointBlockParameter B (layerSamplerDegree I n) α) : ℝ) ≤ D
  outputs : (Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) : ℝ) ≤ D
  rows : ∀ j, (Fintype.card (O j) : ℝ) ≤ D
  coefficients : ∀ j : Fin m,
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ D
  profile : (probabilityProfileLipschitz : ℝ) ≤ D

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeTwoVariableSplitFreezing
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

universe u v

open Module
open scoped TensorProduct NNReal

theorem exists_controlled_frozen_niltest (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {bound : σ → ℕ} (D : RationalFilteredNilmanifold L s d)
      (M : D.MultidegreeStructure bound) (S : Finset σ) (b : σ → ℤ)
      (g : M.filtration.realification.PolynomialOrbit)
      (u : D.Space → ℂ) (ℓ B : ℝ≥0)
      (_hu : letI := D.metricSpace; LipschitzWith ℓ u) (_hub : ∀ x, ‖u x‖ ≤ B)
      {p : ℝ}, M.ComplexityLE p → (ℓ : ℝ) ≤ Real.exp p → (B : ℝ) ≤ Real.exp p →
      ∃ E : RationalFilteredNilmanifold
          (M.filtration.weightedSubalgebra (retainedCoordinateWeight S))
          (multidegreeWeight (retainedCoordinateWeight S) bound)
          (finrank ℚ (M.filtration.weightedSubalgebra (retainedCoordinateWeight S))),
        E.filtration = M.filtration.weightedFiltration (retainedCoordinateWeight S) ∧
        E.lattice = D.lattice.comap
          (NilpotentLieBCHGroup.mapOfSteps
            (M.filtration.weightedSubalgebra (retainedCoordinateWeight S)).incl) ∧
        letI := moduleTopology ℝ
          (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S))
        letI : IsTopologicalAddGroup
            (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S)) :=
          IsModuleTopology.topologicalAddGroup ℝ _
        letI : T2Space (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S)) :=
          realification_moduleTopology_t2 E.basis
        ∃ T : E.Niltest (fun _ : S => 1), T.normBound = B ∧
          T.ComplexityLE ((p + C) ^ C) ∧
          E.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
          ∀ x, T.eval x = u (QuotientGroup.mk
            (M.filtration.realification.polynomialOrbitEval (freezeCoordinates S b x) g)) := by
  obtain ⟨a, _, hrep⟩ := Erdos3.exists_realification_representatives_exp_bound s
  obtain ⟨k, _, hleft⟩ := exists_bounded_normalization_left_lipschitz s a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget
    ((X + 3) ^ 11 + 2 * X + (X + Polynomial.C a + 2 + Polynomial.C k) ^ k + (X + 4) ^ 2 + 4)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ _ d bound D M S b g u ℓ B hu hub p hM hℓ hB
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let c := retainedCoordinateWeight S
  let K := M.filtration.weightedSubalgebra c
  let r := normalizedSquareLeftBudget a k p
  have hr : 0 ≤ r := normalizedSquareLeftBudget_nonneg a k hp
  have hcost : (p + 3) ^ 11 + (2 * p + r + (p + 4) ^ 2 + 4) ≤ (p + C) ^ C := by
    convert hpoly p hp using 1
    simp [X, r, normalizedSquareLeftBudget, Polynomial.eval₂_pow]
    ring
  have hgeom : (p + 3) ^ 11 ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ 2 * p + r + (p + 4) ^ 2 + 4)).trans hcost
  have hobs : 2 * p + r + (p + 4) ^ 2 + 4 ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity : 0 ≤ (p + 3) ^ 11)).trans hcost
  obtain ⟨E, hEF, hEL, hE, he⟩ := M.exists_weighted_model c hM
  obtain ⟨A, _, hAb, hA⟩ := hleft D p hp hM.1
  obtain ⟨ε, hε, γ, hγ, hfactor⟩ :=
    hrep D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice D.grid
      ⌈Real.exp p⌉₊ (p + 1) D.grid_pos D.inner_grid
      (fun i j k => rationalHeightLE_ceil_exp (hM.1.2.2.1 i j k))
      (by linarith) (by simpa only [Fintype.card_fin] using hM.1.1.trans (show p ≤ p + 1 by linarith))
      (ceil_exp_le_exp_add_one hp) (hM.1.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
      (M.filtration.realification.polynomialOrbitEval (freezeCoordinates S b 0) g)
  refine ⟨E, hEF, hEL, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 E.basis
  let H := ⌈Real.exp (p + 1)⌉₊
  obtain ⟨T, hTnorm, hTlip, hTzero, hTeval⟩ := M.exists_frozen_niltest S E hEF hEL b g
    u ℓ B hu hub ε γ hγ hfactor A (hA ε hε) H
    (fun i j => rationalHeightLE_ceil_exp (he i j))
  have hdim : (finrank ℚ K : ℝ) ≤ p :=
    (Nat.cast_le.mpr (lie_subalgebra_finrank_le D.basis K)).trans
      (by simpa only [Fintype.card_fin] using hM.1.1)
  have hH : (H : ℝ) ≤ Real.exp (p + 2) := by
    simpa only [show p + 1 + 1 = p + 2 by ring] using
      ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)
  have hP : (coordinateLipschitzBound d (finrank ℚ K) H : ℝ) ≤ Real.exp ((p + 4) ^ 2) := by
    simpa only [NNReal.coe_natCast, show p + 2 + 2 = p + 4 by ring] using
      coordinateLipschitzBound_le_exp d (finrank ℚ K) H (by linarith : 0 ≤ p + 2)
        (hM.1.1.trans (by linarith)) (hdim.trans (by linarith)) hH
  have hTL : (T.lipBound : ℝ) ≤ Real.exp (p + r + (p + 4) ^ 2) := by
    rw [hTlip]
    change (ℓ : ℝ) * ((A : ℝ) * (coordinateLipschitzBound d (finrank ℚ K) H : ℝ)) ≤ _
    calc
      _ ≤ Real.exp p * (Real.exp r * Real.exp ((p + 4) ^ 2)) := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  refine ⟨T, hTnorm, ⟨hE.mono E hgeom, ?_⟩, hTzero, hTeval⟩
  have hn : (T.normBound : ℝ) ≤ Real.exp p := by rw [hTnorm]; exact hB
  have hb := niltest_log_bound_of_exp T.normBound T.lipBound hp
    (by positivity : 0 ≤ p + r + (p + 4) ^ 2) hn hTL
  exact hb.trans (by linarith)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DilationCost
namespace OAI

section

namespace Erdos3.MultilinearityBudget

open scoped TensorProduct NNReal

theorem niltest_complexity {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s n : ℕ} (Q : RationalFilteredNilmanifold L s n) {w : σ → ℕ} (T : Q.Niltest w)
    (C d H : ℕ) (A : ℝ≥0) {p : ℝ} (hp : 0 ≤ p)
    (hQ : Q.GeometryComplexityLE (quotient p))
    (hd : (d : ℝ) ≤ reconstruction C p) (hH : (H : ℝ) ≤ Real.exp (reconstruction C p))
    (hA : (A : ℝ) ≤ Real.exp (reconstruction C p))
    (hnorm : T.normBound = 1) (hlip : T.lipBound = rationalReconstructionLipschitzBound s d n H A 1) :
    T.ComplexityLE (total C (reconstructionExponent s) p) := by
  have hR := reconstruction_bounds C hp
  have hQle : quotient p ≤ reconstruction C p :=
    (le_add_of_nonneg_right zero_le_one).trans hR.2.2.1
  have hTlip : (T.lipBound : ℝ) ≤
      Real.exp ((reconstruction C p + reconstructionExponent s) ^ reconstructionExponent s) := by
    rw [hlip]
    exact reconstructionExponent_control s d n H A 1 _ hR.1 hd (hQ.1.trans hQle) hH hA
      (by simpa only [NNReal.coe_one] using Real.one_le_exp hR.1)
  have hpower : 0 ≤ (reconstruction C p + reconstructionExponent s) ^ reconstructionExponent s :=
    pow_nonneg (add_nonneg hR.1 (Nat.cast_nonneg _)) _
  have hlog := niltest_log_bound_of_exp T.normBound T.lipBound (a := 0) (by norm_num) hpower
    (by simp only [hnorm, NNReal.coe_one, Real.exp_zero, le_refl]) hTlip
  refine ⟨hQ.mono Q (total_bounds C (reconstructionExponent s) hp).1, ?_⟩
  have hlog' : Real.log (2 + (T.normBound : ℝ) + T.lipBound) ≤
      (reconstruction C p + reconstructionExponent s) ^ reconstructionExponent s + 4 := by
    simpa only [zero_add] using hlog
  exact hlog'.trans (total_bounds C (reconstructionExponent s) hp).2

end Erdos3.MultilinearityBudget

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDilationOrbit
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realifiedDilationPairOrbit_zero (q : ℚ)
    (p : (F.realification.dilationPairMultidegree q).PolynomialOrbit)
    (hp : (F.realification.dilationPairMultidegree q).polynomialOrbitEval 0 p = 1) :
    (F.dilationPairMultidegree q).realification.polynomialOrbitEval 0
      (F.realifiedDilationPairOrbit q p) = 1 := by
  apply NilpotentLieBCHGroup.ext
  apply (F.ordinary.realifiedDilationPairEquiv q).injective
  rw [F.realifiedDilationPairOrbit_eval, hp]
  exact (map_zero _).symm

theorem exists_real_normalized_dilationPair_orbit (q : ℤ)
    (p : F.realification.PolynomialOrbit) (a b : F.realification.Group)
    (hp0 : F.realification.polynomialOrbitEval 0 p = a * b) :
    ∃ g : (F.dilationPairMultidegree (q : ℚ)).realification.PolynomialOrbit,
      (F.dilationPairMultidegree (q : ℚ)).realification.polynomialOrbitEval 0 g = 1 ∧
      ∀ x : σ → ℤ,
        let h := (F.dilationPairMultidegree (q : ℚ)).realification.polynomialOrbitEval x g
        F.ordinary.realDilationPairProjection (q : ℚ) 0 h =
          a⁻¹ * F.realification.polynomialOrbitEval (fun i => q * x i) p * b⁻¹ ∧
        F.ordinary.realDilationPairProjection (q : ℚ) 1 h =
          a⁻¹ * F.realification.polynomialOrbitEval x p * b⁻¹ := by
  obtain ⟨g, hg0, hg⟩ := F.realification.exists_normalized_dilationPair_orbit q p a b hp0
  refine ⟨F.realifiedDilationPairOrbit (q : ℚ) g,
    F.realifiedDilationPairOrbit_zero (q : ℚ) g hg0, ?_⟩
  intro x
  dsimp only
  have he (j : Fin 2) := F.ordinary.realDilationPairProjection_coord (q : ℚ) j
    ((F.dilationPairMultidegree (q : ℚ)).realification.polynomialOrbitEval x
      (F.realifiedDilationPairOrbit (q : ℚ) g))
  simp only [F.realifiedDilationPairOrbit_eval, hg x] at he
  exact ⟨NilpotentLieBCHGroup.ext (he 0), NilpotentLieBCHGroup.ext (he 1)⟩

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.DilationFrequencyPhase
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem MultidegreeLieFiltration.realDilationPair_frequency_phase
    {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
    (q : ℤ) (η : L →ₗ[ℚ] ℚ)
    (g : (F.dilationPairMultidegree (q : ℚ)).realification.Group)
    (hg : g ∈ (F.dilationPairMultidegree (q : ℚ)).realification.subgroup bound) :
    (realifyFunctional η (F.ordinary.realDilationPairProjection (q : ℚ) 0 g).coord : CircleFourier.Circle) =
      (q ^ ∑ i, bound i) • (realifyFunctional η
        (F.ordinary.realDilationPairProjection (q : ℚ) 1 g).coord : CircleFourier.Circle) := by
  rw [F.realDilationPair_top_group_relation q g hg, NilpotentLieBCHGroup.coord_zpow,
    map_zsmul, AddCircle.coe_zsmul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeWeightPairRemoval
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

namespace NativeMixedReductionData

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

noncomputable def translationTerm (k : Fin V.outputDim) (a : MixedExpansionIndex V)
    (b : Fin (D.translation.selectedExpansion k a).count) (x : Fin 3 → ℤ) : ℂ :=
  ((D.translation.selectedExpansion k a).test b).eval x

noncomputable def lowerTerm (h δ : ℤ) (a : MixedExpansionIndex V)
    (c : Fin (D.lower h δ a).count) (n : ℤ) : ℂ :=
  ((D.lower h δ a).test c).eval (fun _ => n)

end NativeMixedReductionData

end Erdos3

end

section

namespace Erdos3

namespace NativeMixedReductionData

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

noncomputable def translationCoordinates (k : Fin 4 → Fin V.outputDim) (t : D.TranslationCode k) :
    Fin 4 → Fin V.outputDim :=
  ![k 0, firstTranslationCoordinate (mixedTranslationCoordinates s) t.second,
    k 2, firstTranslationCoordinate (mixedTranslationCoordinates s) t.fourth]

noncomputable def translationGlobal (k : Fin 4 → Fin V.outputDim) (t : D.TranslationCode k)
    (x : Fin 5 → ℤ) : ℂ :=
  D.translationTerm (k 1) t.second t.secondTerm ![x 1, x 3, x 4] *
    star (D.translationTerm (k 3) t.fourth t.fourthTerm ![x 1 + x 2 - x 0, x 3, x 4])

noncomputable def translationLower {k : Fin 4 → Fin V.outputDim} (t : D.TranslationCode k)
    (h₂ h₄ δ : ℤ) (c : D.LowerCode t h₂ h₄ δ) (n : ℤ) : ℂ :=
  D.lowerTerm h₂ δ t.second c.second n * star (D.lowerTerm h₄ δ t.fourth c.fourth n)

structure ReductionCode (k : Fin 4 → Fin V.outputDim) where
  translations : D.TranslationCode k
  term : Fin (D.parallelogram (D.translationCoordinates k translations)).count

noncomputable def globalError (k : Fin 4 → Fin V.outputDim) (a : D.ReductionCode k)
    (x : Fin 5 → ℤ) : ℂ :=
  D.translationGlobal k a.translations x *
    ((D.parallelogram (D.translationCoordinates k a.translations)).test a.term).eval
      ![x 0, x 1, x 2, x 3]

end NativeMixedReductionData

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem native_weight_pair_removal {I : Type} [Fintype I] [Nonempty I]
    {d : ℕ} {p : ℝ} (hp : 2 ≤ p) (A : Finset ℤ) (hA : A.Nonempty)
    (S : I → Finset ℤ) (hSA : ∀ i, S i ⊆ A)
    (weight : ℤ → ℂ) (a v : I → ℤ → ℂ)
    (E : ∀ i, NativeIntegerExpansion (fun _ : Unit => 1) d p (fun x => v i (x ())))
    (hw : ∀ x ∈ A, ‖weight x‖ ≤ 1) (ha : ∀ i x, x ∈ S i → ‖a i x‖ ≤ 1)
    (hsize : ∀ i, Real.exp (-p) ≤ (S i).card / (A.card : ℝ))
    (hcorr : ∀ i, Real.exp (-p) ≤ ‖𝔼 x ∈ S i, weight x * (a i x * v i x)‖) :
    ∃ P : Finset (I × I), P.Nonempty ∧
      Real.exp (-(8 * p + 1)) * (Fintype.card I : ℝ) ^ 2 ≤ (P.card : ℝ) ∧
      ∀ t ∈ P, (S t.1 ∩ S t.2).Nonempty ∧
        Real.exp (-(8 * p + 1)) ≤ (S t.1 ∩ S t.2).card / (A.card : ℝ) ∧
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) d (mixedErrorPairBudget p)
          (fun x => v t.1 (x ()) * star (v t.2 (x ())))) ∧
        Real.exp (-(8 * p + 1)) ≤ ‖𝔼 x ∈ S t.1 ∩ S t.2,
          (a t.1 x * star (a t.2 x)) * (v t.1 x * star (v t.2 x))‖ := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  let u (i : I) (x : ℤ) := (Real.exp (-(2 * p)) : ℂ) * (a i x * v i x)
  have hu (i : I) (x : ℤ) (hx : x ∈ S i) : ‖u i x‖ ≤ 1 := by
    apply exp_scaled_norm_le_one
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (ha i x hx) ((E i).norm_eval_le (fun _ => x))
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have huc (i : I) : Real.exp (-(3 * p)) ≤ ‖𝔼 x ∈ S i, weight x * u i x‖ := by
    have heq : (𝔼 x ∈ S i, weight x * u i x) =
        (Real.exp (-(2 * p)) : ℂ) * (𝔼 x ∈ S i, weight x * (a i x * v i x)) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      dsimp only [u]
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ = Real.exp (-(2 * p)) * Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcorr i) (Real.exp_nonneg _)
  obtain ⟨P, hP, hPsize, hpair⟩ := exists_supported_correlation_pairs A hA S hSA
    weight u (Real.exp_pos (-p)) (Real.exp_pos (-(3 * p))) hw hu hsize huc
  have hthreshold : Real.exp (-(8 * p + 1)) ≤ (Real.exp (-p) * Real.exp (-(3 * p))) ^ 2 / 2 := by
    have heq : (Real.exp (-p) * Real.exp (-(3 * p))) ^ 2 = Real.exp (-(8 * p)) := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      ring
    rw [heq]
    simpa only [show -(8 * p + 1) = -(8 * p) - 1 by ring] using exp_sub_one_le_half_exp (-(8 * p))
  refine ⟨P, hP, (mul_le_mul_of_nonneg_right hthreshold (sq_nonneg _)).trans hPsize, ?_⟩
  intro t ht
  obtain ⟨hJ, hcor, hvol⟩ := hpair t ht
  refine ⟨hJ, hthreshold.trans hvol, ⟨(E t.1).mul (E t.2).conjugate hp⟩, ?_⟩
  have hcoef : (Real.exp (-(4 * p)) : ℂ) =
      (Real.exp (-(2 * p)) : ℂ) * (Real.exp (-(2 * p)) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1
    ring_nf
  have hmean : (𝔼 x ∈ S t.1 ∩ S t.2, u t.1 x * star (u t.2 x)) =
      𝔼 x ∈ S t.1 ∩ S t.2, ((Real.exp (-(4 * p)) : ℂ) * (a t.1 x * star (a t.2 x))) *
        (v t.1 x * star (v t.2 x)) := by
    apply Finset.expect_congr rfl
    intro x _
    simp only [u, star_mul, Complex.star_def, Complex.conj_ofReal, hcoef]
    ring
  have hc := hthreshold.trans hcor
  rw [hmean] at hc
  exact finite_remove_normalization (S t.1 ∩ S t.2)
    (fun x => a t.1 x * star (a t.2 x)) (fun x => v t.1 x * star (v t.2 x))
    (by linarith : 0 ≤ 4 * p) hc

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinateSplitFreezing
namespace OAI

section

namespace Erdos3.NativeCoordinateSplit

open scoped TensorProduct BigOperators

attribute [local instance] NativeCoordinateSplit.lie NativeCoordinateSplit.algebra
  NativeCoordinateSplit.topology NativeCoordinateSplit.topologicalAdd
  NativeCoordinateSplit.continuousSMul NativeCoordinateSplit.hausdorff

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

attribute [local instance] NativeCoordinateSplit.lie NativeCoordinateSplit.algebra
  NativeCoordinateSplit.topology NativeCoordinateSplit.topologicalAdd
  NativeCoordinateSplit.continuousSMul NativeCoordinateSplit.hausdorff

variable {σ : Type} [Fintype σ] [DecidableEq σ] [Nonempty σ] {i : σ} {s d : ℕ}
  {p epsilon : ℝ} {f : (σ → ℤ) → ℂ} (R : NativeCoordinateSplit i s d p epsilon f)

noncomputable def firstFactor (j : Fin R.count) (n : ℤ) : ℂ :=
  (R.test false j).eval (fun _ => n)

theorem firstFactor_norm (j : Fin R.count) (n : ℤ) : ‖R.firstFactor j n‖ ≤ 1 :=
  ((R.test false j).norm_eval_le _).trans
    (show ((R.test false j).normBound : ℝ) ≤ 1 from R.test_norm false j)

end Erdos3.NativeCoordinateSplit

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoordinateTransfer
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def antisymmetricBoxValue (i j : Fin W.outputDim) (n : Fin 4 → ℤ) : ℂ :=
  let K := fun x y => star (W.eval i (correlationInput x y)) * W.eval j (correlationInput y x)
  K (n 0) (n 2) * star (K (n 1) (n 2)) * star (K (n 0) (n 3)) * K (n 1) (n 3)

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankPairs
namespace OAI

section

namespace Erdos3

namespace NativeDegreeRankFamily

variable {s r : ℕ} {G : Type*} [AddGroup G] {p : ℝ} (W : NativeDegreeRankFamily s r G p)

noncomputable def shiftPair (i : Fin W.outputDim) (a h : G) (δ n : ℤ) : ℂ :=
  star (W.eval i h n) * W.eval i (h - a) (n + δ)

theorem shiftPair_norm (i : Fin W.outputDim) (a h : G) (δ n : ℤ) :
    ‖W.shiftPair i a h δ n‖ ≤ 1 := by
  rw [shiftPair, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval i h n)).trans
    (W.norm_eval i (h - a) (n + δ))

theorem shiftPair_mul_star (i : Fin W.outputDim) (a h k : G) (δ n : ℤ) :
    W.shiftPair i a h δ n * star (W.shiftPair i a k δ n) =
      fourPointProduct (W.eval i h) (W.eval i (h - a))
        (W.eval i k) (W.eval i (k - a)) δ n := by
  simp only [shiftPair, fourPointProduct, star_mul, star_star]
  ring

theorem quadruple_common_anchor (i : Fin W.outputDim) (a h k : G) (δ n : ℤ) (w v : ℂ) :
    fourPointProduct (W.eval i h) (W.eval i (h - a))
        (W.eval i k) (W.eval i (k - a)) δ n * w * v =
      (w * star (W.shiftPair i a k δ n)) * (W.shiftPair i a h δ n * v) := by
  rw [← W.shiftPair_mul_star]
  ring

end NativeDegreeRankFamily

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeIntervalWeightPairs
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem native_interval_weight_pairs {I : Type} [Fintype I] [Nonempty I]
    {s r d N : ℕ} [NeZero N] {p b : ℝ}
    (W : NativeDegreeRankFamily s r (ZMod N) b) (out : Fin W.outputDim)
    (a k : ZMod N) (δ : ℤ) (h : I → ZMod N) (c len : I → ℕ)
    (weight : ℤ → ℂ) (v : I → ℤ → ℂ)
    (E : ∀ i, NativeIntegerExpansion (fun _ : Unit => 1) d p (fun x => v i (x ())))
    (hp : 2 ≤ p) (hw : ∀ n, ‖weight n‖ ≤ 1)
    (hN : ∀ i, c i + len i ≤ N) (hshort : ∀ i, 2 * ((len i : ℤ) - 1) < N)
    (hsize : ∀ i, Real.exp (-p) ≤ (len i : ℝ) / N)
    (hcorr : ∀ i, Real.exp (-p) ≤ ‖𝔼 n ∈ Finset.Ico (c i : ℤ) (c i + len i),
      fourPointProduct (W.eval out (h i)) (W.eval out (h i - a))
        (W.eval out k) (W.eval out (k - a)) δ n * weight n * v i n‖) :
    ∃ Q : Finset (I × I), Q.Nonempty ∧
      Real.exp (-(8 * p + 1)) * (Fintype.card I : ℝ) ^ 2 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, ∃ c' len' : ℕ, 0 < len' ∧ c' + len' ≤ N ∧
        2 * ((len' : ℤ) - 1) < N ∧ Real.exp (-(8 * p + 1)) ≤ (len' : ℝ) / N ∧
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) d (mixedErrorPairBudget p)
          (fun x => v t.1 (x ()) * star (v t.2 (x ())))) ∧
        Real.exp (-(8 * p + 1)) ≤ ‖𝔼 n ∈ Finset.Ico (c' : ℤ) (c' + len'),
          fourPointProduct (W.eval out (h t.1)) (W.eval out (h t.1 - a))
            (W.eval out (h t.2)) (W.eval out (h t.2 - a)) δ n * (v t.1 n * star (v t.2 n))‖ := by
  let A := Finset.Ico (0 : ℤ) N
  let S (i : I) := Finset.Ico (c i : ℤ) (c i + len i)
  let B (n : ℤ) := weight n * star (W.shiftPair out a k δ n)
  have hA : A.Nonempty := by
    exact ⟨0, Finset.mem_Ico.mpr ⟨le_rfl, by exact_mod_cast NeZero.pos N⟩⟩
  have hAcard : A.card = N := by simpa only [A, Nat.cast_zero, zero_add] using integerIco_card 0 N
  have hB (n : ℤ) (_ : n ∈ A) : ‖B n‖ ≤ 1 := by
    dsimp only [B]
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hw n)).trans (W.shiftPair_norm out a k δ n)
  have hcor (i : I) : Real.exp (-p) ≤ ‖𝔼 n ∈ S i, B n * (W.shiftPair out a (h i) δ n * v i n)‖ := by
    simpa only [S, B, W.quadruple_common_anchor] using hcorr i
  have hvol (i : I) : Real.exp (-p) ≤ (S i).card / (A.card : ℝ) := by
    simpa only [S, integerIco_card, hAcard] using hsize i
  obtain ⟨Q, hQ, hQsize, hpairs⟩ := native_weight_pair_removal hp A hA S
    (fun i => integerIco_subset_range (c i) (len i) N (hN i)) B
    (fun i => W.shiftPair out a (h i) δ) v E hB
    (fun i n _ => W.shiftPair_norm out a (h i) δ n) hvol hcor
  refine ⟨Q, hQ, hQsize, ?_⟩
  intro t ht
  obtain ⟨hJ, hJvol, hE, hJcor⟩ := hpairs t ht
  obtain ⟨c', len', hlen', hN', hle, _, heq⟩ := integerIco_intersection
    (c t.1) (len t.1) (c t.2) (len t.2) N (hN t.1) (hN t.2) hJ
  refine ⟨c', len', hlen', hN', ?_, ?_, hE, ?_⟩
  · have hs := hshort t.1
    omega
  · simpa only [S, heq, integerIco_card, hAcard] using hJvol
  · simpa only [S, heq, W.shiftPair_mul_star] using hJcor

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankRelationExistence
namespace OAI

section

namespace Erdos3

structure NativeAnchoredRankFibers {s r N : ℕ} [NeZero N] {b p : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} (F : NativeWeightedRankIntervals W out H p) where
  anchor : ZMod N
  branch : Bool
  selected : Finset (Fin F.count)
  parameters : Finset (ZMod N)
  parameters_nonempty : parameters.Nonempty
  parameters_density : Real.exp (-p) / 4 * (Fintype.card (ZMod N) : ℝ) ≤ parameters.card
  anchor_eq : ∀ i ∈ selected, (F.index i).2.2 = anchor
  branch_eq : ∀ i ∈ selected, F.branch i = branch
  pair_injective : Set.InjOn (fun i => ((F.index i).1, (F.index i).2.1)) (selected : Set (Fin F.count))
  fiber_density : ∀ a ∈ parameters, Real.exp (-p) / 4 * (Fintype.card (ZMod N) : ℝ) ≤
    ((selected.filter (fun i => (F.index i).1 = a)).card : ℝ)

namespace NativeAnchoredRankFibers

variable {s r N : ℕ} [NeZero N] {b p : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim} {H : Finset (ZMod N)}
  {F : NativeWeightedRankIntervals W out H p} (A : NativeAnchoredRankFibers F)

noncomputable def fiber (a : ZMod N) : Finset (Fin F.count) :=
  A.selected.filter (fun i => (F.index i).1 = a)

theorem fiber_nonempty (a : ZMod N) (ha : a ∈ A.parameters) : (A.fiber a).Nonempty := by
  have hN : (0 : ℝ) < Fintype.card (ZMod N) := by exact_mod_cast Fintype.card_pos
  have hpos : (0 : ℝ) < (A.fiber a).card :=
    lt_of_lt_of_le (by positivity) (A.fiber_density a ha)
  exact Finset.card_pos.mp (by exact_mod_cast hpos)

theorem fiber_parameter (a : ZMod N) (i : A.fiber a) : (F.index i.val).1 = a :=
  (Finset.mem_filter.mp i.property).2

theorem fiber_anchor (a : ZMod N) (i : A.fiber a) : (F.index i.val).2.2 = A.anchor :=
  A.anchor_eq i.val (Finset.mem_filter.mp i.property).1

theorem fiber_branch (a : ZMod N) (i : A.fiber a) : F.branch i.val = A.branch :=
  A.branch_eq i.val (Finset.mem_filter.mp i.property).1

theorem fiber_shift_injective (a : ZMod N) :
    Function.Injective (fun i : A.fiber a => (F.index i.val).2.1) := by
  intro i j hij
  apply Subtype.ext
  apply A.pair_injective (Finset.mem_filter.mp i.property).1 (Finset.mem_filter.mp j.property).1
  exact Prod.ext ((A.fiber_parameter a i).trans (A.fiber_parameter a j).symm) hij

end NativeAnchoredRankFibers

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AntisymmetricPartitionApproximation
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeAntisymmetricFrozenDescent.lie NativeAntisymmetricFrozenDescent.algebra
  NativeAntisymmetricFrozenDescent.topology NativeAntisymmetricFrozenDescent.topologicalAdd
  NativeAntisymmetricFrozenDescent.continuousSMul NativeAntisymmetricFrozenDescent.hausdorff

structure NativeAntisymmetricLocalModels {p q : ℝ}
    {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {N : ℕ}
    {V : NativeAntisymmetricOrbitFactors W N p} (R : NativeAntisymmetricFrozenDescent V q)
    (b : ℝ) where
  period : ℕ
  period_pos : 0 < period
  period_bound : (period : ℝ) ≤ Real.exp b
  local_model : ∀ y : Fin 4 → ℤ, (∀ i, |(y i : ℝ)| ≤ (N : ℝ)) →
    ∃ S : R.model.Niltest (fun _ : Fin 4 => 1), S.orbit = R.orbit ∧ S.ComplexityLE q ∧
      ∀ (x : Fin 4 → ℤ) (δ : ℝ), 0 ≤ δ →
        (∀ i, |(x i : ℝ)| ≤ (N : ℝ)) → (∀ i, (period : ℤ) ∣ x i - y i) →
        (∀ i, |(x i : ℝ) - (y i : ℝ)| ≤ (N : ℝ) * δ) →
        ‖W.antisymmetricBoxValue V.leftIndex V.rightIndex x - S.eval x‖ ≤ Real.exp b * δ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeRankZeroNiltest
namespace OAI

section

namespace Erdos3.NativeDegreeRankFamily

open scoped NNReal

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {s r : ℕ} {A : Type*} {p : ℝ} (W : NativeDegreeRankFamily s r A p)

theorem component_complexity (hp : 0 ≤ p) (i : Fin W.outputDim) (a : A) :
    (W.component i a).ComplexityLE (p + 4) := by
  refine ⟨W.complexity.1.mono W.model (by linarith), ?_⟩
  have h := niltest_log_bound_of_exp (1 : ℝ≥0) W.vertical.lipBound
    (a := 0) (b := p) (by norm_num) hp (by simp) W.vertical.lip_bound
  simpa only [component, zero_add] using h

end Erdos3.NativeDegreeRankFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankIntervalFactorization
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

variable {ι σ : Type*} [Fintype ι] [Nonempty ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s r : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (R : ∀ i, (D i).DegreeRankStructure r)

theorem productProjectionHom_mem_rank (i : ι) (k j : ℕ) (g : (pi D).RealGroup)
    (hg : g ∈ (piRank D R).realSubgroup k j) :
    productProjectionHom D i g ∈ (R i).realSubgroup k j := by
  apply baseChange_mem_of_mapsTo ((piRank D R).filtration.layer k j)
    ((R i).filtration.layer k j) (liePiEval i).toLinearMap _ hg
  intro x hx
  exact (DegreeRankLieFiltration.mem_pi_layer (fun i => (R i).filtration) k j x).mp hx i

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MarkedPolynomialGenerators
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

variable {I σ L : Type*} [Fintype I] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def finiteMarkedPolynomialValues (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (s d k l : ℕ) : Finset (VectorPolynomial σ ℚ L) := by
  classical
  exact (markedParameterExponents σ s).biUnion (fun α =>
    (finiteMarkedLieValues v w marked s d (k + Finsupp.weight (fun _ : σ => 1) α) l).image
      (monomial (R := ℚ) α))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedShiftGeneratorBounds
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

variable {I L : Type*} [Fintype I] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)

abbrev MarkedShiftGeneratorIndex (t h n : ℕ) :=
  (finiteMarkedPolynomialValues (σ := Fin t) v w marked s n h 0) ⊕
    {_i : Fin t // n = 0 ∧ h ≤ 1}

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MultidegreeIntegralModel
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  (e : Basis (Fin d) ℚ L)
  (b : ∀ a, Basis (Fin (finrank ℚ (F.layer a))) ℚ (F.layer a))
  {H : ℕ} (hb : ∀ a i j, RationalHeightLE (e.repr ((b a) i).val j) H)
  (B : ℕ) (hB : 0 < B)
  (hstable : ∀ x ∈ coordinateGridModule e B, ∀ y ∈ coordinateGridModule e B,
    lieBCH s x y ∈ coordinateGridModule e B)

noncomputable def boundedIntegralModel : RationalFilteredNilmanifold L s d where
  filtration := F.ordinary
  basis := e
  layerBasis i := (F.exists_bounded_ordinaryLayer_basis b e hb (i.val + 1)).choose
  lattice := coordinateGridBCHSubgroup e B F.ordinary.lowerCentralSeries_eq_bot hstable
  grid := B
  grid_pos := hB
  inner_grid := by rw [coordinateGridBCHSubgroup_coordinates]
  outer_grid := by
    rw [coordinateGridBCHSubgroup_coordinates]
    exact scaledIntegerGrid_le_denominatorGrid B B

noncomputable def boundedIntegralStructure :
    (F.boundedIntegralModel e b hb B hB hstable).MultidegreeStructure bound where
  filtration := F
  ordinary := rfl
  basis a := b (fun i => (a i).val)

theorem boundedIntegralModel_coordinates :
    bchSubgroupCoordinates (F.boundedIntegralModel e b hb B hB hstable).basis
      (F.boundedIntegralModel e b hb B hB hstable).lattice = scaledIntegerGrid B :=
  coordinateGridBCHSubgroup_coordinates e B F.ordinary.lowerCentralSeries_eq_bot hstable

theorem boundedIntegralStructure_complexity {p : ℝ} (hd : (d : ℝ) ≤ p)
    (hgrid : (B : ℝ) ≤ Real.exp p) (hheight : (H : ℝ) ≤ Real.exp p)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) :
    (F.boundedIntegralStructure e b hb B hB hstable).ComplexityLE p := by
  refine ⟨⟨hd, hgrid, ?_, ?_⟩, ?_⟩
  · exact fun i j k => rationalLogHeight_le_of_height (hc i j k) hheight
  · intro i j k
    exact rationalLogHeight_le_of_height
      ((F.exists_bounded_ordinaryLayer_basis b e hb (i.val + 1)).choose_spec j k) hheight
  · intro a i j
    exact rationalLogHeight_le_of_height (hb (fun k => (a k).val) i j) hheight

omit B hB hstable in
include b hb in
theorem exists_bounded_integral_model
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (l : ℕ) (hl : 0 < l) :
    ∃ B : ℕ, 0 < B ∧ l ∣ B ∧ B ≤ bchIntegralDenominatorBound s * H ^ (d ^ 3) * l ∧
      ∃ D : RationalFilteredNilmanifold L s d, ∃ M : D.MultidegreeStructure bound,
        M.filtration = F ∧ D.basis = e ∧ D.grid = B ∧
        bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid B ∧
        ∀ p : ℝ, (d : ℝ) ≤ p → (B : ℝ) ≤ Real.exp p → (H : ℝ) ≤ Real.exp p → M.ComplexityLE p := by
  obtain ⟨B, hB, hdiv, hbound, hstable⟩ :=
    exists_bch_stable_integral_grid e F.ordinary.lowerCentralSeries_eq_bot l hl hc
  refine ⟨B, hB, hdiv, ?_, F.boundedIntegralModel e b hb B hB hstable,
    F.boundedIntegralStructure e b hb B hB hstable, rfl, rfl, rfl,
    F.boundedIntegralModel_coordinates e b hb B hB hstable, ?_⟩
  · simpa only [Fintype.card_fin] using hbound
  · intro p hd hgrid hheight
    exact F.boundedIntegralStructure_complexity e b hb B hB hstable hd hgrid hheight hc

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonAffineOrbitEvaluation
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

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

end MultidegreeLieFiltration

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

namespace NativeSampleCorrelation

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))

abbrev AntisymmetricPairAlgebra :=
  ∀ k : Option (Fin 2), optionLieSpace V.L (fun _ : Fin 2 => W.L) k

end NativeSampleCorrelation

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFixedScaleJointMarginal
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

noncomputable def narrowPhysicalSiteMap {G J X T : Type*}
    [Fintype G] [Fintype J] [Fintype X] [DecidableEq X]
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (N : X → ℕ) (hN : ∀ i, 0 < N i)
    (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (root : T → G ⊕ J → ℤ) (hroot : ∀ t, (∑ k, |(root t k : ℝ)|) ≤ W) :
    (trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0 (narrowTrimmedSpatialWidths (G := G) (J := J) W τ ξ N) 1) →
      T → integerBox N :=
  fun z t => ⟨jointIntegerPhysicalSite (root t) (z.1.val, z.2.val),
    jointIntegerPhysicalSite_mem_box (root t) N (spatialTrimMargin τ N) hmargin _
      (narrowTrimmedSpatial_site_width hW hτ hξ (root t) (hroot t) N hN) z⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

open Module Submodule

abbrev B (q : ℕ) (_ : LayerSamplerAxis (I q) (n q)) : Type := PEmpty

noncomputable def o (q : ℕ) (j : Fin q) :
    OrthonormalBasis (I q j) ℝ (euclideanSubspace (U q j)) :=
  (Basis.empty _).toOrthonormalBasis ⟨fun i => isEmptyElim i,
    fun i => isEmptyElim i⟩

end Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSourceNormalization
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)

structure AllocatedSourceNumerics (P : ℝ) : Prop where
  nonneg : 0 ≤ P
  degree : (m : ℝ) ≤ P
  variable_count : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P
  length : (S.value : ℝ) ≤ Real.exp P
  radius_inv : ∀ j, (R j)⁻¹ ≤ Real.exp P
  width_inv : ∀ j, (σ j)⁻¹ ≤ Real.exp P
  coefficients : ∀ j : Fin m,
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P
  real_axes : ∀ j, (Fintype.card (I j) : ℝ) ≤ P
  integer_axes : ∀ j, (n j : ℝ) ≤ P
  ambient_axes : ∀ j, (Fintype.card (J j) : ℝ) ≤ P
  profile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P
  chart : ∀ j, (C j : ℝ) ≤ Real.exp P
  covolume : ∀ j, (V j : ℝ) ≤ Real.exp P
  root : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ Real.exp P

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedFullSiteSupport
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedFullMixedSiteValue
    (w : ∀ j : Fin m, (I j → ℝ) × (Fin (n j) → ℤ)) : LayerSamplerAxis I n → ℝ
  | ⟨j, .inl i⟩ => (w j).1 i / R j
  | ⟨j, .inr i⟩ => ((w j).2 i : ℝ) / (basisAxisScale (b j) i : ℝ) / R j

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalSingleSiteCommonCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S))

noncomputable def allocatedOriginalSamplePhysicalMixedValue
    (j : Fin m) : (I j → ℝ) × (Fin (n j) → ℤ) :=
  mixedArrayRegroup (I j) (Fin (n j)) Unit
    (canonicalCoefficientJetArrays
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y)
      (fun (_ : Fin m) (_ : Unit) => (∅ : Finset Empty)) sample j) ()

end Erdos3.VectorPolynomial

end

section

namespace Erdos3
open scoped BigOperators Classical

namespace VectorPolynomial
open Module
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "sides" => allocatedPrincipalSides B U basis S

variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S))

theorem allocatedPrincipalSides_not_short (a : Active)
    (p : B a.val × Fin (layerSamplerDegree I n a.val)) :
    sides ⟨a.val,p⟩ = S.value := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · rfl
  · exact allocatedPrincipalSides_active B U basis S j i (Nat.lt_of_not_ge ha) p.1 p.2

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSlicedGridGeometryBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : Fin (n j))

local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))

noncomputable def allocatedSlicedGridHeightCutoff (T : ℕ) : ℕ :=
  T ^ (layerTailDegree m + 1) + denom * 2 ^ degree * T ^ degree + 2 * denom

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastInactiveAffineIntervalFixedResidueSite
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

attribute [local instance] ScalarSiteExpansion.termFinite

noncomputable def forecastInactiveFixedOutput
    (selected : A → Σ j : Fin m, Fin (n j))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S)) :
    A → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ := fun a =>
  boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
    (allocatedPhysicalCubeDirections B U b S x y) ((selected a).1.val + 1)
    (fun t : (Finset.univ : Finset (Finset Empty)) => (t : Finset Empty)) *ᵥ c a

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BufferedSampledCurrentGradePhase
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def majorPhasePlateauKernel (d : ℕ) : PatchKernel d where
  value x := linearCutoff (1 / 8) (1 / 8) ‖x‖
  nonneg x := (linearCutoff_range _ _ _).1
  le_one x := (linearCutoff_range _ _ _).2
  support x hx i := by
    have hnorm : ‖x‖ < (1 / 4 : ℝ) := by
      by_contra h
      apply hx
      apply linearCutoff_eq_zero
      norm_num at h ⊢
      exact h
    have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    exact hi.trans hnorm.le
  lip := 8
  lipschitz := by
    have h := (linearCutoff_lipschitz (1 / 8) (1 / 8) (by norm_num)).comp
      (lipschitzWith_one_norm : LipschitzWith 1 (fun x : Fin d → ℝ => ‖x‖))
    simpa only [Function.comp_def, one_div, inv_inv, mul_one] using h

@[simp] theorem majorPhasePlateauKernel_lip (d : ℕ) :
    (majorPhasePlateauKernel d).lip = 8 := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedCappedContinuousSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {A : Type*} [Fintype A]

noncomputable def forecastInactiveSlicedSiteNumerics
    (selected : A → Σ j : Fin m, Fin (n j)) (q Hchild : ℕ)
    (δ P Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0) : Prop :=
    let degree := fun a => (selected a).1.val + 1
    let denom := fun a => inactiveDenominator (principalProfileSize (R (selected a).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
    let torus := fun a => blockTorusFactor (Fintype.card Empty) (degree a)
      (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
    let V := fun a => (torus a : ℝ) * ((denom a : ℝ) * 2 ^ degree a) / δ ^ degree a
    let cap := fun a => uniformSpectrumAbsoluteCap (selected a).1.val 1 (degree a) P (V a) (V a)
    let cutoff := fun a => max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
      (selected a).1 (selected a).2 (Nat.ceil ((q : ℝ) / δ)))
      (denom a * 2 ^ degree a * Hchild ^ degree a + 2 * denom a)
    let R0 := fun a => (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (degree a)) : ℝ) *
      R (selected a).1
    let ε := uniformProductAccuracy (Fintype.card A) Cactual δout / 2
    let ζ := fun a => uniformBlockRetainedBias (selected a).1.val 1 (degree a) P (V a) (V a) ε
    let freq := fun a => Real.toNNReal (uniformScaledRetainedFrequencyBound (selected a).1.val 1 P (V a) (ζ a))
    (∀ a, max (cutoff a : ℝ) (cap a) ≤ Cactual) ∧
    (∀ a, R0 a + 1 / 4 ≤ Real.exp Q) ∧
    (∀ a, (ε / (cap a + 1))⁻¹ ≤ Real.exp Q) ∧
    (∀ a, (CircleFourier.characterLipConstant * freq a + 4 : ℝ≥0) ≤ Real.exp Q) ∧
    (∀ a, (cutoff a : ℝ) ≤ Real.exp Q) ∧
    (∀ a, (2 * (cutoff a : ℝ≥0) ^ 2 * (cutoff a : ℝ≥0) : ℝ≥0) ≤ Real.exp Q) ∧
    ε⁻¹ ≤ Real.exp Q ∧
    (∀ a, max ((uniformSpectrumSizeConstant (selected a).1.val 1 (degree a) P (V a) (V a) /
      ε ^ max (majorArcSpectrumExponent (selected a).1.val 1)
        (majorArcLengthExponent (selected a).1.val * degree a)) * Real.exp (4 * Q + 8))
      (Real.exp (4 * Q + 8)) ≤ Nt) ∧
    (∀ a, max (uniformScaledRetainedDenominatorBound (selected a).1.val 1 (degree a) P
      (V a) (V a) (ζ a)) 1 ≤ Vt) ∧
    (∀ a, max (cap a * Real.exp (4 * Q + 8 + Q)) (Real.exp (4 * Q + 8 + Q)) ≤ Ct) ∧
    (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4 : ℝ≥0) ≤ Lt ∧
    (∀ a, R0 a + 1 / 4 ≤ Ht)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastNativePullbackBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal BigOperators

variable {X : Type*} [Fintype X]

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (P : LayerSamplerAxis I n → Prop)
variable {A : Type*} [Fintype A] (selected : A → Σ j : Fin m, Fin (n j))
variable (R : Fin m → ℝ)

def forecastNormalizedActiveCoordinates (v : LayerSamplerAxis I n → ℝ) :
    (Σ _a : {a : LayerSamplerAxis I n // ¬P a}, Unit) → ℝ := fun a => v a.1.val

end Erdos3.VectorPolynomial

end

end OAI
end


