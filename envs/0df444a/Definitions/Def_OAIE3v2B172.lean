-- Prove2me | Definitions.Def_OAIE3v2B172
-- name    : OAIE3v2B172
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:38:01.38836+00:00
-- url     : https://prove2.me/theorems/cb9146c7-ed9b-424e-a72a-cf18f6db8b55
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 174 of 311
-- statement:
--   Definitions bundle 174 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B151`, `OAIE3v2B152`, `OAIE3v2B157`, `OAIE3v2B158`, `OAIE3v2B159` of this split.
--
--   Modules: `Dynamics/NormalizedNativeUniformBudget.lean`, `Dynamics/ReducedTwistedTranslationBudget.lean`, `Dynamics/TranslationMajorDetectedPotential.lean`, `Dynamics/TranslationMajorDimensionBudget.lean`, `Estimates/AntisymmetricPartitionApproximation.lean`, `Estimates/CommonCoefficientFourAnnihilators.lean`, `Estimates/DetectedTranslationNormalizedLogBounds.lean`, `Estimates/HomogeneousQuotientSymbolLiftBounds.lean`, `Estimates/LowTaggedGradedSpace.lean`, `Estimates/NativeRefilteredSymbolConditions.lean`, `Estimates/NativeSampleModelFamily.lean`, `Estimates/NativeSubspaceFreeModel.lean`, `Estimates/NormalizedNativeFamilyMonotone.lean`, `Estimates/QuadraticAntisymmetricCorrelation.lean`, `Estimates/RealAnnihilatorCorrections.lean`, `Estimates/ReducedTranslationMajorTwistedVerticalSelection.lean`, `Estimates/SampledNativeModel.lean`, `Estimates/StepOneSymbolLinearPart.lean`, `Estimates/StrongRefiltrationReconstruction.lean`, `Estimates/TranslationMajorCorrelationDecomposition.lean`, `Fourier/NormalizedTwistLocalizedFourierSelection.lean`, `Fourier/WeightedTranslationTwistedCentralFrequency.lean`, `Geometry/NativeCorrelationCoordinates.lean`, `Lattices/RetainedPhysicalCRT.lean`, `Lattices/SpatialAffineFullMass.lean`, `Linear/ActualMarkedSlowKernelCells.lean`, `Linear/FrozenDiagramKernelInvariance.lean`, `Linear/InducedUnitRankFamily.lean`, `Linear/RealFourAnnihilatorKernel.lean`, `Nilpotent/CanonicalReducedMajorTwistedNiltest.lean`, `Nilpotent/LocalMajorDenseSliceNiltest.lean`, `Nilpotent/NiltestOrbitOne.lean`, `Nilpotent/WeightedTranslationTwistedNiltest.lean`, `Polynomial/MajorPhaseVectorDecomposition.lean`, `Polynomial/NativePolynomialOrbitConstruction.lean`, `Polynomial/NormalizedFrozenPolynomialMass.lean`, `Polynomial/OrdinaryPolynomialPhaseAffineInverse.lean`, `Polynomial/PolynomialTagRestrictionBudget.lean`, `Polynomial/ProductPolynomialMaps.lean`, `Polynomial/RefilteredPolynomialProjection.lean`, `Polynomial/RetainedPhysicalLowerDegree.lean`, `Probability/AllocatedMixedLiftNormalizedMass.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B151
import Definitions.Def_OAIE3v2B152
import Definitions.Def_OAIE3v2B157
import Definitions.Def_OAIE3v2B158
import Definitions.Def_OAIE3v2B159

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LocalMajorDenseSliceNiltest
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

open _root_.MvPolynomial PolynomialTranslationLie
open scoped TensorProduct NNReal

attribute [local instance] OAI.Erdos3.OrdinaryPolynomialPhase.phaseBasisFintype
noncomputable abbrev nilmanifold (s : ℕ) :=
  weightedTranslationNilmanifold weight s weight_pos (weight_le s)

theorem nilmanifold_geometry (s : ℕ) : (nilmanifold s).GeometryComplexityLE (budget s) := by
  apply RationalFilteredNilmanifold.GeometryComplexityLE.mono _
    (weightedTranslationNilmanifold_complexity_budget weight s weight_pos (weight_le s))
  simpa only [Fintype.card_fin, budget] using le_max_left
    (((0 + (0 + 1)^s + s.factorial + 2*s + 1 : ℕ) : ℝ))
    (Real.log (3 + (2 * bufferedTranslationTermLip weight s
      (localTentKernel 0 8 (by decide)) 0 : ℝ≥0)))

theorem exists_phase_orbit {U : Type*} (s : ℕ) (hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) :
    ∃ q : (nilmanifold s).filtration.realification.PolynomialOrbit (fun _ : U => 1),
      ∀ u : U → ℝ,
        bchRealTranslationHom weight s (weight_le s)
          ((nilmanifold s).filtration.realification.polynomialOrbitRealEval
            (fun _ : U => 1) u q) = ⟨0, C (eval u P)⟩ := by
  have hslot : ∀ u : U → ℝ,
      specializeMajorParameters (RingHom.id ℝ) (rename (Sum.inl : U → U ⊕ Fin 0) P) u ∈
        weightedSupportLT weight s := by
    intro u α _
    have hα : α = 0 := Subsingleton.elim _ _
    change Finsupp.weight weight α < s
    simpa only [hα, map_zero] using hs
  obtain ⟨q, hq⟩ := exists_translation_coordinate_polynomialOrbit weight s weight_pos
    (weight_le s) (fun _ : Fin 0 => (0 : MvPolynomial U ℝ)) (fun i => Fin.elim0 i)
    (rename Sum.inl P)
    (majorParameterRename_degree (fun _ : U => 1) weight
      ((mem_weightedSupportLE_one_iff P s).mpr hP)) hslot
  refine ⟨q, fun u => ?_⟩
  change bchRealTranslationHom weight s (weight_le s)
    ((weightedFiltration weight s (weight_le s)).realification.polynomialOrbitRealEval
      (fun _ : U => 1) u q) = _
  rw [hq u, specialize_rename]
  rfl

end Erdos3.OrdinaryPolynomialPhase

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RefilteredPolynomialProjection
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

theorem realPolynomialGroupMap_value
    (g : (F.realification.adaptedPolynomialFiltration w).Group) (x : σ → ℝ) :
    G.adaptedPolynomialRealValueHom w x (F.realPolynomialGroupMap G φ hφ w g) =
      realificationMap (hnil := F.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) φ
        (F.adaptedPolynomialRealValueHom w x g) := by
  apply NilpotentLieBCHGroup.ext
  exact eval₂_map (realificationLieHom φ).toLinearMap x
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))

theorem realPolynomialGroupMap_constant (c : F.realification.Group) :
    F.realPolynomialGroupMap G φ hφ w (F.realification.adaptedConstantGroupHom w c) =
      G.realification.adaptedConstantGroupHom w
        (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
          (hM := G.lowerCentralSeries_eq_bot) φ c) := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  change VectorPolynomial.map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ)
    (monomial 0 c.coord) = monomial 0 (realificationLieHom φ c.coord)
  exact map_monomial _ _ _

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StrongRefiltrationReconstruction
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (w : σ → ℕ)

theorem homogeneousGradedProjection_image_eq
    (W : LieSubalgebra ℚ F.AssociatedGraded) :
    (W.map (F.associatedGradedMap G φ hφ)).map
      (G.homogeneousAssociatedGradedEquiv c ν hG hc).toLieHom =
      W.map (F.homogeneousGradedProjection G c ν hG hc φ hφ) := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.WeightedTranslationTwistedNiltest
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)

variable [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

theorem weightedTranslationTwistedNiltest_complexity {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (A K : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ A)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r))
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) {p : ℝ}
    (hgeometry : (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p)
    (hbound : Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ A K : ℝ≥0)) ≤ p) :
    (weightedTranslationTwistedNiltest w d hw hwd M hM ω hd Ψ D₀ A K hdegree hD T hT hLip q).ComplexityLE p := by
  refine ⟨hgeometry, ?_⟩
  simpa only [weightedTranslationTwistedNiltest, NNReal.coe_one,
    show (2 : ℝ) + 1 = 3 by norm_num] using hbound

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.WeightedTranslationTwistedCentralFrequency
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_vertical_decomposition_preserving_bounds_and_characters (T : D.Niltest w)
    {p rho : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p) (hrho : 0 < rho)
    (hrhop : rho⁻¹ ≤ Real.exp p) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (eta : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest w),
      (Fintype.card J : ℝ) ≤ Real.exp (verticalDecompositionBudget p) ∧
      (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ j, (U j).ComplexityLE p ∧ (U j).orbit = T.orbit ∧
        (U j).normBound = T.normBound ∧ (U j).lipBound = T.lipBound) ∧
      (∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
        (U j).observable (z • x) =
          character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x) ∧
      (∀ j, (∃ x, (U j).observable x ≠ 0) → ∀ z : D.RealGroup,
        z ∈ D.filtration.realification.subgroup s → z ∈ D.realLattice →
          ∃ n : ℤ, realifyFunctional (eta j) z.coord = n) ∧
      (∀ (z : D.RealGroup) (c : ℂ), (∀ x, T.observable (z • x) = c * T.observable x) →
        ∀ j x, (U j).observable (z • x) = c * (U j).observable x) ∧
      (∀ x, ‖(∑ j, (U j).observable x) - T.observable x‖ ≤ rho) ∧
      ∀ x : σ → ℤ, ‖(∑ j, (U j).eval x) - T.eval x‖ ≤ rho := by
  let := D.metricSpace
  have hK : (T.lipBound : ℝ) ≤ Real.exp p := by
    have h := observable_budget hT
    have hB := T.normBound.coe_nonneg
    linarith
  obtain ⟨J, inst, eta, v, hcard, hheight, hv, hchar, hpres, herr⟩ :=
    D.exists_controlled_vertical_decomposition hp hT.1 T.observable T.lipBound T.normBound
      T.lipschitz T.norm_le hK rho hrho hrhop
  let U : J → D.Niltest w := fun j =>
    { orbit := T.orbit
      observable := v j
      normBound := T.normBound
      lipBound := T.lipBound
      norm_le := (hv j).2
      lipschitz := (hv j).1 }
  refine ⟨J, inst, eta, U, hcard, hheight, fun _ => ⟨hT, rfl, rfl, rfl⟩, hchar, ?_, hpres, herr, ?_⟩
  · intro j hne z hz hGamma
    exact vertical_frequency_integral_on_lattice D.filtration D.realLattice (eta j) (v j)
      (hchar j) hne z hz hGamma
  · intro x
    exact herr (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x T.orbit))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_native_vertical_pair_preserving_characters_on_finset
    {X σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
    (D : RationalFilteredNilmanifold L s d) (D' : RationalFilteredNilmanifold M s e)
    {w : σ → ℕ} (Q : D.Niltest w) (R : D'.Niltest w)
    {p q delta rho eta : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hdelta : 0 < delta)
    (hrho : 0 < rho) (heta : 0 < eta) (hrhop : rho⁻¹ ≤ Real.exp p) (hetaq : eta⁻¹ ≤ Real.exp q)
    (hQc : Q.ComplexityLE p) (hRc : R.ComplexityLE q)
    (hQcap : (Q.normBound : ℝ) ≤ 1) (hRcap : (R.normBound : ℝ) ≤ 1)
    (hsmall : rho + Real.exp (verticalDecompositionBudget p) * eta ≤ delta / 2)
    (B : Finset X) (hB : B.Nonempty) (sample : X → σ → ℤ) (U : X → ℂ)
    (hU : ∀ x ∈ B, ‖U x‖ ≤ 1)
    (hcorr : delta ≤ ‖𝔼 x ∈ B, U x * Q.eval (sample x) * R.eval (sample x)‖) :
    ∃ (freq : L →ₗ[ℚ] ℚ) (freq' : M →ₗ[ℚ] ℚ) (V : D.Niltest w) (W : D'.Niltest w),
      V.ComplexityLE p ∧ V.orbit = Q.orbit ∧ V.normBound = Q.normBound ∧
      W.ComplexityLE q ∧ W.orbit = R.orbit ∧ W.normBound = R.normBound ∧
      (∀ i, rationalLogHeight (freq (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ i, rationalLogHeight (freq' (D'.basis i)) ≤ verticalDecompositionBudget q) ∧
      (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        V.observable (z • x) = character ((realifyFunctional freq z.coord : ℝ) : CircleFourier.Circle) *
          V.observable x) ∧
      (∀ z, z ∈ D'.filtration.realification.subgroup s → ∀ x,
        W.observable (z • x) = character ((realifyFunctional freq' z.coord : ℝ) : CircleFourier.Circle) *
          W.observable x) ∧
      (∀ (z : D.RealGroup) (c : ℂ),
        (∀ x, Q.observable (z • x) = c * Q.observable x) →
          ∀ x, V.observable (z • x) = c * V.observable x) ∧
      (∀ (z : D'.RealGroup) (c : ℂ),
        (∀ x, R.observable (z • x) = c * R.observable x) →
          ∀ x, W.observable (z • x) = c * W.observable x) ∧
      (∃ x, V.observable x ≠ 0) ∧ (∃ x, W.observable x ≠ 0) ∧
      (delta / 2) / (Real.exp (verticalDecompositionBudget p) * Real.exp (verticalDecompositionBudget q)) ≤
        ‖𝔼 x ∈ B, U x * V.eval (sample x) * W.eval (sample x)‖ := by
  obtain ⟨I, instI, freqV, V, hI, hheightV, hcertV, hvertV, _, hpresV, _, happroxV⟩ :=
    Q.exists_vertical_decomposition_preserving_bounds_and_characters hp hQc hrho hrhop
  let := instI
  obtain ⟨J, instJ, freqW, W, hJ, hheightW, hcertW, hvertW, _, hpresW, _, happroxW⟩ :=
    R.exists_vertical_decomposition_preserving_bounds_and_characters hq hRc heta hetaq
  let := instJ
  obtain ⟨i, j, hbias⟩ := exists_correlating_components_on_finset B hB U
    (fun x => Q.eval (sample x)) (fun x => R.eval (sample x))
    (fun i x => (V i).eval (sample x)) (fun j x => (W j).eval (sample x))
    hdelta (Real.exp_pos _) (Real.exp_pos _) hrho.le heta.le hI hJ hU
    (fun x _ => (R.norm_eval_le (sample x)).trans hRcap)
    (fun i x _ => ((V i).norm_eval_le (sample x)).trans (by rw [(hcertV i).2.2.1]; exact hQcap))
    (fun x _ => by simpa only [norm_sub_rev] using happroxV (sample x))
    (fun x _ => by simpa only [norm_sub_rev] using happroxW (sample x)) hsmall hcorr
  have hbiaspos : 0 < ‖𝔼 x ∈ B, U x * (V i).eval (sample x) * (W j).eval (sample x)‖ :=
    lt_of_lt_of_le (div_pos (div_pos hdelta (by norm_num))
      (mul_pos (Real.exp_pos _) (Real.exp_pos _))) hbias
  have hVne : ∃ x, (V i).observable x ≠ 0 := by
    by_contra! hzero
    have heval : ∀ x, (V i).eval (sample x) = 0 := fun x => hzero _
    simp [heval] at hbiaspos
  have hWne : ∃ x, (W j).observable x ≠ 0 := by
    by_contra! hzero
    have heval : ∀ x, (W j).eval (sample x) = 0 := fun x => hzero _
    simp [heval] at hbiaspos
  exact ⟨freqV i, freqW j, V i, W j, (hcertV i).1, (hcertV i).2.1, (hcertV i).2.2.1,
    (hcertW j).1, (hcertW j).2.1, (hcertW j).2.2.1, hheightV i, hheightW j, hvertV i, hvertW j,
    (fun z c hz => hpresV z c hz i), (fun z c hz => hpresW z c hz j), hVne, hWne, hbias⟩

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_native_vertical_pair_preserving_characters_power :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X σ L M : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (D : RationalFilteredNilmanifold L s d) (D' : RationalFilteredNilmanifold M s e)
      {w : σ → ℕ} (Q : D.Niltest w) (R : D'.Niltest w) (p : ℝ), 0 ≤ p →
      Q.ComplexityLE p → R.ComplexityLE p →
      (Q.normBound : ℝ) ≤ 1 → (R.normBound : ℝ) ≤ 1 →
      ∀ (B : Finset X), B.Nonempty → ∀ (sample : X → σ → ℤ) (U : X → ℂ),
      (∀ x ∈ B, ‖U x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ B, U x * Q.eval (sample x) * R.eval (sample x)‖ →
      ∃ (freq : L →ₗ[ℚ] ℚ) (freq' : M →ₗ[ℚ] ℚ) (V : D.Niltest w) (W : D'.Niltest w),
        V.ComplexityLE ((p + C) ^ C) ∧ V.orbit = Q.orbit ∧ V.normBound = Q.normBound ∧
        W.ComplexityLE ((p + C) ^ C) ∧ W.orbit = R.orbit ∧ W.normBound = R.normBound ∧
        (∀ i, rationalLogHeight (freq (D.basis i)) ≤ (p + C) ^ C) ∧
        (∀ i, rationalLogHeight (freq' (D'.basis i)) ≤ (p + C) ^ C) ∧
        (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          V.observable (z • x) = character ((realifyFunctional freq z.coord : ℝ) : CircleFourier.Circle) *
            V.observable x) ∧
        (∀ z, z ∈ D'.filtration.realification.subgroup s → ∀ x,
          W.observable (z • x) = character ((realifyFunctional freq' z.coord : ℝ) : CircleFourier.Circle) *
            W.observable x) ∧
        (∀ (z : D.RealGroup) (c : ℂ),
          (∀ x, Q.observable (z • x) = c * Q.observable x) →
            ∀ x, V.observable (z • x) = c * V.observable x) ∧
        (∀ (z : D'.RealGroup) (c : ℂ),
          (∀ x, R.observable (z • x) = c * R.observable x) →
            ∀ x, W.observable (z • x) = c * W.observable x) ∧
        (∃ x, V.observable x ≠ 0) ∧ (∃ x, W.observable x ≠ 0) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 x ∈ B, U x * V.eval (sample x) * W.eval (sample x)‖ := by
  obtain ⟨C, hC, hprecision⟩ := exists_vertical_pair_precision
  refine ⟨C, hC, ?_⟩
  intro X σ L M _ _ _ _ s d e _ _ _ _ _ _ _ _ D D' w Q R p hp hQ hR hQcap hRcap
    B hB sample U hU hcorr
  obtain ⟨q, r, rho, eta, hpq, hpr, hqC, hrC, hVq, hVr, hrho, heta, hrhoq, hetar, hsmall, hloss⟩ :=
    hprecision p hp
  obtain ⟨freq, freq', V, W, hVc, hVo, hVn, hWc, hWo, hWn, hVheight, hWheight,
      hvertV, hvertW, hpresV, hpresW, hVne, hWne, hbias⟩ :=
    exists_native_vertical_pair_preserving_characters_on_finset D D' Q R
      (hp.trans hpq) (hp.trans hpr) (Real.exp_pos _) hrho heta hrhoq hetar
      (hQ.mono hpq) (hR.mono hpr) hQcap hRcap hsmall B hB sample U hU hcorr
  exact ⟨freq, freq', V, W, hVc.mono hqC, hVo, hVn, hWc.mono hrC, hWo, hWn,
    fun i => (hVheight i).trans hVq, fun i => (hWheight i).trans hVr,
    hvertV, hvertW, hpresV, hpresW, hVne, hWne, hloss.trans hbias⟩

end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial CircleFourier
open scoped TensorProduct

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

theorem weightedTranslation_frequency_one_of_central
    {σ : Type*} [Fintype σ] (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
    (Γ : Subgroup (weightedFiltration w d hwd).realification.Group)
    (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
    (f : (weightedFiltration w d hwd).realification.Group ⧸ Γ → ℂ)
    (hvert : ∀ z ∈ (weightedFiltration w d hwd).realification.subgroup d, ∀ x,
      f (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * f x)
    (hne : ∃ x, f x ≠ 0)
    (hline : ∀ t x, f (centralRealLine w d hw hd hwd t • x) =
      (Real.fourierChar t : ℂ) * f x) :
    η (centralRationalElement w d hd 1) = 1 := by
  apply vertical_frequency_eq_one_of_real_line (weightedFiltration w d hwd) Γ
    η f hvert hne _ (centralRationalElement_mem_top w d hd hwd 1)
  intro t x
  have he : (⟨t ⊗ₜ[ℚ] centralRationalElement w d hd 1⟩ :
      (weightedFiltration w d hwd).realification.Group) = centralRealLine w d hw hd hwd t := by
    apply NilpotentLieBCHGroup.ext
    exact (centralRealLine_coord w d hw hd hwd t).symm
  rw [he, central_character_eq_fourierChar]
  exact hline t x

theorem weightedTranslation_selected_frequency_one
    (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ)
    (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
    (f : (weightedTranslationNilmanifold w d hw hwd).Space → ℂ)
    (hvert : ∀ z ∈ (weightedFiltration w d hwd).realification.subgroup d, ∀ x,
      f (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * f x)
    (hne : ∃ x, f x ≠ 0)
    (hpres : ∀ (z : (weightedFiltration w d hwd).realification.Group) (c : ℂ),
      (∀ x, weightedTranslationBufferedObservable w d hw hwd Ψ D₀ (z • x) =
        c * weightedTranslationBufferedObservable w d hw hwd Ψ D₀ x) →
      ∀ x, f (z • x) = c * f x) :
    η (centralRationalElement w d hd 1) = 1 := by
  apply vertical_frequency_eq_one_of_real_line
    (weightedFiltration w d hwd) (weightedTranslationNilmanifold w d hw hwd).realLattice
    η f hvert hne _ (centralRationalElement_mem_top w d hd hwd 1)
  intro t x
  have he : (⟨t ⊗ₜ[ℚ] centralRationalElement w d hd 1⟩ :
      (weightedFiltration w d hwd).realification.Group) = centralRealLine w d hw hd hwd t := by
    apply NilpotentLieBCHGroup.ext
    exact (centralRealLine_coord w d hw hd hwd t).symm
  rw [he, central_character_eq_fourierChar]
  apply hpres
  intro y
  rw [weightedTranslationBufferedObservable_central w d hw hd hwd]
  exact mul_comm _ _

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial CircleFourier

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]
    (M : ℕ) (hM : 0 < M)

theorem weightedTranslationTwistedObservable_central
    (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ) (t : ℝ)
    (x : (weightedTranslationResidueNilmanifold w d hw hwd M hM).Space) :
    weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T
      (centralRealLine w d hw hd hwd t • x) =
      weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T x *
        (Real.fourierChar t : ℂ) := by
  induction x using Quotient.inductionOn with
  | h g =>
    change weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T
      (QuotientGroup.mk (centralRealLine w d hw hd hwd t * g)) = _
    rw [(centralRealLine_commute w d hw hd hwd t g).eq]
    simp only [weightedTranslationTwistedObservable_mk, map_mul, centralRealLine_map]
    exact twistedBufferedTranslationPhase_central M Ψ D₀ T _ t

theorem weightedTranslation_twisted_selected_frequency_one
    (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
    (f : (weightedTranslationResidueNilmanifold w d hw hwd M hM).Space → ℂ)
    (hvert : ∀ z ∈ (weightedFiltration w d hwd).realification.subgroup d, ∀ x,
      f (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * f x)
    (hne : ∃ x, f x ≠ 0)
    (hpres : ∀ (z : (weightedFiltration w d hwd).realification.Group) (c : ℂ),
      (∀ x, weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T (z • x) =
        c * weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T x) →
      ∀ x, f (z • x) = c * f x) :
    η (centralRationalElement w d hd 1) = 1 := by
  apply weightedTranslation_frequency_one_of_central w d hw hd hwd
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).realLattice η f hvert hne
  intro t x
  apply hpres
  intro y
  rw [weightedTranslationTwistedObservable_central w d hw hd hwd M hM]
  exact mul_comm _ _

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SampledNativeModel
namespace OAI

section

namespace Erdos3

open scoped TensorProduct Pointwise BigOperators

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {σ X : Type*} {w : σ → ℕ} {degree : ℕ} {p : ℝ}
  {sample : X → σ → ℤ} {f : X → ℂ}

noncomputable def NativeSampleModel.constOne (hp : 2 ≤ p) :
    NativeSampleModel w degree p sample (fun _ => 1) where
  L := RationalTorus.Algebra 0
  dim := 0
  model := RationalTorus.trivialNilmanifold degree
  test := RationalFilteredNilmanifold.Niltest.const (RationalTorus.trivialNilmanifold degree) w 1
  norm := by simp [RationalFilteredNilmanifold.Niltest.const]
  complexity := RationalTorus.trivialNilmanifold_const_one_complexity degree w hp
  eval _ := rfl

noncomputable def NativeSampleCorrelation.ofMean {S : Finset X} (hp : 2 ≤ p)
    (hmean : Real.exp (-p) ≤ ‖𝔼 x ∈ S, f x‖) :
    NativeSampleCorrelation w degree p S sample f where
  L := RationalTorus.Algebra 0
  dim := 0
  model := RationalTorus.trivialNilmanifold degree
  test := RationalFilteredNilmanifold.Niltest.const (RationalTorus.trivialNilmanifold degree) w 1
  complexity := RationalTorus.trivialNilmanifold_const_one_complexity degree w hp
  correlation := by simpa only [RationalFilteredNilmanifold.Niltest.eval_const, star_one, mul_one] using hmean

noncomputable def NativeSampleModel.smul (F : NativeSampleModel w degree p sample f)
    (c : ℂ) (hc : ‖c‖ ≤ 1) : NativeSampleModel w degree p sample (c • f) where
  L := F.L
  dim := F.dim
  model := F.model
  test := F.test.scaleComplex c
  norm := (F.test.scaleComplex_norm hc).trans F.norm
  complexity := F.test.scaleComplex_complexity hc F.complexity
  eval x := by change c * f x = c * F.test.eval (sample x); rw [F.eval]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativePolynomialOrbitConstruction
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

namespace NativePolynomialOrbitFactors

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}
  {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
  {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p q : ℝ}
  (R : NativePolynomialOrbitFactors D g eta A p)

noncomputable def mono (hpq : p ≤ q) (hA : ∀ i, 0 < A i) :
    NativePolynomialOrbitFactors D g eta A q :=
  { R with
    basis_height := fun i j => (R.basis_height i j).trans hpq
    generator_height := fun i j => (R.generator_height i j).trans hpq
    denominator_bound := R.denominator_bound.trans (Real.exp_le_exp.mpr hpq)
    slow_bound := fun α i => (R.slow_bound α i).trans
      (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hpq) (monomialScale_pos A hA α).le) }

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HomogeneousQuotientSymbolLiftBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {σ R S V W : Type*} [CommRing R] [CommRing S]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem weightedHomogeneousPart_tmul (w : σ → ℕ) (d : ℕ)
    (P : MvPolynomial σ R) (v : V) :
    weightedHomogeneousPart w d (P ⊗ₜ[R] v) =
      MvPolynomial.weightedHomogeneousComponent w d P ⊗ₜ[R] v := rfl

theorem coefficients_weightedHomogeneousPart (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) :
    coefficients (weightedHomogeneousPart w d p) α =
      if Finsupp.weight w α = d then coefficients p α else 0 := by
  classical
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul polynomial vector =>
    rw [weightedHomogeneousPart_tmul, coefficients_tmul,
      MvPolynomial.coeff_weightedHomogeneousComponent, coefficients_tmul]
    split <;> simp_all
  | add first second hfirst hsecond =>
    simp only [map_add, Finsupp.add_apply, hfirst, hsecond]
    split <;> simp

theorem weightedHomogeneousPart_monomial (w : σ → ℕ) (d : ℕ)
    (α : σ →₀ ℕ) (v : V) :
    weightedHomogeneousPart w d (monomial (R := R) α v) =
      if Finsupp.weight w α = d then monomial α v else 0 := by
  classical
  apply coefficients.injective
  ext β
  split <;> rename_i hd
  all_goals rw [coefficients_weightedHomogeneousPart]
  by_cases h : α = β
  · subst β
    simp [hd]
  · simp [Ne.symm h]
  by_cases h : α = β
  · subst β
    simp [hd]
  · simp [Ne.symm h]

theorem weightedHomogeneousPart_homogeneous (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) (hα : Finsupp.weight w α ≠ d) :
    coefficients (weightedHomogeneousPart w d p) α = 0 := by
  rw [coefficients_weightedHomogeneousPart, if_neg hα]

theorem weightedHomogeneousPart_eq_self {w : σ → ℕ} {d : ℕ}
    {p : VectorPolynomial σ R V}
    (hp : ∀ α, Finsupp.weight w α ≠ d → coefficients p α = 0) :
    weightedHomogeneousPart w d p = p := by
  apply coefficients.injective
  ext α
  rw [coefficients_weightedHomogeneousPart]
  split
  · rfl
  · exact (hp α ‹_›).symm

theorem coordinate_weightedHomogeneousPart (f : V →+ S) (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ R V) :
    coordinate f (weightedHomogeneousPart w d p) =
      MvPolynomial.weightedHomogeneousComponent w d (coordinate f p) := by
  classical
  ext α
  simp only [coeff_coordinate, coefficients_weightedHomogeneousPart,
    MvPolynomial.coeff_weightedHomogeneousComponent]
  split <;> simp

theorem eval₂_weightedHomogeneousPart [Algebra R S] [Module S V] [IsScalarTower R S V]
    (w : σ → ℕ) (d : ℕ) (x : σ → S) (p : VectorPolynomial σ R V) :
    eval₂ x (weightedHomogeneousPart w d p) =
      ∑ α ∈ (coefficients p).support,
        if Finsupp.weight w α = d then
          (α.prod fun i n => x i ^ n) • coefficients p α else 0 := by
  classical
  conv_lhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, weightedHomogeneousPart_monomial]
  apply Finset.sum_congr rfl
  intro α _
  split <;> simp [eval₂_monomial]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {σ V : Type*} [AddCommGroup V] [Module ℚ V] [Module ℝ V]
  [IsScalarTower ℚ ℝ V]

noncomputable def weightedRadialPolynomial (w : σ → ℕ)
    (p : VectorPolynomial σ ℚ V) (x : σ → ℝ) : VectorPolynomial Unit ℚ V :=
  ∑ α ∈ (coefficients p).support,
    monomial (Finsupp.single () (Finsupp.weight w α))
      ((α.prod fun i n => x i ^ n) • coefficients p α)

theorem weightedRadialPolynomial_eval (w : σ → ℕ)
    (p : VectorPolynomial σ ℚ V) (x : σ → ℝ) (r : ℚ) :
    eval (fun _ : Unit => r) (weightedRadialPolynomial w p x) =
      eval₂ (fun i => (r : ℝ) ^ w i * x i) p := by
  classical
  unfold weightedRadialPolynomial
  conv_rhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, eval_monomial, eval₂_monomial]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finsupp.prod_single_index (by simp), weighted_monomial_dilation]
  rw [mul_smul, ← Rat.cast_pow, ← IsScalarTower.algebraMap_smul ℝ (r ^ Finsupp.weight w α)]
  rfl

omit [IsScalarTower ℚ ℝ V] in
theorem weightedRadialPolynomial_coefficient (w : σ → ℕ)
    (p : VectorPolynomial σ ℚ V) (x : σ → ℝ) (d : ℕ) :
    coefficients (weightedRadialPolynomial w p x) (Finsupp.single () d) =
      ∑ α ∈ (coefficients p).support,
        if Finsupp.weight w α = d then
          (α.prod fun i n => x i ^ n) • coefficients p α else 0 := by
  classical
  simp only [weightedRadialPolynomial, map_sum, Finsupp.finsetSum_apply,
    coefficients_monomial, Finsupp.single_apply, (Finsupp.single_injective ()).eq_iff]

theorem weightedRadialPolynomial_eq_zero (w : σ → ℕ)
    (p : VectorPolynomial σ ℚ V) (x : σ → ℝ)
    (hp : ∀ r : ℚ, eval₂ (fun i => (r : ℝ) ^ w i * x i) p = 0) :
    weightedRadialPolynomial w p x = 0 := by
  apply eq_zero_of_eval_zero
  intro r
  have hr : r = fun _ : Unit => r () := by funext i; cases i; rfl
  rw [hr, weightedRadialPolynomial_eval]
  exact hp (r ())

theorem eval₂_weightedHomogeneousPart_eq_zero_on (w : σ → ℕ)
    (p : VectorPolynomial σ ℚ V) (K : Set (σ → ℝ))
    (hK : ∀ x ∈ K, ∀ r : ℚ, (fun i => (r : ℝ) ^ w i * x i) ∈ K)
    (hp : ∀ x ∈ K, eval₂ x p = 0) (d : ℕ) (x : σ → ℝ) (hx : x ∈ K) :
    eval₂ x (weightedHomogeneousPart w d p) = 0 := by
  have hz := weightedRadialPolynomial_eq_zero w p x (fun r => hp _ (hK x hx r))
  have hc := congrArg (fun q : VectorPolynomial Unit ℚ V =>
    coefficients q (Finsupp.single () d)) hz
  rw [eval₂_weightedHomogeneousPart]
  simpa only [weightedRadialPolynomial_coefficient, map_zero, Finsupp.zero_apply] using hc

theorem eval₂_weightedHomogeneousPart_eq_on (w : σ → ℕ)
    (p q : VectorPolynomial σ ℚ V) (K : Set (σ → ℝ))
    (hK : ∀ x ∈ K, ∀ r : ℚ, (fun i => (r : ℝ) ^ w i * x i) ∈ K)
    (hpq : ∀ x ∈ K, eval₂ x p = eval₂ x q)
    (d : ℕ) (x : σ → ℝ) (hx : x ∈ K) :
    eval₂ x (weightedHomogeneousPart w d p) =
      eval₂ x (weightedHomogeneousPart w d q) := by
  have hzero : ∀ y ∈ K, eval₂ y (p - q) = 0 := by
    intro y hy
    rw [map_sub, hpq y hy, sub_self]
  have h := eval₂_weightedHomogeneousPart_eq_zero_on w (p - q) K hK hzero d x hx
  exact sub_eq_zero.mp (by simpa only [map_sub] using h)

theorem eval₂_weightedHomogeneousPart_decomposition_on (w : σ → ℕ)
    (p a c : VectorPolynomial σ ℚ V) (K : Set (σ → ℝ))
    (hK : ∀ x ∈ K, ∀ r : ℚ, (fun i => (r : ℝ) ^ w i * x i) ∈ K)
    (d : ℕ) (hp : ∀ α, Finsupp.weight w α ≠ d → coefficients p α = 0)
    (hdecomp : ∀ x ∈ K, eval₂ x p = eval₂ x a + eval₂ x c)
    (x : σ → ℝ) (hx : x ∈ K) :
    eval₂ x p = eval₂ x (weightedHomogeneousPart w d a) +
      eval₂ x (weightedHomogeneousPart w d c) := by
  have heq : ∀ y ∈ K, eval₂ y p = eval₂ y (a + c) := by
    intro y hy
    simpa only [map_add] using hdecomp y hy
  have h := eval₂_weightedHomogeneousPart_eq_on w p (a + c) K hK heq d x hx
  simpa only [weightedHomogeneousPart_eq_self hp, map_add] using h

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NormalizedNativeUniformBudget
namespace OAI

section

namespace Erdos3
open scoped NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

noncomputable def NativeSampleModel.weaken {σ X : Type*} {w : σ → ℕ}
    {degree : ℕ} {p q : ℝ} {sample : X → σ → ℤ} {f : X → ℂ}
    (F : NativeSampleModel w degree p sample f) (hpq : p ≤ q) :
    NativeSampleModel w degree q sample f :=
  { F with complexity := F.complexity.mono hpq }

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ReducedTwistedTranslationBudget
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open scoped NNReal

theorem exists_weightedTranslationBuffered_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {m : ℕ} (w : Fin m → ℕ) (hw : ∀ i, 0 < w i)
      (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]
      (Ψ : PatchKernel m) (M : ℝ≥0) (p : ℝ),
      0 ≤ p → (m : ℝ) ≤ p → (Ψ.lip : ℝ) ≤ Real.exp p → (M : ℝ) ≤ Real.exp p →
      (weightedTranslationNilmanifold w d hw hwd).GeometryComplexityLE ((p + C) ^ C) ∧
      ((2 * bufferedTranslationTermLip w d Ψ M : ℝ≥0) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨C, hC, hbound⟩ := exists_weightedTranslationBuffered_scalar_budget d
  refine ⟨C, hC, ?_⟩
  intro m w hw hwd _ Ψ M p hp hm hΨ hM
  have hcard : Fintype.card (WeightedBasisIndex w d) ≤ m + (m + 1) ^ d := by
    simpa only [Fintype.card_fin] using weightedBasisIndex_card_le w d hw
  obtain ⟨hgeometry, hlip⟩ := hbound m (Fintype.card (WeightedBasisIndex w d)) p
    Ψ.lip M hp hm hcard Ψ.lip.coe_nonneg M.coe_nonneg hΨ hM
  constructor
  · apply RationalFilteredNilmanifold.GeometryComplexityLE.mono
      (weightedTranslationNilmanifold w d hw hwd)
      (weightedTranslationNilmanifold_complexity_budget w d hw hwd)
    simpa only [Fintype.card_fin] using hgeometry
  · change 2 * max (8 * weightedTranslationDisplacementConstant d m
        (Fintype.card (WeightedBasisIndex w d)))
      (((Ψ.lip : ℝ) + 2 * Real.pi * (1 + (M : ℝ) * m * d)) *
        weightedTranslationDisplacementConstant d m
          (Fintype.card (WeightedBasisIndex w d))) ≤ _
    exact hlip

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open scoped NNReal TensorProduct

theorem twistedBufferedTranslation_log_bound {m : ℕ} (w : Fin m → ℕ) (d : ℕ)
    [Fintype (WeightedBasisIndex w d)] (Ψ : PatchKernel m) (A K : ℝ≥0)
    {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hB : ((2 * bufferedTranslationTermLip w d Ψ A : ℝ≥0) : ℝ) ≤ Real.exp r)
    (hK : (K : ℝ) ≤ Real.exp p) :
    Real.log (3 + ((2 * twistedBufferedTranslationTermLip w d Ψ A K : ℝ≥0) : ℝ)) ≤
      p + r + 6 := by
  let B : ℝ := bufferedTranslationTermLip w d Ψ A
  let C : ℝ := translationDisplacementNN w d
  have hBn : 0 ≤ B := NNReal.coe_nonneg _
  have hCn : 0 ≤ C := NNReal.coe_nonneg _
  have hCB : C ≤ B := by
    have hh : 8 * C ≤ B := le_max_left _ _
    linarith
  change 2 * B ≤ Real.exp r at hB
  have hBe : B ≤ Real.exp r := by linarith
  have hCe : C ≤ Real.exp r := hCB.trans hBe
  have hBpr : B ≤ Real.exp (p + r) :=
    hBe.trans (Real.exp_le_exp.mpr (by linarith))
  have hCpr : C ≤ Real.exp (p + r) := hCB.trans hBpr
  have hKC : (K : ℝ) * C ≤ Real.exp (p + r) := by
    rw [Real.exp_add]
    exact mul_le_mul hK hCe hCn (Real.exp_nonneg _)
  have hmax : max (2 * C) (B + (K : ℝ) * C) ≤ 2 * Real.exp (p + r) := by
    exact max_le (by linarith) (by linarith)
  have hfour : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hLip : ((2 * twistedBufferedTranslationTermLip w d Ψ A K : ℝ≥0) : ℝ) ≤
      Real.exp (p + r + 3) := by
    change 2 * max (2 * C) (B + (K : ℝ) * C) ≤ _
    calc
      _ ≤ 4 * Real.exp (p + r) := by linarith
      _ ≤ Real.exp 3 * Real.exp (p + r) :=
        mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  calc
    _ ≤ 4 * Real.exp (p + r + 3) := by
      linarith [Real.one_le_exp (show 0 ≤ p + r + 3 by linarith)]
    _ ≤ Real.exp 3 * Real.exp (p + r + 3) :=
      mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem exists_weightedTwistedTranslation_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {m : ℕ} (w : Fin m → ℕ) (hw : ∀ i, 0 < w i)
      (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]
      (M : ℕ) (hM : 0 < M) (Ψ : PatchKernel m) (A K : ℝ≥0) (p : ℝ),
      0 ≤ p → (m : ℝ) ≤ p → (M : ℝ) ≤ Real.exp p →
      (Ψ.lip : ℝ) ≤ Real.exp p → (A : ℝ) ≤ Real.exp p → (K : ℝ) ≤ Real.exp p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE
        ((p + C) ^ C) ∧
      Real.log (3 + ((2 * twistedBufferedTranslationTermLip w d Ψ A K : ℝ≥0) : ℝ)) ≤
        (p + C) ^ C := by
  obtain ⟨a, _, hbuffer⟩ := exists_weightedTranslationBuffered_budget d
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + X + 6)
  refine ⟨C, hC, ?_⟩
  intro m w hw hwd _ M hM Ψ A K p hp hm hMp hΨ hA hK
  obtain ⟨hG, hB⟩ := hbuffer w hw hwd Ψ A p hp hm hΨ hA
  have hbound : (p + a) ^ a + p + 6 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hlogM : Real.log (M : ℝ) ≤ p :=
    (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hM)).mpr hMp
  constructor
  · apply RationalFilteredNilmanifold.GeometryComplexityLE.mono
      (weightedTranslationResidueNilmanifold w d hw hwd M hM)
      (weightedTranslationResidueNilmanifold_complexity_add_log w d hw hwd M hM hG)
    linarith
  · exact (twistedBufferedTranslation_log_bound w d Ψ A K hp (by positivity) hB hK).trans
      (by linarith)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open scoped NNReal

theorem exists_majorRationalLift_detection_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U : Type*} [Fintype U] {m : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
      (Ψ : PatchKernel m) (a : Fin m → ℤ) (p : ℝ),
      0 ≤ p → ((Fintype.card U + m : ℕ) : ℝ) ≤ p →
      (M : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, |(a i : ℝ)| ≤ Real.exp p) →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE
        ((p + C) ^ C) ∧
      Real.log (3 + ((2 * twistedBufferedTranslationTermLip w d Ψ
        (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d)
        (rationalLiftCharacterTwistLip M a) : ℝ≥0) : ℝ)) ≤ (p + C) ^ C := by
  obtain ⟨b, _, htwisted⟩ := exists_weightedTwistedTranslation_budget d
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ :=
    (Polynomial.C (d + 2) * (X + 1) + 8 + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro U _ m w hw hwd _ M hM Ψ a p hp hdim hMexp hΨ ha
  let q : ℝ := majorRationalLiftInputScale d p
  have hq := majorRationalLiftInputScale_bounds d p hp
  have hmp : (m : ℝ) ≤ p := by
    have hsum : (m : ℝ) ≤ ((Fintype.card U + m : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left m (Fintype.card U)
    exact hsum.trans hdim
  let B : ℝ≥0 := ((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d
  have hB : (B : ℝ) ≤ Real.exp q :=
    majorRationalLiftInputScale_mass d p hp (Fintype.card U) m hdim
  have hK : (rationalLiftCharacterTwistLip M a : ℝ) ≤ Real.exp q := by
    apply (rationalLiftCharacterTwistLip_le_exp_of_dim M hM a p p hmp ha).trans
    apply Real.exp_le_exp.mpr
    change p + p + 8 ≤ majorRationalLiftInputScale d p
    linarith [hq.2.2]
  obtain ⟨hgeometry, hlog⟩ := htwisted w hw hwd M hM Ψ B
    (rationalLiftCharacterTwistLip M a) q hq.1 (hmp.trans hq.2.1)
    (hMexp.trans (Real.exp_le_exp.mpr hq.2.1))
    (hΨ.trans (Real.exp_le_exp.mpr hq.2.1)) hB hK
  have hcost : (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [Q, X, q, majorRationalLiftInputScale, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨RationalFilteredNilmanifold.GeometryComplexityLE.mono _ hgeometry hcost,
    hlog.trans hcost⟩

end Erdos3.PolynomialTranslationLie

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

theorem RationalFilteredNilmanifold.observable_frozen_right_eq
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (u : D.Space → ℂ)
    (a b r r' : D.RealGroup)
    (h : (QuotientGroup.mk r : D.Space) = QuotientGroup.mk r') :
    u (QuotientGroup.mk (a * b * r)) = u (QuotientGroup.mk (a * b * r')) :=
  congrArg (fun x : D.Space => u ((a * b) • x)) h

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeAntisymmetricFrozenDescent.lie NativeAntisymmetricFrozenDescent.algebra
  NativeAntisymmetricFrozenDescent.topology NativeAntisymmetricFrozenDescent.topologicalAdd
  NativeAntisymmetricFrozenDescent.continuousSMul NativeAntisymmetricFrozenDescent.hausdorff

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestOrbitOne
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem oneOnOrbit_vertical (T : D.Niltest w) (z : D.RealGroup) (x : D.Space) :
    T.oneOnOrbit.observable (z • x) =
      CircleFourier.character ((realifyFunctional (0 : L →ₗ[ℚ] ℚ) z.coord : ℝ) : CircleFourier.Circle) *
        T.oneOnOrbit.observable x := by
  simp only [oneOnOrbit, realifyFunctional_zero, AddCircle.coe_zero,
    CircleFourier.character_zero, mul_one]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSampleModelFamily
namespace OAI

section

open scoped TensorProduct BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι σ : Type*} {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  {D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)} {w : σ → ℕ}

noncomputable def selectedOrbitFactors (base T : ∀ i, (D i).Niltest w)
    (active : Finset ι) (i : ι) : (D i).Niltest w := by
  classical
  exact if i ∈ active then T i else (base i).oneOnOrbit

theorem selectedOrbitFactors_eval [Fintype ι] (base T : ∀ i, (D i).Niltest w)
    (active : Finset ι) (x : σ → ℤ) :
    (∏ i, (selectedOrbitFactors base T active i).eval x) = ∏ i ∈ active, (T i).eval x := by
  classical
  have heval (i : ι) : (selectedOrbitFactors base T active i).eval x =
      if i ∈ active then (T i).eval x else 1 := by
    by_cases hi : i ∈ active <;>
      simp only [selectedOrbitFactors, hi, ite_true, ite_false, Niltest.oneOnOrbit_eval]
  simp only [heval, Finset.prod_ite_mem_eq]

theorem selectedOrbitFactors_normBound (base T : ∀ i, (D i).Niltest w) (active : Finset ι)
    (hcap : ∀ i ∈ active, (T i).normBound ≤ 1) (i : ι) :
    (selectedOrbitFactors base T active i).normBound ≤ 1 := by
  classical
  by_cases hi : i ∈ active
  · simpa only [selectedOrbitFactors, hi, ite_true] using hcap i hi
  · simp only [selectedOrbitFactors, hi, ite_false, Niltest.oneOnOrbit, le_refl]

theorem selectedOrbitFactors_complexity (base T : ∀ i, (D i).Niltest w)
    (active : Finset ι) {p : ℝ} (hp : 2 ≤ p) (hD : ∀ i, (D i).GeometryComplexityLE p)
    (hT : ∀ i ∈ active, (T i).ComplexityLE p) (i : ι) :
    (selectedOrbitFactors base T active i).ComplexityLE p := by
  classical
  by_cases hi : i ∈ active
  · simpa only [selectedOrbitFactors, hi, ite_true] using hT i hi
  · simpa only [selectedOrbitFactors, hi, ite_false] using
      (base i).oneOnOrbit_complexity hp (hD i)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff
  NativeSampleModelFamily.lie NativeSampleModelFamily.algebra
  NativeSampleModelFamily.topology NativeSampleModelFamily.topologicalAdd
  NativeSampleModelFamily.continuousSMul NativeSampleModelFamily.hausdorff

namespace NativeSampleModelFamily

variable {ι σ X : Type*} {w : σ → ℕ} {degree : ℕ} {p : ℝ}
  {sample : X → σ → ℤ} {g : ι → X → ℂ}

noncomputable def ofModels {ι : Type} [Fintype ι] {g : ι → X → ℂ}
    (V : ∀ i, NativeSampleModel w degree p sample (g i))
    (hp : 2 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) :
    NativeSampleModelFamily w degree (productNiltestBudget p) sample g := by
  classical
  let D := fun i => (V i).model
  let base := fun i => (V i).test
  let : FiniteDimensional ℚ (∀ i, (V i).L) :=
    (RationalFilteredNilmanifold.productFinBasis D).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, (V i).L))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, (V i).L)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ i, (V i).L)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis D)
  let factors := fun j => RationalFilteredNilmanifold.selectedOrbitFactors base base {j}
  have hD : ∀ i, (D i).GeometryComplexityLE p := fun i => (V i).complexity.1
  have hcomp : ∀ j i, (factors j i).ComplexityLE p := fun j =>
    RationalFilteredNilmanifold.selectedOrbitFactors_complexity base base {j} hp hD
      (fun i _ => (V i).complexity)
  have hcap : ∀ j i, (factors j i).normBound ≤ 1 := fun j =>
    RationalFilteredNilmanifold.selectedOrbitFactors_normBound base base {j}
      (fun i _ => (V i).norm)
  have hp0 : 0 ≤ p := by linarith
  let tests := fun j => RationalFilteredNilmanifold.unitBoundedPiNiltest
    D (factors j) hp0 hι (hcomp j) (hcap j)
  refine {
    L := ∀ i, (V i).L
    dim := Fintype.card (Σ i, Fin (V i).dim)
    model := RationalFilteredNilmanifold.pi D
    test := tests
    norm := fun _ => le_rfl
    complexity := fun j => RationalFilteredNilmanifold.unitBoundedPiNiltest_complexity
      D (factors j) hp0 hι (hcomp j) (hcap j)
    eval := ?_ }
  intro j x
  change g j x = (RationalFilteredNilmanifold.unitBoundedPiNiltest
    D (factors j) hp0 hι (hcomp j) (hcap j)).eval (sample x)
  rw [RationalFilteredNilmanifold.unitBoundedPiNiltest_eval]
  change g j x = ∏ i, (RationalFilteredNilmanifold.selectedOrbitFactors base base {j} i).eval
    (sample x)
  rw [RationalFilteredNilmanifold.selectedOrbitFactors_eval]
  simpa only [Finset.prod_singleton] using (V j).eval x

end NativeSampleModelFamily

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FrozenDiagramKernelInvariance
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem realificationLieHom_injective
    {H M : Type*} [LieRing H] [LieAlgebra ℚ H] [LieRing M] [LieAlgebra ℚ M]
    (ψ : H →ₗ⁅ℚ⁆ M) (hψ : Function.Injective ψ) :
    Function.Injective (realificationLieHom ψ) := by
  let _ : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ) ψ.toLinearMap hψ

namespace NilpotentLieBCHGroup

theorem realificationMap_injective
    {H M : Type*} [LieRing H] [LieAlgebra ℚ H] [LieRing M] [LieAlgebra ℚ M]
    {s t : ℕ} {hH : LieModule.lowerCentralSeries ℚ H H s = ⊥}
    {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}
    (ψ : H →ₗ⁅ℚ⁆ M) (hψ : Function.Injective ψ) :
    Function.Injective (realificationMap (hnil := hH) (hM := hM) ψ) := by
  intro x y hxy
  apply ext
  apply realificationLieHom_injective ψ hψ
  exact congrArg coord hxy

end NilpotentLieBCHGroup

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StepOneSymbolLinearPart
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (F : NilpotentLieFiltration L 1) (b : Basis ι ℚ L)

theorem stepOne_basis_layers (j : ℕ) :
    F.layer j = Submodule.span ℚ (b '' {i | j ≤ (fun _ : ι => 1) i}) := by
  by_cases hj : j ≤ 1
  · have htop : F.layer j = ⊤ := top_unique (F.one_eq_top ▸ F.antitone hj)
    simpa only [hj, Set.ofPred_true, Set.image_univ, b.span_eq] using htop
  · have hbot : F.layer j = ⊥ := bot_unique ((F.antitone (by omega : 2 ≤ j)).trans F.terminal.le)
    simpa only [hj, Set.ofPred_false, Set.image_empty, Submodule.span_empty] using hbot

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSubspaceFreeModel
namespace OAI

section

namespace Erdos3.SubspaceFreeLift

open Module VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (S : Fin s → Submodule ℚ L)

variable (B : ∀ d, Basis (Fin (finrank ℚ (S d))) ℚ (S d))

variable (F : DegreeRankLieFiltration L s r)
  (hS : ∀ d, S d ≤ F.layer (d.val + 1) 0)

theorem evaluation_generator (x : Alphabet S) :
    evaluation S B F hS (generator S r x) = (B x.1 x.2).val :=
  FreeDegreeRankLieAlgebra.lift_of _ _ _ _ _ x

theorem evaluation_coefficientLift (d : Fin s) (x : S d) :
    evaluation S B F hS (coefficientLift S B r d x) = x.val := by
  have heq : (evaluation S B F hS).toLinearMap.comp (coefficientLift S B r d) =
      (S d).subtype := by
    apply (B d).ext
    intro i
    change evaluation S B F hS ((B d).constr ℚ _ (B d i)) = _
    rw [Basis.constr_basis]
    exact evaluation_generator S B F hS ⟨d, i⟩
  exact LinearMap.congr_fun heq x

end Erdos3.SubspaceFreeLift

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonCoefficientFourAnnihilators
namespace OAI

section

namespace Erdos3

open Module

variable {V μ ι κ : Type*} [AddCommGroup V] [Module ℚ V]

theorem fourBasisVectors_logHeight (e : Basis μ ℚ V) (D : Submodule ℚ V)
    (b : Basis κ ℚ D) {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ a i, rationalLogHeight (e.repr (b a : V) i) ≤ p)
    (a : Σ _ : Fin 4, κ) (k : Fin 4) (i : μ) :
    rationalLogHeight (e.repr (fourBasisVectors D b a k) i) ≤ p := by
  classical
  rw [fourBasisVectors_apply, LinearMap.single_apply]
  by_cases h : k = a.1
  · rw [h, Pi.single_eq_same]
    exact hb a.2 i
  · rw [Pi.single_eq_of_ne h]
    simpa [rationalLogHeight] using hp

theorem fourBalancedGenerators_logHeight (e : Basis μ ℚ V) (D : Submodule ℚ V)
    (b : Basis κ ℚ D) {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ a i, rationalLogHeight (e.repr (b a : V) i) ≤ p)
    (a : Σ _ : Fin 4, κ) (k : Fin 4) (i : μ) :
    rationalLogHeight (e.repr (fourBalanceProjection (R := ℚ) (fourBasisVectors D b a) k) i) ≤ p := by
  classical
  rcases a with ⟨a, j⟩
  rw [fourBasisVectors_apply, fourBalanceProjection_apply]
  fin_cases a <;> fin_cases k <;>
    first
    | simpa [LinearMap.single_apply, rationalLogHeight] using hb j i
    | simpa [LinearMap.single_apply, rationalLogHeight] using hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealFourAnnihilatorKernel
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem mem_realified_coordinate_kernel_iff
    {V J : Type*} [AddCommGroup V] [Module ℚ V] [Fintype J]
    (ℓ : V →ₗ[ℚ] (J → ℚ)) (x : ℝ ⊗[ℚ] V) :
    x ∈ (LinearMap.ker ℓ).baseChange ℝ ↔
      ∀ j, realifyFunctional ((LinearMap.proj j).comp ℓ) x = 0 := by
  have hker : LinearMap.ker ℓ = ⨅ j, LinearMap.ker ((LinearMap.proj j).comp ℓ) := by
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_iInf, LinearMap.comp_apply, LinearMap.proj_apply]
    exact funext_iff
  rw [hker, real_baseChange_iInf]
  simp only [Submodule.mem_iInf, mem_realified_frequency_kernel_iff]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealAnnihilatorCorrections
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {V I J : Type*} [AddCommGroup V] [Module ℚ V] [Fintype I] [Fintype J]

theorem mem_realified_coordinate_kernel_iff_eq_zero
    (ℓ : V →ₗ[ℚ] (J → ℚ)) (x : ℝ ⊗[ℚ] V) :
    x ∈ (LinearMap.ker ℓ).baseChange ℝ ↔ realifyCoordinateMap ℓ x = 0 := by
  rw [mem_realified_coordinate_kernel_iff]
  exact ⟨fun h => funext h, fun h j => congrFun h j⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCorrelationCoordinates
namespace OAI

section

namespace Erdos3.NativeVectorCorrelation

open scoped TensorProduct BigOperators

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

noncomputable def mapCoordinates {I J : Type*} {degree N : ℕ} [NeZero N] {p : ℝ}
    {f : I → ZMod N → ℂ} (W : NativeVectorCorrelation degree N p f)
    (g : J → ZMod N → ℂ) (e : I → J) (he : ∀ i x, g (e i) x = f i x) :
    NativeVectorCorrelation degree N p g :=
  { W with coordinate := e W.coordinate
           correlation := by simpa only [he] using W.correlation }

noncomputable def scaleSignal {I : Type*} {degree N : ℕ} [NeZero N] {p q : ℝ}
    {f : I → ZMod N → ℂ} (W : NativeVectorCorrelation degree N p f)
    (c : ℂ) (hq : 0 ≤ q) (hc : Real.exp (-q) ≤ ‖c‖) :
    NativeVectorCorrelation degree N (p + q) (fun i x => c * f i x) :=
  { W with
    complexity := W.complexity.mono (le_add_of_nonneg_right hq)
    correlation := by
      have he : (𝔼 x, (c * f W.coordinate x) * star (W.test.evalCyclic N (fun _ => x))) =
          c * (𝔼 x, f W.coordinate x * star (W.test.evalCyclic N (fun _ => x))) := by
        simp only [mul_assoc, Finset.mul_expect]
      rw [he, norm_mul, show -(p + q) = -q + -p by ring, Real.exp_add]
      exact mul_le_mul hc W.correlation (Real.exp_nonneg _) (norm_nonneg _) }

theorem exists_half_signal {I : Type*} {degree N : ℕ} [NeZero N] {p : ℝ}
    {f : I → ZMod N → ℂ} (W : NativeVectorCorrelation degree N p f) :
    Nonempty (NativeVectorCorrelation degree N (p + 1) (fun i x => f i x / 2)) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hc : Real.exp (-1) ≤ ‖(1 / 2 : ℂ)‖ := by
    norm_num only [norm_div, norm_one, Complex.norm_ofNat]
    rw [Real.exp_neg, one_div]
    exact (inv_le_inv₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)).mpr htwo
  have h := W.scaleSignal (1 / 2) (by norm_num : (0 : ℝ) ≤ 1) hc
  refine ⟨h.mapCoordinates _ id ?_⟩
  intro i x
  simp only [id_eq, div_eq_mul_inv, one_mul, mul_comm]

end Erdos3.NativeVectorCorrelation

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.InducedUnitRankFamily
namespace OAI

section

namespace Erdos3.NativeVectorCorrelation

theorem exists_combined_factor_correlation {A I J K : Type*}
    {degree N : ℕ} [NeZero N] {p : ℝ}
    (f : A → ZMod N → ℂ) (g : K → ZMod N → ℂ)
    (a : I → ZMod N → ℂ) (b : J → ZMod N → ℂ)
    (c : I × J → ZMod N → ℂ) (j : J → K)
    (hc : ∀ ij x, c ij x = a ij.1 x * b ij.2 x)
    (W : NativeVectorCorrelation degree N p (fun z : A × (I × J) => fun x =>
      f z.1 x * star (g (j z.2.2) x) * star (a z.2.1 x) * star (b z.2.2 x))) :
    Nonempty (NativeVectorCorrelation degree N p (fun z : (A × K) × (I × J) => fun x =>
      f z.1.1 x * star (g z.1.2 x) * star (c z.2 x))) := by
  refine ⟨W.mapCoordinates _ (fun z => ((z.1, j z.2.2), z.2)) ?_⟩
  intro z x
  rw [hc, star_mul]
  ring

end Erdos3.NativeVectorCorrelation

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticAntisymmetricCorrelation
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeTwoVariableSplit.lie NativeTwoVariableSplit.algebra
  NativeTwoVariableSplit.topology NativeTwoVariableSplit.topologicalAdd
  NativeTwoVariableSplit.continuousSMul NativeTwoVariableSplit.hausdorff

theorem NativeTwoVariableSplit.second_eval_eq_degree_one {d : ℕ} {p epsilon : ℝ}
    {f : (Fin 2 → ℤ) → ℂ} (R : NativeTwoVariableSplit 1 d p epsilon f)
    (j : Fin R.count) (x y : Fin 2 → ℤ) (hxy : x 0 = y 0) :
    (R.test true j).eval x = (R.test true j).eval y := by
  unfold RationalFilteredNilmanifold.Niltest.eval
  rw [R.test_orbit true j, (R.multi true).orbitToOrdinary_eval,
    (R.multi true).orbitToOrdinary_eval]
  apply congrArg (R.test true j).observable
  apply congrArg QuotientGroup.mk
  apply (R.multi true).filtration.realification.polynomialOrbitEval_eq_of_zero_coordinate
    1 (show totalDegreeSplitBound 1 true 1 = 0 from rfl) (R.orbit true) x y
  intro i hi
  fin_cases i
  · exact hxy
  · exact (hi rfl).elim

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CanonicalReducedMajorTwistedNiltest
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped NNReal TensorProduct

variable {U : Type*} {m : ℕ}

theorem majorZeroParameterSlice_mass (D : MvPolynomial (U ⊕ Fin m) ℝ) :
    realPolynomialMass (specializeMajorParameters (RingHom.id ℝ) D 0) ≤
      realPolynomialMass D := by
  rw [majorZeroParameterSlice_eq]
  exact realPolynomialMass_zeroParameterEval_le D

variable (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

theorem exists_majorTranslation_buffered_niltest (hd : 0 < d)
    (Ψ : PatchKernel m) (D : MvPolynomial (U ⊕ Fin m) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (M : ℝ≥0) (hM : realPolynomialMass D ≤ M) :
    ∃ F : (weightedTranslationNilmanifold w d hw hwd).Niltest (fun _ : U => 1),
      F.normBound = 1 ∧ F.lipBound = 2 * bufferedTranslationTermLip w d Ψ M ∧
      F.orbit = majorTranslationPolynomialOrbit w d hw hwd D hD A hA ∧
      (∀ u : U → ℝ, ∀ β : Fin m → ℤ,
        (∀ i, |eval u (A i) - (β i : ℝ)| ≤ 1 / 2) →
        F.evalReal u = (Ψ.value (fun i => eval u (A i) - (β i : ℝ)) : ℂ) *
          (Real.fourierChar (eval (Sum.elim u (fun i => (β i : ℝ))) D) : ℂ)) ∧
      (∀ u : U → ℝ, ‖F.evalReal u‖ ≤ 1) := by
  let q := majorTranslationPolynomialOrbit w d hw hwd D hD A hA
  have hq := majorTranslationPolynomialOrbit_realEval w d hw hwd D hD A hA
  let D₀ := specializeMajorParameters (RingHom.id ℝ) D 0
  have hdegree : D₀.totalDegree ≤ d := majorZeroParameterSlice_degree w hw hD
  have hmass : realPolynomialMass D₀ ≤ M := (majorZeroParameterSlice_mass D).trans hM
  let F := weightedTranslationBufferedNiltest w d hw hwd (fun _ : U => 1)
    hd Ψ D₀ M hdegree hmass q
  refine ⟨F, rfl, rfl, rfl, ?_, ?_⟩
  · intro u β hβ
    change bufferedTranslationPhase Ψ D₀
      (bchRealTranslationHom w d hwd
        ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
          (fun _ : U => 1) u q)) = _
    rw [hq u]
    exact bufferedTranslationPhase_majorSymbol Ψ D D₀ A u β hβ
  · intro u
    exact weightedTranslationBufferedObservable_norm_le_one w d hw hwd Ψ D₀ _

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3

open _root_.MvPolynomial

theorem fractionalCoefficientPolynomial_mass_le_of_weightedSupportLE
    {σ : Type*} [Fintype σ] (D : MvPolynomial σ ℝ)
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (d : ℕ)
    (hD : D ∈ weightedSupportLE w d) :
    realPolynomialMass (fractionalCoefficientPolynomial D) ≤
      ((Fintype.card σ : ℝ) + 1) ^ d := by
  refine (fractionalCoefficientPolynomial_mass_le_card D).trans ?_
  have hcard := boundedExponentSet_card_le (fractionalCoefficientPolynomial D).support d
    (fun a ha => (exponentSum_le_positive_weight w hw a).trans
      (fractionalCoefficientPolynomial_mem_weightedSupportLE D w d hD ha))
  exact_mod_cast hcard

end Erdos3

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped NNReal TensorProduct

theorem exists_majorTranslation_degree_reduced_niltest (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U : Type*} [Fintype U] {m : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      (_hd : 0 < d) (Ψ : PatchKernel m) (D : MvPolynomial (U ⊕ Fin m) ℝ)
      (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
      {p : ℝ} (_hp : 0 ≤ p) (_hdim : (Fintype.card U + m : ℕ) ≤ p)
      (_hΨ : (Ψ.lip : ℝ) ≤ Real.exp p),
      ∃ F : (weightedTranslationNilmanifold w d hw hwd).Niltest (fun _ : U => 1),
        F.normBound = 1 ∧ F.ComplexityLE ((p + C) ^ C) ∧
        F.orbit = majorTranslationPolynomialOrbit w d hw hwd
          (fractionalCoefficientPolynomial D)
          (fractionalCoefficientPolynomial_mem_weightedSupportLE D
            (Sum.elim (fun _ : U => 1) w) d hD) A hA ∧
        ∀ u : U → ℤ, ∀ β : Fin m → ℤ,
          (∀ i, |eval (fun j => (u j : ℝ)) (A i) - (β i : ℝ)| ≤ 1 / 2) →
          F.eval u =
            (Ψ.value (fun i => eval (fun j => (u j : ℝ)) (A i) - (β i : ℝ)) : ℂ) *
              (Real.fourierChar (eval (fun j => ((Sum.elim u β j : ℤ) : ℝ)) D) : ℂ) := by
  obtain ⟨a, ha, hbudget⟩ := exists_weightedTranslationBuffered_budget d
  let X : Polynomial ℕ := Polynomial.X
  let Q := (Polynomial.C (d + 1) * (X + 1) + Polynomial.C a) ^ a + 4
  obtain ⟨C, hC, hCbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro U _ m w hw hwd _ _ _ _ _ hd Ψ D hD A hA p hp hdim hΨ
  let v : U ⊕ Fin m → ℕ := Sum.elim (fun _ : U => 1) w
  have hv : ∀ i, 0 < v i := by intro i; cases i with
    | inl i => exact Nat.zero_lt_one
    | inr i => exact hw i
  let Dred := fractionalCoefficientPolynomial D
  have hDred : Dred ∈ weightedSupportLE v d :=
    fractionalCoefficientPolynomial_mem_weightedSupportLE D v d hD
  let M : ℝ≥0 := ((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d
  have hmass : realPolynomialMass Dred ≤ M := by
    change realPolynomialMass Dred ≤ (((Fintype.card U + m + 1 : ℕ) : ℝ) ^ d)
    have hh := fractionalCoefficientPolynomial_mass_le_of_weightedSupportLE D v hv d hD
    simpa only [Dred,
      Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hh
  obtain ⟨F, hnorm, hlip, horbit, heval, _⟩ := exists_majorTranslation_buffered_niltest
    w d hw hwd hd Ψ Dred hDred A hA M hmass
  let q : ℝ := (d + 1 : ℕ) * (p + 1)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    dsimp [q]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hm : (m : ℝ) ≤ q := by
    have hh : (m : ℝ) ≤ (Fintype.card U + m : ℕ) := by exact_mod_cast Nat.le_add_left m (Fintype.card U)
    exact hh.trans (hdim.trans hpq)
  have hM : (M : ℝ) ≤ Real.exp q := by
    have hb : ((Fintype.card U + m + 1 : ℕ) : ℝ) ≤ Real.exp (p + 1) := by
      push_cast at hdim ⊢
      linarith [Real.add_one_le_exp (p + 1)]
    calc
      (M : ℝ) ≤ (Real.exp (p + 1)) ^ d := by
        change (((Fintype.card U + m + 1 : ℕ) : ℝ) ^ d) ≤ _
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) hb d
      _ = Real.exp ((d : ℝ) * (p + 1)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp q := by apply Real.exp_le_exp.mpr; dsimp [q]; push_cast; nlinarith
  obtain ⟨hgeometry, hlipBudget⟩ := hbudget w hw hwd Ψ M q hq hm
    (hΨ.trans (Real.exp_le_exp.mpr hpq)) hM
  have hcost : (q + a) ^ a + 4 ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hCbudget p hp
  have hlog : Real.log (3 + (F.lipBound : ℝ)) ≤ (q + a) ^ a + 4 := by
    have hnonneg : 0 ≤ (q + a) ^ a := by positivity
    have hh := add_le_exp_add_one (by norm_num : (0 : ℝ) ≤ 3) hnonneg
      (show (3 : ℝ) ≤ Real.exp 3 by linarith [Real.add_one_le_exp (3 : ℝ)])
      (show (F.lipBound : ℝ) ≤ Real.exp ((q + a) ^ a) by rw [hlip]; exact hlipBudget)
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    convert hh using 1
    congr 1
    ring
  refine ⟨F, hnorm, ⟨RationalFilteredNilmanifold.GeometryComplexityLE.mono _
    hgeometry (by linarith), ?_⟩, horbit, ?_⟩
  · simpa only [hnorm, NNReal.coe_one, show (2 : ℝ) + 1 = 3 by norm_num]
      using hlog.trans hcost
  · intro u β hβ
    rw [← F.evalReal_integer u, heval _ β hβ]
    have hcast : Sum.elim (fun j => (u j : ℝ)) (fun i => (β i : ℝ)) =
        (fun j => ((Sum.elim u β j : ℤ) : ℝ)) := by
      funext j
      cases j <;> rfl
    rw [hcast]
    congr 1
    exact congrArg (fun z : Circle => (z : ℂ))
      (fractionalCoefficientPolynomial_fourierChar D (Sum.elim u β))

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedTranslationMajorTwistedVerticalSelection
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial CircleFourier
open scoped TensorProduct BigOperators NNReal

theorem exists_translation_major_twisted_vertical_selection :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X U L : Type*} [LieRing L] [LieAlgebra ℚ L]
      {m d t e : ℕ} (w : Fin m → ℕ) (hw : ∀ i, 0 < w i)
      (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (M : ℕ) (hM : 0 < M) (D : RationalFilteredNilmanifold L t e) (htd : t < d) (ω : U → ℕ)
      (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (mass K : ℝ≥0)
      (_hdegree : D₀.totalDegree ≤ d) (_hD : realPolynomialMass D₀ ≤ mass)
      (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (_hT : ∀ x r, ‖T x r‖ ≤ 1) (_hLip : ∀ r, LipschitzWith K (fun x => T x r))
      (orbit : (weightedFiltration w d hwd).realification.PolynomialOrbit ω)
      (R : D.Niltest ω) (p : ℝ), 0 ≤ p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p →
      Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ mass K : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (B : Finset X), B.Nonempty → ∀ (sample : X → U → ℤ) (multiplier : X → ℂ),
      (∀ x ∈ B, ‖multiplier x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ B, multiplier x *
        twistedBufferedTranslationPhase M Ψ D₀ T (bchRealTranslationHom w d hwd
          ((weightedFiltration w d hwd).realification.polynomialOrbitEval ω (sample x) orbit)) *
        R.eval (sample x)‖ →
      ∃ (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
        (V : (weightedTranslationResidueNilmanifold w d hw hwd M hM).Niltest ω)
        (W : (D.raiseStep htd.le).Niltest ω),
        V.ComplexityLE ((raisedNiltestBudget p + C) ^ C) ∧
        V.orbit = orbit ∧ V.normBound = 1 ∧
        W.ComplexityLE ((raisedNiltestBudget p + C) ^ C) ∧
        W.orbit = D.raiseStepRealOrbit htd.le R.orbit ∧ W.normBound = R.normBound ∧
        (∀ i, rationalLogHeight (η ((weightedTranslationResidueNilmanifold w d hw hwd M hM).basis i)) ≤
          (raisedNiltestBudget p + C) ^ C) ∧
        η (centralRationalElement w d hd 1) = 1 ∧
        (∀ z, z ∈ (weightedFiltration w d hwd).realification.subgroup d → ∀ x,
          V.observable (z • x) =
            character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x) ∧
        (∀ z, z ∈ (D.raiseStep htd.le).filtration.realification.subgroup d → ∀ x,
          W.observable (z • x) =
            character ((realifyFunctional (0 : L →ₗ[ℚ] ℚ) z.coord : ℝ) : CircleFourier.Circle) *
              W.observable x) ∧
        (∃ x, V.observable x ≠ 0) ∧ (∃ x, W.observable x ≠ 0) ∧
        Real.exp (-((raisedNiltestBudget p + C) ^ C)) ≤
          ‖𝔼 x ∈ B, multiplier x * V.eval (sample x) * W.eval (sample x)‖ := by
  obtain ⟨C, hC, hselect⟩ := exists_native_vertical_pair_preserving_characters_power
  refine ⟨C, hC, ?_⟩
  intro X U L _ _ m d t e w hw hd hwd _ _ _ _ _ _ _ _ _ M hM D htd ω Ψ D₀ mass K hdegree hD T hT hLip
    orbit R p hp hgeometry hbound hR hRcap B hB sample multiplier hmultiplier hcorr
  let Q := weightedTranslationTwistedNiltest w d hw hwd M hM ω hd Ψ D₀ mass K hdegree hD T hT hLip orbit
  have hQ : Q.ComplexityLE p :=
    weightedTranslationTwistedNiltest_complexity w d hw hwd M hM ω hd Ψ D₀ mass K hdegree hD T hT hLip orbit
      hgeometry hbound
  have hraise := le_raisedNiltestBudget p
  have hraisedcorr : Real.exp (-(raisedNiltestBudget p)) ≤
      ‖𝔼 x ∈ B, multiplier x * Q.eval (sample x) * (R.raiseStep htd.le).eval (sample x)‖ := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hraise)).trans
    simpa only [Q, weightedTranslationTwistedNiltest_eval,
      RationalFilteredNilmanifold.Niltest.raiseStep_eval] using hcorr
  obtain ⟨η, η', V, W, hVc, hVo, hVn, hWc, hWo, hWn, hVheight, _, hvertV, _,
      hpresV, _, hVne, hWne, hbias⟩ :=
    hselect (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le)
      Q (R.raiseStep htd.le) (raisedNiltestBudget p) (hp.trans hraise)
      (hQ.mono hraise) (R.raiseStep_complexity htd.le hp hR)
      (by change (1 : ℝ) ≤ 1; exact le_rfl) hRcap
      B hB sample multiplier hmultiplier hraisedcorr
  have hη : η (centralRationalElement w d hd 1) = 1 :=
    weightedTranslation_twisted_selected_frequency_one w d hw hd hwd M hM Ψ D₀ T η V.observable
      hvertV hVne hpresV
  exact ⟨η, V, W, hVc, hVo, hVn, hWc, hWo, hWn, hVheight, hη, hvertV,
    D.raiseStep_observable_top_vertical htd W.observable, hVne, hWne, hbias⟩

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ProductPolynomialMaps
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct

namespace NilpotentLieFiltration

theorem piRealOrbit_projection_log {ι σ : Type*} [Fintype ι]
    {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
    (F : ∀ i, NilpotentLieFiltration (L i) s) {w : σ → ℕ}
    (g : ∀ i, (F i).realification.PolynomialOrbit w) (a : ι) :
    VectorPolynomial.map ((realificationLieHom (liePiEval a)).toLinearMap.restrictScalars ℚ)
      (piRealOrbit F g).log = (g a).log := by
  classical
  apply coefficients.injective
  ext α
  simp only [coefficients_map, piRealOrbit, polynomialOrbitOfLog_log, map_sum,
    Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single a]
  · exact realProductSingle_projection a _
  · intro j _ hja
    exact realProductSingle_projection_ne (Ne.symm hja) _
  · simp

end NilpotentLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorDetectedPotential
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem weightedBasis_polynomial_height_of_coordinates
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (x : weightedSubalgebra w d) {H : ℕ} (hH : 1 ≤ H)
    (hx : ∀ i, RationalHeightLE ((weightedBasis w d hw).repr x i) H) :
    RationalPolynomialHeightLE x.val.polynomial H := by
  intro α
  by_cases hα : Finsupp.weight w α < d
  · exact hx (Sum.inr ⟨α, hα⟩)
  · have hz : x.val.polynomial.coeff α = 0 := by
      by_contra hne
      have hb := x.property.2 (MvPolynomial.mem_support_iff.mpr hne)
      change Finsupp.weight w α + 1 ≤ d at hb
      omega
    rw [hz]
    exact rationalHeightLE_zero hH

theorem explicit_projected_weighted_potential
    (w : σ → ℕ) (v : τ → ℕ) {d : ℕ}
    (hd : 0 < d) (hvd : ∀ i, v i ≤ d)
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ)) (hBA : ∀ x, B (A x) = x)
    [DecidableEq σ] [DecidableEq τ]
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (hBweight : ∀ i j, w i ≠ v j → B (Pi.single i 1) j = 0)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hgraded : ∀ x ∈ U, topProjection w d x ∈ U)
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0)
    (L : τ → PolynomialTranslationLie σ)
    (hL : ∀ j, L j ∈ U) (hbase : ∀ j, (L j).base = A (Pi.single j 1))
    (hhom : ∀ j, (L j).polynomial.IsWeightedHomogeneous w (d - v j)) :
    let P := fun j => polynomialLinearRestriction A (L j).polynomial
    let W := polynomialLinearRestriction B (weightedPolynomialPotential v d P)
    W.IsWeightedHomogeneous w d ∧
      ∀ x ∈ U, x.base ∈ A.range → ∀ z ∈ A.range,
        eval z (scalarDirectionalDerivative x.base W) = eval z x.polynomial := by
  let P := fun j => polynomialLinearRestriction A (L j).polynomial
  let V := weightedPolynomialPotential v d P
  let W := polynomialLinearRestriction B V
  let rel := projectedPotentialRelation A hA w d U hgraded frequency hfrequency hkill
  have hPhom : ∀ j, (P j).IsWeightedHomogeneous v (d - v j) :=
    fun j => polynomialLinearRestriction_isWeightedHomogeneous A v w hweight (hhom j)
  have hlift : ∀ j, (Pi.single j 1, P j) ∈ rel.space := by
    intro j
    apply (mem_relationSpace _ _ _).mpr
    let y : baseRange A := ⟨L j, by
      change (L j).base ∈ A.range
      rw [hbase j]
      exact A.mem_range_self (Pi.single j 1)⟩
    refine ⟨y, hL j, ?_⟩
    apply PolynomialTranslationLie.ext
    · apply hA
      exact (apply_projectedBaseCoordinates A hA y).trans (hbase j)
    · rfl
  have hV : V.IsWeightedHomogeneous v d :=
    weightedPolynomialPotential_homogeneous v d P hvd hPhom
  have hres : polynomialLinearRestriction A W = V :=
    polynomialLinearRestriction_leftInverse A B hBA V
  refine ⟨polynomialLinearRestriction_isWeightedHomogeneous B w v hBweight hV, ?_⟩
  intro x hx hxrange z hz
  let x' : baseRange A := ⟨x, hxrange⟩
  have hderiv : scalarDirectionalDerivative (projectedBaseCoordinates A hA x') V =
      polynomialLinearRestriction A x.polynomial :=
    rel.weighted_potential_derivative P hlift v hd hvd hPhom _ _
      ((mem_relationSpace _ _ _).mpr ⟨x', hx, rfl⟩)
  have hpoly : polynomialLinearRestriction A (scalarDirectionalDerivative x.base W) =
      polynomialLinearRestriction A x.polynomial := by
    rw [← apply_projectedBaseCoordinates A hA x',
      ← scalarDirectionalDerivative_linearRestriction, hres]
    exact hderiv
  obtain ⟨t, ht⟩ := hz
  have he := congrArg (eval t) hpoly
  simpa only [eval_polynomialLinearRestriction, ht] using he

theorem weightedBasis_projection_polynomial_height
    (w : σ → ℕ) (d j : ℕ) (hw : ∀ i, 0 < w i)
    (x : weightedSubalgebra w d) {H : ℕ} (hH : 1 ≤ H)
    (hx : RationalPolynomialHeightLE x.val.polynomial H) :
    RationalPolynomialHeightLE
      (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).val.polynomial H := by
  intro α
  by_cases hα : Finsupp.weight w α < d
  · rw [weightedBasis_projection_coeff w d j hw x ⟨α, hα⟩]
    split_ifs
    · exact hx α
    · exact rationalHeightLE_zero hH
  · have hz :
        (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).val.polynomial.coeff α = 0 := by
      by_contra hne
      have hb := (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).property.2
        (MvPolynomial.mem_support_iff.mpr hne)
      change Finsupp.weight w α + 1 ≤ d at hb
      omega
    rw [hz]
    exact rationalHeightLE_zero hH

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorDimensionBudget
namespace OAI

section

universe level

namespace Erdos3

open Module

namespace PolynomialTranslationLie

variable {σ : Type*} [Fintype σ]

theorem card_le_weightedBasisIndex (w : σ → ℕ) (d : ℕ)
    [Fintype (WeightedBasisIndex w d)] :
    Fintype.card σ ≤ Fintype.card (WeightedBasisIndex w d) :=
  Fintype.card_le_of_injective (Sum.inl : σ → WeightedBasisIndex w d) Sum.inl_injective

end PolynomialTranslationLie
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DetectedTranslationNormalizedLogBounds
namespace OAI

section

namespace Erdos3

theorem scaleMvPolynomialAxes_mass_le_of_totalDegree {U : Type*} [Fintype U]
    (T : U → ℝ) (hT : ∀ i, 0 < T i) (P : MvPolynomial U ℝ)
    {d : ℕ} (hd : P.totalDegree ≤ d) {A : ℝ} (hA : 0 ≤ A)
    (hcoeff : ∀ α, |P.coeff α| ≤ A / monomialScale T α) :
    realPolynomialMass (scaleMvPolynomialAxes T P) ≤
      ((Fintype.card U : ℝ) + 1) ^ d * A := by
  apply (scaleMvPolynomialAxes_mass_le T hT P hcoeff).trans
  apply mul_le_mul_of_nonneg_right _ hA
  exact_mod_cast mvPolynomial_support_card_le_totalDegree P hd

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.NormalizedTwistLocalizedFourierSelection
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem torus_integer_character_real_phase {J : Type*} [Fintype J]
    (a : J → ℤ) (x : J → ℝ) :
    (∏ j, CircleFourier.character (a j • (x j : UnitAddCircle))) =
      (Real.fourierChar (∑ j, (a j : ℝ) * x j) : ℂ) := by
  rw [← CircleFourier.character_fintype_sum]
  have he : (∑ j, a j • (x j : UnitAddCircle)) =
      ((∑ j, (a j : ℝ) * x j : ℝ) : UnitAddCircle) := by
    simp only [← AddCircle.coe_zsmul, zsmul_eq_mul]
    exact (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
      (fun j => (a j : ℝ) * x j) Finset.univ).symm
  rw [he, CircleFourier.character_coe_exp, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowTaggedGradedSpace
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem lowTaggedCoordinates_mem_iff_low (d : ℕ)
    (K : Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ))
    (hK : BasisGradedSubmodule (Pi.basisFun ℝ _) (lowTaggedWeight J d) K)
    (x : ∀ j, J j → ℝ) :
    lowTaggedCoordinates J d x ∈ K ↔
      ∀ j, j.val + 1 ≤ d → x j ∈ lowTaggedSubspaceFamily J d K j := by
  rw [lowTaggedCoordinates_mem_iff J d K hK x]
  constructor
  · exact fun hx j _ => hx j
  · intro hx j
    by_cases hj : j.val + 1 ≤ d
    · exact hx j hj
    · simp only [lowTaggedSubspaceFamily, dif_neg hj, Submodule.mem_top]

theorem lowTaggedSubspaceFamily_span {A : Type*} (d : ℕ)
    (g : A → Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (hg : BasisGradedSubmodule (Pi.basisFun ℝ _) (lowTaggedWeight J d)
      (Submodule.span ℝ (Set.range g)))
    (j : Fin m) (hj : j.val + 1 ≤ d) :
    lowTaggedSubspaceFamily J d (Submodule.span ℝ (Set.range g)) j =
      Submodule.span ℝ (Set.range (fun a k => g a (lowTaggedSlot J d j hj k))) := by
  rw [lowTaggedSubspaceFamily, dif_pos hj]
  exact lowTagged_comap_span_eq J d j hj g hg

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeRefilteredSymbolConditions
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {L σ ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (W : LieSubalgebra ℚ F.AssociatedGraded)
  (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem native_refiltered_symbol_conditions
    (q : (F.gradedRefiltration W).realification.PolynomialOrbit w)
    (middle : (F.realification.adaptedPolynomialFiltration w).Group)
    (hmap : VectorPolynomial.map
      (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
      q.log = (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) :
    (F.realPolynomialSymbolHom b ω hF w middle).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W) ∧
    coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈
      F.realGradedRefiltrationLayer W 1 := by
  have hcoeff : ∀ α,
      coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
        F.realGradedRefiltrationLayer W (Finsupp.weight w α) := by
    intro α
    rw [← hmap, coefficients_map]
    exact (F.mem_native_refiltration_layer W (Finsupp.weight w α) _).mp
      (((F.gradedRefiltration W).realification.adapted_iff_coefficients w q.log).mp
        q.adapted α)
  constructor
  · apply (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF w W _).mpr
    exact (F.real_symbol_values_iff_refiltration_coefficients b ω hF w W middle.coord).mpr hcoeff
  · rw [← hmap, coefficients_map]
    apply (F.mem_native_refiltration_layer W 1 _).mp
    rw [(F.gradedRefiltration W).realification.one_eq_top]
    trivial

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedNativeFamilyMonotone
namespace OAI

section

namespace Erdos3

variable {σ Ω : Type*} {w : σ → ℕ} {degree : ℕ} {p q : ℝ}
  {sample : Ω → σ → ℤ} {f : Ω → ℂ}

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

noncomputable def NativeSampleModel.mono (F : NativeSampleModel w degree p sample f)
    (hpq : p ≤ q) : NativeSampleModel w degree q sample f where
  L := F.L
  dim := F.dim
  model := F.model
  test := F.test
  norm := F.norm
  complexity := F.complexity.mono hpq
  eval := F.eval

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslationMajorCorrelationDecomposition
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial

theorem realPolynomialMass_weightedHomogeneousComponent_le
    {σ : Type*} (P : MvPolynomial σ ℝ) (w : σ → ℕ) (d : ℕ) :
    realPolynomialMass (weightedHomogeneousComponent w d P) ≤ realPolynomialMass P := by
  classical
  have hs : (weightedHomogeneousComponent w d P).support ⊆ P.support := by
    rw [support_weightedHomogeneousComponent]
    exact Finset.filter_subset _ _
  rw [realPolynomialMass_eq_sum_of_support_subset _ P.support hs]
  apply Finset.sum_le_sum
  intro α _
  rw [coeff_weightedHomogeneousComponent]
  split_ifs
  · exact le_rfl
  · simpa only [abs_zero] using abs_nonneg (P.coeff α)

theorem realPolynomialMass_specializeMajorParameters_zero_le
    {U B : Type*} (P : MvPolynomial (U ⊕ B) ℝ) :
    realPolynomialMass (specializeMajorParameters (RingHom.id ℝ) P 0) ≤ realPolynomialMass P := by
  have h := realPolynomialMass_substitution_le P
    (Sum.elim (fun _ : U => (0 : MvPolynomial B ℝ)) X)
    (M := 1) le_rfl (fun i => by
      cases i with
      | inl i => simpa only [Sum.elim_inl, realPolynomialMass_zero] using (zero_le_one : (0 : ℝ) ≤ 1)
      | inr i => exact (realPolynomialMass_X i).le) (d := P.totalDegree) le_rfl
  simpa only [specializeMajorParameters, RingHomCompTriple.comp_eq, RingHom.coe_comp,
    Function.comp_apply, RingHom.id_apply, Pi.zero_apply, map_zero, one_pow, mul_one] using h

theorem reducedMajorZeroSlice_mass_le
    {U B : Type*} [Fintype U] [Fintype B]
    (w : B → ℕ) (hw : ∀ i, 0 < w i) (d : ℕ)
    (F : MvPolynomial (U ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    realPolynomialMass (specializeMajorParameters (RingHom.id ℝ)
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
        (fractionalCoefficientPolynomial F)) 0) ≤
      ((Fintype.card U : ℝ) + (Fintype.card B : ℝ) + 1)^d := by
  apply (realPolynomialMass_specializeMajorParameters_zero_le _).trans
  apply (realPolynomialMass_weightedHomogeneousComponent_le _ _ _).trans
  have h := fractionalCoefficientPolynomial_mass_le_of_weightedSupportLE F
    (Sum.elim (fun _ : U => 1) w) (fun i => by cases i <;> simp_all) d hF
  simpa only [Fintype.card_sum, Nat.cast_add] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RetainedPhysicalLowerDegree
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

def HasNativeLowerDegreeOrbit {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (w : σ → ℕ) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) : Prop :=
  ∃ (q : (F.gradedRefiltration W).realification.PolynomialOrbit w)
    (qbar : (F.gradedRefiltration W).quotientTop.realification.PolynomialOrbit w),
    VectorPolynomial.map
      (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
      q.log = p ∧ coefficients q.log 0 = 0 ∧ DegreeLE w s qbar.log ∧
    ∀ x, (F.gradedRefiltration W).quotientTop.realification.polynomialOrbitEval w x qbar =
      (F.gradedRefiltration W).realQuotientStepHom
        ((F.gradedRefiltration W).layerIdeal (s + 1)) le_rfl
        ((F.gradedRefiltration W).realification.polynomialOrbitEval w x q)

end NilpotentLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedPhysicalCRT
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {J : Type*} [Fintype J] {q : ℕ} [NeZero q]

noncomputable def affinePeriodParameterLaw (D : ℕ) (a : J → ℤ) :
    FiniteProbabilityWeights (J → ZMod q) :=
  (FiniteProbabilityWeights.uniform (J → ZMod q)).fiberLaw
    (fun s j => (a j : ZMod q) + (D : ZMod q) * s j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SpatialAffineFullMass
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {K X : Type*} [Fintype K]

theorem spatialAffineTop_mass_le
    (frame : Option K → X → ℝ) (T : K → ℝ) (hT : ∀ k, 0 ≤ T k) (x : X) :
    realPolynomialMass
      (scaleMvPolynomialAxes T (homogeneousComponent 1 (affineFramePolynomial frame x))) ≤
        ∑ k, |frame (some k) x| * T k := by
  rw [scaleMvPolynomialAxes_affineFrame_top_one]
  apply (realPolynomialMass_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  have h := realPolynomialMass_C_mul_le (frame (some k) x * T k) (MvPolynomial.X k)
  simpa only [realPolynomialMass_X, mul_one, abs_mul, abs_of_nonneg (hT k)] using h

theorem spatialAffineTop_inv_mul_mass_le
    (frame : Option K → X → ℝ) (T : K → ℝ) (hT : ∀ k, 0 ≤ T k)
    (x : X) (N : ℝ) (hN : 0 < N) :
    realPolynomialMass (C N⁻¹ *
      scaleMvPolynomialAxes T (homogeneousComponent 1 (affineFramePolynomial frame x))) ≤
        N⁻¹ * ∑ k, |frame (some k) x| * T k := by
  apply (realPolynomialMass_C_mul_le _ _).trans
  rw [abs_of_pos (inv_pos.mpr hN)]
  exact mul_le_mul_of_nonneg_left (spatialAffineTop_mass_le frame T hT x)
    (inv_nonneg.mpr hN.le)

theorem spatialAffineTop_scaled_inv_mul_mass_le
    (frame : Option K → X → ℝ) (T : K → ℝ) (hT : ∀ k, 0 ≤ T k)
    (x : X) (N : ℝ) (hN : 0 < N) :
    realPolynomialMass (scaleMvPolynomialAxes T
      (C N⁻¹ * homogeneousComponent 1 (affineFramePolynomial frame x))) ≤
        N⁻¹ * ∑ k, |frame (some k) x| * T k := by
  rw [scaleMvPolynomialAxes_C_mul]
  exact spatialAffineTop_inv_mul_mass_le frame T hT x N hN

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualMarkedSlowKernelCells
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_bounded_subgroup_net
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) {H : ℕ}
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (K : Subgroup (NilpotentLieBCHGroup L s hnil))
    (B : ℝ≥0) (hB : 1 ≤ B) {N : ℕ} (hN : 0 < N) :
    let := rightMetricSpace (hnil := hnil) e
    ∃ center : (ι → Fin (N + 1)) → NilpotentLieBCHGroup L s hnil,
      (∀ j, center j ∈ K) ∧
      (∀ j i, |e.repr (center j).coord i| ≤ B) ∧
      ∀ g : NilpotentLieBCHGroup L s hnil, g ∈ K →
        (∀ i, |e.repr g.coord i| ≤ B) →
        ∃ j, dist g (center j) ≤
          bchBoxMetricConstant s (Fintype.card ι) H B * (4 * B / N) := by
  classical
  let := rightMetricSpace (hnil := hnil) e
  let Ω := {g : NilpotentLieBCHGroup L s hnil //
    g ∈ K ∧ ∀ i, |e.repr g.coord i| ≤ B}
  have hBr : (1 : ℝ) ≤ B := hB
  let : Nonempty Ω := ⟨⟨1, K.one_mem, by simp⟩⟩
  obtain ⟨code, rep, hrep⟩ := exists_uniform_parameter_net
    (fun g : Ω => e.equivFun g.val.coord) (by positivity : (0 : ℝ) < B)
    (fun g i => g.property.2 i) hN
  refine ⟨fun j => (rep j).val, fun j => (rep j).property.1,
    fun j i => (rep j).property.2 i, ?_⟩
  intro g hg hgb
  let x : Ω := ⟨g, hg, hgb⟩
  refine ⟨code x, ?_⟩
  apply dist_le_bchBoxMetricConstant e c hstructure hc B hB (by positivity)
    g (rep (code x)).val hgb (rep (code x)).property.2
  intro i
  exact (show |e.repr g.coord i - e.repr (rep (code x)).val.coord i| ≤
      dist (e.equivFun x.val.coord) (e.equivFun (rep (code x)).val.coord) from
    by simpa only [Real.dist_eq, Basis.equivFun_apply, x] using
      dist_le_pi_dist (e.equivFun x.val.coord)
        (e.equivFun (rep (code x)).val.coord) i).trans (hrep x)

theorem exists_bounded_kernel_net {G : Type*} [Group G]
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) {H : ℕ}
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (π : NilpotentLieBCHGroup L s hnil →* G)
    (B : ℝ≥0) (hB : 1 ≤ B) {N : ℕ} (hN : 0 < N) :
    let := rightMetricSpace (hnil := hnil) e
    ∃ center : (ι → Fin (N + 1)) → NilpotentLieBCHGroup L s hnil,
      (∀ j, π (center j) = 1) ∧
      (∀ j i, |e.repr (center j).coord i| ≤ B) ∧
      ∀ g : NilpotentLieBCHGroup L s hnil, π g = 1 →
        (∀ i, |e.repr g.coord i| ≤ B) →
        ∃ j, dist g (center j) ≤
          bchBoxMetricConstant s (Fintype.card ι) H B * (4 * B / N) := by
  exact exists_bounded_subgroup_net e c hstructure hc π.ker B hB hN

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_bounded_kernel_net_with_budget {G : Type*} [Group G]
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) {H : ℕ}
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (π : NilpotentLieBCHGroup L s hnil →* G)
    (B : ℝ≥0) (hB : 1 ≤ B) {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hd : (Fintype.card ι : ℝ) ≤ p) (hBp : (B : ℝ) ≤ Real.exp p)
    (hK : (bchBoxMetricConstant s (Fintype.card ι) H B : ℝ) ≤ Real.exp p)
    (hεinv : 1 / ε ≤ Real.exp p) :
    letI := rightMetricSpace (hnil := hnil) e
    ∃ N : ℕ, 0 < N ∧
      (Fintype.card (ι → Fin (N + 1)) : ℝ) ≤
        Real.exp ((p + 1) * (3 * (p + 1) + 4)) ∧
      ∃ center : (ι → Fin (N + 1)) → NilpotentLieBCHGroup L s hnil,
        (∀ j, π (center j) = 1) ∧
        (∀ j i, |e.repr (center j).coord i| ≤ B) ∧
        ∀ g : NilpotentLieBCHGroup L s hnil, π g = 1 →
          (∀ i, |e.repr g.coord i| ≤ B) →
          ∃ j, dist g (center j) ≤ ε := by
  classical
  let := rightMetricSpace (hnil := hnil) e
  let K := bchBoxMetricConstant s (Fintype.card ι) H B
  let N := boxCoverMeshCount (2 * B) K ε
  have hN : 0 < N := boxCoverMeshCount_pos _ _ _
  have hexp : Real.exp p ≤ Real.exp (p + 1) := Real.exp_le_exp.mpr (by linarith)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hBp' : 2 * (B : ℝ) ≤ Real.exp (p + 1) := by
    rw [Real.exp_add]
    exact (mul_le_mul_of_nonneg_left hBp (by norm_num)).trans
      (by nlinarith [Real.exp_pos p])
  have hcard := boxCoverCount_dimension_bound (Fintype.card ι) K
    (by positivity : 0 ≤ 2 * (B : ℝ)) hε (by linarith : 0 ≤ p + 1)
    (by linarith : (Fintype.card ι : ℝ) ≤ p + 1) hBp' (hK.trans hexp)
    (hεinv.trans hexp)
  obtain ⟨center, hmark, hbound, hnet⟩ :=
    exists_bounded_kernel_net e c hstructure hc π B hB hN
  refine ⟨N, hN, ?_, center, hmark, hbound, ?_⟩
  · simpa only [Fintype.card_fun, Fintype.card_fin] using hcard
  · intro g hg hgb
    obtain ⟨j, hj⟩ := hnet g hg hgb
    refine ⟨j, hj.trans ?_⟩
    have hm := boxCoverMeshCount_error (B := 2 * (B : ℝ)) K hε
    dsimp only [N, K] at *
    simpa only [show (2 : ℝ) * (2 * B) = 4 * B by ring] using hm

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorPhaseVectorDecomposition
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module RationalFilteredNilmanifold PolynomialTranslationLie

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)] (d : ℕ)

noncomputable def majorPhaseTaggedGenerators {A : Type*}
    (g : A → weightedSubalgebra (lowTaggedWeight J d) d)
    (j : Fin m) (hj : j.val + 1 ≤ d) (a : A) (i : J j) : ℚ :=
  (g a).val.base (lowTaggedSlot J d j hj i)

 theorem majorPhaseTaggedGenerators_logHeight {A : Type*}
    (g : A → weightedSubalgebra (lowTaggedWeight J d) d) {B : ℝ}
    (hheight : ∀ a i, rationalLogHeight
      ((weightedBasis (lowTaggedWeight J d) d (lowTaggedWeight_pos J d)).repr (g a) i) ≤ B)
    (j : Fin m) (hj : j.val + 1 ≤ d) (a : A) (i : J j) :
    rationalLogHeight (majorPhaseTaggedGenerators J d g j hj a i) ≤ B := by
  have h := hheight a (Sum.inl (lowTaggedSlot J d j hj i))
  simpa only [weightedBasis_repr_inl, majorPhaseTaggedGenerators] using h

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OrdinaryPolynomialPhaseAffineInverse
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedMixedLiftNormalizedMass
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial

theorem normalizedPolynomialMass_neg {V : Type*} (p : MvPolynomial V ℝ) :
    realPolynomialMass (-p) = realPolynomialMass p := by
  simp only [realPolynomialMass, support_neg, coeff_neg, abs_neg]

end Erdos3

end

section

namespace Erdos3
open Module Submodule

variable {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

variable [Fintype V]

theorem mixedLiftPolynomial_scaled_mass
    (e : J → V →₀ ℕ) (he : Function.Injective e)
    (a : (I → J → ℝ) × (Fin n → J → ℤ))
    (T : V → ℝ) (hT : ∀ v, 0 < T v) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (hc : ∀ i j, |a.1 i j| * monomialScale T (e j) ≤ R)
    (hz : ∀ i j, |(a.2 i j : ℝ) / basisAxisScale b i| * monomialScale T (e j) ≤ R)
    {s : ℕ} (hdegree : ∀ j, (e j).sum (fun _ k => k) ≤ s) (d : D) :
    realPolynomialMass (scaleMvPolynomialAxes T (mixedLiftPolynomial W b o e a d)) ≤
      ((s + 1 : ℕ) : ℝ) * ((Fintype.card V + 1 : ℕ) : ℝ) ^ s *
        (C * (((Fintype.card I : ℝ) + 1) * R)) := by
  apply (scaleMvPolynomialAxes_mass_le T hT _
    (fun α => mixedLiftPolynomial_scaled_coefficients W b o e he a T hT hC hR
      hchart hc hz α d)).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast polynomial_support_card_le _ (mixedLiftPolynomial_degree W b o e a hdegree d)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NormalizedFrozenPolynomialMass
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial

theorem realPolynomialMass_freezePolynomial_le {I : Type*} (keep : I → Prop)
    (fixed : {i // ¬ keep i} → ℝ) (hfixed : ∀ i, |fixed i| ≤ 1)
    (P : MvPolynomial I ℝ) :
    realPolynomialMass (freezePolynomial keep fixed P) ≤ realPolynomialMass P := by
  have hf : ∀ i, realPolynomialMass (frozenCoordinate keep fixed i) ≤ 1 := by
    intro i
    classical
    by_cases hi : keep i
    · simp only [frozenCoordinate, dif_pos hi, realPolynomialMass_X, le_refl]
    · simpa only [frozenCoordinate, dif_neg hi, realPolynomialMass_C] using hfixed ⟨i, hi⟩
  have h := realPolynomialMass_substitution_le P (frozenCoordinate keep fixed)
    (M := 1) le_rfl hf le_rfl
  change realPolynomialMass (eval₂Hom C (frozenCoordinate keep fixed) P) ≤ _
  simpa only [one_pow, mul_one] using h

theorem normalizedMass_freezePolynomial_le {I : Type*} (keep : I → Prop)
    (T : I → ℝ) (hT : ∀ i, 0 < T i) (fixed : {i // ¬ keep i} → ℝ)
    (hfixed : ∀ i, |fixed i| ≤ T i.val) (P : MvPolynomial I ℝ) :
    realPolynomialMass
      (scaleMvPolynomialAxes (fun i : {i // keep i} => T i.val) (freezePolynomial keep fixed P)) ≤
      realPolynomialMass (scaleMvPolynomialAxes T P) := by
  rw [scaleMvPolynomialAxes_freezePolynomial keep T (fun i => (hT i).ne')]
  apply realPolynomialMass_freezePolynomial_le
  intro i
  rw [abs_div, abs_of_pos (hT i.val)]
  exact (div_le_one (hT i.val)).mpr (hfixed i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTagRestrictionBudget
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {U B I : Type*} [Fintype I]

theorem polynomialTagLinearEmbedding_mass_le (E : B → I → ℝ)
    {L : ℝ} (hE : ∀ b i, |E b i| ≤ L) (j : U ⊕ B) :
    realPolynomialMass (polynomialTagLinearEmbedding E j) ≤
      max 1 ((Fintype.card I : ℝ) * L) := by
  classical
  cases j with
  | inl u =>
      simpa only [polynomialTagLinearEmbedding_inl, realPolynomialMass_X]
        using le_max_left 1 ((Fintype.card I : ℝ) * L)
  | inr b =>
      rw [polynomialTagLinearEmbedding_inr]
      apply (realPolynomialMass_sum_le _ _).trans
      apply le_trans (b := ∑ _i : I, L)
      · apply Finset.sum_le_sum
        intro i _
        exact (realPolynomialMass_C_mul_le _ _).trans
          (by simpa only [realPolynomialMass_X, mul_one] using hE b i)
      · simp

theorem polynomialTagRestriction_mass_le (E : B → I → ℝ)
    (p : MvPolynomial (U ⊕ B) ℝ) {L : ℝ} {s : ℕ}
    (hE : ∀ b i, |E b i| ≤ L) (hp : p.totalDegree ≤ s) :
    realPolynomialMass (aeval (polynomialTagLinearEmbedding E) p) ≤
      realPolynomialMass p * (max 1 ((Fintype.card I : ℝ) * L)) ^ s :=
  realPolynomialMass_substitution_le p (polynomialTagLinearEmbedding E)
    (le_max_left _ _) (polynomialTagLinearEmbedding_mass_le E hE) hp

end Erdos3

end

end OAI
end


