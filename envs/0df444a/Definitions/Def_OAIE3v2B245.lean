-- Prove2me | Definitions.Def_OAIE3v2B245
-- name    : OAIE3v2B245
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T05:03:21.892262+00:00
-- url     : https://prove2.me/theorems/d0be2bdc-2d24-49b4-8328-538b4fc11bbb
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 250 of 311
-- statement:
--   Definitions bundle 250 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B301`, `OAIE3v2B220`, `OAIE3v2B225`, `OAIE3v2B228`, `OAIE3v2B231`, `OAIE3v2B232`, `OAIE3v2B233`, `OAIE3v2B234` of this split.
--
--   Modules: `Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean`, `Estimates/AllocatedExternalCandidateStepZero.lean`, `Estimates/AllocatedFrozenTaggedTwistStepDrop.lean`, `Estimates/AllocatedSlicedRowsProjectedSource.lean`, `Estimates/UnconditionalStepDrop.lean`, `Estimates/UnitVerticalNativeInverseModels.lean`, `Fourier/AllocatedRecoveredTagTorusVariation.lean`, `Geometry/ActualFixedSpatialSlicedAnalyticIdentification.lean`, `Geometry/AllocatedExternalLocalChartOrbitValues.lean`, `Lattices/AllocatedModularRankAffineFullWitness.lean`, `Lattices/CertifiedFullChartAffineTerminal.lean`, `Linear/AllocatedCanonicalSlicedConstructedProjection.lean`, `Probability/ActualFixedSpatialSlicedDensityBounds.lean`, `Sampling/ForecastPreparedScaleBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B301
import Definitions.Def_OAIE3v2B220
import Definitions.Def_OAIE3v2B225
import Definitions.Def_OAIE3v2B228
import Definitions.Def_OAIE3v2B231
import Definitions.Def_OAIE3v2B232
import Definitions.Def_OAIE3v2B233
import Definitions.Def_OAIE3v2B234

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnconditionalStepDrop
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_frozen_middle_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} {σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      {g : (D.filtration.realification.adaptedPolynomialFiltration
        (fun _ : σ => 1)).Group}
      {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
      (R : NativePolynomialOrbitFactors D g eta A p)
      (T : D.Niltest (fun _ : σ => 1)), 0 ≤ p → T.ComplexityLE p →
      (∀ z : D.RealGroup,
        z.coord ∈ D.filtration.realGradedRefiltrationLayer R.subalgebra (s + 1) →
        ∀ x, T.observable (z • x) = T.observable x) →
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.exp p → ∀ a r : D.RealGroup,
        (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp p) →
        (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m →
        Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C)
          (fun x => T.observable (QuotientGroup.mk (R.frozenMiddleValue a r x)))) := by
  obtain ⟨B, _, hmodel⟩ := exists_native_middle_model
  obtain ⟨K, _, hdesc⟩ := exists_uniform_frozen_descent s 1
  let X : Polynomial ℕ := Polynomial.X
  let P := X + (X + Polynomial.C B) ^ B + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C K) ^ K)
  refine ⟨C, hC, ?_⟩
  intro L σ _ _ _ _ _ _ d D g eta A p R T hp hT hinv m hm hmb a r ha hr
  obtain ⟨E, hEF, _hEL, hE, hinc, h, hh⟩ := hmodel D R hp hT.1
  let : TopologicalSpace (ℝ ⊗[ℚ]
      D.filtration.gradedRefiltrationSubalgebra R.subalgebra) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
      D.filtration.gradedRefiltrationSubalgebra R.subalgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  let t := p + (p + B) ^ B + 4
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith [pow_nonneg (by positivity : 0 ≤ p + B) B]
  have hEt : (p + B) ^ B ≤ t := by dsimp [t]; linarith
  obtain ⟨_Λ, _hΛ, _hchar, _hnormal, _hfinite, _hindex,
      n, _hn, Q, hQF, _hQL, _hQ, hfamily⟩ :=
    hdesc E D (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl T h ht
      (hE.mono E hEt) (hT.mono hpt) (fun i j => (hinc j i).trans hEt)
      m hm (hmb.trans (Real.exp_le_exp.mpr hpt))
  let : TopologicalSpace (ℝ ⊗[ℚ]
      (D.filtration.gradedRefiltrationSubalgebra R.subalgebra ⧸
        E.filtration.layerIdeal (s + 1))) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
      (D.filtration.gradedRefiltrationSubalgebra R.subalgebra ⧸
        E.filtration.layerIdeal (s + 1))) := IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  have ha' : ∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((t + 2) ^ 1) :=
    fun i => (ha i).trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  obtain ⟨S, _hSo, _hSn, hSc, hSe⟩ := hfamily a r ha' hr
    (D.frozen_refiltered_top_invariant R.subalgebra E hEF T.observable hinv a r)
  have hcost : (t + K) ^ K ≤ (p + C) ^ C := by
    simpa [P, X, t, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨NativeIntegerExpansion.ofTest S (hSc.mono hcost) ?_⟩
  intro x
  exact ((hSe x).trans (congrArg
    (fun z : D.RealGroup => T.observable (QuotientGroup.mk (a * z * r))) (hh x))).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalNativeInverseModels
namespace OAI

section

namespace Erdos3

theorem exists_vertical_native_inverse_models {s C : ℕ} (hI : CyclicNativeInverse s C) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 2) f →
      ∃ R : NativeCommonDerivativeModels s N ((p + D) ^ D) f,
        Nonempty (NativeVerticalDerivativeData R) := by
  obtain ⟨a, _, hmodels⟩ := exists_normalized_native_inverse_models hI
  obtain ⟨b, _, hvertical⟩ := exists_native_vertical_derivative_models
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C a) ^ a + Polynomial.C b) ^ b)
  refine ⟨D, hD, ?_⟩
  intro N _ p hp f hf hG
  have hq : 0 ≤ (p + a) ^ a := by positivity
  have hcost : ((p + a) ^ a + b) ^ b ≤ (p + D) ^ D := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨B, hB⟩ := hmodels hp f hf hG
  obtain ⟨R, ⟨V⟩⟩ := hvertical hq hf B hB
  exact ⟨R.mono hcost, ⟨V.mono hcost⟩⟩

end Erdos3

end

section

namespace Erdos3

theorem exists_unit_vertical_native_inverse_models {s C : ℕ} (hI : CyclicNativeInverse s C) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 2) f →
      ∃ R : NativeCommonDerivativeModels s N ((p + D) ^ D) f,
      ∃ V : NativeVerticalDerivativeData R,
        Nonempty (NativeUnitVerticalData R V ((p + D) ^ D)) := by
  obtain ⟨a, _, hmodels⟩ := exists_vertical_native_inverse_models hI
  obtain ⟨b, _, hunit⟩ := exists_native_unit_vertical_data s
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget (P + (P + Polynomial.C b) ^ b)
  refine ⟨D, hD, ?_⟩
  intro N _ p hp f hf hG
  have hp0 : 0 ≤ (p + a) ^ a := by positivity
  have hp1 : 0 ≤ ((p + a) ^ a + b) ^ b := by positivity
  have htotal : (p + a) ^ a + ((p + a) ^ a + b) ^ b ≤ (p + D) ^ D := by
    simpa [P, X, Polynomial.eval₂_pow] using hbudget p hp
  have h0 : (p + a) ^ a ≤ (p + D) ^ D := by linarith
  have h1 : ((p + a) ^ a + b) ^ b ≤ (p + D) ^ D := by linarith
  obtain ⟨B, ⟨V⟩⟩ := hmodels hp f hf hG
  obtain ⟨U⟩ := hunit B V hp0 hf
  exact ⟨B.mono h0, V.mono h0, ⟨U.mono h0 h1⟩⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedRowsProjectedSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

universe uX

theorem exists_allocated_sliced_projected_source (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    [DecidableEq (LayerSamplerVariables G I n B)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (x : G → IntegerScalarCubeBox (Fin q) S.value)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P W : ℝ} (_hP : 0 ≤ P) (_hm : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hW : 0 ≤ W) (_hbudget : allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ W)
    (_hWP : W ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M)
    {X : Type uX} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ ξ : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (signal : (X → ℤ) → ℂ) (_hsignal : ∀ v, ‖signal v‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty)
    (D : ℕ)
    (f : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U basis S) →
      EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ),
    let density := allocatedCoefficientDensity B U basis hb o hR hσ S
    ∀ (_hproject : ∀ y, physicalDensityProjection.{_, _, uX, 0} U
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) D density (f y)),
    let widths := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (hwidths : ∀ z, 0 < widths z) (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    ∀ law : FiniteProbabilityWeights (PrincipalIntegerTuples B (layerSamplerDegree I n)
      (Fin q) (allocatedPrincipalSides B U basis S)),
    let Z := selectedJointDensityMass bases stride T widths (allocatedJointBaseDensity B U basis hb o hR hσ S X p hm)
    ∀ (_hZ : 0 < Z) (_hZi : Z⁻¹ ≤ Real.exp P) {κ : ℝ},
    κ ≤ (law.complexMean (fun y => allocatedSlicedTupleValue B U basis hb o hR hσ S X p hm
      N hN _hW _hτ _hξ stride T hmass bases x y signal)).re →
    ∃ base ∈ bases,
      let projected := fun y => ∑' z,
        ((selectedResidueSmoothPMF stride T widths hwidths hmass z).toReal : ℂ) *
          physicalCubePositiveTest U D p hm (f y) (integerSelfSiteTest q signal) (physicalCubeRootDifferences
            (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U basis S x y) base z)
      κ - Real.exp (-P) ≤ (law.complexMean projected / (Z : ℂ)).re := by
  obtain ⟨A, hA, hprojection⟩ := exists_allocated_original_density_projection_law m q
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ _ n B _ _ _ J _ U _ basis R σ S x hb o hR hσ C V hC hV
    hσ1 Cinv hCinv hchart hsmall P W hP hmSize hK hW hroot hWP hL hRP hσP hcount hI hn hJ
    hAP hCP hVP M hperiod X _ _ hX hdim p hp hm stride hs hsP τ ξ hτ hτP hξ hξ1 hξP
    N hN hsize rank hrank hRank signal hsignal T hT bases hbases D f density hproject widths hwidths hmass
    law Z hZ hZi κ hsource
  obtain ⟨base, hbase, hpositive⟩ := allocatedSlicedTupleValue_select_base B U basis hb o hR hσ S X p hm
    N hN hW hτ hξ stride T hmass bases hbases x law signal hsource
  have he := hprojection B U basis S (fun _ => 0) x hb o hR hσ C V hC hV hσ1
    Cinv hCinv hchart hsmall hP hmSize hK hW hroot hWP hL hRP hσP hcount hI hn hJ hAP hCP hVP
    hperiod hX hdim p hp hm base stride hs hsP hτ hτP hξ hξ1 hξP N hsize hrank hRank
    (integerSelfSiteTest q signal) (integerSelfSiteTest_norm_le q signal hsignal) T hT D f hproject
    hZ hZi hwidths hmass law
  refine ⟨base, hbase, ?_⟩
  dsimp only at he ⊢
  have hdiff := (Complex.re_le_norm _).trans he
  rw [Complex.sub_re] at hdiff
  change κ ≤ _ at hpositive
  dsimp only [allocatedJointBaseDensity] at hpositive
  linarith only [hpositive, hdiff]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

universe uX

theorem exists_allocated_sliced_rows_projected_source (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    [DecidableEq (LayerSamplerVariables G I n B)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (x : G → IntegerScalarCubeBox (Fin q) S.value)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P W : ℝ} (_hP : 0 ≤ P) (_hm : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hW : 0 ≤ W) (_hbudget : allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ W)
    (_hWP : W ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M)
    {X : Type uX} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ ξ : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (signal : (X → ℤ) → ℂ) (_hsignal : ∀ v, ‖signal v‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty)
    (D : ℕ)
    (f : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U basis S) →
      EuclideanJetLayers U (fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)}) → ℝ),
    let density := allocatedCoefficientDensity B U basis hb o hR hσ S
    ∀ (_hproject : ∀ y, physicalDensityProjection.{_, _, uX, 0} U
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) D density (fun z => f y ((physicalRowsStandardEquiv U).symm z))),
    let widths := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (hwidths : ∀ z, 0 < widths z) (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    ∀ law : FiniteProbabilityWeights (PrincipalIntegerTuples B (layerSamplerDegree I n)
      (Fin q) (allocatedPrincipalSides B U basis S)),
    let Z := selectedJointDensityMass bases stride T widths (allocatedJointBaseDensity B U basis hb o hR hσ S X p hm)
    ∀ (_hZ : 0 < Z) (_hZi : Z⁻¹ ≤ Real.exp P) {κ : ℝ},
    κ ≤ (law.complexMean (fun y => allocatedSlicedTupleValue B U basis hb o hR hσ S X p hm
      N hN _hW _hτ _hξ stride T hmass bases x y signal)).re →
    ∃ base ∈ bases,
      let projected := fun y => ∑' z,
        ((selectedResidueSmoothPMF stride T widths hwidths hmass z).toReal : ℂ) *
          (physicalCubeSiteTest (integerSelfSiteTest q signal) (physicalCubeRootDifferences
            (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U basis S x y) base z) *
          (f y (physicalCubeRowSample U D (fun j =>
            (Subtype.val : {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)} → Finset (Fin q))) p hm
            (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
              (allocatedPhysicalCubeDirections B U basis S x y) base z)) : ℂ))
      κ - Real.exp (-P) ≤ (law.complexMean projected / (Z : ℂ)).re := by
  obtain ⟨A, hA, hprojection⟩ := exists_allocated_sliced_projected_source.{uX} m q
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ _ n B _ _ _ J _ U _ basis R σ S x hb o hR hσ C V hC hV
    hσ1 Cinv hCinv hchart hsmall P W hP hmSize hK hW hroot hWP hL hRP hσP hcount hI hn hJ
    hAP hCP hVP M hperiod X _ _ hX hdim p hp hm stride hs hsP τ ξ hτ hτP hξ hξ1 hξP
    N hN hsize rank hrank hRank signal hsignal T hT bases hbases D f density hproject widths hwidths hmass
    law Z hZ hZi κ hsource
  obtain ⟨base, hbase, he⟩ := hprojection B U basis S x hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall
    hP hmSize hK hW hroot hWP hL hRP hσP hcount hI hn hJ hAP hCP hVP hperiod hX hdim p hp hm
    stride hs hsP hτ hτP hξ hξ1 hξP N hN hsize hrank hRank signal hsignal T hT bases hbases D
    (fun y z => f y ((physicalRowsStandardEquiv U).symm z)) hproject hwidths hmass law hZ hZi hsource
  refine ⟨base, hbase, ?_⟩
  simpa only [physicalCubePositiveTest_rows U D p hp hm] using he

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

theorem enlargedPreparedCommonSampler_variables_card (Jalloc : ℕ) :
    Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc)
      (PreparedSamplerContinuous L) (preparedSamplerTransverse L)
      (EnlargedPreparedCommonSamplerBlock L Jalloc)) =
      (m + 1) * (m + 3) + (m + 1) * Jalloc + ∑ j : Fin m,
        Fintype.card (L j).Coord * ((preparedCommonBlockCount m j + Jalloc) * (j.val + 1)) := by
  rw [samplerTupleIndex_card]
  simp only [EnlargedPreparedCommonKernel, Fintype.card_fin, LayerSamplerAxis, Fintype.sum_sigma,
    EnlargedPreparedCommonSamplerBlock, layerSamplerDegree, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simpa only [PreparedSamplerContinuous, Fintype.card_fin, Nat.cast_id] using
    congrArg (fun d : ℕ => d * ((preparedCommonBlockCount m j + Jalloc) * (j.val + 1)))
      (preparedSampler_axis_card L j)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineFullWitness
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]
variable (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ)

theorem allocatedActualPrimeBad_depth (A : ℕ → ℕ) (p : ℕ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    largestTestedBadDepth A (allocatedActualPrimeBad inactive spatial kernel block P C) p f =
      allocatedCongruenceBadDepth inactive (allocatedReadNoise f) (allocatedReadDeck f)
        (fun j a => allocatedReadProjection f ⟨j, a.val⟩) spatial kernel block P A C p := by
  unfold allocatedCongruenceBadDepth largestTestedBadDepth
  apply congrArg (fun t : Finset ℕ => t.sup id)
  apply Finset.filter_congr
  intro a _
  exact (allocatedActualPrimeBad_eq_rankBad inactive spatial kernel block P C p a f).to_iff

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedNativeAmbientComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {T : Type*} [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
  (allocatedLayerWidths B U basis S j)
  (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable (base : X → ℤ) (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (box : X → ℕ) (hbox : ∀ a, 0 < box a) {τ : ℝ} (hτ : τ ≠ 0)
variable (q : ℕ) [NeZero q] (hm : 0 < m)
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
variable (hbase : canonicalCoefficientSample U basis hb o sample =
  affineSampleCoefficientTorus U nativePoly hmem
    (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
      integerFrame) (k, x) : ℝ)))
variable (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)
variable (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)
variable (HG : G → ℕ) (hHG : ∀ g, 2 ≤ HG g) (cG : G → ℤ) (stepG : ℕ)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
  Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (S.value : ℤ))

local instance slicedNativeSourceMeanCoverNeZero_raa0a83_1 : NeZero W.cover := ⟨W.cover_pos.ne'⟩
noncomputable def allocatedSlicedNativeEvalMean : ℂ :=
  let kernel := FiniteProbabilityWeights.pi (fun g =>
    integerScalarCubeWeights Empty (HG g) (lt_of_lt_of_le (by decide : 0 < 2) (hHG g)))
  let active := FiniteProbabilityWeights.pi (fun j : Input =>
    integerScalarCubeWeights Empty (H j) (lt_of_lt_of_le (by decide : 0 < 2) (hH j)))
  let embed := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) g =>
    containedProgressionCubeMap Empty S.value (HG g) stepG (cG g)
      S.positive (hcontainedG g) (x g)
  let joined := fun u v => principalAxisJoin short u
    (allocatedActiveContainedProgression B U basis S (fun _ => stepG) H c hsubset v)
  let shortLaw := allocatedInactiveAffineIntervalLaw B U basis S HP stepP cP hinsideP hHP
  shortLaw.complexMean (fun u => kernel.complexMean (fun x => active.complexMean (fun v =>
    W.eval box nativePoly (fun a => base a + integerPhysicalSite
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) (embed x) (joined u v)) integerFrame a))))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateStepZero
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {d : ℕ}
    (D : RationalFilteredNilmanifold L 0 d) (Fmark : NilpotentLieFiltration M 0)
    (φ : L →ₗ⁅ℚ⁆ M)
    (marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace AllocatedExternalCandidateProblem

theorem ambientScore_one_eq (z : P.productive) :
    P.ambientScore 1 z (P.chart z).slice.integerPoints =
      (P.candidate z).score observable weight := by
  unfold ambientScore AllocatedExternalLocalCandidate.score AllocatedExternalLocalCandidate.value
  congr 2
  funext u
  congr 2
  apply congrArg QuotientGroup.mk
  exact (D.filtration.realification.externalCandidate_stepZero_group_eq_one _).trans
    (D.filtration.realification.externalCandidate_stepZero_group_eq_one _).symm

theorem conclusion_stepZero : Nonempty (P.Conclusion cost massThreshold scoreThreshold) := by
  classical
  refine ⟨{
    ambient := 1
    marked := ?_
    retained := P.productive
    subset := fun _ h => h
    mass := P.mass
    step := fun z => (P.chart z).step
    step_pos := fun z => (P.chart z).step_pos
    slice := fun z => (P.chart z).slice
    dense := fun z => (P.chart z).dense
    inside := fun _ _ h => h
    score := ?_
  }⟩
  · apply coefficients.injective
    ext α
    rw [coefficients_map]
    exact (Fmark.realification.externalCandidate_stepZero_coord_eq_zero _).trans
      (Fmark.realification.externalCandidate_stepZero_coord_eq_zero _).symm
  · intro z
    rw [P.ambientScore_one_eq]
    exact P.score z

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedRecoveredTagTorusVariation
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

variable {m : ℕ} {X : Type*} {J : Fin m → Type*} [∀ j, Fintype (J j)]

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G : Type*} [Fintype G] {I E : Fin m → Type*}
variable [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_remainder_at_site
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (x : LayerSamplerVariables G I n B → ℤ) (j : Fin m) (i : J j) :
    eval (fun z => (jointIntegerPhysicalSite x (a, v) z : ℝ)) (poly j) i =
      (c j).val i + mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
        (sample j).1 (sample j).2 (fun k => (x k : ℝ)) i +
      (MvPolynomial.eval x (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample
        (Sum.inr ⟨j, i⟩)) : ℝ) := by
  have hr := h.integerFullChart_remainder B U b hb o S hR hσ poly hm hp c a v sample read
    (fun k => (x k : ℝ)) j i
  rw [← eval_jointIntegerPhysicalSite_eq_frame a v, integerSampledRealChart_eval] at hr
  linarith

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_torus_dist
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (q : ℕ) (hq : 0 < q) (x y : LayerSamplerVariables G I n B → ℤ)
    (hxy : ∀ k, (x k : ZMod q) = (y k : ZMod q))
    {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ j i, |mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
        (sample j).1 (sample j).2 (fun k => (x k : ℝ)) i -
      mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
        (sample j).1 (sample j).2 (fun k => (y k : ℝ)) i| ≤ ε) :
    dist (physicalGridFactorInput q poly (fun z => (jointIntegerPhysicalSite x (a, v) z : ℝ)))
      (physicalGridFactorInput q poly (fun z => (jointIntegerPhysicalSite y (a, v) z : ℝ))) ≤ ε / q := by
  apply physicalGridFactorInput_dist_le_of_integer_remainders q hq poly
    (fun z => (jointIntegerPhysicalSite x (a, v) z : ℝ))
    (fun z => (jointIntegerPhysicalSite y (a, v) z : ℝ))
    (fun j => (c j).val)
    (fun j => mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
      (sample j).1 (sample j).2 (fun k => (x k : ℝ)))
    (fun j => mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
      (sample j).1 (sample j).2 (fun k => (y k : ℝ)))
    (fun j i => MvPolynomial.eval x
      (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample (Sum.inr ⟨j, i⟩)))
    (fun j i => MvPolynomial.eval y
      (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample (Sum.inr ⟨j, i⟩)))
    (h.integerFullChart_remainder_at_site B U b hb o S hR hσ poly hm hp c a v sample read x)
    (h.integerFullChart_remainder_at_site B U b hb o S hR hσ poly hm hp c a v sample read y)
    (fun j i => integerPolynomial_eval_addCircle_div_eq _ q x y hxy) hε herr

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFrozenTaggedTwistStepDrop
namespace OAI

universe u

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.twist_variation
    [Fintype X]
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (x y : LayerSamplerVariables G I n B → ℤ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hx : ∀ k, |(x k : ℝ)| ≤ layerSamplerBox B U b S k)
    (hy : ∀ k, |(y k : ℝ)| ≤ layerSamplerBox B U b S k)
    (hxy : ∀ k, |(x k : ℝ) - (y k : ℝ)| ≤ layerSamplerBox B U b S k * δ)
    (hmod : ∀ k, (x k : ZMod W.modulus) = (y k : ZMod W.modulus))
    (hcover : ∀ k, (x k : ZMod W.cover) = (y k : ZMod W.cover)) :
    ‖W.eval N poly (jointIntegerPhysicalSite x (a, v)) -
      W.eval N poly (jointIntegerPhysicalSite y (a, v))‖ ≤
      (L : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) * δ := by
  let D : ℝ := (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
    ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hε : 0 ≤ D * δ := mul_nonneg hD hδ
  have htag := h.integerFullChart_torus_dist B U b hb o S hR hσ poly hm hp c a v sample read
    W.cover W.cover_pos x y hcover hε
    (fun j i => allocatedLayerSupported_polynomial_variation B U b o hR hσ S hσ1 C hC hchart
      hsmall j (sample j) (h.2.2.1 j).2 _ _ hδ hx hy hxy i)
  have htag' : dist (physicalGridFactorInput W.cover poly (fun z => (jointIntegerPhysicalSite x (a, v) z : ℝ)))
      (physicalGridFactorInput W.cover poly (fun z => (jointIntegerPhysicalSite y (a, v) z : ℝ))) ≤ (1 + D) * δ := by
    apply htag.trans
    have hc : (1 : ℝ) ≤ W.cover := by exact_mod_cast W.cover_pos
    exact (div_le_self hε hc).trans (by nlinarith)
  have hspatial := narrowSpatial_jointPhysicalSite_normalized_dist_le_cell
    (allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)) hτ hτ1 hξ N hN
    (layerSamplerBox B U b S)
    (fun k => (by norm_num : (0 : ℝ) ≤ 1).trans (layerSamplerBox_one_le B U b S k))
    (layerSamplerBox_sum_le_zero_root_budget B U b S) a v hv x y hδ hxy
  have hres : (fun z => (jointIntegerPhysicalSite x (a, v) z : ZMod W.modulus)) =
      (fun z => (jointIntegerPhysicalSite y (a, v) z : ZMod W.modulus)) := by
    funext z
    simp only [jointIntegerPhysicalSite, Pi.add_apply, integerPhysicalSite,
      Int.cast_add, Int.cast_sum, Int.cast_mul, hmod]
  have hout := W.eval_sub_eval_of_component_dist N poly _ _ hres
    (hspatial.trans (show δ ≤ (1 + D) * δ by nlinarith)) htag'
  exact hout.trans_eq (by dsimp [D]; ring)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.frozen_twist_variation
    [Fintype X]
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)

    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i <
      Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) i.val)
    (x y : integerBox (fun i : {i // keep i} =>
      Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) i.val))
    (hres : ∀ i, (x.val i : ZMod (W.modulus * W.cover)) = (y.val i : ZMod (W.modulus * W.cover)))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcell : ∀ i, |(x.val i : ℝ) /
      ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) i.val : ℕ) : ℝ) -
      (y.val i : ℝ) /
      ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) i.val : ℕ) : ℝ)| ≤ δ) :
    ‖W.eval N poly (integerSampledSpatial
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) x.val) -
      W.eval N poly (integerSampledSpatial
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) y.val)‖ ≤
      (L : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) * δ := by
  classical
  let xx := finiteSplitPoint keep x.val fixed
  let yy := finiteSplitPoint keep y.val fixed
  have hT : ∀ i, 0 < layerSamplerBox B U b S i :=
    fun i => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S i)
  have hxy : ∀ i, |(xx i : ℝ) - (yy i : ℝ)| ≤ layerSamplerBox B U b S i * δ := by
    intro i
    by_cases hi : keep i
    · have hc := hcell ⟨i, hi⟩
      rw [← allocatedParameterBox_side_eq B U b S i, ← sub_div, abs_div,
        abs_of_pos (hT i)] at hc
      simpa only [xx, yy, finiteSplitPoint, dif_pos hi, mul_comm] using
        (div_le_iff₀ (hT i)).mp hc
    · simp only [xx, yy, finiteSplitPoint, dif_neg hi, sub_self, abs_zero]
      exact mul_nonneg (hT i).le hδ
  have hmod : ∀ i, (xx i : ZMod W.modulus) = (yy i : ZMod W.modulus) := by
    intro i
    by_cases hi : keep i
    · have hc := congrArg (ZMod.castHom (dvd_mul_right W.modulus W.cover) (ZMod W.modulus))
        (hres ⟨i, hi⟩)
      simpa only [map_intCast, xx, yy, finiteSplitPoint, dif_pos hi] using hc
    · simp only [xx, yy, finiteSplitPoint, dif_neg hi]
  have hcover : ∀ i, (xx i : ZMod W.cover) = (yy i : ZMod W.cover) := by
    intro i
    by_cases hi : keep i
    · have hc := congrArg (ZMod.castHom (dvd_mul_left W.cover W.modulus) (ZMod W.cover))
        (hres ⟨i, hi⟩)
      simpa only [map_intCast, xx, yy, finiteSplitPoint, dif_pos hi] using hc
    · simp only [xx, yy, finiteSplitPoint, dif_neg hi]
  rw [allocatedFrozenIntegerFullChart_spatial, allocatedFrozenIntegerFullChart_spatial]
  exact h.twist_variation B U b hb o S hR hσ poly hm hp c a N hN hτ hτ1 hξ v hv sample read
    hσ1 C hC hchart hsmall W xx yy hδ
    (allocatedFrozenParameterBox_bound B U b S keep fixed hfixed x.val x.property)
    (allocatedFrozenParameterBox_bound B U b S keep fixed hfixed y.val y.property)
    hxy hmod hcover

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedAnalyticIdentification
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in
theorem kernelSupport (g : G) :
    integerProgressionSupport (slice.kernelStart g) (slice.step : ℤ) (slice.kernelLength g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ) :=
  integerProgressionSupport_subset_of_fin _ _ _ _ (slice.kernelInside g)

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalLocalChartOrbitValues
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
    {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

namespace AllocatedExternalLocalChart

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)
    (g : (F.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group)

theorem globalOrbit_chart_values (u : C.Variables → ℤ) :
    F.adaptedPolynomialRealValueHom (fun _ : C.Variables => 1) (fun i => (u i : ℝ))
      (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : C.Variables => 1) (integerSampledRealChart C.integerChart)
        C.integerChart_support g) =
      F.realification.polynomialOrbitRealEval (fullTaggedVariableWeight J)
        (fun i => (C.chartValues u i : ℝ))
        ((F.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J)).symm g) := by
  rw [F.adaptedPolynomialRealValueHom_weightedChart]
  have heval : (fun i => MvPolynomial.eval (fun j => (u j : ℝ))
      (integerSampledRealChart C.integerChart i)) =
      (fun i => (C.chartValues u i : ℝ)) := by
    funext i
    exact integerSampledRealChart_eval C.integerChart u i
  rw [heval]
  rfl

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CertifiedFullChartAffineTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem fullTaggedAffineMapChart_top
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (v : X ⊕ (Σ j, J j)) :
    weightedHomogeneousComponent (fullTaggedVariableWeight J) (fullTaggedVariableWeight J v)
      (fullTaggedAffineMapChart J P c v) = fullTaggedLinearMapChart J P v := by
  cases v with
  | inl x => exact weightedHomogeneousComponent_eq_self (isWeightedHomogeneous_X (R := ℝ) _ _)
  | inr v =>
    change weightedHomogeneousComponent _ _ (C _ + _) = _
    rw [map_add, weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_C (R := ℝ) _ _)]
    simp only [fullTaggedVariableWeight, Sum.elim_inr, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, ↓reduceIte, zero_add]
    exact weightedHomogeneousComponent_eq_self (fullTaggedLinearMapChart_homogeneous J P _)

theorem fullTaggedAffineMapChart_top_mem_set
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (hP : ∀ j x, P j x ∈ U j)
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ))
    (hK : ∀ y, (∀ j, (fun i => y (Sum.inr ⟨j, i⟩)) ∈ U j) → y ∈ K)
    (x : X ⊕ (Σ j, J j) → ℝ) :
    (fun v => MvPolynomial.eval x
      (weightedHomogeneousComponent (fullTaggedVariableWeight J) (fullTaggedVariableWeight J v)
        (fullTaggedAffineMapChart J P c v))) ∈ K := by
  apply hK
  intro j
  simp_rw [fullTaggedAffineMapChart_top, fullTaggedLinearMapChart_eval_tag]
  exact hP j _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedCanonicalSlicedConstructedProjection
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal
universe uX

theorem exists_allocated_sliced_constructed_projection (m q : ℕ) :
    ∃ A Asample : ℕ, 2 ≤ A ∧ 2 ≤ Asample ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P)
    (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M),
    ∀ (period : ℕ), 0 < period → (period : ℝ) ≤ Real.exp P →
    ∃ d : ℕ, period ∣ d ∧ 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + (q + 2 : ℕ) + A) ^ A) ∧
    ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := Fin q) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
    [BorelSpace (CoefficientTorus (K := Fin q) U)]
    (μrows : Measure (CoefficientTorus (K := Fin q) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows],
    let density := allocatedCoefficientDensity B U b hb o hR hσ S
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)} => ν j))
    let densityLip := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) *
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V *
      allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let sectionLip := (Fintype.card (Finset (Fin q)) : ℝ≥0) *
      Real.toNNReal (Real.exp ((P + (q + 2 : ℕ) + A) ^ A))
    let reconstructionLip := ∑ j : Fin m, (Fintype.card (BoundedBooleanJet (Fin q) (j.val + 1)) : ℝ≥0)
    let Row := fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)}
    let Tuple := PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S)
    ∃ g : Tuple → EuclideanJetLayers U Row → ℝ,
      (∀ y, Continuous (g y)) ∧
      (∀ y z, g y z ∈ Set.Icc (0 : ℝ) cap) ∧
      (∀ y, Integrable (g y) ξ) ∧
      (∀ y, (∫ z, g y z ∂ξ) = 1) ∧
      (∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
        (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y)
          (fun j => (Subtype.val : Row j → Finset (Fin q)))) = realDensityMeasure ξ (g y)) ∧
      (∀ y, physicalDensityProjection.{_, _, uX, 0} U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U b S x y) d density
        (fun z => g y ((physicalRowsStandardEquiv U).symm z))) ∧
      (∀ y, ∃ F : (JetAmbientIndex Row J → UnitAddCircle) → ℂ,
        LipschitzWith (densityLip * sectionLip * reconstructionLip) F ∧
        (∀ z, ‖F z‖ ≤ cap) ∧
        ∀ z, (g y z : ℂ) = F (coveredJetAmbientTorus U 1 z)) ∧
      (∀ law : FiniteProbabilityWeights Tuple,
        ∃ F : (JetAmbientIndex Row J → UnitAddCircle) → ℂ,
          LipschitzWith (densityLip * sectionLip * reconstructionLip) F ∧
          (∀ z, ‖F z‖ ≤ cap) ∧
          ∀ z, law.complexMean (fun y => (g y z : ℂ)) = F (coveredJetAmbientTorus U 1 z)) ∧
      AllocatedSlicedSourceProjection.{uX} B U b S x hb o hR hσ C V d g Asample P := by
  obtain ⟨A, hA, hcover⟩ := exists_allocated_rows_ambient_projected_family_multiple m q
  obtain ⟨An, hAn, hnorm⟩ := exists_allocated_narrow_normalization m
  obtain ⟨Ap, hAp, hprojectSource⟩ := exists_allocated_sliced_rows_projected_source.{uX} m q
  refine ⟨A, max An Ap, hA, hAn.trans (le_max_left _ _), ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ S x P hP hG hL M hperiod period hp hpP
  obtain ⟨d, hdiv, hd, hdb, hconstruct⟩ := hcover B U b S (fun _ => 0) x hP hG
    (fun _ => by simpa using Real.exp_nonneg P) hL hperiod period hp hpP
  refine ⟨d, hdiv, hd, hdb, ?_⟩
  intro _ _ _ _ _ _ hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    _ _ _ μrows _ _ density cap cover ξhaar densityLip sectionLip reconstructionLip Row Tuple
  obtain ⟨g, hgc, hgb, hgi, hgm, hglaw, hprojection, hambient, hmean⟩ :=
    hconstruct hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ ν μrows
  refine ⟨g, hgc, hgb, hgi, hgm, hglaw, hprojection, hambient, hmean, ?_⟩
  unfold AllocatedSlicedSourceProjection
  intro W hPone hmSize hK hW hroot hWP hRP hσP hcount hI hn hJ hAP hCP hVP
    X _ _ hX hdim p hpoly hm stride hs hsP τ ξ hτ hτP hξ hξ1 hξP N hN hsize
    rank hrank hRank T hT bases hbases widths Z
  have hnCut := Real.exp_le_exp.mpr (shifted_power_self_mono hP (by omega : 1 ≤ An)
    (le_max_left An Ap))
  have hpCut := Real.exp_le_exp.mpr (shifted_power_self_mono hP (by omega : 1 ≤ Ap)
    (le_max_right An Ap))
  obtain ⟨hwidths, hmass, _, hglobal⟩ := hnorm B U b S hb o μ ν hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall hP hmSize hK hX hdim hRP hσP hcount hI hn hJ hAP hL hCP hVP
    p hpoly hm stride hs hsP hW hWP hτ hτP hξ hξ1 hξP N (fun i => hnCut.trans (hsize i))
    hrank (hnCut.trans hRank) T hT
  have hnormal := hglobal bases hbases
  change |Z - 1| ≤ Real.exp (-P) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
    0 < Z ∧ Z⁻¹ ≤ 2 at hnormal
  refine ⟨hmass, hnormal, ?_⟩
  intro law signal hsignal κ hsource
  have hZi : Z⁻¹ ≤ Real.exp P := hnormal.2.2.2.trans
    (by linarith [Real.add_one_le_exp P])
  exact hprojectSource B U b S x hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall
    hP hmSize hK hW hroot hWP hL hRP hσP hcount hI hn hJ hAP hCP hVP hperiod hX hdim
    p hpoly hm stride hs hsP hτ hτP hξ hξ1 hξP N hN (fun i => hpCut.trans (hsize i))
    hrank (hpCut.trans hRank) signal hsignal T hT bases hbases d g hprojection hwidths hmass law
    hnormal.2.2.1 hZi hsource

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal
universe uX

theorem exists_allocated_canonical_constructed_projection (m q : ℕ) :
    ∃ A Asample : ℕ, 2 ≤ A ∧ 2 ≤ Asample ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P)
    (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (selection : Fin q ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
    {Pk : ℝ} (_hMk : (M : ℝ) ≤ Real.exp Pk) (_hPk : ((m + 1 : ℕ) : ℝ) * Pk ≤ P),
    let period := kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m)

    ∃ d : ℕ, period ∣ d ∧ 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + (q + 2 : ℕ) + A) ^ A) ∧
    ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := Fin q) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
    [BorelSpace (CoefficientTorus (K := Fin q) U)]
    (μrows : Measure (CoefficientTorus (K := Fin q) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows],
    let density := allocatedCoefficientDensity B U b hb o hR hσ S
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)} => ν j))
    let densityLip := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) *
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V *
      allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let sectionLip := (Fintype.card (Finset (Fin q)) : ℝ≥0) *
      Real.toNNReal (Real.exp ((P + (q + 2 : ℕ) + A) ^ A))
    let reconstructionLip := ∑ j : Fin m, (Fintype.card (BoundedBooleanJet (Fin q) (j.val + 1)) : ℝ≥0)
    let Row := fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)}
    let Tuple := PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S)
    ∃ g : Tuple → EuclideanJetLayers U Row → ℝ,
      (∀ y, Continuous (g y)) ∧
      (∀ y z, g y z ∈ Set.Icc (0 : ℝ) cap) ∧
      (∀ y, Integrable (g y) ξ) ∧
      (∀ y, (∫ z, g y z ∂ξ) = 1) ∧
      (∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
        (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y)
          (fun j => (Subtype.val : Row j → Finset (Fin q)))) = realDensityMeasure ξ (g y)) ∧
      (∀ y, physicalDensityProjection.{_, _, uX, 0} U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U b S x y) d density
        (fun z => g y ((physicalRowsStandardEquiv U).symm z))) ∧
      (∀ y, ∃ F : (JetAmbientIndex Row J → UnitAddCircle) → ℂ,
        LipschitzWith (densityLip * sectionLip * reconstructionLip) F ∧
        (∀ z, ‖F z‖ ≤ cap) ∧
        ∀ z, (g y z : ℂ) = F (coveredJetAmbientTorus U 1 z)) ∧
      (∀ law : FiniteProbabilityWeights Tuple,
        ∃ F : (JetAmbientIndex Row J → UnitAddCircle) → ℂ,
          LipschitzWith (densityLip * sectionLip * reconstructionLip) F ∧
          (∀ z, ‖F z‖ ≤ cap) ∧
          ∀ z, law.complexMean (fun y => (g y z : ℂ)) = F (coveredJetAmbientTorus U 1 z)) ∧
      AllocatedSlicedSourceProjection.{uX} B U b S x hb o hR hσ C V d g Asample P := by
  obtain ⟨A, Asample, hA, hAsample, hconstruct⟩ := exists_allocated_sliced_constructed_projection.{uX} m q
  refine ⟨A, Asample, hA, hAsample, ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ S x P hP hG hL M selection hx Pk hMk hPk period
  exact hconstruct B U b S x hP hG hL hx.2 period (kernelPeriodCandidate_pos _ _)
    ((kernelPeriodCandidate_le_exp hMk _ _).trans (Real.exp_le_exp.mpr hPk))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ActualFixedSpatialSlicedDensityBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in
theorem slicedBlock_det_ne_zero (second : Bool) :
    (fixedSpatialKernelBlock spatialEquiv Wsp Lsp
      (fixedSpatialKernelSliceFrame Wsp Lsp slice.path.normalizedNoise
        slice.kernelLower slice.kernelWidth) second).det ≠ 0 := by
  have hbase : (fixedSpatialKernelBlock spatialEquiv Wsp Lsp slice.path.normalizedNoise second).det ≠ 0 := by
    cases second
    · exact slice.path.detFalse
    · exact slice.path.detTrue
  let w : X → ℝ := fun i => slice.kernelWidth
    (spatialEquiv.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i))
  have hmatrix : fixedSpatialKernelBlock spatialEquiv Wsp Lsp
      (fixedSpatialKernelSliceFrame Wsp Lsp slice.path.normalizedNoise
        slice.kernelLower slice.kernelWidth) second =
      fixedSpatialKernelBlock spatialEquiv Wsp Lsp slice.path.normalizedNoise second * Matrix.diagonal w := by
    ext x i
    rw [fixedSpatialKernelBlock_slice, Matrix.mul_diagonal]
  rw [hmatrix, Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero hbase (Finset.prod_ne_zero_iff.mpr (fun i _ => slice.kernelWidth_ne_zero _))

noncomputable def slicedBlockEquiv (second : Bool) : (X → ℝ) ≃L[ℝ] (X → ℝ) :=
  fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp
    (fixedSpatialKernelSliceFrame Wsp Lsp slice.path.normalizedNoise
      slice.kernelLower slice.kernelWidth) second (slice.slicedBlock_det_ne_zero second)

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end


