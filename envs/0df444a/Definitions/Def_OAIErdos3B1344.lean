-- Prove2me | Definitions.Def_OAIErdos3B1344
-- name    : OAIErdos3B1344
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T23:24:16.708978+00:00
-- url     : https://prove2.me/theorems/ec45e053-39c8-4235-a1b4-38129ec7430e
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1345 of 1376
-- statement:
--   Definitions bundle 1345 of 1376 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1343`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1345 available.
--
--   Modules: `OAI.Erdos3.RationalFilteredNilmanifold.exists_nativeOptionPair_weighted_common_orbit_factors`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.referenceLocalDensity`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.referenceRetainedCRTInputLaw`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.referenceRetainedCRTModulus`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.referenceRetainedCRTModulus_dvd`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.referenceRetainedCRTModulus_eq`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.referenceRetainedModulus`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.referenceRetainedModulus_dvd`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.referenceRetainedModulus_pos`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.referenceRetainedPrimes`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.retainedCRTIndependentForecast`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.retainedCRTReferenceForecast`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.retainedLabelDecidableEq`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.retainedReferenceForecast`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.retainedReferencePrimeNeZero`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.smallReferenceModulusNeZero`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.smallReferencePrimeNeZero`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.fullReferenceNonzero`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.recoveredG`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.recoveredRationalFactor`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.retainedRecoveredG`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.retainedRecoveredRationalFactor`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.retainedReferenceNonzero`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.scaledRetainedRecoveredG`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateTaggedPairFamily.extendedJointOrbit`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateTaggedPairFamily.extendedJointOrbit_mem`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateTaggedPairFamily.extendedLongJointOrbit`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateTaggedPairFamily.extendedLongJointOrbit_mem`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateTaggedPairFamily.longJointOrbit`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateTaggedPairFamily.quotientFiltration`, `OAI.Erdos3.VectorPolynomial.allocatedFrozenTaggedFamilyInputBudget`, `OAI.Erdos3.VectorPolynomial.allocatedFrozenTaggedFamilyInputBudget_mono`, `OAI.Erdos3.VectorPolynomial.allocatedFrozenTaggedPairBudget`, `OAI.Erdos3.VectorPolynomial.allocatedFrozenTaggedPairBudget_mono`, `OAI.Erdos3.VectorPolynomial.candidateFrontFactorScalarConclusion`, `OAI.Erdos3.VectorPolynomial.exists_allocatedFrozenTaggedFamily_common_factors`, `OAI.Erdos3.bufferedSpatialWeight`, `OAI.Erdos3.exists_sliceLaw_localPivot_weighted_native_vertical_partners`, `OAI.Erdos3.spatialPatchExtractionCost`, `OAI.Erdos3.spatialPatchExtractionMesh`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1322
import Definitions.Def_OAIErdos3B1331
import Definitions.Def_OAIErdos3B1340

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.NativeSliceLawVerticalPartners
namespace OAI

section

namespace Erdos3
open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_sliceLaw_localPivot_weighted_native_vertical_partners
    {Ω K X σ τ : Type*} [Fintype Ω] [Fintype K] [Fintype X] [DecidableEq X]
    {L : K → Type*} {Llocal : Ω → K → Type*}
    [∀ k, LieRing (L k)] [∀ k, LieAlgebra ℚ (L k)]
    [∀ a k, LieRing (Llocal a k)] [∀ a k, LieAlgebra ℚ (Llocal a k)]
    {s : ℕ} {d : K → ℕ} {sLocal dLocal : Ω → K → ℕ}
    [∀ k, TopologicalSpace (ℝ ⊗[ℚ] L k)]
    [∀ k, IsTopologicalAddGroup (ℝ ⊗[ℚ] L k)]
    [∀ k, ContinuousSMul ℝ (ℝ ⊗[ℚ] L k)] [∀ k, T2Space (ℝ ⊗[ℚ] L k)]
    [∀ a k, TopologicalSpace (ℝ ⊗[ℚ] Llocal a k)]
    [∀ a k, IsTopologicalAddGroup (ℝ ⊗[ℚ] Llocal a k)]
    [∀ a k, ContinuousSMul ℝ (ℝ ⊗[ℚ] Llocal a k)]
    [∀ a k, T2Space (ℝ ⊗[ℚ] Llocal a k)]
    (D : ∀ k, RationalFilteredNilmanifold (L k) s (d k))
    (Dlocal : ∀ a k, RationalFilteredNilmanifold (Llocal a k) (sLocal a k) (dLocal a k))
    {w : σ → ℕ} {wLocal : τ → ℕ}
    (Q : ∀ k, (D k).Niltest w) (P : ∀ a k, (Dlocal a k).Niltest wLocal)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    {N : X → ℕ} (stride : Ω → K → ℕ)
    (S : ∀ a k, ResidueBoxSlice N (stride a k))
    (hstride : ∀ a ∈ H, ∀ k, 0 < stride a k)
    (hlen : ∀ a k i, 0 < (S a k).length i)
    (pointAmbient : Ω → integerBox N → σ → ℤ) (pointLocal : Ω → K → integerBox N → τ → ℤ)
    (twist : Ω → K → integerBox N → ℂ) {pNative pLocal r q : ℝ}
    (hpLocal : 0 ≤ pLocal) (hr : 0 ≤ r) (hpq : pNative ≤ q)
    (hprecision : pLocal + r + 1 ≤ q)
    (hQ : ∀ k, (Q k).ComplexityLE pNative)
    (hcap : ∀ k, ((Q k).normBound : ℝ) ≤ 1)
    (hP : ∀ a ∈ H, ∀ k, (P a k).ComplexityLE pLocal)
    (htwist : ∀ a ∈ H, ∀ k t, ‖twist a k t‖ ≤ 1)
    (hcorr : ∀ a ∈ H, ∀ k, Real.exp (-r) ≤
      ‖((S a k).fullSliceLaw (hlen a k)).complexMean (fun t =>
        ((P a k).eval (pointLocal a k t) * twist a k t) * (Q k).eval (pointAmbient a t))‖) :
    ∃ (freq : ∀ k, L k →ₗ[ℚ] ℚ) (V : ∀ k, (D k).Niltest w) (retained : Finset Ω),
      retained ⊆ H ∧ 0 < outer.mass retained ∧
      Real.exp (-verticalDecompositionBudget q * Fintype.card K) * outer.mass H ≤
        outer.mass retained ∧
      (∀ k, (V k).ComplexityLE pNative ∧ (V k).orbit = (Q k).orbit ∧
        (V k).normBound = (Q k).normBound ∧ (V k).lipBound = (Q k).lipBound ∧
        ((V k).normBound : ℝ) ≤ 1) ∧
      (∀ k i, rationalLogHeight (freq k ((D k).basis i)) ≤ verticalDecompositionBudget q) ∧
      (∀ k (z : (D k).RealGroup), z ∈ (D k).filtration.realification.subgroup s → ∀ x,
        (V k).observable (z • x) =
          character ((realifyFunctional (freq k) z.coord : ℝ) : CircleFourier.Circle) *
            (V k).observable x) ∧
      (∀ k (z : (D k).RealGroup), z ∈ (D k).filtration.realification.subgroup s →
        z ∈ (D k).realLattice → ∃ n : ℤ, realifyFunctional (freq k) z.coord = n) ∧
      (∀ k (z : (D k).RealGroup) (c : ℂ),
        (∀ x, (Q k).observable (z • x) = c * (Q k).observable x) →
        ∀ x, (V k).observable (z • x) = c * (V k).observable x) ∧
      ∀ a ∈ retained, ∀ k, Real.exp (-r) / (2 * Real.exp (verticalDecompositionBudget q)) ≤
        ‖((S a k).fullSliceLaw (hlen a k)).complexMean (fun t =>
          ((P a k).eval (pointLocal a k t) * twist a k t) * (V k).eval (pointAmbient a t))‖ := by
  classical
  have hfiniteCorr (a : Ω) (ha : a ∈ H) (k : K) :
      Real.exp (-r) ≤ ‖𝔼 t ∈ (S a k).fullSlicePoints,
        ((P a k).eval (pointLocal a k t) * twist a k t) * (Q k).eval (pointAmbient a t)‖ := by
    rw [← (S a k).fullSliceLaw_complexMean_eq_expect_points (hlen a k) (hstride a ha k)]
    exact hcorr a ha k
  obtain ⟨freq, V, retained, hsub, hpos, hmass, hcert, hheight, hvert, hint,
      hpres, hselected⟩ := exists_localPivot_weighted_native_vertical_partners
    D Dlocal Q P outer H hH (fun a k => (S a k).fullSlicePoints)
    pointAmbient pointLocal twist hpLocal hr hpq hprecision hQ hcap hP
    (fun a ha k t _ => htwist a ha k t) hfiniteCorr
  refine ⟨freq, V, retained, hsub, hpos, hmass, hcert, hheight, hvert, hint, hpres, ?_⟩
  intro a ha k
  rw [(S a k).fullSliceLaw_complexMean_eq_expect_points (hlen a k) (hstride a (hsub ha) k)]
  exact hselected a ha k

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairUniformFactors
namespace OAI

universe u

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

theorem exists_nativeOptionPair_weighted_common_orbit_factors (s : ℕ) :
    ∃ C A : ℕ, 2 ≤ C ∧ 2 ≤ A ∧
    ∀ {J α σ Ω : Type*} [Fintype J] [Fintype α] [Fintype σ] [Fintype Ω]
      {β : J → Type*} [∀ j, Fintype (β j)]
      {L : Type u} {M : J → Type u}
      [LieRing L] [LieAlgebra ℚ L] [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]
      {d₀ : ℕ} {d : J → ℕ}
      (D : RationalFilteredNilmanifold L s d₀)
      (E : ∀ j, RationalFilteredNilmanifold (M j) s (d j))
      (e : Basis α ℚ (∀ i : Option J, optionLieSpace L M i)) (ω : α → ℕ)
      (hF : ∀ k, (optionProduct D E).filtration.layer k =
        Submodule.span ℚ (e '' {i | k ≤ ω i}))
      (b : ∀ j, Basis (β j) ℚ (PairAlgebra L (M j))) (ν : ∀ j, β j → ℕ)
      (hG : ∀ j k, (pi (pairModels D (E j))).filtration.layer k =
        Submodule.span ℚ (b j '' {i | k ≤ ν j i}))
      {height : ℕ}, 1 ≤ height →
      (∀ j i k, RationalHeightLE ((b j).repr (optionPairProjection j (e k)) i) height) →
    ∀ {p : ℝ}, 0 ≤ p → (Fintype.card α : ℝ) ≤ p →
      (∀ j, (Fintype.card (β j) : ℝ) ≤ p) →
      (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (height : ℝ) ≤ Real.exp p →
      (∀ i j k, rationalLogHeight (e.repr ⁅e i, e j⁆ k) ≤ p) →
      let P := p + (p + C) ^ C
      ∀ side : σ → ℝ, (∀ i, Real.exp ((P + 2) ^ A) ≤ side i) →
      ∀ (outer : FiniteProbabilityWeights Ω) (H : Finset Ω), 0 < outer.mass H →
      ∀ (g : Ω → ∀ i : Option J,
          (optionFactors D E i).filtration.realification.PolynomialOrbit (fun _ : σ => 1))
        (η : J → L →ₗ[ℚ] ℚ) (θ : ∀ j, M j →ₗ[ℚ] ℚ),
        (∀ a ∈ H, ∀ j,
          (pi (pairModels D (E j))).filtration.ControlledSymbolFactorization
            (b j) (ν j) (hG j) (pairFrequency (η j) (θ j)) side
            (pairOrbitSymbol D (E j) (g a none) (g a (some j)) (b j) (ν j) (hG j)) p) →
        let q := (P + 2) ^ A + (((P + 2) ^ 2 + 2) ^ 63 + 1) + P + 1
        ∃ (W : LieSubalgebra ℚ (optionProduct D E).filtration.AssociatedGraded)
          (v : Fin (Fintype.card α) → (optionProduct D E).filtration.AssociatedGraded)
          (m : ℕ) (H' : Finset Ω),
          H' ⊆ H ∧ 0 < outer.mass H' ∧
          Real.exp (-((q + 2) ^ 5 + q)) * outer.mass H ≤ outer.mass H' ∧
          Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
          BasisGradedSubmodule ((optionProduct D E).filtration.associatedGradedBasis e ω hF)
            ω W.toSubmodule ∧
          (∀ i k, rationalLogHeight
            (((optionProduct D E).filtration.associatedGradedBasis e ω hF).repr (v i) k) ≤ q) ∧
          (∀ j x, x ∈ (optionProduct D E).filtration.realGradedRefiltrationLayer W s →
            realifyFunctional ((pairFrequency (η j) (θ j)).comp
              (optionPairProjection j).toLinearMap) x = 0) ∧
          0 < m ∧ (m : ℝ) ≤ Real.exp q ∧
          ∀ a ∈ H', (optionProduct D E).filtration.HasCommonRefilteredOrbitFactors
            e ω hF side q m W
            ⟨⟨(piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).log,
              (piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).property⟩⟩ := by
  obtain ⟨C, hC, hbudget⟩ := exists_controlledProjectionUniformBudget_power s
  obtain ⟨A, hA, hcommon⟩ := exists_weighted_common_refiltered_orbit_factors s
  refine ⟨C, A, hC, hA, ?_⟩
  intro J α σ Ω _ _ _ _ β _ L M _ _ _ _ d₀ d D E e ω hF b ν hG
    height hheight hentries p hp hα hβ hσ hJ hheightp hstructure P side hside
    outer H hH g η θ hfactor
  have hpP : p ≤ P := by
    dsimp only [P]
    exact le_add_of_nonneg_right (by positivity)
  have hliftP : (p + C) ^ C ≤ P := by
    dsimp only [P]
    exact le_add_of_nonneg_left hp
  have hsidepos (i) : 0 < side i := (Real.exp_pos _).trans_le (hside i)
  apply hcommon (optionProduct D E).filtration e ω hF
    (fun j => (pairFrequency (η j) (θ j)).comp (optionPairProjection j).toLinearMap)
    (hp.trans hpP) (hα.trans hpP) (hσ.trans hpP) (hJ.trans hpP)
    (fun i j k => (hstructure i j k).trans hpP) side hside outer H hH
    (fun a => ⟨⟨(piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).log,
      (piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).property⟩⟩)
  intro a ha j
  obtain ⟨U, hU⟩ := (hfactor a ha j).exists_fastWitness
    (pi (pairModels D (E j))).filtration (b j) (ν j) (hG j)
  have hpull := (optionProduct D E).filtration.controlledSymbolFactorizationAtFast_projection_of_dimensions
    e ω hF (pi (pairModels D (E j))).filtration (b j) (ν j) (hG j)
    (optionPairProjection j) (optionPairProjection_layers D E j)
    (optionPairProjection_layer_surjective D E j) hheight (hentries j)
    hp hα (hβ j) hσ hheightp side hsidepos
    ((optionProduct D E).filtration.realPolynomialSymbolHom e ω hF (fun _ => 1)
      ⟨⟨(piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).log,
        (piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).property⟩⟩)
    (pairFrequency (η j) (θ j)) U
    (by rw [optionPairProjection_jointOrbitSymbol D E j e ω hF (b j) (ν j) (hG j)]; exact hU)
  obtain ⟨m, E₀, P₀, R₀, v₀, hdata⟩ := hpull.mono
    (optionProduct D E).filtration e ω hF ((hbudget p hp).trans hliftP) hsidepos
  exact ⟨m, E₀, P₀, R₀, _, v₀, hdata⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.VectorPolynomial

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct Classical

def allocatedFrozenTaggedPairBudget (s C A : ℕ) (pGeo p : ℝ) : ℝ :=
  (fixedAdaptedSymbolTransferInput pGeo
    (pGeo + p + ((p + 2 + C) ^ C + (s : ℝ) * (9 * p + 23))) + A) ^ A

def allocatedFrozenTaggedFamilyInputBudget (b t : ℝ) : ℝ :=
  b + t + (b + 3) ^ 4 + 1

theorem exists_allocatedFrozenTaggedFamily_common_factors (s : ℕ) (hs : 1 ≤ s) :
    ∃ C A K T : ℕ, 2 ≤ C ∧ 2 ≤ A ∧ 2 ≤ K ∧ 2 ≤ T ∧
    ∀ {Pivot α Ω : Type*} [Fintype Pivot] [Fintype α] [Fintype Ω]
      {LG : Type u} {MG : Pivot → Type u}
      [LieRing LG] [LieAlgebra ℚ LG] [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
      [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] MG j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] MG j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] MG j)] [∀ j, T2Space (ℝ ⊗[ℚ] MG j)]
      {d₀ : ℕ} {d : Pivot → ℕ}
      (D : RationalFilteredNilmanifold LG s d₀)
      (E : ∀ j, RationalFilteredNilmanifold (MG j) s (d j))
      {pGeo p bnd : ℝ}, 0 ≤ pGeo → 0 ≤ p → 0 ≤ bnd →
      (∀ j, (pi (pairModels D (E j))).GeometryComplexityLE pGeo) →
      pGeo ≤ bnd → (pGeo + 3) ^ 5 ≤ bnd →
      (Fintype.card α : ℝ) ≤ bnd → (Fintype.card Pivot : ℝ) ≤ bnd →
    ∀ (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG MG i)) (ω : α → ℕ)
      (hF : ∀ k, (optionProduct D E).filtration.layer k =
        Submodule.span ℚ (e '' {i | k ≤ ω i})),
      (∀ i j k, rationalLogHeight (e.repr ⁅e i, e j⁆ k) ≤ bnd) →
      (∀ i k, rationalLogHeight ((optionProduct D E).basis.repr (e i) k) ≤ bnd) →
      let localCost := allocatedFrozenTaggedPairBudget s C A pGeo p
      let r := allocatedFrozenTaggedFamilyInputBudget bnd localCost
      let P := r + (r + K) ^ K
    ∀ {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
      {I Jgeo : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (Jgeo j)]
      {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
      (Γ : AllocatedFrozenTaggedContext (G := G) (X := X) (J := Jgeo) B)
      (Deck : Fin m → Type*) (keep : LayerSamplerVariables G I n B → Prop)
      [Nonempty {i // keep i}], (Fintype.card {i // keep i} : ℝ) ≤ bnd →
      (∀ i, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤ (Γ.sides keep i : ℝ)) →
      (∀ i, Real.exp ((P + 2) ^ T) ≤ (Γ.sides keep i : ℝ)) →
    ∀ (outer : FiniteProbabilityWeights Ω) (H : Finset Ω), 0 < outer.mass H →
    ∀ (g : Ω → ∀ i : Option Pivot,
        (optionFactors D E i).filtration.realification.PolynomialOrbit
          (fun _ : {i // keep i} => 1))
      (eta : Pivot → LG →ₗ[ℚ] ℚ) (theta : ∀ j, MG j →ₗ[ℚ] ℚ)
      (input : ∀ _a : {a // a ∈ H}, ∀ j,
        AllocatedFrozenTaggedPairInput Γ Deck keep D (E j) p),
      (∀ a j
        (c : Basis (Fin (finrank ℚ (PairAlgebra LG (MG j)))) ℚ (PairAlgebra LG (MG j)))
        (w : Fin (finrank ℚ (PairAlgebra LG (MG j))) → ℕ)
        (hc : ∀ k, (pi (pairModels D (E j))).filtration.layer k =
          Submodule.span ℚ (c '' {i | k ≤ w i})),
        pairOrbitSymbol D (E j) (input a j).V.orbit (input a j).W.orbit c w hc =
          pairOrbitSymbol D (E j) (g a.val none) (g a.val (some j)) c w hc) →
      (∀ a j, (input a j).η = eta j) →
      (∀ a j, (input a j).θ = theta j) →
      let q := (P + 2) ^ T + (((P + 2) ^ 2 + 2) ^ 63 + 1) + P + 1
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
          realifyFunctional ((pairFrequency (eta j) (theta j)).comp
            (optionPairProjection j).toLinearMap) x = 0) ∧
        0 < den ∧ (den : ℝ) ≤ Real.exp q ∧
        ∀ a ∈ H', (optionProduct D E).filtration.HasCommonRefilteredOrbitFactors
          e ω hF (fun i => (Γ.sides keep i : ℝ)) q den W
          ⟨⟨(piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).log,
            (piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).property⟩⟩ := by
  obtain ⟨C, A, hC, hA, hstep⟩ := exists_allocatedFrozenTaggedPairInput_fixed_basis_step_drop s hs
  obtain ⟨K, T, hK, hT, hcommon⟩ := exists_nativeOptionPair_weighted_common_orbit_factors s
  refine ⟨C, A, K, T, hC, hA, hK, hT, ?_⟩
  intro Pivot α Ω _ _ _ LG MG _ _ _ _ _ _ _ _ _ _ _ _ d₀ d D E
    pGeo p bnd hpGeo hp hbnd hGeo hpGeoB hInvB hα hPivot e ω hF hstructure he
    localCost r P m G X _ _ I Jgeo _ _ n B _ Γ Deck keep _ hkeep hlong hcommonLong
    outer H hH g eta theta input hsymbol heta htheta
  classical
  choose b ν hG _hforward hinverse hlocal using fun j => hstep D (E j) hpGeo (hGeo j)
  have hcost : 0 ≤ localCost := by
    dsimp [localCost, allocatedFrozenTaggedPairBudget, fixedAdaptedSymbolTransferInput]
    positivity
  have hbndR : bnd ≤ r := by
    dsimp [r, allocatedFrozenTaggedFamilyInputBudget]
    linarith [pow_nonneg (show 0 ≤ bnd + 3 by linarith) 4]
  have hcostR : localCost ≤ r := by
    dsimp [r, allocatedFrozenTaggedFamilyInputBudget]
    linarith [pow_nonneg (show 0 ≤ bnd + 3 by linarith) 4]
  have hheightR : (bnd + 3) ^ 4 + 1 ≤ r := by
    dsimp [r, allocatedFrozenTaggedFamilyInputBudget]
    linarith
  have hdim (j) : (Fintype.card (Σ i : Bool, Fin (Bool.rec (d j) d₀ i)) : ℝ) ≤ bnd :=
    (hGeo j).1.trans hpGeoB
  have hβ (j) : (Fintype.card (Fin (finrank ℚ (PairAlgebra LG (MG j)))) : ℝ) ≤ bnd := by
    simpa only [Fintype.card_fin, finrank_eq_card_basis (pi (pairModels D (E j))).basis]
      using hdim j
  have hentries (j i k) : RationalHeightLE
      ((b j).repr (optionPairProjection j (e k)) i) ⌈Real.exp ((bnd + 3) ^ 4)⌉₊ :=
    rationalHeightLE_ceil_exp (optionPairProjection_adapted_logHeight D E j e (b j)
      hbnd (hdim j) he (fun i k => (hinverse j i k).trans hInvB) k i)
  have hheight : (⌈Real.exp ((bnd + 3) ^ 4)⌉₊ : ℝ) ≤ Real.exp r :=
    (ceil_exp_le_exp_add_one (by positivity)).trans (Real.exp_le_exp.mpr hheightR)
  have hsidepos (i) : 0 < (Γ.sides keep i : ℝ) := (Real.exp_pos _).trans_le (hlong i)
  apply hcommon D E e ω hF b ν hG (one_le_ceil_exp _) hentries
    (hbnd.trans hbndR) (hα.trans hbndR) (fun j => (hβ j).trans hbndR)
    (hkeep.trans hbndR) (hPivot.trans hbndR) hheight
    (fun i j k => (hstructure i j k).trans hbndR)
    (fun i => (Γ.sides keep i : ℝ)) hcommonLong outer H hH g eta theta
  intro a ha j
  have hfactor := hlocal j B Γ Deck keep (input ⟨a, ha⟩ j) hlong
  have hfactor' : (pi (pairModels D (E j))).filtration.ControlledSymbolFactorization
      (b j) (ν j) (hG j) (pairFrequency (eta j) (theta j))
      (fun i => (Γ.sides keep i : ℝ))
      (pairOrbitSymbol D (E j) (g a none) (g a (some j)) (b j) (ν j) (hG j)) localCost := by
    simpa only [heta, htheta, hsymbol, allocatedFrozenTaggedPairBudget, localCost]
      using hfactor
  exact hfactor'.mono (pi (pairModels D (E j))).filtration (b j) (ν j) (hG j)
    hcostR hsidepos

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial

open RationalFilteredNilmanifold

theorem allocatedFrozenTaggedPairBudget_mono (s C A : ℕ)
    {pGeo pGeo' p p' : ℝ} (hGeo0 : 0 ≤ pGeo) (hp0 : 0 ≤ p)
    (hGeo : pGeo ≤ pGeo') (hp : p ≤ p') :
    allocatedFrozenTaggedPairBudget s C A pGeo p ≤
      allocatedFrozenTaggedPairBudget s C A pGeo' p' := by
  unfold allocatedFrozenTaggedPairBudget fixedAdaptedSymbolTransferInput
  gcongr

theorem allocatedFrozenTaggedFamilyInputBudget_mono {b b' t t' : ℝ}
    (hb : 0 ≤ b) (hbb : b ≤ b') (htt : t ≤ t') :
    allocatedFrozenTaggedFamilyInputBudget b t ≤
      allocatedFrozenTaggedFamilyInputBudget b' t' := by
  unfold allocatedFrozenTaggedFamilyInputBudget
  gcongr

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

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

def extendedJointOrbit
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck {a // a ∈ H} Pivot
      D E Fmark φ marked keep cost p periodCap coverCap Lip)
    (a : Ω) : ∀ i : Option Pivot,
      (optionFactors D E i).filtration.realification.PolynomialOrbit
        (fun _ : {i // keep i} => 1) :=
  if ha : a ∈ H then F.jointOrbit ⟨a, ha⟩ else fun _ => 1

omit [Fintype Ω] in
@[simp] theorem extendedJointOrbit_mem
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck {a // a ∈ H} Pivot
      D E Fmark φ marked keep cost p periodCap coverCap Lip)
    (a : Ω) (ha : a ∈ H) : F.extendedJointOrbit a = F.jointOrbit ⟨a, ha⟩ := by
  simp only [extendedJointOrbit, dif_pos ha]

end AllocatedExternalCandidateTaggedPairFamily

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

def candidateFrontFactorScalarConclusion (s : ℕ)
    (p actualGeometry cost terminal commonInput fast longThreshold
      aProjected aCommon aMarkInput common aAdapted aMarkBudget aJointGeo initialShort : ℝ) : Prop :=
  terminal ∈ Set.Icc 0 commonInput ∧
    allocatedCandidateCommonFastBudget s terminal ≤ fast ∧
    max cost initialShort ≤ longThreshold ∧
    (aProjected + 2) ^ 3 + aCommon ≤ commonInput ∧
    aMarkInput ∈ Set.Icc 0 commonInput ∧
    aCommon ∈ Set.Icc 0 common ∧
    p ≤ commonInput ∧ actualGeometry ≤ commonInput ∧
    aAdapted ≤ commonInput ∧ aMarkBudget ≤ commonInput ∧
    aJointGeo ≤ commonInput ∧ (aProjected + 2) ^ 4 ≤ commonInput ∧ cost ≤ commonInput

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

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

def longJointOrbit
    {Λ : Type*}
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck Λ Pivot
      D E Fmark φ marked keep cost p periodCap coverCap Lip)
    (keepLong : LayerSamplerVariables G I n B → Prop) (a : Λ) :
    ∀ i : Option Pivot, (optionFactors D E i).filtration.realification.PolynomialOrbit
      (fun _ : {i // keepLong i} => 1) :=
  fun i => (optionFactors D E i).filtration.polynomialOrbitRealChart
    (fun _ : {i // keep i} => 1) (fun _ : {i // keepLong i} => 1)
    ((F.chart a).axisPolynomial keepLong (fun _ => 0))
    ((F.chart a).axisPolynomial_support keepLong (fun _ => 0)) (F.jointOrbit a i)

def extendedLongJointOrbit
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck {a // a ∈ H} Pivot
      D E Fmark φ marked keep cost p periodCap coverCap Lip)
    (keepLong : LayerSamplerVariables G I n B → Prop) (a : Ω) :
    ∀ i : Option Pivot, (optionFactors D E i).filtration.realification.PolynomialOrbit
      (fun _ : {i // keepLong i} => 1) :=
  if ha : a ∈ H then F.longJointOrbit keepLong ⟨a, ha⟩ else fun _ => 1

omit [Fintype Ω] in
@[simp] theorem extendedLongJointOrbit_mem
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck {a // a ∈ H} Pivot
      D E Fmark φ marked keep cost p periodCap coverCap Lip)
    (keepLong : LayerSamplerVariables G I n B → Prop) (a : Ω) (ha : a ∈ H) :
    F.extendedLongJointOrbit keepLong a = F.longJointOrbit keepLong ⟨a, ha⟩ := by
  simp only [extendedLongJointOrbit, dif_pos ha]

end AllocatedExternalCandidateTaggedPairFamily

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

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

variable
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck {a // a ∈ H} Pivot
      D E Fmark φ marked keep cost p periodCap coverCap Lip)

variable (outer : FiniteProbabilityWeights Ω) (js : List Pivot)
    {α κ : Type*} [Fintype α] [Fintype κ]
    (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG MG i)) (ω : α → ℕ)
    (hF : ∀ k, (optionProduct D E).filtration.layer k =
      Submodule.span ℚ (e '' {i | k ≤ ω i}))

abbrev quotientFiltration := D.filtration.pivotProductQuotientFiltration φ F.η js
  (NilpotentLieFiltration.pi (fun j => (E j).filtration))

variable
    (c : Basis κ ℚ ((LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js) × (∀ j, MG j)))
    (ν : κ → ℕ)
    (hQ : ∀ k, (F.quotientFiltration js).layer k = Submodule.span ℚ (c '' {i | k ≤ ν i}))

end AllocatedExternalCandidateTaggedPairFamily

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ActualFixedSpatialGoodPrimeDeletion
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

local instance retainedReferencePrimeNeZero : ∀ p : path.primes, NeZero p.val :=
  path.primeNeZero

noncomputable def referenceRetainedPrimes (cutoff : ℕ) : Finset path.primes :=
  Finset.univ.filter (fun p => path.referenceBadDepth p.val ≠ 0 ∨
    path.prescribed p.val ≠ 0 ∨ p.val ≤ cutoff)

noncomputable def referenceLocalDensity
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus)
    (p : path.primes) : ℝ :=
  rationalOutputDensity
    (FiniteProbabilityWeights.uniform
      (LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B →
        ZMod (p.val ^ path.exponent p.val)))
    (localPrimePowerIntegerPolynomialOutput p.val (path.exponent p.val) (path.prescribed p.val)
      (path.localReferencePolynomial raw) (path.origin p)) (p.val ^ path.exponent p.val)
    (fun j => ZMod.castHom (Finset.dvd_prod_of_mem
      (fun p : path.primes => p.val ^ path.exponent p.val) (Finset.mem_univ p))
      (ZMod (p.val ^ path.exponent p.val)) (β j))

noncomputable def retainedReferenceForecast {Ω Z : Type*} [Fintype Ω]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (raw : Ω → PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (cutoff : ℕ) (gridVolume : ℝ) (z : Z)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) : ℝ :=
  gridVolume * inactive.fiberMean gridPoint z (fun i =>
    ∏ p ∈ path.referenceRetainedPrimes cutoff, path.referenceLocalDensity (raw i) β p)

noncomputable def referenceRetainedModulus (cutoff : ℕ) : ℕ :=
  ∏ p ∈ path.referenceRetainedPrimes cutoff, p.val ^ path.exponent p.val

omit [Fintype Tsp] in
theorem referenceRetainedModulus_pos (cutoff : ℕ) :
    0 < path.referenceRetainedModulus cutoff := by
  apply Finset.prod_pos
  intro p _
  exact pow_pos (path.prime p.val p.property).pos _

omit [Fintype Tsp] in
theorem referenceRetainedModulus_dvd (cutoff : ℕ) :
    path.referenceRetainedModulus cutoff ∣ path.referenceModulus :=
  Finset.prod_dvd_prod_of_subset (path.referenceRetainedPrimes cutoff) Finset.univ
    (fun p : path.primes => p.val ^ path.exponent p.val) (Finset.subset_univ _)

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialRetainedModulusBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

namespace VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

@[instance_reducible] noncomputable def retainedLabelDecidableEq (cutoff : ℕ) :
    DecidableEq (path.referenceRetainedPrimes cutoff) := Classical.decEq _

attribute [local instance] retainedLabelDecidableEq

noncomputable def referenceRetainedCRTModulus (cutoff : ℕ) : ℕ :=
  ∏ p : path.referenceRetainedPrimes cutoff, p.val.val ^ path.exponent p.val.val

omit [Fintype Tsp] in
theorem referenceRetainedCRTModulus_eq (cutoff : ℕ) :
    path.referenceRetainedCRTModulus cutoff = path.referenceRetainedModulus cutoff := by
  exact Finset.prod_coe_sort (path.referenceRetainedPrimes cutoff)
    (fun p : path.primes => p.val ^ path.exponent p.val)

omit [Fintype Tsp] in
theorem referenceRetainedCRTModulus_dvd (cutoff : ℕ) :
    path.referenceRetainedCRTModulus cutoff ∣ path.referenceModulus := by
  rw [path.referenceRetainedCRTModulus_eq]
  exact path.referenceRetainedModulus_dvd cutoff

local instance smallReferencePrimeNeZero : ∀ p : path.primes, NeZero p.val :=
  path.primeNeZero

local instance smallReferenceModulusNeZero (cutoff : ℕ) :
    NeZero (path.referenceRetainedCRTModulus cutoff) :=
  ⟨by rw [path.referenceRetainedCRTModulus_eq]; exact (path.referenceRetainedModulus_pos cutoff).ne'⟩

noncomputable def referenceRetainedCRTInputLaw (cutoff : ℕ) : FiniteProbabilityWeights
    (LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B →
      ZMod (path.referenceRetainedCRTModulus cutoff)) :=
  crtPolynomialInputLaw (fun p : path.referenceRetainedPrimes cutoff => p.val.val)
    (fun p : path.referenceRetainedPrimes cutoff => path.exponent p.val.val)
    (fun p : path.referenceRetainedPrimes cutoff => path.prescribed p.val.val)
    (primePower_crt_coprime (fun p : path.referenceRetainedPrimes cutoff => p.val.val)
      (fun p : path.referenceRetainedPrimes cutoff => path.exponent p.val.val)
      (fun p => path.prime p.val.val p.val.property)
      (Subtype.val_injective.comp Subtype.val_injective)) (fun p => path.origin p.val)

noncomputable def retainedCRTReferenceForecast {Ω Z : Type*} [Fintype Ω]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (raw : Ω → PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (cutoff : ℕ) (gridVolume : ℝ) (z : Z)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) : ℝ :=
  rationalInactiveForecast inactive (fun _ => path.referenceRetainedCRTInputLaw cutoff) gridPoint
    (fun i => integerLongPolynomialOutput path.referencePolynomial (raw i)
      (path.referenceRetainedCRTModulus cutoff))
    (path.referenceRetainedCRTModulus cutoff) gridVolume z
    (fun j => ZMod.castHom (path.referenceRetainedCRTModulus_dvd cutoff)
      (ZMod (path.referenceRetainedCRTModulus cutoff)) (β j))

noncomputable def retainedCRTIndependentForecast {Ω Z : Type*} [Fintype Ω]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (raw : Ω → PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (cutoff : ℕ) (gridVolume : ℝ) (z : Z)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) : ℝ :=
  rationalInactiveForecast inactive
    (fun _ => crtPrimePowerPolynomialLaw
      (V := LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B)
      (fun p : path.referenceRetainedPrimes cutoff => p.val.val)
      (fun p : path.referenceRetainedPrimes cutoff => path.exponent p.val.val)) gridPoint
    (fun i => crtPrimePowerIntegerPolynomialOutput
      (fun p : path.referenceRetainedPrimes cutoff => p.val.val)
      (fun p : path.referenceRetainedPrimes cutoff => path.exponent p.val.val)
      (fun p : path.referenceRetainedPrimes cutoff => path.prescribed p.val.val)
      (primePower_crt_coprime (fun p : path.referenceRetainedPrimes cutoff => p.val.val)
        (fun p : path.referenceRetainedPrimes cutoff => path.exponent p.val.val)
        (fun p => path.prime p.val.val p.val.property)
        (Subtype.val_injective.comp Subtype.val_injective))
      (path.localReferencePolynomial (raw i)) (fun p => path.origin p.val))
    (path.referenceRetainedCRTModulus cutoff) gridVolume z
    (fun j => ZMod.castHom (path.referenceRetainedCRTModulus_dvd cutoff)
      (ZMod (path.referenceRetainedCRTModulus cutoff)) (β j))

end ActualFixedSpatialForecastPath
end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualFixedSpatialSlicedRetainedKernelComparison
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

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

noncomputable def recoveredG
    (v : X → ℝ) (r : X → ZMod slice.path.referenceModulus)
    (β : Fin d → ℤ) (y : Fin d → ℝ) : ℝ := by
  letI : NeZero slice.path.referenceModulus := ⟨slice.path.referenceModulus_pos.ne'⟩
  exact forecastLawRecoveredKernel B U b S slice.principalLaw
    (slice.density hB) selected slice.path.sample slice.path.commonTuple
    (fun _ => slice.path.referenceInputLaw)
    (fun z t j => integerLongPolynomialOutput slice.path.referencePolynomial
      (fun k => (z k.1 k.2 : ℤ)) slice.path.referenceModulus t j)
    slice.path.referenceModulus (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    slice.path.base physicalN τ o hb bW v r
    (fun a => β (e.symm a)) (fun a => y (e.symm a))

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

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

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

local instance fullReferenceNonzero : NeZero slice.path.referenceModulus :=
  ⟨slice.path.referenceModulus_pos.ne'⟩
local instance retainedReferenceNonzero (cutoff : ℕ) :
    NeZero (slice.path.referenceRetainedCRTModulus cutoff) :=
  ⟨by rw [slice.path.referenceRetainedCRTModulus_eq];
      exact (slice.path.referenceRetainedModulus_pos cutoff).ne'⟩

noncomputable def retainedRecoveredG (cutoff : ℕ)
    (v : X → ℝ) (r : X → ZMod (slice.path.referenceRetainedCRTModulus cutoff))
    (β : Fin d → ℤ) (y : Fin d → ℝ) : ℝ :=
  forecastLawRecoveredKernel B U b S slice.principalLaw
    (slice.density hB) selected slice.path.sample slice.path.commonTuple
    (fun _ => slice.path.referenceRetainedCRTInputLaw cutoff)
    (fun z t j => integerLongPolynomialOutput slice.path.referencePolynomial
      (fun k => (z k.1 k.2 : ℤ)) (slice.path.referenceRetainedCRTModulus cutoff) t j)
    (slice.path.referenceRetainedCRTModulus cutoff)
    (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    slice.path.base physicalN τ o hb bW v r
    (fun a => β (e.symm a)) (fun a => y (e.symm a))

noncomputable def recoveredRationalFactor
    (r : X → ZMod slice.path.referenceModulus) (β : Fin d → ℤ) : ℝ :=
  forecastLawRecoveredRationalFactor B U b S slice.principalLaw selected
    slice.path.sample slice.path.commonTuple (fun _ => slice.path.referenceInputLaw)
    (fun z t j => integerLongPolynomialOutput slice.path.referencePolynomial
      (fun k => (z k.1 k.2 : ℤ)) slice.path.referenceModulus t j)
    slice.path.referenceModulus (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    hb bW r (fun a => β (e.symm a))

noncomputable def retainedRecoveredRationalFactor (cutoff : ℕ)
    (r : X → ZMod (slice.path.referenceRetainedCRTModulus cutoff)) (β : Fin d → ℤ) : ℝ :=
  forecastLawRecoveredRationalFactor B U b S slice.principalLaw selected
    slice.path.sample slice.path.commonTuple (fun _ => slice.path.referenceRetainedCRTInputLaw cutoff)
    (fun z t j => integerLongPolynomialOutput slice.path.referencePolynomial
      (fun k => (z k.1 k.2 : ℤ)) (slice.path.referenceRetainedCRTModulus cutoff) t j)
    (slice.path.referenceRetainedCRTModulus cutoff)
    (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ)) hb bW r
    (fun a => β (e.symm a))

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

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

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)


variable (cutoff : ℕ)
local notation "q" => slice.path.referenceRetainedCRTModulus cutoff
local notation "vol" => (∏ a, (basisAxisScale (b (Sigma.fst (selected a))) (Sigma.snd (selected a)) : ℝ))
local notation "Y" => (fun z t j => integerLongPolynomialOutput slice.path.referencePolynomial
  (fun k => (z (Prod.fst k) (Prod.snd k) : ℤ)) q t j)

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

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

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

local notation "labels" => forecastRecoveredIntegerLabels U b hb bW

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialRetainedPatchEndpoint
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal
open BoxProgressionPartition

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def bufferedSpatialWeight {Ω Θ : Type*} {m : ℕ}
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ) (T : Ω → (Fin m → ℤ) → ℝ)
    (G : Θ → Ω → (Fin m → ℤ) → ℝ) (z : Θ) (u : Ω) : ℝ :=
  ∑' b, χ.value (fun i => x u i - (b i : ℝ)) * G z u b * T u b

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

noncomputable def spatialPatchExtractionCost (L : ℝ) : ℝ := 20 * (L + 1) ^ 2

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def spatialPatchExtractionMesh (L : ℝ) : ℕ :=
  ⌈Real.exp (5 * L)⌉₊

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators NNReal Classical

end Erdos3

end

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

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

noncomputable def scaledRetainedRecoveredG (cutoff : ℕ) (κ : ℝ)
    (v : X → ℝ) (r : X → ZMod (slice.path.referenceRetainedCRTModulus cutoff))
    (β : Fin d → ℤ) (y : Fin d → ℝ) : ℝ :=
  κ * slice.retainedRecoveredG selected hB o bW hb e cutoff v r β y

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI

end


