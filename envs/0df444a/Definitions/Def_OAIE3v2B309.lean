-- Prove2me | Definitions.Def_OAIE3v2B309
-- name    : OAIE3v2B309
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T07:49:40.490246+00:00
-- url     : https://prove2.me/theorems/9f27e2b3-e2f4-4f8b-90ca-bebd091b6635
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 292 of 311
-- statement:
--   Definitions bundle 292 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B274`, `OAIE3v2B275`, `OAIE3v2B276`, `OAIE3v2B279` of this split.
--
--   Modules: `Estimates/AllocatedExternalCandidateLocalFixedCenterFront.lean`, `Lattices/AllocatedAffineCanonicalBackendBudget.lean`, `Lattices/AllocatedAffinePhysicalBoundsSuccessor.lean`, `Lattices/AllocatedAffinePhysicalTerminalReset.lean`, `Linear/AllocatedExternalCandidateCommonKeepPositiveKernelPreparation.lean`, `Polynomial/AllocatedNestedDegreeInduction.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B274
import Definitions.Def_OAIE3v2B275
import Definitions.Def_OAIE3v2B276
import Definitions.Def_OAIE3v2B279

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedExternalCandidateCommonKeepPositiveKernelPreparation
namespace OAI

section

namespace Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem

theorem positiveKernelPreparationParameter_ge_input {p : ℝ} (hp : 0 ≤ p) :
    p + 3 ≤ positiveKernelPreparationParameter p := by
  have hC := positiveKernelPreparationExponent_ge_two
  have hbase : 1 ≤ p + 5 := by linarith
  have hself : p + 5 ≤ (p + 5) ^ positiveKernelPreparationExponent := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase
      (by omega : 1 ≤ positiveKernelPreparationExponent)
  unfold positiveKernelPreparationParameter
  linarith

theorem positiveKernelPreparationParameter_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ positiveKernelPreparationParameter p := by
  have := positiveKernelPreparationParameter_ge_input hp
  linarith

theorem positiveKernelPreparationBinLog_nonneg {p : ℝ} (hp : 0 ≤ p) (e : ℕ) :
    0 ≤ positiveKernelPreparationBinLog p e := by
  have := positiveKernelPreparationParameter_nonneg hp
  unfold positiveKernelPreparationBinLog
  positivity

end Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateLocalFixedCenterFront
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler

variable {B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.fixedCenterMaskSiteNonempty
theorem exists_fixedCenter_mask_models (degree : ℕ)
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {u p pSlice pTest localBudget Pnative massLog capLog Edata P C : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hNative : 0 ≤ Pnative)
    (hSliceNonneg : 0 ≤ pSlice) (hTestBudget : 2 ≤ pTest)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : capLog ≤ p)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ Edata)
    (hPrecision : u + 2 * p + max (max localBudget (3 * Pnative + 3))
      (2 * u + 4 * p + max 0 massLog + 20) + 32 ≤ P)
    (hdirect : A.NativeDetection degree pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) C (Real.exp capLog)))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy P)
    {Forecast : Type} [Nonempty Forecast]
    (data : Forecast → ActualForecastData N poly Pnative massLog capLog Edata)
    {Freq Bin Y : Type*}
    (F : Freq → integerBox N → Y → ℂ) (centers : Freq → Bin → Y → ℂ)
    {ε : ℝ} (hnet : ∀ f x, ∃ i, ∀ y, ‖F f x y - centers f i y‖ ≤ ε)
    (input : integerBox N → ℂ) (hinput : ∀ v, ‖input v‖ ≤ Real.exp p) :
    let Packet := UniversalLocalMajorSliceTest A.sides degree pSlice pTest
    let commonBudget := max localBudget (3 * Pnative + 3)
    let Qmodel := max commonBudget (2 * u + 4 * p + max 0 massLog + 20)
    let native := twistedNativeSampleFunctions (1 : X → ℕ) degree commonBudget
      (fun v : integerBox N => v.val)
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp commonBudget) (Real.exp commonBudget)
        ⟨Real.exp commonBudget, Real.exp_nonneg _⟩)
        (v : integerBox N) => W.eval N poly v.val)
    ∃ models : Freq × Bin → CenteredForecastModel (integerBox N), ∀ branch,
      (∀ i, (models branch).models i ∈ native) ∧
      externalNetMaskFamily F centers hnet input branch =
        (∑ i, (models branch).coefficient i • (models branch).models i) +
          (models branch).residual ∧
      (∑ i, |(models branch).coefficient i|) ≤ Real.exp (Qmodel + 2) ∧
      sampledSliceSeminorm A.law (A.physicalBox hξone hmargin)
        (fun _ (packet : Packet) => packet.slice.subtypeSites)
        (fun _ (packet : Packet) site => packet.weight site.val) (models branch).residual ≤
        Real.exp (-u) ∧
      (∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).correlation
        (models branch).residual (data f).target‖ ≤ Real.exp (-u)) ∧
      ((models branch).nterms : ℝ) ≤ Real.exp (2 * Qmodel + 2 * u + 4 * p + 34) := by
  classical
  intro Packet commonBudget Qmodel native
  have hmodel := fun branch : Freq × Bin =>
    A.exists_fixedCenter_universal_forecast_model degree hξone hmargin
      hu hp hbudget hNative hSliceNonneg hTestBudget hSliceLog hC hCp hCap hAccuracy
      hPrecision hdirect hexcess data (externalNetMaskFamily F centers hnet input branch)
      (externalNetMaskFamily_norm_le F centers hnet input (Real.exp_nonneg p) hinput branch)
  choose models hmodels using hmodel
  exact ⟨models, hmodels⟩

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffinePhysicalTerminalReset
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped Classical TensorProduct BigOperators
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
    {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : ℕ → LayerSamplerVariables G I n B → Prop)
    {ι κ η : Type} {χ : ℕ → Type} [Fintype ι] [Fintype κ] [∀ r, Fintype (χ r)] [Fintype η]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark

structure AffinePhysicalTerminalData
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (Fmark.AssociatedGraded ⧸ (fast).toSubmodule)))
    (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
    (Bphase budget pAffine pFull : ℝ) (a : ℕ)
    (history : CertifiedFullChartFiniteHistory Fmark bF ν hF J (fast).toSubmodule
      basis lift Z Set.univ U poly N Bphase s)
    (separation : ℝ) where
  selected : P.CertifiedThresholdAffineRefinement history.K pAffine separation
  denominator_pos : 0 < selected.affine.commonDenominator
  denominator_bound : (selected.affine.commonDenominator : ℝ) ≤
    Real.exp ((m : ℝ) * certifiedAffineCenterBudget pAffine)
  q : ℕ
  nFinal : ℕ
  q_pos : 0 < q
  q_bound : (q : ℝ) ≤ Real.exp budget
  nFinal_pos : 0 < nFinal
  nFinal_bound : (nFinal : ℝ) ≤
    Real.exp ((pFull + allocatedEarlyAffineRightExponent s a) ^ allocatedEarlyAffineRightExponent s a)
  denominator_dvd : q * selected.affine.commonDenominator ^ s ∣ nFinal
  factors :
    let wt := fullTaggedVariableWeight (X := X) J
    let β := selected.affine.globalChart
    let pull := Fmark.realSymbolHomogeneousPullbackHom bF ν hF wt wt
      (fun i => weightedHomogeneousComponent wt (wt i) (β i))
      (fun _ => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    GlobalMarkedNativeFactors Fmark bF ν hF wt fast
      (Fmark.weightedAdaptedRealChartHom wt wt β selected.affine.globalChart_support
        (Fmark.realification.polynomialOrbitCoordinates wt marked))
      (pull history.outer.1) (pull history.outer.2)
  right_grid : Fmark.PolynomialRationalGrid bF (fullTaggedVariableWeight J) nFinal factors.right
  local_left : ∀ z : selected.affine.refinement.problem.productive,
    let C := selected.affine.refinement.problem.chart z
    Fmark.PolynomialSlowBound bF (fun _ : C.Variables => 1)
      (fun i => (A.sides i.val : ℝ))
      (Real.exp ((pFull + allocatedEarlyAffineLeftExponent s a) ^ allocatedEarlyAffineLeftExponent s a))
      (Fmark.weightedAdaptedRealChartHom (fullTaggedVariableWeight J) (fun _ : C.Variables => 1)
        (integerSampledRealChart C.integerChart) C.integerChart_support factors.left)
  physical_left : ∀ x ∈ integerBox N, ∀ i,
    |(bF.baseChange ℝ).repr
      (Fmark.realification.polynomialOrbitEval (fullTaggedVariableWeight J) (P.physicalIntegerPoint x)
        ((Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J)).symm factors.left)).coord i| ≤
      Real.exp ((pFull + allocatedEarlyAffineLeftExponent s a) ^ allocatedEarlyAffineLeftExponent s a)
  physical_right : ∀ x : X → ℤ, (bF.baseChange ℝ).equivFun
    (Fmark.realification.polynomialOrbitEval (fullTaggedVariableWeight J) (P.physicalIntegerPoint x)
      ((Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J)).symm factors.right)).coord ∈
      realDenominatorGrid nFinal

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineCanonicalBackendBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open NilpotentLieFiltration

theorem allocatedAffineResetMapBudget_bounds (s : ℕ) {p0 pFull : ℝ}
    (hp0 : 0 ≤ p0) (hFull : 0 ≤ pFull) :
    AllocatedAffineResetMapBudgetBounds s p0 pFull := by
  have hsection : 0 ≤ ordinaryImagePointwiseBudget (s + 1) (s + 1) p0 :=
    hp0.trans (ordinaryImagePointwiseBudget_ge (s + 1) (s + 1) hp0)
  have hheight : 0 ≤ allocatedAffineResetHeightLog p0 := by
    unfold allocatedAffineResetHeightLog
    positivity
  have hright : 0 ≤ allocatedAffineResetRightLog s pFull := by
    unfold allocatedAffineResetRightLog
    positivity
  constructor <;> dsimp only [allocatedAffineResetMapBudget] <;> linarith

theorem allocatedAffineResetMapBudget_denominator (s : ℕ) {p0 pFull : ℝ}
    (hp0 : 0 ≤ p0) (hFull : 0 ≤ pFull) {l n : ℕ}
    (hl : (l : ℝ) ≤ Real.exp p0)
    (hn : (n : ℝ) ≤ Real.exp (allocatedAffineResetRightLog s pFull)) :
    ((l * n : ℕ) : ℝ) ≤ Real.exp (allocatedAffineResetMapBudget s p0 pFull) := by
  rw [Nat.cast_mul]
  calc
    (l : ℝ) * n ≤ Real.exp p0 * Real.exp (allocatedAffineResetRightLog s pFull) :=
      mul_le_mul hl hn (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (p0 + allocatedAffineResetRightLog s pFull) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (allocatedAffineResetMapBudget_bounds s hp0 hFull).denominatorLog

theorem allocatedAffineCanonicalBudget_bounds (s : ℕ) {p0 pFull : ℝ}
    (hp0 : 0 ≤ p0) (hFull : 0 ≤ pFull) :
    AllocatedAffineCanonicalBudgetBounds s p0 pFull := by
  have hm := allocatedAffineResetMapBudget_bounds s hp0 hFull
  obtain ⟨hn, hnf, hnm, hnq, hnl, hn4, hn3⟩ :=
    affineResetNativeBudget_bounds (allocatedEarlyAffineLeftExponent (s + 1) 4)
      hFull hm.nonnegative (q := p0)
  change 0 ≤ allocatedAffineCanonicalNativeBudget s p0 pFull at hn
  change pFull ≤ allocatedAffineCanonicalNativeBudget s p0 pFull at hnf
  change allocatedAffineResetMapBudget s p0 pFull ≤
    allocatedAffineCanonicalNativeBudget s p0 pFull at hnm
  change p0 ≤ allocatedAffineCanonicalNativeBudget s p0 pFull at hnq
  have hreset := allocatedAffineResetLogBudget_nonnegative s hn
  have hcompare : 0 ≤ allocatedAffineResetCompareLog s
      (allocatedAffineCanonicalNativeBudget s p0 pFull) := by
    unfold allocatedAffineResetCompareLog
    positivity
  have hleft : 0 ≤ allocatedAffineResetLeftLog s pFull := by
    unfold allocatedAffineResetLeftLog
    positivity
  have hs : (0 : ℝ) ≤ (s + 2 : ℕ) := Nat.cast_nonneg _
  constructor
  · dsimp only [allocatedAffineCanonicalBudget]; linarith [hm.nonnegative]
  · exact hm.nonnegative
  · exact hn
  · dsimp only [allocatedAffineCanonicalBudget]; linarith [hm.nonnegative]
  · dsimp only [allocatedAffineCanonicalBudget]; linarith [hm.nonnegative]
  · dsimp only [allocatedAffineCanonicalBudget]; linarith
  · dsimp only [allocatedAffineCanonicalBudget]; linarith [hm.nonnegative]
  · exact hnq
  · exact hnf
  · exact hnm
  · dsimp only [allocatedAffineCanonicalBudget]; linarith [hm.nonnegative]
  · dsimp only [allocatedAffineCanonicalBudget]; linarith [hm.nonnegative]
  · dsimp only [allocatedAffineCanonicalBudget]; linarith [hm.nonnegative]
  · dsimp only [allocatedAffineCanonicalBudget]; linarith [hm.nonnegative]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open NilpotentLieFiltration

theorem allocatedAffineCanonical_cutoffCost_le_recursive (s : ℕ) {p0 pFull : ℝ}
    (hp0 : 0 ≤ p0) (hFull : 0 ≤ pFull) :
    candidateSideCutoffCost
      (Real.exp (candidatePrimitiveFreezingCutoff s 1
        (allocatedAffineCanonicalBudget s p0 pFull))) ≤
      finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1)
        (allocatedAffineCanonicalBudget s p0 pFull) := by
  have hp := (allocatedAffineCanonicalBudget_bounds s hp0 hFull).nonnegative
  exact ((candidatePrimitiveFreezingCutoff_integer_cost s 1 hp).trans
    (candidatePrimitiveFreezingCutoff_add_two_le_budget s 1 hp)).trans
      (power_le_recursiveParameter _ hp)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffinePhysicalBoundsSuccessor
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration
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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem.CertifiedThresholdAffineRefinement

variable {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p separation : ℝ}

variable (selected : P.CertifiedThresholdAffineRefinement K p separation)

theorem withKeep_original_dense
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : selected.problem.productive, (selected.problem.chart z).keep = keep)
    (z : (selected.problem.withKeep keep hkeep).productive) :
    IsDenseCommonStrideBox
      (fun i : ((selected.problem.withKeep keep hkeep).chart z).Variables => A.sides i.val)
      cost ((selected.problem.withKeep keep hkeep).chart z).slice.integerPoints := by
  suffices h : ∀ (keep' : LayerSamplerVariables G I n B → Prop)
      (heq : (selected.problem.chart z).keep = keep'),
      IsDenseCommonStrideBox
        (fun i : ((selected.problem.chart z).withKeep keep' heq).Variables => A.sides i.val)
        cost ((selected.problem.chart z).withKeep keep' heq).slice.integerPoints by
    exact h keep (hkeep z)
  intro keep' heq
  cases heq
  exact selected.original_dense z

end AllocatedExternalCandidateProblem.CertifiedThresholdAffineRefinement
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realChartSubstitute realPolynomialGroupMap associatedGradedMap gradedRefiltrationMap
  PolynomialRationalGrid PolynomialSlowBound
  realSymbolHomogeneousPullbackHom CertifiedFullChartFiniteHistory.outer

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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem

variable {L M : Type} {nMarkedBasis : ℕ} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (c : Basis (Fin nMarkedBasis) ℚ M)
    (ν : Fin nMarkedBasis → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i}))
    {η : Type} [Fintype η]
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (Fmark.filtration.AssociatedGraded ⧸
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule)))
    (lift : (Fmark.filtration.AssociatedGraded ⧸
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule) →ₗ[ℚ]
        Fmark.filtration.AssociatedGraded)
    (Bphase budget pAffine pFull separation : ℝ)
    (history : CertifiedFullChartFiniteHistory Fmark.filtration c ν hF J
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule
      basis lift
      (Fmark.filtration.realPolynomialSymbolHom c ν hF (fullTaggedVariableWeight J)
        (Fmark.filtration.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked))
      Set.univ U poly N Bphase (s + 1))
    (data : P.AffinePhysicalTerminalData c ν hF hφ W basis lift
      Bphase budget pAffine pFull 4 history separation)
    (hcost : Real.exp cost ≤ separation)

theorem conclusion_of_affinePhysicalTerminal_nativeReset_degreeRule
    {p logSlow massLog : ℝ} {denominator e : ℕ}
    (reset : AllocatedExternalGlobalNativeResetFamily Fmark φ hφ
      data.selected.problem (fun i => candidateSideCutoff separation ≤ A.sides i)
      (data.selected.common_keep hcost) W data.factors (Real.exp logSlow) denominator)
    (hp0 : 0 ≤ p)
    (hseparation : separation = Real.exp (candidatePrimitiveFreezingCutoff s 1 p))
    (hDNative : D.GeometryComplexityLE p)
    (hRetainedCount : (Fintype.card { i : LayerSamplerVariables G I n B //
      candidateSideCutoff separation ≤ A.sides i } : ℝ) ≤ p)
    (hMarkedDimension : (nMarkedBasis : ℝ) ≤ p)
    (hSectionMapHeight : ∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p)
    (hdenominatorPos : 0 < denominator)
    (hdenominatorBound : (denominator : ℝ) ≤ Real.exp p)
    (hdenominatorDvd : data.nFinal ∣ denominator)
    (hlogSlow : logSlow ≤ p)
    (hphysical : (pFull + allocatedEarlyAffineLeftExponent (s + 1) 4) ^
      allocatedEarlyAffineLeftExponent (s + 1) 4 ≤ p)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p)
    (hscoreInput : Real.exp (-p) ≤ scoreThreshold)
    (hcostInput : cost ≤ p)
    (hmassLog : massLog ≤ p)
    (hmassInput : Real.exp (-massLog) ≤
      Real.exp (-((2 * certifiedAffineCenterBudget pAffine + 3) ^ 3)) * massThreshold)
    (dw : Fin d → ℕ)
    (hdb : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ dw i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis dw hdb) dw W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hξ1 : ξ ≤ 1)
    (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp p)
    (hOriginalLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hFGeo : Fmark.GeometryComplexityLE p)
    {Generator : Type} [Fintype Generator]
    (generators : Generator → D.filtration.AssociatedGraded)
    (hspan : span ℚ (Set.range generators) = W.toSubmodule)
    (hgeneratorCount : (Fintype.card Generator : ℝ) ≤ p)
    (hmarkedBasis : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p)
    (hmarkHeight : ∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p)
    (hgeneratorHeight : ∀ i j,
      rationalLogHeight ((D.filtration.associatedGradedBasis D.basis dw hdb).repr (generators i) j) ≤ p)
    (htopKernel : ∀ x : L, x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) → φ x = 0 → x = 0)
    (hOriginalNet : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y, ‖observable x y - observable (oc i).val y‖ ≤ η)
    (outputCost : ℝ)
    (lowerIH : A.DegreeGlobalizationAt (E := E) weight s
      (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0} s 1 e + 2)
      (finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1) p) outputCost) :
    Nonempty (P.Conclusion (max outputCost (candidateSideCutoffCost separation))
      (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  classical
  let keep : LayerSamplerVariables G I n B → Prop :=
    fun i => candidateSideCutoff separation ≤ A.sides i
  let hkeep := data.selected.common_keep hcost
  let reset' : AllocatedExternalGlobalNativeResetFamily Fmark φ hφ
      data.selected.problem keep hkeep W data.factors (Real.exp p) denominator :=
    { reset with
      slow_left := fun z => D.filtration.polynomialSlowBound_mono D.basis
        (fun _ : {i // keep i} => 1) (fun i => (A.sides i.val : ℝ))
        (fun i => Nat.cast_pos.mpr (A.sides_pos i.val))
        (Real.exp_le_exp.mpr hlogSlow) _ (reset.slow_left z) }
  have hslowMark : ∀ z, Fmark.filtration.PolynomialSlowBound c
      (fun _ : {i // keep i} => 1) (fun i => (A.sides i.val : ℝ)) (Real.exp p)
      (Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : {i // keep i} => 1)
        (integerSampledRealChart ((data.selected.problem.withKeep keep hkeep).chart z).integerChart)
        ((data.selected.problem.withKeep keep hkeep).chart z).integerChart_support data.factors.left) := by
    intro z
    suffices h : ∀ (keep' : LayerSamplerVariables G I n B → Prop)
        (heq : (data.selected.problem.chart z).keep = keep'),
        Fmark.filtration.PolynomialSlowBound c
          (fun _ : ((data.selected.problem.chart z).withKeep keep' heq).Variables => 1)
          (fun i => (A.sides i.val : ℝ)) (Real.exp p)
          (Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
            (fun _ : ((data.selected.problem.chart z).withKeep keep' heq).Variables => 1)
            (integerSampledRealChart ((data.selected.problem.chart z).withKeep keep' heq).integerChart)
            ((data.selected.problem.chart z).withKeep keep' heq).integerChart_support data.factors.left) by
      exact h keep (hkeep z)
    intro keep' heq
    cases heq
    exact Fmark.filtration.polynomialSlowBound_mono c
      (fun _ : (data.selected.problem.chart z).Variables => 1)
      (fun i => (A.sides i.val : ℝ))
      (fun i => Nat.cast_pos.mpr (A.sides_pos i.val))
      (Real.exp_le_exp.mpr hphysical) _ (data.local_left z)
  have hgrid := Fmark.filtration.polynomialRationalGrid_of_dvd c
    (fullTaggedVariableWeight J) data.nFinal_pos hdenominatorDvd data.factors.right data.right_grid
  have hside (i : {i // keep i}) :
      Real.exp (candidatePrimitiveFreezingCutoff s 1 p) ≤ (A.sides i.val : ℝ) := by
    rw [← hseparation]
    exact (lt_candidateSideCutoff separation).le.trans (Nat.cast_le.mpr i.property)
  have hcostRounded : max cost (candidateSideCutoffCost separation) ≤
      candidatePrimitiveFreezingCutoff s 1 p + 2 := by
    apply max_le
    · have h := candidatePrimitiveFreezingCutoff_ge_input s 1 hp0
      linarith
    · rw [hseparation]
      exact candidatePrimitiveFreezingCutoff_integer_cost s 1 hp0
  have hmarkedPhysicalLeft : ∀ x ∈ integerBox N, ∀ i,
      |(c.baseChange ℝ).repr
        (Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
          ((data.selected.problem.withKeep keep hkeep).physicalIntegerPoint x) reset'.leftMark).coord i| ≤
        Real.exp p := by
    intro x hx i
    rw [data.selected.withKeep_physicalIntegerPoint keep hkeep x]
    exact (data.physical_left x hx i).trans (Real.exp_le_exp.mpr hphysical)
  obtain ⟨out⟩ := data.selected.problem.conclusion_of_roundedThreshold_nativeReset_degreeRule
    Fmark φ hφ keep hkeep W c ν hF data.factors reset' hσ1 H hH hchart hsmall hp
    1 hp0 hDNative (by simpa only [Fintype.card_eq_nat_card] using hRetainedCount)
    hMarkedDimension hSectionMapHeight
    hdenominatorPos hdenominatorBound (Real.exp_le_exp.mpr (by simp)) hslowMark hgrid
    (data.selected.withKeep_original_dense keep hkeep) hside hweight hscoreInput
    hcostRounded hcostInput hmassLog hmassInput dw hdb hW hsurj hξ1 ℓ hℓ
    hmarkedPhysicalLeft hOriginalLip hpositive hFGeo generators hspan hgeneratorCount
    hmarkedBasis hmarkHeight hgeneratorHeight htopKernel hOriginalNet outputCost lowerIH
  exact ⟨data.selected.conclusion out⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realChartSubstitute realPolynomialGroupMap associatedGradedMap gradedRefiltrationMap
  PolynomialRationalGrid PolynomialSlowBound
  realSymbolHomogeneousPullbackHom CertifiedFullChartFiniteHistory.outer

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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem

variable {L M : Type} {nMarkedBasis : ℕ} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (c : Basis (Fin nMarkedBasis) ℚ M)
    (ν : Fin nMarkedBasis → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i}))
    {η : Type} [Fintype η]
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (Fmark.filtration.AssociatedGraded ⧸
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule)))
    (lift : (Fmark.filtration.AssociatedGraded ⧸
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule) →ₗ[ℚ]
        Fmark.filtration.AssociatedGraded)
    (Bphase budget pAffine pFull separation : ℝ)
    (history : CertifiedFullChartFiniteHistory Fmark.filtration c ν hF J
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule
      basis lift
      (Fmark.filtration.realPolynomialSymbolHom c ν hF (fullTaggedVariableWeight J)
        (Fmark.filtration.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked))
      Set.univ U poly N Bphase (s + 1))
    (data : P.AffinePhysicalTerminalData c ν hF hφ W basis lift
      Bphase budget pAffine pFull 4 history separation)
    (hcost : Real.exp cost ≤ separation)

variable {Fmark φ hφ P W c ν hF basis lift Bphase budget pAffine pFull separation history data hcost}

structure AffinePhysicalTerminalData.SuccessorInputs
    (data : P.AffinePhysicalTerminalData c ν hF hφ W basis lift
      Bphase budget pAffine pFull 4 history separation)
    (p : ℝ) (e : ℕ) (outputCost : ℝ) where
  nonnegative : 0 ≤ p
  separation_eq : separation = Real.exp (candidatePrimitiveFreezingCutoff s 1 p)
  source_geometry : D.GeometryComplexityLE p
  retained_count : (Fintype.card { i : LayerSamplerVariables G I n B //
    candidateSideCutoff separation ≤ A.sides i } : ℝ) ≤ p
  marked_dimension : (nMarkedBasis : ℝ) ≤ p
  section_height : ∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p
  physical_budget : (pFull + allocatedEarlyAffineLeftExponent (s + 1) 4) ^
    allocatedEarlyAffineLeftExponent (s + 1) 4 ≤ p
  scale_le_one : ∀ j, σ j ≤ 1
  chart_bound : Fin m → ℝ
  chart_nonnegative : ∀ j, 0 ≤ chart_bound j
  chart_norm : ∀ j v,
    ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ chart_bound j * ‖v‖
  chart_small : ∀ j, chart_bound j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8
  polynomial_degree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)
  weight_bound : ∀ x, ‖weight x‖ ≤ Real.exp p
  score_bound : Real.exp (-p) ≤ scoreThreshold
  cost_bound : cost ≤ p
  mass_log : ℝ
  mass_log_bound : mass_log ≤ p
  mass_bound : Real.exp (-mass_log) ≤
    Real.exp (-((2 * certifiedAffineCenterBudget pAffine + 3) ^ 3)) * massThreshold
  weights : Fin d → ℕ
  adapted : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ weights i})
  graded : BasisGradedSubmodule
    (D.filtration.associatedGradedBasis D.basis weights adapted) weights W.toSubmodule
  surjective : ∀ j, ∀ y ∈ Fmark.filtration.layer j,
    ∃ x ∈ D.filtration.layer j, φ x = y
  width_le_one : ξ ≤ 1
  lipschitz_constant : ℝ≥0
  lipschitz_bound : (lipschitz_constant : ℝ) ≤ Real.exp p
  lipschitz : ∀ x, letI := D.metricSpace; LipschitzWith lipschitz_constant (observable x)
  positive : ∀ x y, (observable x y).im = 0 ∧
    0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1
  marked_geometry : Fmark.GeometryComplexityLE p
  Generator : Type
  generator_fintype : Fintype Generator
  generators : Generator → D.filtration.AssociatedGraded
  generator_span : span ℚ (Set.range generators) = W.toSubmodule
  generator_count : (@Fintype.card Generator generator_fintype : ℝ) ≤ p
  marked_basis_height : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p
  mark_height : ∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p
  generator_height : ∀ i j,
    rationalLogHeight
      ((D.filtration.associatedGradedBasis D.basis weights adapted).repr (generators i) j) ≤ p
  top_kernel : ∀ x : L,
    x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) → φ x = 0 → x = 0
  net : ∀ accuracy : ℝ, 0 < accuracy → accuracy ≤ 1 → ∃ count : ℕ,
    (count : ℝ) ≤ Real.exp ((p + Real.log (1 / accuracy) + e) ^ e) ∧
    ∃ centers : Fin count → {x : X → ℤ // x ∈ integerBox N},
      ∀ x ∈ integerBox N, ∃ i, ∀ y,
        ‖observable x y - observable (centers i).val y‖ ≤ accuracy
  lower_degree : A.DegreeGlobalizationAt (E := E) weight s
    (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0} s 1 e + 2)
    (finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1) p) outputCost

theorem AffinePhysicalTerminalData.SuccessorInputs.conclusion_of_reset
    {p logSlow outputCost : ℝ} {denominator e : ℕ}
    (input : data.SuccessorInputs p e outputCost)
    (reset : AllocatedExternalGlobalNativeResetFamily Fmark φ hφ
      data.selected.problem (fun i => candidateSideCutoff separation ≤ A.sides i)
      (data.selected.common_keep hcost) W data.factors (Real.exp logSlow) denominator)
    (hlogSlow : logSlow ≤ p)
    (hdenominatorPos : 0 < denominator)
    (hdenominatorBound : (denominator : ℝ) ≤ Real.exp p)
    (hdenominatorDvd : data.nFinal ∣ denominator) :
    Nonempty (P.Conclusion (max outputCost (candidateSideCutoffCost separation))
      (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  let _ := input.generator_fintype
  exact P.conclusion_of_affinePhysicalTerminal_nativeReset_degreeRule Fmark φ hφ W c ν hF
    basis lift Bphase budget pAffine pFull separation history data hcost reset
    input.nonnegative input.separation_eq input.source_geometry input.retained_count
    input.marked_dimension input.section_height hdenominatorPos hdenominatorBound hdenominatorDvd
    hlogSlow input.physical_budget input.scale_le_one input.chart_bound input.chart_nonnegative
    input.chart_norm input.chart_small input.polynomial_degree input.weight_bound input.score_bound
    input.cost_bound input.mass_log_bound input.mass_bound input.weights input.adapted input.graded
    input.surjective input.width_le_one input.lipschitz_constant input.lipschitz_bound input.lipschitz
    input.positive input.marked_geometry input.generators input.generator_span input.generator_count
    input.marked_basis_height input.mark_height input.generator_height input.top_kernel input.net
    outputCost input.lower_degree

end AllocatedExternalCandidateProblem
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

namespace AllocatedExternalCandidateProblem

theorem positiveKernelPreparationBinLog_mono_netExponent {p : ℝ}
    (hp : 0 ≤ p) {e f : ℕ} (hef : e ≤ f) :
    positiveKernelPreparationBinLog p e ≤ positiveKernelPreparationBinLog p f := by
  have hq := positiveKernelPreparationParameter_nonneg hp
  have hef' : (e : ℝ) ≤ f := Nat.cast_le.mpr hef
  have hf : (0 : ℝ) ≤ f := Nat.cast_nonneg f
  unfold positiveKernelPreparationBinLog
  calc
    _ ≤ (2 * p + positiveKernelPreparationParameter p + 5 + f) ^ e :=
      pow_le_pow_left₀ (by positivity) (by linarith only [hef']) e
    _ ≤ _ := pow_le_pow_right₀ (by linarith only [hp, hq, hf]) hef

end AllocatedExternalCandidateProblem

end Erdos3.VectorPolynomial

end

end OAI
end


