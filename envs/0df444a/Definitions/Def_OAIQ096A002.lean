-- Prove2me | Definitions.Def_OAIQ096A002
-- name    : OAIQ096A002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T03:29:05.521219+00:00
-- url     : https://prove2.me/theorems/a18baf25-6e4b-4529-8dee-ed16c40b0cc7
-- title:
--   Definitions bundle OAIQ096A002 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 413 declarations of OpenAI's Lean: 130 definitions, 1 inductive type or structure and 282 theorems. The definitions and types are `OAI.CubicFirstMoment.MetaplecticStripPolynomial`, `OAI.CubicFirstMoment.MontgomeryVaughanBound`, `OAI.CubicFirstMoment.PrimeMellinControl`, `OAI.CubicFirstMoment.SemiprimeAngularWeightParameters`, `OAI.CubicFirstMoment.TangentL2`, `OAI.CubicFirstMoment.affineSchwartzProfile`, `OAI.CubicFirstMoment.angularAbelDerivative`, `OAI.CubicFirstMoment.angularAbelWeight`, `OAI.CubicFirstMoment.angularAnnulus`, `OAI.CubicFirstMoment.angularAnnulusSchwartz`, `OAI.CubicFirstMoment.angularComplexCutoff`, `OAI.CubicFirstMoment.angularLogExtension`, `OAI.CubicFirstMoment.angularLogPerturbation`, `OAI.CubicFirstMoment.angularPlanePhase`, `OAI.CubicFirstMoment.angularPositiveCutoff`, `OAI.CubicFirstMoment.angularWeightOperator`, `OAI.CubicFirstMoment.annularLogSchwartz`, `OAI.CubicFirstMoment.antiHarmonicGaussian`, `OAI.CubicFirstMoment.closedVerticalStrip`, `OAI.CubicFirstMoment.commonNonzeroCost`, `OAI.CubicFirstMoment.complexMulEquiv`, `OAI.CubicFirstMoment.complexMulMatrix`, `OAI.CubicFirstMoment.coreDyadicConductor`, `OAI.CubicFirstMoment.cubeDyadTriples`, `OAI.CubicFirstMoment.cubicBesselDerivativePowerConstant`, `OAI.CubicFirstMoment.cubicBesselHeat`, `OAI.CubicFirstMoment.cubicBesselHeatDerivative`, `OAI.CubicFirstMoment.cubicBesselKernel`, `OAI.CubicFirstMoment.cubicBesselKernelDerivative`, `OAI.CubicFirstMoment.cubicBesselLogDerivative`, `OAI.CubicFirstMoment.cubicBesselLogWeight`, `OAI.CubicFirstMoment.cubicBesselSquareHeat`, `OAI.CubicFirstMoment.cubicBesselSumShear`, `OAI.CubicFirstMoment.cubicBesselSumWeight`, `OAI.CubicFirstMoment.cubicBesselTriangle`, `OAI.CubicFirstMoment.cubicThetaAngularAbsorption`, `OAI.CubicFirstMoment.cubicThetaCartesianKernel`, `OAI.CubicFirstMoment.cubicThetaCoordinateSmooth`, `OAI.CubicFirstMoment.cubicThetaCoordinateValues`, `OAI.CubicFirstMoment.cubicThetaCuspCutoff` and 91 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicGram_CubeEstimates`, `CubicGram_GramPoisson`, `CubicGram_LatticePoisson`, `CubicGram_MellinDecay`, `CubicGram_Periodization`, `CubicMoment_Angular_AngularLatticeProfile`, `CubicMoment_Angular_AngularLogCutoff`, `CubicMoment_Angular_AngularModel`, `CubicMoment_Angular_AngularWeightOperator`, `CubicMoment_Decomposition_DistinguishedPrimeVariation`, `CubicMoment_Decomposition_DistinguishedScalePartition`, `CubicMoment_Decomposition_PrimeProductEnvelope`, `CubicMoment_Estimates_AntiHarmonicGaussian`, `CubicMoment_Estimates_CommonNonzeroBound`, `CubicMoment_Estimates_CompactParameterWeights`, `CubicMoment_Estimates_CubeSchwartz`, `CubicMoment_Estimates_CubicBesselBounds`, `CubicMoment_Estimates_CubicBesselContinuity`, `CubicMoment_Estimates_CubicBesselDerivative`, `CubicMoment_Estimates_CubicBesselDerivativeBounds`, `CubicMoment_Estimates_CubicBesselIntegral`, `CubicMoment_Estimates_CubicBesselLogDerivative`, `CubicMoment_Estimates_CubicBesselLogIntegrable`, `CubicMoment_Estimates_CubicBesselPowerDecay`, `CubicMoment_Estimates_CubicBesselSquareHeat`, `CubicMoment_Estimates_CubicBesselSumIntegral`, `CubicMoment_Estimates_CubicDyadicCoverage`, `CubicMoment_Estimates_CubicWhittakerDerivative`, `CubicMoment_Estimates_CubicWhittakerExponential`, `CubicMoment_Estimates_CubicWhittakerMellin`, `CubicMoment_Estimates_DyadicWeightIntegral`, `CubicMoment_Estimates_FourierCutoff`, `CubicMoment_Estimates_GaussianDerivativeFactors`, `CubicMoment_Estimates_GaussianRapidDecay`, `CubicMoment_Estimates_GaussianSchwartz`, `CubicMoment_Estimates_GeometricPrimeBins`, `CubicMoment_Estimates_HarmonicGaussian`, `CubicMoment_Estimates_HeckeDualContour`, `CubicMoment_Estimates_HeckeThetaCompletion`, `CubicMoment_Estimates_HeightEndpointRegularity`, `CubicMoment_Estimates_HeightIntegrationByParts`, `CubicMoment_Estimates_HeightWindowCount`, `CubicMoment_Estimates_HuxleyGaussianPacking`, `CubicMoment_Estimates_HuxleyGridPacking`, `CubicMoment_Estimates_IntervalSmoothing`, `CubicMoment_Estimates_LargeTupleCoordinateWeights`, `CubicMoment_Estimates_LargeTupleCutoffBoxes`, `CubicMoment_Estimates_LargeTupleWeights`, `CubicMoment_Estimates_LogarithmicWeightFamily`, `CubicMoment_Estimates_LowHeightIntegral`, `CubicMoment_Estimates_MellinContour`, `CubicMoment_Estimates_MellinPrimeControl`, `CubicMoment_Estimates_MellinSeries`, `CubicMoment_Estimates_MellinSmooth`, `CubicMoment_Estimates_MellinWeights`, `CubicMoment_Estimates_PoissonProfileBudget`, `CubicMoment_Estimates_PolynomialMeanValue`, `CubicMoment_Estimates_PrimeDetectorCutoff`, `CubicMoment_Estimates_RieszHeatKernel`, `CubicMoment_Estimates_SemiprimeGaussTailAngularWeights`, `CubicMoment_Estimates_SemiprimePartition`, `CubicMoment_Estimates_SemiprimeSmoothWeights`, `CubicMoment_Estimates_SharpHeightIntegral`, `CubicMoment_Estimates_SharpHeightPartition`, `CubicMoment_Estimates_ShrinkingProfile`, `CubicMoment_Estimates_SmoothNormPartition`, `CubicMoment_Estimates_SmoothPartitionCount`, `CubicMoment_Estimates_SmoothShortContinuity`, `CubicMoment_Estimates_SmoothTuplePartition`, `CubicMoment_Estimates_SparseEnvelopeWeights`, `CubicMoment_Estimates_SparseStoppingLabels`, `CubicMoment_Estimates_ThetaHeatKernelBound`, `CubicMoment_Estimates_ThetaMellinSplit`, `CubicMoment_Estimates_WideGramMellin`, `CubicMoment_Theta_CubicThetaAngularExponential`, `CubicMoment_Theta_CubicThetaArithmeticEquation`, `CubicMoment_Theta_CubicThetaCompactCoreCover`, `CubicMoment_Theta_CubicThetaCompactDensityBound`, `CubicMoment_Theta_CubicThetaCompactDomination`, `CubicMoment_Theta_CubicThetaCompactPerturbation`, `CubicMoment_Theta_CubicThetaCoordinateIntegrationByParts`, `CubicMoment_Theta_CubicThetaCoordinatePairing`, `CubicMoment_Theta_CubicThetaCoordinateRegularity`, `CubicMoment_Theta_CubicThetaCuspCutoff`, `CubicMoment_Theta_CubicThetaCuspCutoffBounds`, `CubicMoment_Theta_CubicThetaCuspHardy`, `CubicMoment_Theta_CubicThetaCuspStrip`, `CubicMoment_Theta_CubicThetaDualHeatBounds`, `CubicMoment_Theta_CubicThetaEisensteinBounds`, `CubicMoment_Theta_CubicThetaEisensteinTorus`, `CubicMoment_Theta_CubicThetaEnergySimplePole`, `CubicMoment_Theta_CubicThetaEuclideanSmoothing`, `CubicMoment_Theta_CubicThetaFiniteInflation`, `CubicMoment_Theta_CubicThetaFinitePoleInverse`, `CubicMoment_Theta_CubicThetaForcingBoundary`, `CubicMoment_Theta_CubicThetaForcingSmooth`, `CubicMoment_Theta_CubicThetaFourierNonzero`, `CubicMoment_Theta_CubicThetaGlobalMeromorphic`, `CubicMoment_Theta_CubicThetaGlobalSpectralResolvent`, `CubicMoment_Theta_CubicThetaGridJets`, `CubicMoment_Theta_CubicThetaGridLocalJets`, `CubicMoment_Theta_CubicThetaHeightEquation`, `CubicMoment_Theta_CubicThetaHermitianMetric`, `CubicMoment_Theta_CubicThetaHyperbolicChain`, `CubicMoment_Theta_CubicThetaHyperbolicMeasure`, `CubicMoment_Theta_CubicThetaHyperbolicOperator`, `CubicMoment_Theta_CubicThetaIncomingForcing`, `CubicMoment_Theta_CubicThetaIncomingSmooth`, `CubicMoment_Theta_CubicThetaJacobian`, `CubicMoment_Theta_CubicThetaKernelAnalytic`, `CubicMoment_Theta_CubicThetaKernelEquation`, `CubicMoment_Theta_CubicThetaKernelFirstBounds`, `CubicMoment_Theta_CubicThetaKernelRatios`, `CubicMoment_Theta_CubicThetaKernelSecondBounds`, `CubicMoment_Theta_CubicThetaLaplaceSum`, `CubicMoment_Theta_CubicThetaLocalOperator`, `CubicMoment_Theta_CubicThetaLogHeight`, `CubicMoment_Theta_CubicThetaLogMeasure`, `CubicMoment_Theta_CubicThetaLongWindow`, `CubicMoment_Theta_CubicThetaMeromorphicApply`, `CubicMoment_Theta_CubicThetaMeromorphicLinear`, `CubicMoment_Theta_CubicThetaMobiusGenerators`, `CubicMoment_Theta_CubicThetaNonzeroHeat`, `CubicMoment_Theta_CubicThetaNormalizedJets`, `CubicMoment_Theta_CubicThetaPoincareSmooth`, `CubicMoment_Theta_CubicThetaPositiveContraction`, `CubicMoment_Theta_CubicThetaPositiveLocalization`, `CubicMoment_Theta_CubicThetaPositiveStarProduct`, `CubicMoment_Theta_CubicThetaQuadraticDerivatives`, `CubicMoment_Theta_CubicThetaRadialHeckeWeight`, `CubicMoment_Theta_CubicThetaRadialMeanIntegral`, `CubicMoment_Theta_CubicThetaRadialMellin`, `CubicMoment_Theta_CubicThetaRadialTent`, `CubicMoment_Theta_CubicThetaRadialWeightScaling`, `CubicMoment_Theta_CubicThetaResidueCount`, `CubicMoment_Theta_CubicThetaRowHeightEquation`, `CubicMoment_Theta_CubicThetaScalarCuspEnergy`, `CubicMoment_Theta_CubicThetaScatteringMeromorphic`, `CubicMoment_Theta_CubicThetaSecondChain`, `CubicMoment_Theta_CubicThetaSiegelReduction`, `CubicMoment_Theta_CubicThetaSmoothingSupport`, `CubicMoment_Theta_CubicThetaSpatialDerivativeBound`, `CubicMoment_Theta_CubicThetaSpectralSimplePole`, `CubicMoment_Theta_CubicThetaTorusCellIntegral`, `CubicMoment_Theta_CubicThetaTwiceDifferentiation`, `CubicMoment_Theta_CubicThetaVerticalDerivatives`, `CubicMoment_Theta_CubicThetaVerticalProduct`, `CubicMoment_Theta_CubicThetaWeightedTest`, `CubicMoment_Theta_CubicThetaWindowProfile`, `CubicMoment_Theta_CubicThetaZeroFourier`, `CubicMoment_Theta_CubicThetaZeroObservable`, `CubicMoment_Theta_CubicThetaZeroWindow`, `CubicMoment_Transform_MetaplecticMellinShift`, `CubicMoment_Transform_MetaplecticTwistedTransform`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A005` and `OAIQ096A006`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ096_CM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_Periodization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Schwartz lattice periodization and coordinate Poisson summation. -/

section

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology

namespace CubicPoisson

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma schwartz_summable_lattice (L : Submodule ℤ E) [DiscreteTopology L]
    (f : 𝓢(E, ℂ)) : Summable (fun z : L => f z) := by
  let k := Module.finrank ℤ L + 1
  obtain ⟨C, hC, hbound⟩ := f.decay k 0
  have hsum := (ZLattice.summable_norm_pow_inv L k (by dsimp [k]; omega)).mul_left C
  apply Summable.of_norm_bounded_eventually hsum
  filter_upwards [Filter.eventually_cofinite_ne (0 : L)] with z hz
  have hz' : 0 < ‖(z : E)‖ := norm_pos_iff.mpr (by simpa using hz)
  have hb : ‖(z : E)‖ ^ k * ‖f z‖ ≤ C := by simpa using hbound z
  rw [inv_pow]
  change ‖f z‖ ≤ C * (‖(z : E)‖ ^ k)⁻¹
  exact (le_mul_inv_iff₀ (pow_pos hz' k)).mpr (by simpa [mul_comm] using hb)

lemma schwartz_locally_summable_lattice (L : Submodule ℤ E) [DiscreteTopology L]
    (f : 𝓢(E, ℂ)) (K : TopologicalSpace.Compacts E) :
    Summable (fun z : L =>
      ‖((⟨f, f.continuous⟩ : C(E, ℂ)).comp
        (ContinuousMap.addRight (z : E))).restrict K‖) := by
  let k := Module.finrank ℤ L + 1
  obtain ⟨C, hC, hbound⟩ := f.decay k 0
  obtain ⟨R₀, hR₀⟩ := K.isCompact.isBounded.subset_closedBall (0 : E)
  let R := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hKR : ∀ x ∈ K, ‖x‖ ≤ R := by
    intro x hx
    have h : ‖x‖ ≤ R₀ := by simpa using hR₀ hx
    exact h.trans (le_max_left R₀ 1)
  have hclosed : IsClosed (L : Set E) :=
    @AddSubgroup.isClosed_of_discrete _ _ _ _ _ L.toAddSubgroup
      (inferInstanceAs (DiscreteTopology L))
  have hfin : {z : L | ‖(z : E)‖ ≤ 2 * R}.Finite := by
    have h := (Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      (Metric.isBounded_closedBall (x := (0 : E)) (r := 2 * R)) hclosed).preimage_embedding
        (Function.Embedding.subtype (fun x : E => x ∈ L))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp [Metric.mem_closedBall]
  have hsum := (ZLattice.summable_norm_pow_inv L k (by dsimp [k]; omega)).mul_left (2 ^ k * C)
  apply Summable.of_norm_bounded_eventually hsum
  filter_upwards [hfin.eventually_cofinite_notMem] with z hz
  have hz : 2 * R < ‖(z : E)‖ := by simpa only [Set.mem_ofPred_eq, not_le] using hz
  rw [norm_norm]
  refine (ContinuousMap.norm_le _ (by positivity)).mpr ?_
  intro x
  have hxR := hKR x.1 x.2
  have hzpos : 0 < ‖(z : E)‖ := by linarith
  have hxlow : ‖(z : E)‖ / 2 ≤ ‖x.1 + (z : E)‖ := by
    have hn := norm_sub_norm_le (z : E) (-x.1)
    simp only [norm_neg, sub_neg_eq_add] at hn
    rw [add_comm (z : E) x.1] at hn
    linarith
  have hxpos : 0 < ‖x.1 + (z : E)‖ := lt_of_lt_of_le (by positivity) hxlow
  have hb : ‖x.1 + (z : E)‖ ^ k * ‖f (x.1 + (z : E))‖ ≤ C :=
    by simpa using hbound (x.1 + (z : E))
  change ‖f (x.1 + (z : E))‖ ≤ 2 ^ k * C * ‖(z : E)‖⁻¹ ^ k
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ ‖(z : E)‖ / 2) hxlow k
  have hb' : (‖(z : E)‖ / 2) ^ k * ‖f (x.1 + (z : E))‖ ≤ C :=
    (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans hb
  rw [div_pow] at hb'
  rw [inv_pow]
  apply (le_mul_inv_iff₀ (pow_pos hzpos k)).mpr
  calc
    _ = (‖(z : E)‖ ^ k / 2 ^ k * ‖f (x.1 + (z : E))‖) * 2 ^ k := by
      field_simp
    _ ≤ C * 2 ^ k := mul_le_mul_of_nonneg_right hb' (by positivity)
    _ = _ := by ring

def periodization (L : Submodule ℤ E) (f : 𝓢(E, ℂ)) : C(E, ℂ) :=
  ∑' z : L, (⟨f, f.continuous⟩ : C(E, ℂ)).comp (ContinuousMap.addRight (z : E))

lemma periodization_apply (L : Submodule ℤ E) [DiscreteTopology L]
    (f : 𝓢(E, ℂ)) (x : E) :
    periodization L f x = ∑' z : L, f (x + (z : E)) := by
  have hs := ContinuousMap.summable_of_locally_summable_norm
    (schwartz_locally_summable_lattice L f)
  exact (ContinuousMap.tsum_apply hs x).symm

lemma periodization_add (L : Submodule ℤ E) [DiscreteTopology L]
    (f : 𝓢(E, ℂ)) (x : E) (z : L) :
    periodization L f (x + (z : E)) = periodization L f x := by
  simp only [periodization_apply]
  simpa [add_assoc] using (Equiv.addLeft z).tsum_eq (fun w : L => f (x + (w : E)))

section Coordinates
variable {d : Type*} [Fintype d] [DecidableEq d]

abbrev stdLattice (d : Type*) [Fintype d] [DecidableEq d] : Submodule ℤ (d → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ d))

def torusProjection (x : d → ℝ) : UnitAddTorus d := fun i => (x i : UnitAddCircle)

omit [Fintype d] [DecidableEq d] in
lemma torusProjection_openQuotient : IsOpenQuotientMap (torusProjection (d := d)) :=
  IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)

lemma mem_stdLattice_iff (x : d → ℝ) :
    x ∈ stdLattice d ↔ ∀ i, ∃ n : ℤ, (n : ℝ) = x i := by
  simpa using (Pi.basisFun ℝ d).mem_span_iff_repr_mem ℤ x

lemma torusProjection_eq_iff (x y : d → ℝ) :
    torusProjection x = torusProjection y ↔ x - y ∈ stdLattice d := by
  rw [mem_stdLattice_iff, funext_iff]
  change (∀ i, (x i : UnitAddCircle) = (y i : UnitAddCircle)) ↔ _
  apply forall_congr'
  intro i
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  simp only [zsmul_eq_mul, mul_one, Pi.sub_apply]

def torusRepresentative (x : UnitAddTorus d) : d → ℝ :=
  fun i => (AddCircle.equivIoc 1 0 (x i)).1

omit [Fintype d] [DecidableEq d] in
lemma torusProjection_representative (x : UnitAddTorus d) :
    torusProjection (torusRepresentative x) = x := by
  ext i
  exact AddCircle.coe_equivIoc

lemma periodization_eq_of_projection_eq (f : 𝓢(d → ℝ, ℂ)) (x y : d → ℝ)
    (h : torusProjection x = torusProjection y) :
    periodization (stdLattice d) f x = periodization (stdLattice d) f y := by
  have hz := (torusProjection_eq_iff x y).mp h
  simpa using periodization_add (stdLattice d) f y ⟨x - y, hz⟩

def torusPeriodization (f : 𝓢(d → ℝ, ℂ)) : C(UnitAddTorus d, ℂ) where
  toFun x := periodization (stdLattice d) f (torusRepresentative x)
  continuous_toFun := by
    apply torusProjection_openQuotient.isQuotientMap.continuous_iff.mpr
    have he : (fun x : d → ℝ =>
        periodization (stdLattice d) f (torusRepresentative (torusProjection x))) =
        periodization (stdLattice d) f := by
      funext x
      exact periodization_eq_of_projection_eq f _ _ (torusProjection_representative _)
    simpa only [Function.comp_def, he] using (periodization (stdLattice d) f).continuous

lemma torusPeriodization_projection (f : 𝓢(d → ℝ, ℂ)) (x : d → ℝ) :
    torusPeriodization f (torusProjection x) = periodization (stdLattice d) f x :=
  periodization_eq_of_projection_eq f _ _ (torusProjection_representative _)

lemma torusProjection_lattice_add (z : stdLattice d) (x : d → ℝ) :
    torusProjection ((z : d → ℝ) + x) = torusProjection x := by
  rw [torusProjection_eq_iff]
  simp only [add_sub_cancel_right, SetLike.coe_mem]

omit [DecidableEq d] in
lemma stdFundamental_restrict :
    (volume : Measure (d → ℝ)).restrict (ZSpan.fundamentalDomain (Pi.basisFun ℝ d)) =
    volume.restrict {x : d → ℝ | ∀ i, x i ∈ Ioc 0 1} := by
  have hco : ZSpan.fundamentalDomain (Pi.basisFun ℝ d) =
      Set.univ.pi (fun _ : d => Ico (0 : ℝ) 1) := by
    ext x
    simp [ZSpan.fundamentalDomain, Set.mem_pi]
  have hoc : {x : d → ℝ | ∀ i, x i ∈ Ioc 0 1} =
      Set.univ.pi (fun _ : d => Ioc (0 : ℝ) 1) := by
    ext x
    simp [Set.mem_pi]
  rw [hco, hoc, volume_pi, Measure.restrict_pi_pi, Measure.restrict_pi_pi]
  congr 1
  funext i
  exact restrict_Ico_eq_restrict_Ioc

omit [DecidableEq d] in
lemma mFourier_point_norm (n : d → ℤ) (x : UnitAddTorus d) :
    ‖UnitAddTorus.mFourier n x‖ = 1 := by
  simp [UnitAddTorus.mFourier, fourier_apply, Circle.norm_coe]

lemma torusPeriodization_coefficient (f : 𝓢(d → ℝ, ℂ)) (n : d → ℤ) :
    UnitAddTorus.mFourierCoeff (torusPeriodization f) n =
      ∫ x : d → ℝ, UnitAddTorus.mFourier (-n) (torusProjection x) * f x := by
  let : VAddInvariantMeasure (stdLattice d) (d → ℝ) volume :=
    inferInstanceAs (VAddInvariantMeasure (stdLattice d).toAddSubgroup (d → ℝ) volume)
  let g : (d → ℝ) → ℂ := fun x => UnitAddTorus.mFourier (-n) (torusProjection x) * f x
  have hc : Continuous (fun x : d → ℝ => UnitAddTorus.mFourier (-n) (torusProjection x)) :=
    (UnitAddTorus.mFourier (-n)).continuous.comp torusProjection_openQuotient.continuous
  have hg : Integrable g := f.integrable.bdd_mul hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => le_of_eq (mFourier_point_norm (-n) (torusProjection x))))
  have hgc : Continuous g := hc.mul f.continuous
  have hdom := ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ d) (volume : Measure (d → ℝ))
  have hseries : (∑' z : stdLattice d, ∫⁻ x in ZSpan.fundamentalDomain (Pi.basisFun ℝ d),
      ‖g ((z : d → ℝ) + x)‖ₑ) ≠ ⊤ := by
    have hs := hdom.lintegral_eq_tsum'' (fun x => ‖g x‖ₑ)
    change (∫⁻ x : d → ℝ, ‖g x‖ₑ) =
      (∑' z : stdLattice d, ∫⁻ x in ZSpan.fundamentalDomain (Pi.basisFun ℝ d),
        ‖g ((z : d → ℝ) + x)‖ₑ) at hs
    rw [← hs]
    exact (hasFiniteIntegral_iff_enorm.mp hg.hasFiniteIntegral).ne
  calc
    UnitAddTorus.mFourierCoeff (torusPeriodization f) n =
        ∫ x in {x : d → ℝ | ∀ i, x i ∈ Ioc 0 1},
          UnitAddTorus.mFourier (-n) (torusProjection x) *
            periodization (stdLattice d) f x := by
      rw [UnitAddTorus.mFourierCoeff_eq_integral _ _ (0 : d → ℝ)]
      simp only [Pi.zero_apply, zero_add, smul_eq_mul]
      apply integral_congr_ae
      filter_upwards with x
      change _ * torusPeriodization f (torusProjection x) = _
      rw [torusPeriodization_projection]
      rfl
    _ = ∫ x in ZSpan.fundamentalDomain (Pi.basisFun ℝ d),
          UnitAddTorus.mFourier (-n) (torusProjection x) *
            periodization (stdLattice d) f x := by rw [stdFundamental_restrict]
    _ = ∫ x in ZSpan.fundamentalDomain (Pi.basisFun ℝ d),
          ∑' z : stdLattice d, g ((z : d → ℝ) + x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [periodization_apply, ← tsum_mul_left]
      apply tsum_congr
      intro z
      dsimp only [g]
      rw [torusProjection_lattice_add, add_comm (z : d → ℝ) x]
    _ = ∑' z : stdLattice d, ∫ x in ZSpan.fundamentalDomain (Pi.basisFun ℝ d),
          g ((z : d → ℝ) + x) := by
      exact integral_tsum (fun z => (hgc.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
        hseries
    _ = ∫ x : d → ℝ, g x := (hdom.integral_eq_tsum'' g hg).symm

def coordinateFourier (f : 𝓢(d → ℝ, ℂ)) : 𝓢(d → ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : d => ℝ)).symm
    (𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : d => ℝ)) f))

omit [DecidableEq d] in
lemma coordinateFourier_apply (f : 𝓢(d → ℝ, ℂ)) (w : d → ℝ) :
    coordinateFourier f w =
      ∫ x : d → ℝ, (Real.fourierChar (-∑ i, x i * w i) : ℂ) * f x := by
  change (𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : d => ℝ)) f)) (WithLp.toLp 2 w) = _
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  have he := (PiLp.volume_preserving_ofLp d).integral_comp
    (MeasurableEquiv.toLp 2 (d → ℝ)).symm.measurableEmbedding
    (fun x : d → ℝ => (Real.fourierChar (-∑ i, x i * w i) : ℂ) * f x)
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards with x
  simp [PiLp.inner_apply, Circle.smul_def, smul_eq_mul,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, PiLp.coe_continuousLinearEquiv,
    mul_comm]

omit [DecidableEq d] in
lemma mFourier_projection (n : d → ℤ) (x : d → ℝ) :
    UnitAddTorus.mFourier n (torusProjection x) =
      (Real.fourierChar (∑ i, x i * (n i : ℝ)) : ℂ) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, torusProjection,
    fourier_coe_apply, Complex.ofReal_one, div_one, Real.fourierChar_apply,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_sum, Complex.ofReal_intCast]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma torusPeriodization_coefficient_fourier (f : 𝓢(d → ℝ, ℂ)) (n : d → ℤ) :
    UnitAddTorus.mFourierCoeff (torusPeriodization f) n =
      coordinateFourier f (fun i => (n i : ℝ)) := by
  rw [torusPeriodization_coefficient, coordinateFourier_apply]
  apply integral_congr_ae
  filter_upwards with x
  simp only [mFourier_projection, Pi.neg_apply, Int.cast_neg, mul_neg, Finset.sum_neg_distrib]

lemma stdLattice_coordinates (z : stdLattice d) :
    (fun i => ((((Pi.basisFun ℝ d).restrictScalars ℤ).equivFun z i : ℤ) : ℝ)) =
      (z : d → ℝ) := by
  ext i
  exact (Pi.basisFun ℝ d).restrictScalars_repr_apply ℤ z i

lemma schwartz_summable_integerCoordinates (f : 𝓢(d → ℝ, ℂ)) :
    Summable (fun n : d → ℤ => f (fun i => (n i : ℝ))) := by
  apply ((Pi.basisFun ℝ d).restrictScalars ℤ).equivFun.toEquiv.summable_iff.mp
  change Summable (fun z : stdLattice d =>
    f (fun i => ((((Pi.basisFun ℝ d).restrictScalars ℤ).equivFun z i : ℤ) : ℝ)))
  simpa only [stdLattice_coordinates] using schwartz_summable_lattice (stdLattice d) f

lemma torusPeriodization_summable_coefficients (f : 𝓢(d → ℝ, ℂ)) :
    Summable (UnitAddTorus.mFourierCoeff (torusPeriodization f)) := by
  have he : UnitAddTorus.mFourierCoeff (torusPeriodization f) =
      (fun n : d → ℤ => coordinateFourier f (fun i => (n i : ℝ))) := by
    funext n
    exact torusPeriodization_coefficient_fourier f n
  rw [he]
  exact schwartz_summable_integerCoordinates (coordinateFourier f)

lemma periodization_integerCoordinates (f : 𝓢(d → ℝ, ℂ)) (x : d → ℝ) :
    periodization (stdLattice d) f x = ∑' n : d → ℤ, f (x + fun i => (n i : ℝ)) := by
  rw [periodization_apply]
  have he := ((Pi.basisFun ℝ d).restrictScalars ℤ).equivFun.toEquiv.tsum_eq
    (fun n : d → ℤ => f (x + fun i => (n i : ℝ)))
  change (∑' z : stdLattice d,
    f (x + fun i => ((((Pi.basisFun ℝ d).restrictScalars ℤ).equivFun z i : ℤ) : ℝ))) = _ at he
  simpa only [stdLattice_coordinates] using he

theorem poisson_coordinates (f : 𝓢(d → ℝ, ℂ)) (x : d → ℝ) :
    HasSum (fun n : d → ℤ => coordinateFourier f (fun i => (n i : ℝ)) *
      (Real.fourierChar (∑ i, x i * (n i : ℝ)) : ℂ))
      (∑' n : d → ℤ, f (x + fun i => (n i : ℝ))) := by
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
    (torusPeriodization_summable_coefficients f) (torusProjection x)
  simpa only [torusPeriodization_coefficient_fourier, smul_eq_mul, mFourier_projection,
    torusPeriodization_projection, periodization_integerCoordinates, mul_comm] using h

theorem poisson_coordinates_zero (f : 𝓢(d → ℝ, ℂ)) :
    ∑' n : d → ℤ, f (fun i => (n i : ℝ)) =
      ∑' n : d → ℤ, coordinateFourier f (fun i => (n i : ℝ)) := by
  have h := (poisson_coordinates f 0).tsum_eq
  simpa using h.symm

end Coordinates
end CubicPoisson

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_LatticePoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eisenstein real coordinates, measure factors and translated lattice Poisson summation. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology

namespace CubicFirstMoment
open CubicPoisson

def complexMulEquiv (q : ℂ) (hq : q ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  ((LinearEquiv.smulOfNeZero ℂ ℂ q hq).restrictScalars ℝ).toContinuousLinearEquiv

def complexMulMatrix (q : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![q.re, -q.im; q.im, q.re]

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_GramPoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal character Gram kernel and normalized radial Poisson expansion. -/

section

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

noncomputable section
open Filter
open scoped ContDiff

namespace CubicFirstMoment

lemma hasCompactSupport_normProfile {W : ℝ → ℂ} (hW : HasCompactSupport W)
    {Z : ℝ} (hZ : 0 < Z) :
    HasCompactSupport (fun z : ℂ => W (Complex.normSq z / Z)) := by
  have hT := Complex.tendsto_normSq_cocompact_atTop.atTop_div_const hZ
  have hW' : W =ᶠ[cocompact ℝ] 0 := by
    simpa only [coclosedCompact_eq_cocompact] using
      (hasCompactSupport_iff_eventuallyEq.mp hW)
  apply hasCompactSupport_iff_eventuallyEq.mpr
  rw [coclosedCompact_eq_cocompact]
  exact (hW'.filter_mono atTop_le_cocompact).comp_tendsto hT

lemma contDiff_normProfile {W : ℝ → ℂ} (hW : ContDiff ℝ ∞ W) (Z : ℝ) :
    ContDiff ℝ ∞ (fun z : ℂ => W (Complex.normSq z / Z)) := by
  have hr : ContDiff ℝ ∞ (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have hi : ContDiff ℝ ∞ (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  exact hW.comp (((hr.mul hr).add (hi.mul hi)).div_const Z)

end CubicFirstMoment

namespace CubicFirstMoment

def normProfileSchwartz (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (Z : ℝ) (hZ : 0 < Z) : 𝓢(ℂ, ℂ) :=
  (hasCompactSupport_normProfile hW hZ).toSchwartzMap (contDiff_normProfile hW' Z)

@[simp] lemma normProfileSchwartz_apply (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (Z : ℝ) (hZ : 0 < Z) (z : ℂ) :
    normProfileSchwartz W hW hW' Z hZ z = W (Complex.normSq z / Z) := rfl

end CubicFirstMoment

end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_MellinDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separated radial Mellin kernels with uniform rapid decay. -/

section

noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

def gramLogBump : ContDiffBump (0 : ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def gramMellinPhase (t x : ℝ) : ℂ :=
  (Real.fourierChar (t * Real.log x) : ℂ)

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def gramExp (u : ℝ) : ℂ := (Real.exp (u/2) : ℂ)

lemma gramExp_contDiff : ContDiff ℝ ∞ gramExp :=
  Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_id.div_const 2))

def annularLogSchwartz (F : 𝓢(ℂ, ℂ)) (c : ℝ) : 𝓢(ℝ, ℂ) :=
  (gramLogBump.hasCompactSupport.smul_right (f' := fun u => F (c • gramExp u))).toSchwartzMap
    (gramLogBump.contDiff.smul ((F.smooth ⊤).comp (gramExp_contDiff.const_smul c)))

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubeEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric decay, cube frequency dyads and numerical block inequalities. -/

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubeDyadTriples (j : ℕ) : Finset (ℕ×ℕ×ℕ) :=
  ((Finset.range (j+2)).product ((Finset.range (j+2)).product (Finset.range (j+2)))).filter
    (fun z => z.1+2*z.2.1+3*z.2.2 ≤ j+1)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLatticeProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual angular annulus is a smooth compactly supported plane
function. Its area integral is zero in every nonzero integral mode. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff SchwartzMap Topology
namespace CubicFirstMoment

def angularPlanePhase (ℓ : ℤ) (z : ℂ) : ℂ := (z/(‖z‖:ℂ))^ℓ

def angularAnnulus (ℓ : ℤ) (W : ℝ → ℂ) (z : ℂ) : ℂ :=
  angularPlanePhase ℓ z*W (Complex.normSq z)

lemma angularPlanePhase_contDiffAt (ℓ : ℤ) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (angularPlanePhase ℓ) z := by
  have hn : (‖z‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hc : ContDiffAt ℝ ∞ (fun w : ℂ => (‖w‖:ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (contDiffAt_norm ℂ hz)
  have hq : ContDiffAt ℝ ∞ (fun w : ℂ => w/(‖w‖:ℂ)) z := by
    simpa only [div_eq_mul_inv] using! (contDiffAt_id (x := z)).mul (hc.inv hn)
  cases ℓ with
  | ofNat n => simpa only [angularPlanePhase,zpow_natCast] using! hq.pow n
  | negSucc n =>
      have hp := (hq.pow (n+1)).inv (pow_ne_zero _ (div_ne_zero hz hn))
      simpa only [angularPlanePhase,zpow_negSucc] using! hp

lemma angularAnnulus_compact (ℓ : ℤ) {W : ℝ → ℂ} (hW : HasCompactSupport W) :
    HasCompactSupport (angularAnnulus ℓ W) := by
  have hn := hasCompactSupport_normProfile hW (show (0:ℝ) < 1 by norm_num)
  simp only [div_one] at hn
  exact hn.mul_left

lemma angularAnnulus_smooth (ℓ : ℤ) {W : ℝ → ℂ}
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (angularAnnulus ℓ W) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    have hzero : (0:ℝ) ∉ tsupport W := fun hh => (lt_irrefl (0:ℝ)) (hpos hh)
    have ht : Tendsto (fun z : ℂ => Complex.normSq z) (𝓝 0) (𝓝 0) := by
      simpa only [map_zero] using Complex.continuous_normSq.tendsto (0:ℂ)
    have he := (notMem_tsupport_iff_eventuallyEq.mp hzero).comp_tendsto ht
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [he] with w hw
    change W (Complex.normSq w) = 0 at hw
    simp only [angularAnnulus,hw,mul_zero]
  · have hw : ContDiff ℝ ∞ (fun w : ℂ => W (Complex.normSq w)) := by
      simpa only [div_one] using contDiff_normProfile hsm 1
    exact (angularPlanePhase_contDiffAt ℓ hz).mul hw.contDiffAt

def angularAnnulusSchwartz (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) : 𝓢(ℂ,ℂ) :=
  (angularAnnulus_compact ℓ hW).toSchwartzMap (angularAnnulus_smooth ℓ hpos hsm)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLogCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed smooth cutoffs and a proper smooth logarithmic extension.
They transfer the common log-derivative bounds to the actual annuli. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology SchwartzMap
namespace CubicFirstMoment

def angularPositiveCutoff (a b x : ℝ) : ℝ :=
  Real.smoothTransition ((x-a/2)/(a/2))*Real.smoothTransition ((2*b-x)/b)

lemma angularPositiveCutoff_smooth (a b : ℝ) :
    ContDiff ℝ ∞ (angularPositiveCutoff a b) := by
  unfold angularPositiveCutoff
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

lemma angularPositiveCutoff_one {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : a ≤ x ∧ x ≤ b) : angularPositiveCutoff a b x = 1 := by
  rw [angularPositiveCutoff,
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ (by positivity : 0 < a/2)).mpr (by linarith)),
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ hb).mpr (by linarith))]
  exact one_mul _

lemma angularPositiveCutoff_tsupport {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    tsupport (angularPositiveCutoff a b) ⊆ Icc (a/2) (2*b) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra hn
    have hzero : Real.smoothTransition ((x-a/2)/(a/2)) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
    exact hx (by simp only [angularPositiveCutoff,hzero,zero_mul])
  · by_contra hn
    have hzero : Real.smoothTransition ((2*b-x)/b) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hb.le)
    exact hx (by simp only [angularPositiveCutoff,hzero,mul_zero])

lemma angularPositiveCutoff_compact {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasCompactSupport (angularPositiveCutoff a b) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (angularPositiveCutoff_tsupport ha hb)

lemma angularPositiveCutoff_positive {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    tsupport (angularPositiveCutoff a b) ⊆ Ioi 0 := by
  intro x hx
  exact lt_of_lt_of_le (by linarith) (angularPositiveCutoff_tsupport ha hb hx).1

def angularLogPerturbation (a b x : ℝ) : ℝ :=
  angularPositiveCutoff a b x*(-Real.log x-x)

lemma angularLogPerturbation_smooth {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ContDiff ℝ ∞ (angularLogPerturbation a b) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hn : (0:ℝ) ∉ tsupport (angularPositiveCutoff a b) :=
      fun hh => (lt_irrefl (0:ℝ)) (angularPositiveCutoff_positive ha hb hh)
    have he := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with x hx
    change angularPositiveCutoff a b x = 0 at hx
    simp only [angularLogPerturbation,hx,zero_mul]
  · exact (angularPositiveCutoff_smooth a b).contDiffAt.mul
      ((Real.contDiffAt_log.mpr hx).neg.sub contDiffAt_id)

lemma angularLogPerturbation_compact {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasCompactSupport (angularLogPerturbation a b) :=
  (angularPositiveCutoff_compact ha hb).mul_right

def angularLogExtension (a b x : ℝ) : ℝ := x+angularLogPerturbation a b x

lemma angularLogExtension_temperate {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Function.HasTemperateGrowth (angularLogExtension a b) := by
  have ht := (angularLogPerturbation_compact ha hb).hasTemperateGrowth
    (angularLogPerturbation_smooth ha hb)
  exact (ContinuousLinearMap.id ℝ ℝ).hasTemperateGrowth.add ht

lemma angularLogExtension_growth {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C*(1+‖angularLogExtension a b x‖)^k := by
  obtain ⟨M,hM⟩ := (angularLogPerturbation_smooth ha hb).continuous.bounded_above_of_compact_support
    (angularLogPerturbation_compact ha hb)
  refine ⟨1,max M 0+1,?_⟩
  intro x
  have hsmall := hM x
  have htri : ‖x‖ ≤ ‖angularLogExtension a b x‖+‖angularLogPerturbation a b x‖ := by
    have he : x = angularLogExtension a b x-angularLogPerturbation a b x := by
      simp only [angularLogExtension,add_sub_cancel_right]
    calc
      _ = ‖angularLogExtension a b x-angularLogPerturbation a b x‖ := congrArg (fun t : ℝ => ‖t‖) he
      _ ≤ _ := norm_sub_le _ _
  have hm : M ≤ max M 0 := le_max_left _ _
  rw [pow_one]
  nlinarith [_root_.norm_nonneg (angularLogExtension a b x),le_max_right M 0]

lemma angularLogExtension_eq_log {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : a ≤ x ∧ x ≤ b) : angularLogExtension a b x = -Real.log x := by
  rw [angularLogExtension,angularLogPerturbation,angularPositiveCutoff_one ha hb hx,one_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth weights and Mellin twists

The derivative cost below explains why the unweighted published Hecke
estimate continues to give any prescribed logarithmic saving after a
fixed-logarithmic-height norm twist. It is used with `weighted_cubic_prime_bound`.
-/

noncomputable section

namespace CubicFirstMoment

def mellinPhase (u x : ℝ) : ℂ := Complex.exp ((u * Real.log x : ℝ) * Complex.I)

@[simp] theorem mellinPhase_norm (u x : ℝ) : ‖mellinPhase u x‖ = 1 := by
  simp [mellinPhase, Complex.norm_exp]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The sharp fixed-angular prime model

The input is the explicit published Hecke prime estimate, not a weighted
prime-model asymptotic.  Partial summation with `x^(-1/6)/log x` derives
the required little-oh at the sharp first-moment scale.
-/

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology

namespace CubicFirstMoment

def angularAbelWeight (X : ℝ) : ℝ := X ^ (-1 / 6 : ℝ) / Real.log X

def angularAbelDerivative (X : ℝ) : ℝ :=
  -(X ^ (-7 / 6 : ℝ) / Real.log X) * (1 / 6 + 1 / Real.log X)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinContour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contour shifting for the Mellin integrals in the smooth Hecke sum.
The horizontal edges are kept explicit until a uniform decay bound is
available; no functional equation or dual-sum estimate is assumed here. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace CubicFirstMoment

def closedVerticalStrip (a b : ℝ) : Set ℂ :=
  {z | a ≤ z.re ∧ z.re ≤ b}

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic properties of the actual compactly supported smooth norm
weights. Passing to logarithmic coordinates realizes every vertical
Mellin line as a Schwartz Fourier transform. -/

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology SchwartzMap ContDiff FourierTransform

namespace CubicFirstMoment

lemma logPullback_compact (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) :
    HasCompactSupport (fun u : ℝ => W (Real.exp (-u))) := by
  have hc : IsCompact ((fun x : ℝ => -Real.log x) '' tsupport W) :=
    hW.isCompact.image_of_continuousOn
      (Real.continuousOn_log.neg.mono (fun x hx => ne_of_gt (hpos hx)))
  apply HasCompactSupport.of_support_subset_isCompact hc
  intro u hu
  refine ⟨Real.exp (-u), subset_tsupport W hu, ?_⟩
  simp

def mellinLogSchwartz (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ) : 𝓢(ℝ,ℂ) :=
  ((logPullback_compact W hW hpos).smul_left
    (f := fun u : ℝ => Real.exp (-σ*u))).toSchwartzMap
    ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).smul
      (hsm.comp (Real.contDiff_exp.comp contDiff_id.neg)))

lemma mellinLogSchwartz_apply (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ u : ℝ) :
    mellinLogSchwartz W hW hpos hsm σ u = Real.exp (-σ*u) • W (Real.exp (-u)) := rfl

lemma smooth_mellin_power_bounds (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (a b : ℝ) :
    W =O[atTop] (fun x : ℝ => x^(-a)) ∧
      W =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x^(-b)) := by
  have ht : W =ᶠ[atTop] 0 := by
    have h := hasCompactSupport_iff_eventuallyEq.mp hW
    rw [Filter.coclosedCompact_eq_cocompact] at h
    exact h.filter_mono atTop_le_cocompact
  have h0 : (0 : ℝ) ∉ tsupport W := fun h =>
    (lt_irrefl (0 : ℝ)) (Set.mem_Ioi.mp (hpos h))
  have hb : W =ᶠ[𝓝[>] (0 : ℝ)] 0 :=
    (notMem_tsupport_iff_eventuallyEq.mp h0).filter_mono nhdsWithin_le_nhds
  exact ⟨(isBigO_zero _ _).congr' ht.symm Filter.EventuallyEq.rfl,
    (isBigO_zero _ _).congr' hb.symm Filter.EventuallyEq.rfl⟩

theorem smooth_mellin_convergent (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hc : Continuous W) (s : ℂ) :
    MellinConvergent W s := by
  obtain ⟨ht,hb⟩ := smooth_mellin_power_bounds W hW hpos (s.re+1) (s.re-1)
  exact mellinConvergent_of_isBigO_rpow (hc.locallyIntegrable.locallyIntegrableOn _)
    ht (by linarith) hb (by linarith)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute sum-integral interchange for the full norm Dirichlet series
in Mellin inversion. No smooth-duality formula is an input. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

def normDirichletSeries {ι : Type*} (a : ι → ℂ) (N : ι → ℝ) (s : ℂ) : ℂ :=
  ∑' i, a i * (N i : ℂ)^(-s)

lemma mellin_scale_cpow {x Z : ℝ} (hx : 0 < x) (hZ : 0 < Z) (s : ℂ) :
    ((x/Z : ℝ) : ℂ)^(-s) = (Z:ℂ)^s * (x:ℂ)^(-s) := by
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg hx.le hZ.le,
    div_eq_mul_inv,Complex.cpow_neg (Z:ℂ) s,inv_inv,mul_comm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeDualContour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moving finite dual polynomials back to the symmetry line. The only
new conditional analytic input is the bounded-strip polynomial estimate
for the classical Gamma quotient, a specialization of NIST DLMF 5.11.9
(uniformly for bounded real parts). The half-integer-line estimate needed
for the discarded tail was proved directly in GammaLeftLine. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def finiteNormDirichlet {ι : Type*} (S : Finset ι) (a : ι → ℂ)
    (N : ι → ℝ) (s : ℂ) : ℂ := ∑ i ∈ S, a i*(N i:ℂ)^(-s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTwistedTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The norm twist in the original Voronoi formula is exactly the
translated Mellin variable in the shifted transform. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma phaseWeight_compact {W : ℝ → ℂ} (hW : HasCompactSupport W) (t : ℝ) :
    HasCompactSupport (fun x => W x*mellinPhase t x) := hW.mul_right

lemma phaseWeight_positive {W : ℝ → ℂ} (hpos : tsupport W ⊆ Ioi 0) (t : ℝ) :
    tsupport (fun x => W x*mellinPhase t x) ⊆ Ioi 0 :=
  tsupport_mul_subset_left.trans hpos

lemma phaseWeight_smooth {W : ℝ → ℂ} (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (t : ℝ) :
    ContDiff ℝ ∞ (fun x => W x*mellinPhase t x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hz : (0:ℝ) ∉ tsupport W := fun h => (lt_irrefl (0:ℝ)) (hpos h)
    have he := notMem_tsupport_iff_eventuallyEq.mp hz
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    change W y = 0 at hy
    simp only [hy,zero_mul]
  · have hl : ContDiffAt ℝ ∞ (fun y : ℝ => t*Real.log y) x :=
      contDiffAt_const.mul (Real.contDiffAt_log.mpr hx)
    have hc : ContDiffAt ℝ ∞ (fun y : ℝ => ((t*Real.log y:ℝ):ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hl
    exact hsm.contDiffAt.mul (hc.mul contDiffAt_const).cexp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularWeightOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed continuous operator from logarithmic test functions to plane
annuli. It makes the angular lattice bounds uniform over the given weights. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology SchwartzMap
namespace CubicFirstMoment

def angularComplexCutoff (a b : ℝ) (x : ℝ) : ℂ := angularPositiveCutoff a b x

lemma angularNormSq_temperate : Function.HasTemperateGrowth Complex.normSq := by
  have he : (Complex.normSq : ℂ → ℝ) = fun z => ‖z‖^2 :=
    funext Complex.normSq_eq_norm_sq
  rw [he]
  exact Function.hasTemperateGrowth_norm_sq ℂ

lemma angularNormSq_growth :
    ∃ (k : ℕ) (C : ℝ), ∀ z : ℂ, ‖z‖ ≤ C*(1+‖Complex.normSq z‖)^k := by
  refine ⟨1,1,?_⟩
  intro z
  rw [pow_one,one_mul,Real.norm_eq_abs,abs_of_nonneg (Complex.normSq_nonneg z),
    Complex.normSq_eq_norm_sq]
  nlinarith [sq_nonneg (‖z‖-1)]

def angularWeightOperator (ℓ : ℤ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℂ,ℂ) :=
  ((SchwartzMap.smulLeftCLM ℂ (angularAnnulus ℓ (angularComplexCutoff a b))).restrictScalars ℝ).comp
    ((SchwartzMap.compCLM ℝ angularNormSq_temperate angularNormSq_growth).comp
      (SchwartzMap.compCLM ℝ (angularLogExtension_temperate (by positivity : 0 < a/2)
        (by positivity : 0 < 2*b)) (angularLogExtension_growth (by positivity : 0 < a/2)
        (by positivity : 0 < 2*b))))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PolynomialMeanValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ordinary mean values after collecting Eisenstein norms

The input `MontgomeryVaughanBound` is the ordinary Dirichlet-polynomial
mean-square theorem of Montgomery--Vaughan, *Hilbert's inequality*,
J. London Math. Soc. (2) 8 (1974), Corollary 3, p. 75, equation (1.11),
in the form explicitly recorded
in the manuscript as `eq:ordinary-mean-value`.

The deductions below collect the actual Eisenstein norms, record their
multiplicity cost, and preserve an arbitrary fixed angular weight and
an arbitrary translated height. These are the ordinary mean-value steps
in `eq:dispersion-height-small` and `eq:angular-completed-height`.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace CubicFirstMoment

/-- Ordinary Dirichlet polynomial, with positive integer frequencies. -/
def integerNormPolynomial (Z : ℕ) (v : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 Z, v n * mellinPhase t (n : ℝ)

/-- Precise published input: the constant is independent of the interval,
length, coefficients, and any later translation of the height. -/
def MontgomeryVaughanBound (C : ℝ) : Prop :=
  ∀ (Z : ℕ) (v : ℕ → ℂ) (a b : ℝ), a ≤ b →
    (∫ t in a..b, ‖integerNormPolynomial Z v t‖ ^ 2) ≤
      C * (b - a + Z) * ∑ n ∈ Finset.Icc 1 Z, ‖v n‖ ^ 2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CompactParameterWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact smooth parameter family inherits uniform logarithmic
weight estimates from its joint derivatives. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace CubicFirstMoment

lemma norm_iteratedFDeriv_slice_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : E × ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (p : E) (u : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun v => F (p,v)) u‖ ≤
      ‖iteratedFDeriv ℝ n F (p,u)‖ := by
  let G : E × ℝ → ℂ := fun z => F ((p,0)+z)
  have hG : ContDiff ℝ ∞ G := hF.comp (contDiff_const.add contDiff_id)
  have he : (fun v => F (p,v)) = G ∘ ContinuousLinearMap.inr ℝ E ℝ := by
    ext v
    simp [G]
  rw [he,(ContinuousLinearMap.inr ℝ E ℝ).iteratedFDeriv_comp_right hG u (by exact_mod_cast le_top)]
  have hb := (iteratedFDeriv ℝ n G ((ContinuousLinearMap.inr ℝ E ℝ) u)).norm_compContinuousLinearMap_le
    (fun _ : Fin n => ContinuousLinearMap.inr ℝ E ℝ)
  simp only [ContinuousLinearMap.norm_inr,Finset.prod_const_one,mul_one] at hb
  exact hb.trans_eq (by
    rw [iteratedFDeriv_comp_add_left n (p,0)]
    simp)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogarithmicWeightFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial logarithmic derivative cost can be normalized by any
fixed positive power of the outer length. This gives a uniform smooth
family without discarding the original, varying test functions. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma log_power_normalization_bound (A : ℕ) {s : ℝ} (hs : 0 < s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 1 ≤ Y → Y^(-s)*(1+Real.log Y)^A ≤ K := by
  let d := s/((A:ℝ)+1)
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨(1+1/d)^A,by positivity,?_⟩
  intro Y hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hl : 1+Real.log Y ≤ (1+1/d)*Y^d := by
    have hlog := Real.log_le_rpow_div hYp.le hd
    have hone := Real.one_le_rpow hY hd.le
    calc
      _ ≤ Y^d+Y^d/d := add_le_add hone hlog
      _ = _ := by ring
  have hexp : d*(A:ℝ) ≤ s := by
    dsimp [d]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (A:ℝ)+1)).mpr
    nlinarith
  calc
    _ ≤ Y^(-s)*((1+1/d)*Y^d)^A := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith [Real.log_nonneg hY]) hl A) (Real.rpow_nonneg hYp.le _)
    _ = (1+1/d)^A*Y^(-s+d*(A:ℝ)) := by
      rw [mul_pow,← Real.rpow_natCast (Y^d) A,← Real.rpow_mul hYp.le,Real.rpow_add hYp]
      ring
    _ ≤ (1+1/d)^A*Y^(0:ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hY (by linarith)) (by positivity)
    _ = _ := by rw [Real.rpow_zero,mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothShortContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity and Mellin weights for actual finite smooth short sums. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def zeroLineMellinWeight (V : ℝ → ℂ) (Z τ : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*mellin V ((τ:ℂ)*Complex.I)*(Z:ℂ)^((τ:ℂ)*Complex.I)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeDetectorCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit smooth cutoff for the exact prime detector. -/
noncomputable section
open Filter
open scoped ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primeDetectorCutoff (x : ℝ) : ℝ := 1-Real.smoothTransition (x-1)

lemma primeDetectorCutoff_smooth : ContDiff ℝ ∞ primeDetectorCutoff :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedPrimeVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual radial weights when the largest prime lies in a distinguished
tuple coordinate. The detector difference has a uniform scaled derivative,
so the original smooth weight, rather than an arbitrary bounded sequence,
can be used in prime partial summation. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

def distinguishedRadialWeight (W : ℝ → ℂ) (w z x : ℝ) : ℂ :=
  W x*((primeDetectorCutoff (x/w):ℂ)-(primeDetectorCutoff (x/z):ℂ))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticMellinShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Applying the one-pole contour calculation to the Gauss series.
Polynomial strip growth follows from Heath-Brown (19), the finite-divisor
identity and partial summation. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace CubicFirstMoment

def MetaplecticStripPolynomial (F : ℂ → ℂ) (a b : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ σ ∈ Icc a b, ∀ v : ℝ, 1 ≤ |v| →
    ‖F ((σ:ℂ)+(v:ℂ)*Complex.I)‖ ≤ C*(1+|v|)^N

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GeometricPrimeBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete descending geometric binning of the actual prime norms.
The number of bins is logarithmic and all lower endpoints exceed one,
so the exact first-crossing construction applies without empty-bin cases. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def geometricBinCount (ρ B : ℝ) : ℕ := ⌈Real.log B/Real.log ρ⌉₊

def geometricBinLower (ρ B : ℝ) (j : ℕ) : ℝ :=
  ρ^(geometricBinCount ρ B-j)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseStoppingLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual final-bin and two-occupancy index set in the stopping
construction has logarithmic size. No complete occupancy vector occurs. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

attribute [local instance] Classical.propDecidable

def stoppingFactorLimit (X : ℝ) : ℕ := ⌈Real.log X/Real.log 2⌉₊

def stoppingLabelBox (ρ X : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (geometricBinCount ρ X)).product
    ((Finset.range (stoppingFactorLimit X+1)).product
      (Finset.range (stoppingFactorLimit X+1)))).filter (fun t => 1 ≤ t.2.1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothNormPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit finite smooth partition on every bounded positive norm range.
Its fixed weight is supported in `[1,2]`, as required by the smooth
short-factor estimates. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def normPartitionStep (x : ℝ) : ℝ := Real.smoothTransition (3*(x-1))

def normPartitionWeight (x : ℝ) : ℂ :=
  (normPartitionStep x - normPartitionStep (3*x/4) : ℝ)

lemma normPartitionStep_zero {x : ℝ} (hx : x ≤ 1) : normPartitionStep x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma normPartitionStep_one {x : ℝ} (hx : 4/3 ≤ x) : normPartitionStep x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma normPartitionWeight_low {x : ℝ} (hx : x < 1) : normPartitionWeight x = 0 := by
  rw [normPartitionWeight,normPartitionStep_zero hx.le,
    normPartitionStep_zero (show 3*x/4 ≤ 1 by linarith)]
  simp

lemma normPartitionWeight_high {x : ℝ} (hx : 2 < x) : normPartitionWeight x = 0 := by
  rw [normPartitionWeight,normPartitionStep_one (show 4/3 ≤ x by linarith),
    normPartitionStep_one (show 4/3 ≤ 3*x/4 by linarith)]
  simp

lemma normPartitionWeight_smooth : ContDiff ℝ ∞ normPartitionWeight := by
  unfold normPartitionWeight normPartitionStep
  exact Complex.ofRealCLM.contDiff.comp
    ((Real.smoothTransition.contDiff.comp (by fun_prop)).sub
      (Real.smoothTransition.contDiff.comp (by fun_prop)))

lemma normPartitionWeight_tsupport : tsupport normPartitionWeight ⊆ Icc 1 2 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra h
    exact hx (normPartitionWeight_low (lt_of_not_ge h))
  · by_contra h
    exact hx (normPartitionWeight_high (lt_of_not_ge h))

lemma normPartitionWeight_compact : HasCompactSupport normPartitionWeight :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) normPartitionWeight_tsupport

lemma normPartitionWeight_positive_support : tsupport normPartitionWeight ⊆ Ioi 0 := by
  intro x hx
  have := (normPartitionWeight_tsupport hx).1
  exact lt_of_lt_of_le zero_lt_one this

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothTuplePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit smooth partition inserted into finite convolution tuples.
Nonzero pieces automatically have the required product-length comparability. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def normTupleWeight {N : ℕ} (k : ι → Fin N) (x : ι → ℝ) : ℂ :=
  ∏ i, normPartitionWeight (2*x i/(4/3:ℝ)^(k i).val)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothPartitionCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete truncation and subpower cost for the smooth norm partition. -/
noncomputable section
namespace CubicFirstMoment

def normPartitionCount (B : ℝ) : ℕ :=
  ⌈Real.log (2*B)/Real.log (4/3:ℝ)⌉₊

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WideGramMellin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Mellin separation on the entire fixed norm range of a prime
convolution. The cutoff belongs to the transform, so no cutoff is inserted
into the arithmetic coefficients. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

def wideGramLogBump (M : ℝ) (hM : 0 < M) : ContDiffBump (0:ℝ) :=
  ⟨M,2*M,hM,by linarith⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IntervalSmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The endpoint error of a smoothed interval

A normalized integrable kernel approximates an interval indicator with
error controlled by its two tails. The proof retains exact endpoints.
This is the physical-space step of the Fourier truncation argument.
-/

noncomputable section
open MeasureTheory

namespace CubicFirstMoment

def intervalStep (a b s : ℝ) : ℝ := if s ∈ Set.Icc a b then 1 else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FourierCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A concrete Fourier cutoff kernel

The fixed cutoff is a smooth bump, one near zero and supported in [-1,1].
Its inverse Fourier transform is a normalized Schwartz kernel. Mathlib
uses exp(2π i x ξ); this frequency variable differs by 2π from the
height variable in the manuscript.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform

namespace CubicFirstMoment

def frequencyBump : ContDiffBump (0 : ℝ) where
  rIn := 1/2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def frequencyCutoff : SchwartzMap ℝ ℂ :=
  (show HasCompactSupport (fun x : ℝ => (frequencyBump x : ℂ)) from
    frequencyBump.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp frequencyBump.contDiff)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinPrimeControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two Mellin moments and the edge decay needed for prime contour
shifts are controlled by finitely many norms of the logarithmic cutoff. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff SchwartzMap
namespace CubicFirstMoment

structure PrimeMellinControl (W : ℝ → ℂ) (D : ℝ) : Prop where
  nonneg : 0 ≤ D
  decay : ∀ σ : ℝ, |σ| ≤ 2 → ∀ t : ℝ,
    (1+|t|)^2*‖mellin W ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤ D
  mass : ∀ σ : ℝ, |σ| ≤ 2 →
    (∫ t : ℝ, ‖mellin W ((σ:ℂ)+(t:ℂ)*Complex.I)‖) ≤ D
  moment : ∀ σ : ℝ, |σ| ≤ 2 →
    (∫ t : ℝ, |t|^2*‖mellin W ((σ:ℂ)+(t:ℂ)*Complex.I)‖) ≤ D

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShrinkingProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial seminorm costs for affine shrinking of a fixed cutoff. -/
noncomputable section
open scoped BigOperators ContDiff SchwartzMap
namespace CubicFirstMoment

def affineSchwartzProfile (f : 𝓢(ℝ,ℂ)) (J c : ℝ) (hJ : J ≠ 0) : 𝓢(ℝ,ℂ) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ ℝ J hJ).toContinuousLinearEquiv f).compSubConstCLM ℂ c

@[simp] lemma affineSchwartzProfile_apply (f : 𝓢(ℝ,ℂ)) (J c : ℝ) (hJ : J ≠ 0) (x : ℝ) :
    affineSchwartzProfile f J c hJ x = f (J*(x-c)) := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeThetaCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Decompletion of the actual theta Mellin transform. These algebraic bridges
will be applied to the primitive residue-character theta series. -/
noncomputable section
namespace CubicFirstMoment

def thetaHeckeL (A : ℝ) (Λ : ℂ → ℂ) (s : ℂ) : ℂ :=
  (A:ℂ)^(-s)*(Complex.Gamma s)⁻¹*Λ s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyGridPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square-grid packing of the actual lifted reduced fractions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma same_floor_abs_sub_lt_one {x y : ℝ} (h : ⌊x⌋ = ⌊y⌋) : |x-y| < 1 := by
  have hx := Int.floor_le x
  have hy := Int.floor_le y
  have hx' := Int.lt_floor_add_one x
  have hy' := Int.lt_floor_add_one y
  rw [h] at hx hx'
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

def huxleyGrid (Q : ℝ) (z x : ℂ) : ℤ × ℤ :=
  (⌊6*Q*(x-z).re⌋,⌊6*Q*(x-z).im⌋)

lemma huxleyGrid_close {Q : ℝ} (hQ : 0 < Q) {z x y : ℂ}
    (h : huxleyGrid Q z x = huxleyGrid Q z y) :
    ‖x-y‖ < 1/(3*Q) := by
  have h6 : 0 < 6*Q := by positivity
  have hcoord {a b : ℝ} (he : ⌊6*Q*a⌋ = ⌊6*Q*b⌋) : |a-b| < 1/(6*Q) := by
    have hh := same_floor_abs_sub_lt_one he
    rw [show 6*Q*a-6*Q*b = (6*Q)*(a-b) by ring,abs_mul,abs_of_pos h6] at hh
    exact (lt_div_iff₀ h6).mpr (by simpa only [mul_comm] using hh)
  have hre := hcoord (congrArg Prod.fst h)
  have him := hcoord (congrArg Prod.snd h)
  simp only [Complex.sub_re,Complex.sub_im,sub_sub_sub_cancel_right] at hre him
  have ht := Complex.norm_le_abs_re_add_abs_im (x-y)
  simp only [Complex.sub_re,Complex.sub_im] at ht
  have he : 1/(6*Q)+1/(6*Q) = 1/(3*Q) := by ring
  linarith

lemma floor_scaled_in_box {A R x : ℝ} (hA : 0 ≤ A)
    (hx : |x| ≤ R) :
    ⌊A*x⌋ ∈ Finset.Icc (-⌈A*R⌉-1) (⌈A*R⌉+1) := by
  have hx' := abs_le.mp hx
  have hlo := mul_le_mul_of_nonneg_left hx'.1 hA
  have hhi := mul_le_mul_of_nonneg_left hx'.2 hA
  have hc := Int.le_ceil (A*R)
  have hf := Int.floor_le (A*x)
  have hf' := Int.lt_floor_add_one (A*x)
  apply Finset.mem_Icc.mpr
  constructor
  · have hh : ((-⌈A*R⌉-1:ℤ):ℝ) ≤ (⌊A*x⌋:ℝ) := by push_cast; nlinarith
    exact_mod_cast hh
  · have hh : (⌊A*x⌋:ℝ) ≤ ((⌈A*R⌉+1:ℤ):ℝ) := by push_cast; nlinarith
    exact_mod_cast hh


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyGaussianPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian mass of the separated lifted fractions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma huxley_gaussian_weight_summable :
    Summable (fun k : ℕ => ((k:ℝ)+2)*Real.exp (-(k:ℝ))) := by
  have h1 := Real.summable_pow_mul_exp_neg_nat_mul 1 (show (0:ℝ) < 1 by norm_num)
  have h0 := Real.summable_exp_neg_nat
  have h := h1.add (h0.mul_left 2)
  simpa only [pow_one,one_mul,add_mul,neg_one_mul] using h

def huxleyGaussianConstant : ℝ :=
  6000*∑' k : ℕ, ((k:ℝ)+2)*Real.exp (-(k:ℝ))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GaussianDerivativeFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomially controlled factors of all derivatives of the radial Gaussian. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

lemma temperate_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {P : ℂ → F} (hP : P.HasTemperateGrowth) :
    (fderiv ℝ P).HasTemperateGrowth := by
  refine ⟨hP.1.fderiv_right (by simp),?_⟩
  intro n
  obtain ⟨k,C,hC⟩ := hP.2 (n+1)
  exact ⟨k,C,fun z => by simpa only [norm_iteratedFDeriv_fderiv] using hC z⟩

lemma temperate_smulRight {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : ℂ → (ℂ →L[ℝ] ℝ)} {P : ℂ → F}
    (hL : L.HasTemperateGrowth) (hP : P.HasTemperateGrowth) :
    (fun z => (L z).smulRight (P z)).HasTemperateGrowth :=
  (ContinuousLinearMap.smulRightL ℝ ℂ F).bilinear_hasTemperateGrowth hL hP

def radialGaussian (a : ℝ) (z : ℂ) : ℝ := Real.exp (-a*‖z‖^2)

def gaussianLogDerivative (a : ℝ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  (-2*a) • innerSL ℝ

lemma radialGaussian_smooth (a : ℝ) : ContDiff ℝ ∞ (radialGaussian a) := by
  exact (contDiff_const.mul (contDiff_norm_sq ℝ)).exp

lemma radialGaussian_fderiv (a : ℝ) (z : ℂ) :
    fderiv ℝ (radialGaussian a) z = radialGaussian a z • gaussianLogDerivative a z := by
  unfold radialGaussian
  have hd : DifferentiableAt ℝ (fun w : ℂ => ‖w‖^2) z :=
    (differentiable_id.norm_sq ℝ).differentiableAt
  rw [fderiv_exp (hd.const_mul (-a)),fderiv_const_mul hd,fderiv_norm_sq_apply]
  ext w
  simp only [gaussianLogDerivative,smul_apply,smul_smul,smul_eq_mul]
  ring

lemma radialGaussian_derivative_factor (a : ℝ) (n : ℕ) :
    ∃ P : ℂ → ℂ [×n]→L[ℝ] ℝ, P.HasTemperateGrowth ∧
      ∀ z, iteratedFDeriv ℝ n (radialGaussian a) z = radialGaussian a z • P z := by
  induction n with
  | zero =>
    let P : ℂ → ℂ [×0]→L[ℝ] ℝ := fun _ => (continuousMultilinearCurryFin0 ℝ ℂ ℝ).symm 1
    refine ⟨P,Function.HasTemperateGrowth.const _,?_⟩
    intro z
    rw [iteratedFDeriv_zero_eq_comp]
    change (continuousMultilinearCurryFin0 ℝ ℂ ℝ).symm (radialGaussian a z) = _
    rw [← map_smul]
    simp only [smul_eq_mul,mul_one]
  | succ n ih =>
    obtain ⟨P,hP,hfactor⟩ := ih
    let Q : ℂ → ℂ →L[ℝ] (ℂ [×n]→L[ℝ] ℝ) := fun z =>
      (gaussianLogDerivative a z).smulRight (P z) + fderiv ℝ P z
    have hQ : Q.HasTemperateGrowth :=
      (temperate_smulRight (gaussianLogDerivative a).hasTemperateGrowth hP).add (temperate_fderiv hP)
    let e := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => ℂ) ℝ).symm
    refine ⟨fun z => e (Q z),by
      convert e.toContinuousLinearEquiv.hasTemperateGrowth.comp hQ using 1
      all_goals try with_reducible_and_instances rfl
      rfl,?_⟩
    intro z
    have he : iteratedFDeriv ℝ n (radialGaussian a) = fun z => radialGaussian a z • P z := funext hfactor
    rw [iteratedFDeriv_succ_eq_comp_left,he]
    change e (fderiv ℝ (fun z => radialGaussian a z • P z) z) = _
    have hd : fderiv ℝ (fun z => radialGaussian a z • P z) z = radialGaussian a z • Q z := by
      rw [fderiv_fun_smul (radialGaussian_smooth a |>.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) |>.differentiableAt)
        (hP.1.differentiable (by simp) |>.differentiableAt),radialGaussian_fderiv]
      ext w
      simp only [Q,add_apply,smul_apply,
        ContinuousLinearMap.smulRight_apply,smul_add,smul_smul]
      module
    rw [hd,map_smul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GaussianRapidDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial-times-Gaussian bounds at the original computational limits. -/
noncomputable section
namespace CubicFirstMoment

lemma gaussian_power_bound {a : ℝ} (ha : 0 < a) (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → r^k*Real.exp (-a*r^2) ≤ C := by
  let C := 1+(k.factorial:ℝ)/a^k
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (by positivity)
  refine ⟨C,hC,?_⟩
  intro r hr
  have he : Real.exp (-a*r^2) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) (sq_nonneg r))
  by_cases hr1 : r ≤ 1
  · have hk : r^k ≤ 1 := pow_le_one₀ hr hr1
    exact (show r^k*Real.exp (-a*r^2) ≤ 1 from
      (mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le).trans (by simpa using he)).trans hC
  · have hr1 : 1 ≤ r := (lt_of_not_ge hr1).le
    have hpow : r^k ≤ r^(2*k) := by
      apply pow_le_pow_right₀ hr1
      omega
    have hs := Real.pow_div_factorial_le_exp (a*r^2) (mul_nonneg ha.le (sq_nonneg r)) k
    have hfac : 0 < (k.factorial:ℝ) := by positivity
    have hs' := (div_le_iff₀ hfac).mp hs
    have hm := mul_le_mul_of_nonneg_right hs' (Real.exp_pos (-a*r^2)).le
    have hp : (a*r^2)^k = a^k*r^(2*k) := by rw [mul_pow,pow_mul]
    have hex : Real.exp (a*r^2)*Real.exp (-a*r^2) = 1 := by
      rw [← Real.exp_add,show a*r^2 + -a*r^2 = 0 by ring,Real.exp_zero]
    have hb : r^(2*k)*Real.exp (-a*r^2) ≤ (k.factorial:ℝ)/a^k := by
      apply (le_div_iff₀ (pow_pos ha k)).mpr
      have heq : Real.exp (a*r^2)*(k.factorial:ℝ)*Real.exp (-a*r^2) = k.factorial := by
        calc
          _ = (k.factorial:ℝ)*(Real.exp (a*r^2)*Real.exp (-a*r^2)) := by ring
          _ = _ := by rw [hex,mul_one]
      rw [hp,heq] at hm
      convert hm using 1
      all_goals try with_reducible_and_instances rfl
      ring
    exact (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le).trans
      (hb.trans (by dsimp [C]; linarith))

lemma gaussian_polynomial_bound {a : ℝ} (ha : 0 < a) (k d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      r^k*(1+r)^d*Real.exp (-a*r^2) ≤ C := by
  obtain ⟨C,hC,hb⟩ := gaussian_power_bound ha (k+d)
  refine ⟨2^d*C,by positivity,?_⟩
  intro r hr
  have he : Real.exp (-a*r^2) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) (sq_nonneg r))
  by_cases hr1 : r ≤ 1
  · have hk : r^k ≤ 1 := pow_le_one₀ hr hr1
    have hd : (1+r)^d ≤ (2:ℝ)^d := pow_le_pow_left₀ (by positivity) (by linarith) d
    have hm := mul_le_mul hk hd (by positivity) zero_le_one
    calc
      _ ≤ 2^d*1 := mul_le_mul (by simpa using hm) he (Real.exp_pos _).le (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hC (by positivity)
  · have hr1 : 1 ≤ r := (lt_of_not_ge hr1).le
    have hd : (1+r)^d ≤ (2*r)^d := pow_le_pow_left₀ (by positivity) (by linarith) d
    calc
      _ ≤ r^k*(2*r)^d*Real.exp (-a*r^2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (pow_nonneg hr k)) (Real.exp_pos _).le
      _ = 2^d*(r^(k+d)*Real.exp (-a*r^2)) := by rw [mul_pow,pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hb r hr) (by positivity)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GaussianSchwartz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual radial Gaussian as a Schwartz test function for lattice Poisson. -/
noncomputable section
open scoped SchwartzMap
namespace CubicFirstMoment

def radialGaussianSchwartzReal (a : ℝ) (ha : 0 < a) : 𝓢(ℂ,ℝ) where
  toFun := radialGaussian a
  smooth' := radialGaussian_smooth a
  decay' k n := by
    obtain ⟨P,hP,he⟩ := radialGaussian_derivative_factor a n
    obtain ⟨d,C,hC,hb⟩ := hP.norm_iteratedFDeriv_le_uniform 0
    obtain ⟨B,hB,hdecay⟩ := gaussian_polynomial_bound ha k d
    refine ⟨C*B,?_⟩
    intro z
    have hPz : ‖P z‖ ≤ C*(1+‖z‖)^d := by simpa only [norm_iteratedFDeriv_zero] using hb 0 le_rfl z
    rw [he,norm_smul]
    have hn : ‖radialGaussian a z‖ = Real.exp (-a*‖z‖^2) :=
      Real.norm_of_nonneg (Real.exp_pos _).le
    rw [hn]
    calc
      _ ≤ ‖z‖^k*(Real.exp (-a*‖z‖^2)*(C*(1+‖z‖)^d)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPz (Real.exp_pos _).le) (by positivity)
      _ = C*(‖z‖^k*(1+‖z‖)^d*Real.exp (-a*‖z‖^2)) := by ring
      _ ≤ C*B := mul_le_mul_of_nonneg_left (hdecay ‖z‖ (_root_.norm_nonneg z)) hC

def radialGaussianSchwartz (a : ℝ) (ha : 0 < a) : 𝓢(ℂ,ℂ) :=
  (radialGaussianSchwartzReal a ha).postcompCLM Complex.ofRealCLM

@[simp] lemma radialGaussianSchwartz_apply (a : ℝ) (ha : 0 < a) (z : ℂ) :
    radialGaussianSchwartz a ha z = (Real.exp (-a*‖z‖^2):ℝ) := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeSchwartz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubic pullback of the radial Fourier transform is a Schwartz function. -/

noncomputable section
open scoped SchwartzMap ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cube_norm_growth :
    ∃ (k : ℕ) (C : ℝ), ∀ z : ℂ, ‖z‖ ≤ C*(1+‖z^3‖)^k := by
  refine ⟨1,1,?_⟩
  intro z
  simp only [one_mul,pow_one,norm_pow]
  by_cases hz : ‖z‖ ≤ 1
  · nlinarith [pow_nonneg (_root_.norm_nonneg z) 3]
  · have hh : 1 ≤ ‖z‖ := le_of_lt (lt_of_not_ge hz)
    have hp := mul_nonneg (mul_nonneg (_root_.norm_nonneg z) (sub_nonneg.mpr hh))
      (by positivity : 0 ≤ ‖z‖+1)
    nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DyadicWeightIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A supported height weight is controlled by the actual two-sided
dyadic mean. The normalization includes both height intervals. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def dyadicHeightSupport (T : ℝ) : Set ℝ := Icc T (2*T) ∪ Icc (-2*T) (-T)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightIntegrationByParts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact twofold integration by parts for the actual height exponential. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace CubicFirstMoment

def heightFourierIntegral (h : ℝ → ℂ) (ℓ : ℝ) : ℂ := 𝓕 h (-ℓ/(2*Real.pi))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SharpHeightIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete sharp-cutoff smoothing in the manuscript's height variable.
The Fourier convention contributes the explicit Jacobian `1 / (2π)`.
All finite sums below retain their original coefficients and support. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
namespace CubicFirstMoment

def cutoffHeightMultiplier (T t : ℝ) : ℂ :=
  frequencyCutoff ((t/(2*Real.pi))/T) *
    𝓕 (fun x => (intervalStep 0 (Real.log 2) x : ℂ)) (t/(2*Real.pi))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SharpHeightPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth height windows with ratio 3/2. Their support lies in [T,2T]
in absolute value, exactly the range of the proved bilinear estimates.
The finite telescoping identity keeps the actual truncation multiplier. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def heightPartitionBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 4/3
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def heightWindow (T t : ℝ) : ℂ :=
  ((heightPartitionBump (t/((3/2)*T)) - heightPartitionBump (t/T) : ℝ) : ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowHeightIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The low-height weight has a direct polynomial-logarithmic cost.
This transfers the uniform corrected Type-I/II estimates to its integral. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def lowHeightWeight (H T t : ℝ) : ℂ :=
  cutoffHeightMultiplier H t*(heightPartitionBump (t/T):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightWindowCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete finite height partition. Every nonzero window lies below
the Fourier cap, and the number of windows costs only one logarithm. -/
noncomputable section
namespace CubicFirstMoment

def heightWindowCount (S T : ℝ) : ℕ :=
  ⌈Real.log ((2*Real.pi*S)/T)/Real.log (3/2:ℝ)⌉₊

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightEndpointRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness at the removable reciprocal singularity, compact support,
and the exact two-endpoint formula for a localized cutoff. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology
namespace CubicFirstMoment

lemma abs_lt_not_mem_dyadic {T t : ℝ} (ht : |t| < T) :
    t ∉ dyadicHeightSupport T := by
  rintro (hp | hn)
  · exact (not_le_of_gt ht) (hp.1.trans (le_abs_self t))
  · exact (not_le_of_gt ht) ((by linarith [hn.2] : T ≤ -t).trans (neg_le_abs t))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RieszHeatKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Laplace representations of the two radial powers in the Riesz calculation. -/

noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma laplace_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Ioi (0:ℝ), t^(a-1)*Real.exp (-b*t)) =
      Real.Gamma a*b^(-a) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := a-1) (b := b)
    (by norm_num) (by linarith) hb
  simpa only [Real.rpow_one,sub_add_cancel,div_one,one_div_one,mul_one,mul_comm] using h

lemma integrable_laplace_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t^(a-1)*Real.exp (-b*t)) (Ioi 0) := by
  by_contra h
  have hp : 0 < Real.Gamma a*b^(-a) := mul_pos (Real.Gamma_pos_of_pos ha)
    (Real.rpow_pos_of_pos hb _)
  rw [← laplace_rpow ha hb,integral_undef h] at hp
  exact lt_irrefl _ hp

/-- The inverted Gaussian moment is the dual radial power. -/
lemma inverse_gaussian_moment {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Ioi (0:ℝ), t^(-a-1)*Real.exp (-b/t)) = Real.Gamma a*b^(-a) := by
  have h := integral_comp_rpow_Ioi
    (fun u : ℝ => u^(a-1)*Real.exp (-b*u)) (show (-1:ℝ) ≠ 0 by norm_num)
  rw [laplace_rpow ha hb] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  have hp : t^(-a-1) = t^((-1:ℝ)-1)*(t^(-1:ℝ))^(a-1) := by
    rw [← Real.rpow_mul ht.le,← Real.rpow_add ht]
    congr 1
    ring
  rw [hp]
  simp only [abs_neg,abs_one,one_mul,Real.rpow_neg_one,smul_eq_mul]
  rw [show -b/t = -b*t⁻¹ by ring]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicDyadicCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite cover of all noncube frequencies outside the small-core set
by the actual coprime ramified/squarefree blocks used in the moment bounds. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def coreDyadicConductor (i j : ℕ) : ℝ := (2:ℝ)^i*((2:ℝ)^j)^2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseEnvelopeWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed product envelope in the sparse branch gives an actual
uniform family of inner weights on every fixed outer norm dyad. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma scaled_exp_log {s : ℝ} (hs : 0 < s) (u : ℝ) :
    s*Real.exp (-u) = Real.exp (-(u-Real.log s)) := by
  rw [neg_sub,Real.exp_sub,Real.exp_log hs,div_eq_mul_inv,←Real.exp_neg]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_PrimeProductEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed smooth product envelope equals one on the full sharp dyadic
interval. Thus the exact prime cutoff can be retained in the height integral
while every factorized row has a smooth product weight. -/
noncomputable section
open Set Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def primeProductBump : ContDiffBump (3/2 : ℝ) where
  rIn := 1/2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def primeProductEnvelope (x : ℝ) : ℂ := (primeProductBump x : ℝ)

lemma primeProductEnvelope_tsupport :
    tsupport primeProductEnvelope = tsupport primeProductBump := by
  apply congrArg closure
  ext x
  simp [Function.support,primeProductEnvelope]

lemma primeProductEnvelope_compact : HasCompactSupport primeProductEnvelope := by
  change IsCompact (tsupport primeProductEnvelope)
  rw [primeProductEnvelope_tsupport]
  exact primeProductBump.hasCompactSupport

lemma primeProductEnvelope_positive : tsupport primeProductEnvelope ⊆ Ioi 0 := by
  rw [primeProductEnvelope_tsupport,primeProductBump.tsupport_eq]
  intro x hx
  have hx' : |x-3/2| ≤ 1 := by
    simpa only [Metric.mem_closedBall,Real.dist_eq,primeProductBump] using hx
  have h := (abs_le.mp hx').1
  change 0 < x
  linarith

lemma primeProductEnvelope_smooth : ContDiff ℝ ∞ primeProductEnvelope :=
  Complex.ofRealCLM.contDiff.comp primeProductBump.contDiff

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeSmoothWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The roughness transition in each actual semiprime norm piece belongs
to a single uniform smooth family. Capping its scale ratio at two is an
identity on the fixed norm support, so all logarithmic derivatives are
uniform even when the original ratio is unbounded. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def semiprimeSmoothWeight (r x : ℝ) : ℂ :=
  normPartitionWeight x*(1-(primeDetectorCutoff (r*x):ℂ))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite smooth partition of the original semiprime kernel. Every
prime coordinate retains both its roughness weight and the total-product
cutoff; the displayed number of pieces is the actual finite partition. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def semiprimePartitionScale (j : ℕ) : ℝ := (4/3:ℝ)^j/2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single uniform smooth family for the actual distinguished-prime
weights in each large-row norm piece. Both scale ratios are capped only
after proving that the cap leaves the weight unchanged. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

def distinguishedSmoothWeight (r : ℝ × ℝ) (x : ℝ) : ℂ :=
  semiprimeSmoothWeight r.2 x-semiprimeSmoothWeight r.1 x

lemma distinguishedSmoothWeight_contDiff :
    ContDiff ℝ ∞ (Function.uncurry distinguishedSmoothWeight) := by
  change ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ =>
    normPartitionWeight z.2*(1-(primeDetectorCutoff (z.1.2*z.2):ℂ))-
      normPartitionWeight z.2*(1-(primeDetectorCutoff (z.1.1*z.2):ℂ)))
  have hn : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => normPartitionWeight z.2) :=
    normPartitionWeight_smooth.comp contDiff_snd
  have h₁ : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ =>
      (primeDetectorCutoff (z.1.1*z.2):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (primeDetectorCutoff_smooth.comp ((contDiff_fst.fst).mul contDiff_snd))
  have h₂ : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ =>
      (primeDetectorCutoff (z.1.2*z.2):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (primeDetectorCutoff_smooth.comp ((contDiff_fst.snd).mul contDiff_snd))
  exact (hn.mul (contDiff_const.sub h₂)).sub (hn.mul (contDiff_const.sub h₁))

lemma distinguishedSmoothWeight_support (r : ℝ × ℝ) :
    Function.support (distinguishedSmoothWeight r) ⊆ Function.support normPartitionWeight := by
  intro x hx
  change normPartitionWeight x ≠ 0
  intro hn
  apply hx
  simp only [distinguishedSmoothWeight,semiprimeSmoothWeight,hn,zero_mul,sub_self]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleCoordinateWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual independently smoothed prime coordinates of a large row
belong to one uniform family, for every norm partition and roughness scale. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment

def largeTupleNormScale {i j : ℕ} (k : (Fin i ⊕ Fin j) → ℕ)
    (a : Fin i ⊕ Fin j) : ℝ := (4/3:ℝ)^(k a)/2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleCutoffBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sharp distinguished-product condition is automatic on high
boxes and kills low boxes. The remaining boxes are explicitly confined
to a fixed-ratio neighborhood of the original cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largeTupleDistinguishedScale {i j : ℕ} (k : (Fin i ⊕ Fin j) → ℕ) : ℝ :=
  ∏ a : Fin i, largeTupleNormScale k (.inl a)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedScalePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript partitions the distinguished prime scales before
splitting the rough remainder. This exact finite partition introduces no
partial-product cutoff in a high-scale coefficient. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def distinguishedScaleLength {i N : ℕ} (k : Fin i → Fin N) : ℝ :=
  ∏ a, (4/3:ℝ)^(k a).val/2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HarmonicGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Holomorphic polynomial Gaussians and the anti-holomorphic raising
operator used for the fixed angular Fourier transform. -/
noncomputable section
open scoped SchwartzMap
open LineDeriv
namespace CubicFirstMoment

def harmonicGaussian (a : ℝ) (ha : 0 < a) (n : ℕ) : 𝓢(ℂ,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun z : ℂ => z^n) (radialGaussianSchwartz a ha)

@[simp] lemma harmonicGaussian_apply (a : ℝ) (ha : 0 < a) (n : ℕ) (z : ℂ) :
    harmonicGaussian a ha n z = z^n*(radialGaussian a z:ℂ) := by
  rw [harmonicGaussian,SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_AntiHarmonicGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conjugate harmonic monomials, obtained by the measure-preserving
complex reflection. -/
noncomputable section
open scoped SchwartzMap FourierTransform
namespace CubicFirstMoment

def antiHarmonicGaussian (a : ℝ) (ha : 0 < a) (n : ℕ) : 𝓢(ℂ,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Complex.conjLIE.toContinuousLinearEquiv
    (harmonicGaussian a ha n)

@[simp] lemma antiHarmonicGaussian_apply (a : ℝ) (ha : 0 < a) (n : ℕ) (z : ℂ) :
    antiHarmonicGaussian a ha n z = (star z)^n*(radialGaussian a z:ℂ) := by
  simp [antiHarmonicGaussian,harmonicGaussian_apply,radialGaussian]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CommonNonzeroBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Large common-factor recurrence with the exact zero mode removed. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def commonNonzeroCost (C ε B Q A L D : ℝ) : ℝ :=
  C*(B*Q^2*L^3/A)^ε*
    (max 1 (L/D)+A^(1/3:ℝ)*max 1 (L/D)+A^(2/3:ℝ)*(max 1 (L/D))^(2/3:ℝ))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed order-one-third Bessel kernel in the cubic theta expansion.
The Schläfli heat integral is used as the definition; its Mellin mass is
proved by absolute Fubini and the two ordinary Gamma integrals.
Normalization: NIST DLMF 10.32.10, specialized to nu=1/3 and positive
argument; the cubic theta expansion is DR v3 section 5.1, Eq.(5.6). -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

/-- The positive heat integrand for `2*K_(1/3)(2*sqrt x)`. -/
def cubicBesselHeat (x t : ℝ) : ℝ :=
  t^(-4/3:ℝ)*Real.exp (-t)*Real.exp (-x/t)

/-- Fixed Bessel order required by the cubic metaplectic Fourier series. -/
def cubicBesselKernel (x : ℝ) : ℝ :=
  x^(1/6:ℝ)*∫ t in Ioi (0:ℝ), cubicBesselHeat x t

lemma cubicBesselHeat_nonneg {x t : ℝ} (ht : 0 < t) :
    0 ≤ cubicBesselHeat x t := by
  unfold cubicBesselHeat
  positivity

lemma integrable_inverse_laplace_rpow {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t^(-a-1)*Real.exp (-x/t)) (Ioi 0) := by
  by_contra h
  have hp : 0 < Real.Gamma a*x^(-a) :=
    mul_pos (Real.Gamma_pos_of_pos ha) (Real.rpow_pos_of_pos hx _)
  rw [←inverse_gaussian_moment ha hx,integral_undef h] at hp
  exact lt_irrefl _ hp

lemma cubicBesselHeat_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (cubicBesselHeat x) (Ioi 0) := by
  have hi := integrable_inverse_laplace_rpow (by norm_num : (0:ℝ) < 1/3) hx
  have hm : AEStronglyMeasurable (cubicBesselHeat x) (volume.restrict (Ioi 0)) := by
    apply Measurable.aestronglyMeasurable
    unfold cubicBesselHeat
    fun_prop
  apply hi.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  rw [Real.norm_eq_abs,abs_of_nonneg (cubicBesselHeat_nonneg ht)]
  change t^(-4/3:ℝ)*Real.exp (-t)*Real.exp (-x/t) ≤ _
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht])
  calc
    _ ≤ t^(-4/3:ℝ)*1*Real.exp (-x/t) := by gcongr
    _ = _ := by norm_num

lemma cubicBesselKernel_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ cubicBesselKernel x := by
  unfold cubicBesselKernel
  apply mul_nonneg (Real.rpow_nonneg hx _) (setIntegral_nonneg measurableSet_Ioi ?_)
  intro t ht
  exact cubicBesselHeat_nonneg ht

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit exponential decay of the fixed cubic Bessel kernel, obtained
from its defining positive heat integral. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicBessel_exponent_bound {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    -t-x/t ≤ -Real.sqrt x-(x/2)/t := by
  have he : 2*Real.sqrt x ≤ t+x/t := by
    have hs := sq_nonneg (t-Real.sqrt x)
    have hsq := Real.sq_sqrt hx.le
    calc
      _ ≤ (t^2+x)/t := (le_div_iff₀ ht).2 (by nlinarith)
      _ = t+x/t := by field_simp
  have hd : (x/2)/t = (x/t)/2 := by ring
  rw [hd]
  linarith

lemma cubicBesselHeat_exp_bound {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    cubicBesselHeat x t ≤ Real.exp (-Real.sqrt x)*
      (t^(-4/3:ℝ)*Real.exp (-(x/2)/t)) := by
  unfold cubicBesselHeat
  calc
    _ = t^(-4/3:ℝ)*Real.exp (-t-x/t) := by simp only [Real.exp_sub, neg_div, Real.exp_neg]; ring
    _ ≤ t^(-4/3:ℝ)*Real.exp (-Real.sqrt x-(x/2)/t) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (cubicBessel_exponent_bound hx ht))
        (Real.rpow_nonneg ht.le _)
    _ = _ := by simp only [Real.exp_sub, neg_div, Real.exp_neg]; ring

lemma cubicBesselKernel_exp_bound {x : ℝ} (hx : 0 < x) :
    cubicBesselKernel x ≤ x^(1/6:ℝ)*
      (Real.exp (-Real.sqrt x)*(Real.Gamma (1/3)*(x/2)^(-1/3:ℝ))) := by
  have hhalf : 0 < x/2 := by positivity
  have hi : IntegrableOn (fun t : ℝ => t^(-4/3:ℝ)*Real.exp (-(x/2)/t)) (Ioi 0) := by
    convert integrable_inverse_laplace_rpow (by norm_num : (0:ℝ) < 1/3) hhalf using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
  have hb := integral_mono_ae (cubicBesselHeat_integrable hx)
    (hi.const_mul (Real.exp (-Real.sqrt x))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact cubicBesselHeat_exp_bound hx ht)
  unfold cubicBesselKernel
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx.le _)
  apply hb.trans_eq
  rw [integral_const_mul]
  congr 1
  convert inverse_gaussian_moment (by norm_num : (0:ℝ) < 1/3) hhalf using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)

lemma cubicBessel_exp_prefactor {x : ℝ} (hx : 0 < x) :
    x^(1/6:ℝ)*(x/2)^(-1/3:ℝ) = 2^(1/3:ℝ)*x^(-1/6:ℝ) := by
  have he : ((2:ℝ)^(-1/3:ℝ))⁻¹ = 2^(1/3:ℝ) := by
    rw [←Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  have hd : x^(-1/3:ℝ) / 2^(-1/3:ℝ) = x^(-1/3:ℝ)*2^(1/3:ℝ) := by
    rw [div_eq_mul_inv,he]
  rw [Real.div_rpow hx.le (by norm_num : (0:ℝ) ≤ 2),hd]
  calc
    _ = 2^(1/3:ℝ)*(x^(1/6:ℝ)*x^(-1/3:ℝ)) := by ring
    _ = _ := by rw [←Real.rpow_add hx]; congr 1; norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local dominated continuity of the fixed positive Bessel integral. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicBesselHeat_local_bound {a x t : ℝ} (hax : a ≤ x) (ht : 0 < t) :
    ‖cubicBesselHeat x t‖ ≤ t^(-4/3:ℝ)*Real.exp (-a/t) := by
  rw [Real.norm_eq_abs,abs_of_nonneg (cubicBesselHeat_nonneg ht)]
  unfold cubicBesselHeat
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hex : Real.exp (-x/t) ≤ Real.exp (-a/t) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (neg_le_neg hax) ht.le
  calc
    _ ≤ t^(-4/3:ℝ)*1*Real.exp (-a/t) := by gcongr
    _ = _ := by ring

lemma cubicBessel_integral_continuousAt {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun y => ∫ t in Ioi (0:ℝ), cubicBesselHeat y t) x := by
  have hi : IntegrableOn (fun t : ℝ => t^(-4/3:ℝ)*Real.exp (-(x/2)/t)) (Ioi 0) := by
    convert integrable_inverse_laplace_rpow (by norm_num : (0:ℝ) < 1/3)
      (show 0 < x/2 by positivity) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
  apply continuousAt_of_dominated (bound := fun t : ℝ => t^(-4/3:ℝ)*Real.exp (-(x/2)/t))
  · exact Eventually.of_forall (fun y => by
      apply Measurable.aestronglyMeasurable
      unfold cubicBesselHeat
      fun_prop)
  · filter_upwards [eventually_gt_nhds (show x/2 < x by linarith)] with y hy
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicBesselHeat_local_bound hy.le ht
  · exact hi
  · filter_upwards with t
    unfold cubicBesselHeat
    fun_prop

/-- The fixed kernel is continuous on its positive domain. -/
theorem cubicBesselKernel_continuousOn : ContinuousOn cubicBesselKernel (Ioi 0) := by
  intro x hx
  exact ((Real.continuousAt_rpow_const x (1/6:ℝ) (Or.inl (ne_of_gt hx))).mul
    (cubicBessel_integral_continuousAt hx)).continuousWithinAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiate the fixed order-one-third heat integral on its positive
axis. The dominating inverse Laplace moment is integrable there. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicFirstMoment

def cubicBesselHeatDerivative (x t : ℝ) : ℝ := -cubicBesselHeat x t/t

def cubicBesselKernelDerivative (x : ℝ) : ℝ :=
  ((1/6:ℝ)*x^(-5/6:ℝ))*(∫ t in Ioi (0:ℝ),cubicBesselHeat x t)+
    x^(1/6:ℝ)*(∫ t in Ioi (0:ℝ),cubicBesselHeatDerivative x t)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselPowerDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit arbitrary power majorants for the cubic theta kernel. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma pow_mul_exp_neg_le_factorial (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    y^k*Real.exp (-y) ≤ k.factorial := by
  have hf : (0:ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp y hy k)
  calc
    _ ≤ (Real.exp y*(k.factorial:ℝ))*Real.exp (-y) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by rw [mul_right_comm,←Real.exp_add]; simp

lemma exp_neg_div_le_power (k : ℕ) {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    Real.exp (-x/t) ≤ (k.factorial:ℝ)*t^k/x^k := by
  have h := pow_mul_exp_neg_le_factorial k (div_pos hx ht).le
  rw [div_pow] at h
  apply (le_div_iff₀ (pow_pos hx k)).mpr
  have hh := mul_le_mul_of_nonneg_right h (pow_nonneg ht.le k)
  simpa only [neg_div] using (show Real.exp (-(x/t))*x^k ≤ (k.factorial:ℝ)*t^k by
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp))

lemma cubicBesselHeat_power_bound (k : ℕ) {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    cubicBesselHeat x t ≤ ((k.factorial:ℝ)/x^k)*
      (t^((k:ℝ)-4/3)*Real.exp (-t)) := by
  unfold cubicBesselHeat
  calc
    _ ≤ (t^(-4/3:ℝ)*Real.exp (-t))*((k.factorial:ℝ)*t^k/x^k) :=
      mul_le_mul_of_nonneg_left (exp_neg_div_le_power k hx ht) (by positivity)
    _ = _ := by
      rw [←Real.rpow_natCast t k]
      have he : t^(-4/3:ℝ)*t^(k:ℝ) = t^((k:ℝ)-4/3) := by
        rw [←Real.rpow_add ht]
        congr 1
        ring
      calc
        _ = ((k.factorial:ℝ)/x^k)*(t^(-4/3:ℝ)*t^(k:ℝ))*Real.exp (-t) := by ring
        _ = _ := by rw [he]; ring

/-- The power is arbitrary; the coefficient is the exact Gamma integral of
its positive majorant. This is used for summing the actual theta series. -/
theorem cubicBesselKernel_power_bound (k : ℕ) (hk : 1 ≤ k) {x : ℝ} (hx : 0 < x) :
    cubicBesselKernel x ≤ ((k.factorial:ℝ)*Real.Gamma ((k:ℝ)-1/3))*
      x^(1/6-(k:ℝ)) := by
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have ha : 0 < (k:ℝ)-1/3 := by linarith
  have hefun : (fun t : ℝ => t^((k:ℝ)-4/3)*Real.exp (-t)) =
      (fun t : ℝ => t^(((k:ℝ)-1/3)-1)*Real.exp (-1*t)) := by
    funext t
    rw [show (k:ℝ)-1/3-1 = (k:ℝ)-4/3 by ring]
    simp
  have hi : IntegrableOn (fun t : ℝ => t^((k:ℝ)-4/3)*Real.exp (-t)) (Ioi 0) := by
    rw [hefun]
    exact integrable_laplace_rpow ha (by norm_num : (0:ℝ) < 1)
  have hb := integral_mono_ae (cubicBesselHeat_integrable hx)
    (hi.const_mul ((k.factorial:ℝ)/x^k)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact cubicBesselHeat_power_bound k hx ht)
  have he : (∫ t in Ioi (0:ℝ), t^((k:ℝ)-4/3)*Real.exp (-t)) = Real.Gamma ((k:ℝ)-1/3) := by
    rw [hefun,laplace_rpow ha (by norm_num : (0:ℝ) < 1)]
    simp
  calc
    _ ≤ x^(1/6:ℝ)*(((k.factorial:ℝ)/x^k)*Real.Gamma ((k:ℝ)-1/3)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx.le _)
      simpa only [integral_const_mul,he] using hb
    _ = _ := by
      rw [Real.rpow_sub hx,Real.rpow_natCast]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselDerivativeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Power decay of the first derivative of the fixed Bessel kernel.
The same lattice majorants can therefore control vertical theta derivatives. -/
noncomputable section
open MeasureTheory Set Filter
namespace CubicFirstMoment

def cubicBesselDerivativePowerConstant (k : ℕ) : ℝ :=
  ((k.factorial:ℝ)/6+((k+1).factorial:ℝ))*Real.Gamma ((k:ℝ)-1/3)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselLogIntegrable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute integrability of the logarithmic cubic Bessel weight. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicBesselLogWeight (a u : ℝ) : ℝ :=
  Real.exp (-u/3)*Real.exp (-2*a*Real.cosh u)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ThetaHeatKernelBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential bounds for the normalized angular heat kernel. -/
noncomputable section
namespace CubicFirstMoment

lemma power_exp_bound {b : ℝ} (hb : 0 < b) (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    x^n*Real.exp (-b*x) ≤ (n.factorial:ℝ)/b^n := by
  have hs := Real.pow_div_factorial_le_exp (b*x) (mul_nonneg hb.le hx) n
  have hm := mul_le_mul_of_nonneg_right
    ((div_le_iff₀ (show 0 < (n.factorial:ℝ) by positivity)).mp hs)
    (Real.exp_pos (-b*x)).le
  have he : Real.exp (b*x)*(n.factorial:ℝ)*Real.exp (-b*x) = n.factorial := by
    calc
      _ = (n.factorial:ℝ)*(Real.exp (b*x)*Real.exp (-b*x)) := by ring
      _ = _ := by rw [←Real.exp_add,show b*x + -b*x = 0 by ring,Real.exp_zero,mul_one]
  rw [he,mul_pow] at hm
  apply (le_div_iff₀ (pow_pos hb n)).mpr
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselLogDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiation of the fixed cubic Bessel integral in logarithmic
coordinates, with an integrable local majorant. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicFirstMoment

def cubicBesselLogDerivative (a u : ℝ) : ℝ :=
  -2*Real.cosh u*cubicBesselLogWeight a u

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselSumIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive-quadrant Gamma integral needed for the square of the
fixed order-one-third Schlaefli kernel. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicBesselSumWeight (s : ℝ) : ℝ := s^(-4/3:ℝ)*Real.exp (-s)

def cubicBesselTriangle (p : ℝ × ℝ) : ℝ :=
  if p.2 ∈ Ioo 0 p.1 then cubicBesselSumWeight p.1 else 0

def cubicBesselSumShear : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun p := (p.1+p.2,p.2)
  invFun p := (p.1-p.2,p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  measurable_toFun := by
    change Measurable (fun p : ℝ × ℝ => (p.1+p.2,p.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : ℝ × ℝ => (p.1-p.2,p.2))
    fun_prop

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselSquareHeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square of the fixed Schlaefli integral as a positive double heat
integral. Its inner Mellin integral reduces to the proved Gamma sum. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicBesselSquareHeat (p : ℝ × ℝ) (x : ℝ) : ℝ :=
  x^(1/3:ℝ)*cubicBesselHeat x p.1*cubicBesselHeat x p.2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicWhittakerMellin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact archimedean factor of the cubic theta Fourier expansion,
using the fixed Schläfli kernel and the normalization `4*pi*v`. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

/-- The heat-integral realization of `v*K_(1/3)(4*pi*v)`. -/
def cubicThetaWhittaker (v : ℝ) : ℂ :=
  (v:ℂ)/2*(cubicBesselKernel ((2*Real.pi*v)^2):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicWhittakerDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First vertical derivative of the actual cubic Whittaker kernel,
with arbitrary fixed power decay. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaWhittakerDerivative (v : ℝ) : ℂ :=
  ((cubicBesselKernel ((2*Real.pi*v)^2)/2+
    (2*Real.pi*v)^2*cubicBesselKernelDerivative ((2*Real.pi*v)^2):ℝ):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicWhittakerExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential decay retaining an arbitrarily summable polynomial factor. -/
noncomputable section
namespace CubicFirstMoment

def cubicWhittakerExpConstant : ℝ :=
  (Real.Gamma (1/3)*2^(1/3:ℝ)/2)*(2*Real.pi)^(-1/3:ℝ)

lemma cubicBesselKernel_exp_power_bound {x : ℝ} (hx : 0 < x) :
    cubicBesselKernel x ≤ (Real.Gamma (1/3)*2^(1/3:ℝ))*
      x^(-1/6:ℝ)*Real.exp (-Real.sqrt x) := by
  apply (cubicBesselKernel_exp_bound hx).trans_eq
  calc
    _ = (Real.Gamma (1/3)*Real.exp (-Real.sqrt x))*(x^(1/6:ℝ)*(x/2)^(-1/3:ℝ)) := by ring
    _ = _ := by rw [cubicBessel_exp_prefactor hx]; ring

def cubicWhittakerMixedConstant : ℝ := cubicWhittakerExpConstant*720/Real.pi^6

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PoissonProfileBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative profile budget is constructed from finitely many
Schwartz seminorms. It records only the two analytic costs used by the
Poisson argument; it is not an additional published input. -/
noncomputable section
open scoped BigOperators ContDiff SchwartzMap
open Set MeasureTheory
namespace CubicFirstMoment

def poissonProfileLogWidth : ℝ := 1+2*Real.log 2

lemma poissonProfileLogWidth_pos : 0 < poissonProfileLogWidth := by
  dsimp [poissonProfileLogWidth]
  have h : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeGaussTailAngularWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual semiprime coordinates as a uniform smooth prime-weight family.
The angular factor remains separate from the radial weight throughout. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

abbrev SemiprimeAngularWeightParameters :=
  (Ici (0:ℝ) × Ici (1:ℝ)) × (Ici (0:ℝ) × Ici (1:ℝ))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ThetaMellinSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The completed theta Mellin transform as two rapidly convergent tails. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace CubicFirstMoment

def thetaUpper (f : ℝ → ℂ) : ℝ → ℂ := (Ioi 1).indicator f

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAngularExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential cusp decay survives every fixed angular frequency power. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaAngularAbsorption (k : ℕ) : ℝ := (k.factorial:ℝ)/(Real.pi/2)^k

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMobiusGenerators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translation and level inversion matrices in the exact coordinates
used by the cubic theta Fourier and Mellin expansions. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaInversionMatrix (q : ℂ) (hq : q ≠ 0) : SL(2,ℂ) :=
  ⟨!![0,-q⁻¹;q,0],by simp [Matrix.det_fin_two,hq]⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEisensteinBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive quadratic majorant for the initial cubic Eisenstein series.
This supplies actual convergence, rather than relying on formal reindexing. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_two_norm_decay {a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ s) :
    (1+a+b)^(-s) ≤ (1+a)^(-s/2)*(1+b)^(-s/2) := by
  have hA : 0 < 1+a := by positivity
  have hB : 0 < 1+b := by positivity
  have hL : 0 < 1+a+b := by positivity
  have hprod : (1+a)*(1+b) ≤ (1+a+b)^2 := by nlinarith [mul_nonneg ha hb]
  calc
    _ = ((1+a+b)^2)^(-s/2) := by
      rw [←Real.rpow_natCast_mul hL.le]
      congr 1
      ring
    _ ≤ ((1+a)*(1+b))^(-s/2) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos hA hB) hprod (by linarith)
    _ = _ := Real.mul_rpow hA.le hB.le

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary local cardinalities for the Eisenstein scattering factor. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaUnitsEquivIsUnit (R : Type*) [Monoid R] : Rˣ ≃ {x : R // IsUnit x} where
  toFun u := ⟨u,u.isUnit⟩
  invFun x := x.property.unit
  left_inv u := Units.ext u.isUnit.unit_spec
  right_inv x := Subtype.ext x.property.unit_spec

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLaplaceSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute Laplace interchange for the Eisenstein lattice row. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicThetaLaplaceTerm (a : ℂ) (R : ℝ) (s : ℂ) (t : ℝ) : ℂ :=
  a*(t:ℂ)^(s-1)*(Real.exp (-R*t):ℂ)

lemma cubicThetaLaplaceTerm_norm (a : ℂ) (R : ℝ) (s : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖cubicThetaLaplaceTerm a R s t‖ = ‖a‖*t^(s.re-1)*Real.exp (-R*t) := by
  simp only [cubicThetaLaplaceTerm, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.sub_re, Complex.one_re, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_nonneg _)]

lemma cubicThetaLaplaceTerm_integrable (a : ℂ) {R : ℝ} (hR : 0 < R)
    {s : ℂ} (hs : 0 < s.re) : IntegrableOn (cubicThetaLaplaceTerm a R s) (Ioi 0) := by
  have hm : AEStronglyMeasurable (cubicThetaLaplaceTerm a R s)
      (volume.restrict (Ioi 0)) := by
    apply Measurable.aestronglyMeasurable
    unfold cubicThetaLaplaceTerm
    fun_prop
  apply ((integrable_laplace_rpow hs hR).const_mul ‖a‖).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [cubicThetaLaplaceTerm_norm a R s ht]
  simp only [mul_assoc, le_refl]

lemma cubicThetaLaplaceTerm_mass (a : ℂ) {R : ℝ} (hR : 0 < R)
    {s : ℂ} (hs : 0 < s.re) :
    (∫ t in Ioi (0:ℝ), ‖cubicThetaLaplaceTerm a R s t‖) =
      Real.Gamma s.re*(‖a‖*R^(-s.re)) := by
  calc
    _ = ‖a‖*(∫ t in Ioi (0:ℝ), t^(s.re-1)*Real.exp (-R*t)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [cubicThetaLaplaceTerm_norm a R s ht]
      ring
    _ = _ := by rw [laplace_rpow hs hR]; ring

lemma cubicThetaLaplaceTerm_integral (a : ℂ) {R : ℝ} (hR : 0 < R)
    {s : ℂ} (hs : 0 < s.re) :
    (∫ t in Ioi (0:ℝ), cubicThetaLaplaceTerm a R s t) =
      Complex.Gamma s*(a*(R:ℂ)^(-s)) := by
  unfold cubicThetaLaplaceTerm
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  have he : (fun t : ℝ => (t:ℂ)^(s-1)*(Real.exp (-R*t):ℂ)) =
      fun t : ℝ => (t:ℂ)^(s-1)*Complex.exp (-((R:ℂ)*(t:ℂ))) := by
    funext t
    rw [Complex.ofReal_exp]
    push_cast
    rw [neg_mul]
  rw [he, Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hR]
  simp only [one_div, Complex.inv_cpow_ofReal_nonneg hR.le, ← Complex.cpow_neg]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaDualHeatBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summable inverse-square majorants for the nonzero Fourier heat modes. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicTheta_inverse_heat_bound {A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    Real.exp (-A/t) ≤ (2/A^2)*t^2 := by
  have h := power_exp_bound (by norm_num : (0:ℝ) < 1) 2 (A/t) (div_pos hA ht).le
  norm_num only [one_pow, div_one, Nat.factorial_two, Nat.cast_ofNat, one_mul] at h
  simp only [neg_one_mul] at h
  rw [show (2/A^2)*t^2 = (2*t^2)/A^2 by ring]
  apply (le_div_iff₀ (sq_pos_of_pos hA)).mpr
  have hh := (div_le_iff₀ (sq_pos_of_pos ht)).mp
    (show A^2*Real.exp (-A/t)/t^2 ≤ 2 by
      simpa only [div_pow, div_mul_eq_mul_div, neg_div] using h)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

def cubicThetaDualHeat (v : ℝ) (s : ℂ) (A t : ℝ) : ℂ :=
  (t:ℂ)^(s-2)*(Real.exp (-v^2*t-A/t):ℂ)

lemma cubicThetaDualHeat_norm (v : ℝ) (s : ℂ) (A : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖cubicThetaDualHeat v s A t‖ =
      t^(s.re-2)*Real.exp (-v^2*t)*Real.exp (-A/t) := by
  unfold cubicThetaDualHeat
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_nonneg _), show -v^2*t-A/t = -v^2*t+(-A/t) by ring,
    Real.exp_add]
  simp only [Complex.sub_re, Complex.re_ofNat, mul_assoc]

lemma cubicThetaDualHeat_integrable {v : ℝ} (hv : 0 < v) {s : ℂ}
    (hs : 1 < s.re) {A : ℝ} (hA : 0 ≤ A) :
    IntegrableOn (cubicThetaDualHeat v s A) (Ioi 0) := by
  have hm : AEStronglyMeasurable (cubicThetaDualHeat v s A) (volume.restrict (Ioi 0)) := by
    apply Measurable.aestronglyMeasurable
    unfold cubicThetaDualHeat
    fun_prop
  have hi := integrable_laplace_rpow (show 0 < s.re-1 by linarith) (sq_pos_of_pos hv)
  apply hi.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [cubicThetaDualHeat_norm v s A ht]
  have he : Real.exp (-A/t) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr hA) ht.le)
  calc
    _ ≤ t^(s.re-2)*Real.exp (-v^2*t)*1 :=
      mul_le_mul_of_nonneg_left he (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _))
    _ = _ := by rw [mul_one, show s.re-1-1 = s.re-2 by ring]

lemma cubicThetaDualHeat_norm_mass_bound {v : ℝ} (hv : 0 < v) {s : ℂ}
    (hs : 1 < s.re) {A : ℝ} (hA : 0 < A) :
    (∫ t in Ioi (0:ℝ), ‖cubicThetaDualHeat v s A t‖) ≤
      (2/A^2)*(Real.Gamma (s.re+1)*(v^2)^(-(s.re+1))) := by
  have hplus : 0 < s.re+1 := by linarith
  have hi := (integrable_laplace_rpow hplus (sq_pos_of_pos hv)).const_mul (2/A^2)
  calc
    _ ≤ ∫ t in Ioi (0:ℝ), (2/A^2)*(t^((s.re+1)-1)*Real.exp (-v^2*t)) := by
      apply integral_mono_ae (cubicThetaDualHeat_integrable hv hs hA.le).norm hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [cubicThetaDualHeat_norm v s A ht]
      calc
        _ ≤ t^(s.re-2)*Real.exp (-v^2*t)*((2/A^2)*t^2) := by
          exact mul_le_mul_of_nonneg_left (cubicTheta_inverse_heat_bound hA ht)
            (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _))
        _ = _ := by
          have he : t^(s.re-2)*t^2 = t^s.re := by
            rw [← Real.rpow_two, ← Real.rpow_add ht]
            congr 1
            ring
          rw [show (s.re+1)-1 = s.re by ring]
          calc
            _ = (2/A^2)*(t^(s.re-2)*t^2)*Real.exp (-v^2*t) := by ring
            _ = _ := by rw [he]; ring
    _ = _ := by rw [integral_const_mul, laplace_rpow hplus (sq_pos_of_pos hv)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaZeroFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero Fourier mode of the actual Eisenstein row expansion,
including its exact archimedean factor. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaDualHeat_zero_integral {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 1 < s.re) :
    (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s 0 t)=
      Complex.Gamma (s-1)*((v^2:ℝ):ℂ)^(1-s) := by
  have hi := cubicThetaLaplaceTerm_integral (1:ℂ) (sq_pos_of_pos hv)
    (show 0<(s-1).re by simp only [Complex.sub_re,Complex.one_re]; linarith)
  have he : (fun t => cubicThetaDualHeat v s 0 t)=cubicThetaLaplaceTerm 1 (v^2) (s-1) := by
    funext t
    simp only [cubicThetaDualHeat,cubicThetaLaplaceTerm,zero_div,sub_zero,one_mul]
    rw [show s-1-1=s-2 by ring]
  rw [he,hi]
  simp only [one_mul]
  rw [show -(s-1)=1-s by ring]

lemma cubicTheta_zero_height_factor {v n : ℝ} (hv : 0<v) (hn : 0<n) (s : ℂ) :
    ((v/n:ℝ):ℂ)^s*((v^2:ℝ):ℂ)^(1-s)=
      (v:ℂ)^(2-s)*(n:ℂ)^(-s) := by
  have hv0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hn0 := Complex.ofReal_ne_zero.mpr hn.ne'
  have hp : ((v^2:ℝ):ℂ)^(1-s)=(v:ℂ)^(2*(1-s)) := by
    rw [Complex.ofReal_pow,←Complex.cpow_nat_mul' (n:=2)
      (by rw [Complex.arg_ofReal_of_nonneg hv.le]; nlinarith [Real.pi_pos])
      (by rw [Complex.arg_ofReal_of_nonneg hv.le]; nlinarith [Real.pi_pos])]
    norm_num
  rw [hp,Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg hv.le hn.le,Complex.cpow_neg]
  calc
    _ = ((v:ℂ)^s*(v:ℂ)^(2*(1-s)))*((n:ℂ)^s)⁻¹ := by ring
    _ = _ := by
      rw [←Complex.cpow_add _ _ hv0]
      congr 2
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaNonzeroHeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonzero Fourier heat integral is entire in the Eisenstein
parameter: its positive and reciprocal exponential factors control both
ends of the Mellin integral. -/
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace CubicFirstMoment

def cubicThetaDoubleHeat (v A t : ℝ) : ℂ :=
  (Real.exp (-v^2*t-A/t):ℂ)

lemma cubicThetaDoubleHeat_continuous (v A : ℝ) :
    ContinuousOn (cubicThetaDoubleHeat v A) (Ioi 0) := by
  have h : ContinuousOn (fun t : ℝ => -v^2*t-A/t) (Ioi 0) :=
    (continuousOn_const.mul continuousOn_id).sub
      (continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt ht))
  exact Complex.continuous_ofReal.comp_continuousOn
    (Real.continuous_exp.comp_continuousOn h)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaQuadraticDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real coordinate derivatives of the quadratic powers occurring in
the hyperbolic Eisenstein kernel. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

lemma real_cpow_hasDerivAt {f : ℝ → ℝ} {x f' : ℝ}
    (hf : HasDerivAt f f' x) (hp : 0<f x) (r : ℂ) :
    HasDerivAt (fun t : ℝ => (f t:ℂ)^r)
      (r*(f x:ℂ)^(r-1)*(f':ℂ)) x := by
  have h := (Complex.hasStrictDerivAt_cpow_const (c:=r)
    (Complex.ofReal_mem_slitPlane.mpr hp)).hasDerivAt.scomp x hf.ofReal_comp
  change HasDerivAt (fun t : ℝ => (f t:ℂ)^r)
    ((f':ℂ)*(r*(f x:ℂ)^(r-1))) x at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

def cubicThetaQuadraticPower (r : ℂ) (b t : ℝ) : ℂ := ((t^2+b:ℝ):ℂ)^r

def cubicThetaQuadraticFirst (r : ℂ) (b t : ℝ) : ℂ :=
  2*r*(t:ℂ)*cubicThetaQuadraticPower (r-1) b t

def cubicThetaQuadraticSecond (r : ℂ) (b t : ℝ) : ℂ :=
  2*r*cubicThetaQuadraticPower (r-1) b t+
    4*r*(r-1)*(t:ℂ)^2*cubicThetaQuadraticPower (r-2) b t

lemma cubicThetaQuadratic_hasDerivAt (r : ℂ) (b x : ℝ) (hx : 0<x^2+b) :
    HasDerivAt (cubicThetaQuadraticPower r b) (cubicThetaQuadraticFirst r b x) x := by
  have hq : HasDerivAt (fun t : ℝ => t^2+b) (2*x) x := by
    convert ((hasDerivAt_id x).pow 2).add_const b using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
  have h := real_cpow_hasDerivAt hq hx r
  unfold cubicThetaQuadraticFirst cubicThetaQuadraticPower
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

lemma cubicThetaQuadraticFirst_hasDerivAt (r : ℂ) (b x : ℝ) (hx : 0<x^2+b) :
    HasDerivAt (cubicThetaQuadraticFirst r b) (cubicThetaQuadraticSecond r b x) x := by
  have h := ((hasDerivAt_id x).ofReal_comp.mul
    (cubicThetaQuadratic_hasDerivAt (r-1) b x hx)).const_mul (2*r)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
  · beta_reduce
    dsimp only [cubicThetaQuadraticFirst,Pi.mul_apply,id_eq]
    ring
  · dsimp only [cubicThetaQuadraticFirst,cubicThetaQuadraticSecond,id_eq]
    rw [show r-1-1=r-2 by ring]
    push_cast
    ring

lemma cubicThetaQuadratic_deriv (r : ℂ) (b x : ℝ) (hx : 0<x^2+b) :
    deriv (cubicThetaQuadraticPower r b) x=cubicThetaQuadraticFirst r b x :=
  (cubicThetaQuadratic_hasDerivAt r b x hx).deriv

theorem cubicThetaQuadratic_second_deriv (r : ℂ) (b x : ℝ) (hx : 0<x^2+b) :
    deriv (deriv (cubicThetaQuadraticPower r b)) x=cubicThetaQuadraticSecond r b x := by
  have hpos : ∀ᶠ t : ℝ in 𝓝 x, 0<t^2+b := by
    exact (isOpen_lt continuous_const ((continuous_pow 2).add_const b)).mem_nhds hx
  have he : deriv (cubicThetaQuadraticPower r b) =ᶠ[𝓝 x] cubicThetaQuadraticFirst r b := by
    filter_upwards [hpos] with t ht
    exact cubicThetaQuadratic_deriv r b t ht
  exact ((cubicThetaQuadraticFirst_hasDerivAt r b x hx).congr_of_eventuallyEq he).deriv

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaVerticalDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical derivatives of the height-weighted hyperbolic kernel. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

def cubicThetaVerticalKernel (s : ℂ) (b v : ℝ) : ℂ :=
  (v:ℂ)^s*cubicThetaQuadraticPower (-s) b v

def cubicThetaVerticalFirst (s : ℂ) (b v : ℝ) : ℂ :=
  s*(v:ℂ)^(s-1)*cubicThetaQuadraticPower (-s) b v+
    (v:ℂ)^s*cubicThetaQuadraticFirst (-s) b v

def cubicThetaVerticalSecond (s : ℂ) (b v : ℝ) : ℂ :=
  s*(s-1)*(v:ℂ)^(s-2)*cubicThetaQuadraticPower (-s) b v+
    2*s*(v:ℂ)^(s-1)*cubicThetaQuadraticFirst (-s) b v+
    (v:ℂ)^s*cubicThetaQuadraticSecond (-s) b v

lemma cubicThetaHeightPower_hasDerivAt (s : ℂ) {v : ℝ} (hv : 0<v) :
    HasDerivAt (fun t : ℝ => (t:ℂ)^s) (s*(v:ℂ)^(s-1)) v :=
  (Complex.hasStrictDerivAt_cpow_const (c:=s)
    (Complex.ofReal_mem_slitPlane.mpr hv)).hasDerivAt.comp_ofReal

lemma cubicThetaVertical_hasDerivAt (s : ℂ) {b v : ℝ} (hb : 0 ≤ b) (hv : 0<v) :
    HasDerivAt (cubicThetaVerticalKernel s b) (cubicThetaVerticalFirst s b v) v :=
  (cubicThetaHeightPower_hasDerivAt s hv).mul
    (cubicThetaQuadratic_hasDerivAt (-s) b v (add_pos_of_pos_of_nonneg (sq_pos_of_pos hv) hb))

lemma cubicThetaVerticalFirst_hasDerivAt (s : ℂ) {b v : ℝ} (hb : 0 ≤ b) (hv : 0<v) :
    HasDerivAt (cubicThetaVerticalFirst s b) (cubicThetaVerticalSecond s b v) v := by
  have hR : 0<v^2+b := add_pos_of_pos_of_nonneg (sq_pos_of_pos hv) hb
  have h₁ := ((cubicThetaHeightPower_hasDerivAt (s-1) hv).const_mul s).mul
    (cubicThetaQuadratic_hasDerivAt (-s) b v hR)
  have h₂ := (cubicThetaHeightPower_hasDerivAt s hv).mul
    (cubicThetaQuadraticFirst_hasDerivAt (-s) b v hR)
  refine (h₁.add h₂).congr_deriv ?_
  · unfold cubicThetaVerticalSecond
    rw [show s-1-1=s-2 by ring]
    ring

lemma cubicThetaVertical_deriv (s : ℂ) {b v : ℝ} (hb : 0 ≤ b) (hv : 0<v) :
    deriv (cubicThetaVerticalKernel s b) v=cubicThetaVerticalFirst s b v :=
  (cubicThetaVertical_hasDerivAt s hb hv).deriv

theorem cubicThetaVertical_second_deriv (s : ℂ) {b v : ℝ} (hb : 0 ≤ b) (hv : 0<v) :
    deriv (deriv (cubicThetaVerticalKernel s b)) v=cubicThetaVerticalSecond s b v := by
  have he : deriv (cubicThetaVerticalKernel s b) =ᶠ[𝓝 v] cubicThetaVerticalFirst s b := by
    filter_upwards [eventually_gt_nhds hv] with t ht
    exact cubicThetaVertical_deriv s hb ht
  exact ((cubicThetaVerticalFirst_hasDerivAt s hb hv).congr_of_eventuallyEq he).deriv

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaKernelEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The hyperbolic eigenvalue equation for the actual height-power
kernel, in Cartesian coordinates on the upper half-space. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaCartesianKernel (s : ℂ) (x y v : ℝ) : ℂ :=
  (v:ℂ)^s*((x^2+y^2+v^2:ℝ):ℂ)^(-s)

lemma cubicThetaCartesian_horizontal_second (s : ℂ) (x y : ℝ)
    {v : ℝ} (hv : 0<v) :
    deriv (deriv (fun t : ℝ => cubicThetaCartesianKernel s t y v)) x=
      (v:ℂ)^s*cubicThetaQuadraticSecond (-s) (y^2+v^2) x := by
  have he : (fun t : ℝ => cubicThetaCartesianKernel s t y v)=
      (fun t : ℝ => (v:ℂ)^s*cubicThetaQuadraticPower (-s) (y^2+v^2) t) := by
    funext t
    unfold cubicThetaCartesianKernel cubicThetaQuadraticPower
    rw [add_assoc]
  rw [he]
  simp_rw [deriv_const_mul_field']
  rw [cubicThetaQuadratic_second_deriv (-s) (y^2+v^2) x
    (by nlinarith [sq_nonneg x,sq_nonneg y,sq_pos_of_pos hv])]

lemma cubicThetaCartesian_y_second (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    deriv (deriv (fun t : ℝ => cubicThetaCartesianKernel s x t v)) y=
      (v:ℂ)^s*cubicThetaQuadraticSecond (-s) (x^2+v^2) y := by
  have he : (fun t : ℝ => cubicThetaCartesianKernel s x t v)=
      (fun t : ℝ => cubicThetaCartesianKernel s t x v) := by
    funext t
    unfold cubicThetaCartesianKernel
    rw [add_comm (x^2) (t^2)]
  rw [he]
  exact cubicThetaCartesian_horizontal_second s y x hv

lemma cubicThetaCartesian_vertical (s : ℂ) (x y : ℝ) :
    (fun t : ℝ => cubicThetaCartesianKernel s x y t)=
      cubicThetaVerticalKernel s (x^2+y^2) := by
  funext t
  unfold cubicThetaCartesianKernel cubicThetaVerticalKernel cubicThetaQuadraticPower
  rw [add_comm (x^2+y^2) (t^2)]

lemma cubicThetaKernel_jet_equation (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    (v:ℂ)^2*((v:ℂ)^s*cubicThetaQuadraticSecond (-s) (y^2+v^2) x+
      (v:ℂ)^s*cubicThetaQuadraticSecond (-s) (x^2+v^2) y+
      cubicThetaVerticalSecond s (x^2+y^2) v)-
        (v:ℂ)*cubicThetaVerticalFirst s (x^2+y^2) v=
      s*(s-2)*cubicThetaCartesianKernel s x y v := by
  let R : ℝ := x^2+y^2+v^2
  have hR : 0<R := by dsimp [R]; nlinarith [sq_nonneg x,sq_nonneg y,sq_pos_of_pos hv]
  have hRc : (R:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hvc : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hx : x^2+(y^2+v^2)=R := by dsimp [R]; ring
  have hy : y^2+(x^2+v^2)=R := by dsimp [R]; ring
  have hz : v^2+(x^2+y^2)=R := by dsimp [R]; ring
  simp only [cubicThetaQuadraticSecond,cubicThetaVerticalSecond,cubicThetaVerticalFirst,
    cubicThetaQuadraticFirst,cubicThetaQuadraticPower,cubicThetaCartesianKernel]
  rw [hx,hy,hz]
  change (v:ℂ)^2*((v:ℂ)^s*(2*(-s)*(R:ℂ)^(-s-1)+
      4*(-s)*(-s-1)*(x:ℂ)^2*(R:ℂ)^(-s-2))+
    (v:ℂ)^s*(2*(-s)*(R:ℂ)^(-s-1)+4*(-s)*(-s-1)*(y:ℂ)^2*(R:ℂ)^(-s-2))+
    (s*(s-1)*(v:ℂ)^(s-2)*(R:ℂ)^(-s)+
      2*s*(v:ℂ)^(s-1)*(2*(-s)*(v:ℂ)*(R:ℂ)^(-s-1))+
      (v:ℂ)^s*(2*(-s)*(R:ℂ)^(-s-1)+4*(-s)*(-s-1)*(v:ℂ)^2*(R:ℂ)^(-s-2))))-
    (v:ℂ)*(s*(v:ℂ)^(s-1)*(R:ℂ)^(-s)+
      (v:ℂ)^s*(2*(-s)*(v:ℂ)*(R:ℂ)^(-s-1)))=
        s*(s-2)*((v:ℂ)^s*(R:ℂ)^(-s))
  rw [Complex.cpow_sub (-s) 1 hRc,Complex.cpow_sub (-s) 2 hRc,
    Complex.cpow_sub s 2 hvc,Complex.cpow_sub s 1 hvc]
  norm_num only [Complex.cpow_one,Complex.cpow_ofNat]
  have he : (R:ℂ)=(x:ℂ)^2+(y:ℂ)^2+(v:ℂ)^2 := by
    dsimp [R]
    push_cast
    rfl
  field_simp
  rw [he]
  ring

theorem cubicThetaCartesian_eigenvalue (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    (v:ℂ)^2*(deriv (deriv (fun t : ℝ => cubicThetaCartesianKernel s t y v)) x+
      deriv (deriv (fun t : ℝ => cubicThetaCartesianKernel s x t v)) y+
      deriv (deriv (fun t : ℝ => cubicThetaCartesianKernel s x y t)) v)-
        (v:ℂ)*deriv (fun t : ℝ => cubicThetaCartesianKernel s x y t) v=
      s*(s-2)*cubicThetaCartesianKernel s x y v := by
  rw [cubicThetaCartesian_horizontal_second s x y hv,
    cubicThetaCartesian_y_second s x y hv,cubicThetaCartesian_vertical,
    cubicThetaVertical_second_deriv s (add_nonneg (sq_nonneg x) (sq_nonneg y)) hv,
    cubicThetaVertical_deriv s (add_nonneg (sq_nonneg x) (sq_nonneg y)) hv]
  exact cubicThetaKernel_jet_equation s x y hv

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHyperbolicOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The upper-half-space differential operator used by the Eisenstein
series, with its horizontal translation and local-equality rules. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

def cubicThetaHyperbolicOperator (F : ℝ → ℝ → ℝ → ℂ) (x y v : ℝ) : ℂ :=
  (v:ℂ)^2*(deriv (deriv (fun t : ℝ => F t y v)) x+
    deriv (deriv (fun t : ℝ => F x t v)) y+
    deriv (deriv (fun t : ℝ => F x y t)) v)-
      (v:ℂ)*deriv (fun t : ℝ => F x y t) v

lemma cubicTheta_deriv_translate (f : ℝ → ℂ) (a : ℝ) :
    deriv (fun t : ℝ => f (t+a))=(fun t : ℝ => deriv f (t+a)) :=
  funext (fun t => deriv_comp_add_const f a t)

lemma cubicThetaHyperbolicOperator_translate (F : ℝ → ℝ → ℝ → ℂ)
    (C : ℂ) (a b x y v : ℝ) :
    cubicThetaHyperbolicOperator (fun u w t => C*F (u+a) (w+b) t) x y v=
      C*cubicThetaHyperbolicOperator F (x+a) (y+b) v := by
  have hx : deriv (deriv (fun t : ℝ => F (t+a) (y+b) v)) x=
      deriv (deriv (fun t : ℝ => F t (y+b) v)) (x+a) := by
    rw [cubicTheta_deriv_translate (fun t : ℝ => F t (y+b) v) a]
    exact deriv_comp_add_const (deriv (fun t : ℝ => F t (y+b) v)) a x
  have hy : deriv (deriv (fun t : ℝ => F (x+a) (t+b) v)) y=
      deriv (deriv (fun t : ℝ => F (x+a) t v)) (y+b) := by
    rw [cubicTheta_deriv_translate (fun t : ℝ => F (x+a) t v) b]
    exact deriv_comp_add_const (deriv (fun t : ℝ => F (x+a) t v)) b y
  unfold cubicThetaHyperbolicOperator
  simp only [deriv_const_mul_field']
  rw [hx,hy]
  ring

lemma cubicThetaHyperbolicOperator_congr {F G : ℝ → ℝ → ℝ → ℂ}
    (hFG : ∀ x y v, 0<v → F x y v=G x y v) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator F x y v=cubicThetaHyperbolicOperator G x y v := by
  have hx : (fun t : ℝ => F t y v)=(fun t : ℝ => G t y v) :=
    funext (fun t => hFG t y v hv)
  have hy : (fun t : ℝ => F x t v)=(fun t : ℝ => G x t v) :=
    funext (fun t => hFG x t v hv)
  have he {u : ℝ} (hu : 0<u) : (fun t : ℝ => F x y t) =ᶠ[𝓝 u] (fun t : ℝ => G x y t) := by
    filter_upwards [eventually_gt_nhds hu] with t ht
    exact hFG x y t ht
  have hd : deriv (fun t : ℝ => F x y t) =ᶠ[𝓝 v] deriv (fun t : ℝ => G x y t) := by
    filter_upwards [eventually_gt_nhds hv] with t ht
    exact (he ht).deriv_eq
  unfold cubicThetaHyperbolicOperator
  rw [hx,hy,hd.deriv_eq,(he hv).deriv_eq]

theorem cubicThetaHyperbolicOperator_kernel (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator (cubicThetaCartesianKernel s) x y v=
      s*(s-2)*cubicThetaCartesianKernel s x y v :=
  cubicThetaCartesian_eigenvalue s x y hv

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHeightEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The leading cusp-height term satisfies the same eigenvalue
equation as the nonzero Eisenstein summands. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaHeightPower_deriv (s : ℂ) {v : ℝ} (hv : 0<v) :
    deriv (fun t : ℝ => (t:ℂ)^s) v=s*(v:ℂ)^(s-1) :=
  (cubicThetaHeightPower_hasDerivAt s hv).deriv

lemma cubicThetaHeightPower_second_deriv (s : ℂ) {v : ℝ} (hv : 0<v) :
    deriv (deriv (fun t : ℝ => (t:ℂ)^s)) v=s*(s-1)*(v:ℂ)^(s-2) := by
  have he : deriv (fun t : ℝ => (t:ℂ)^s) =ᶠ[𝓝 v]
      (fun t : ℝ => s*(t:ℂ)^(s-1)) := by
    filter_upwards [eventually_gt_nhds hv] with t ht
    exact cubicThetaHeightPower_deriv s ht
  have hd := (cubicThetaHeightPower_hasDerivAt (s-1) hv).const_mul s
  have hd' := (hd.congr_of_eventuallyEq he).deriv
  simpa only [show s-1-1=s-2 by ring,mul_assoc] using hd'

theorem cubicThetaHyperbolicOperator_height (s : ℂ) (x y : ℝ)
    {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator (fun _ _ t => (t:ℂ)^s) x y v=
      s*(s-2)*(v:ℂ)^s := by
  have hn := Complex.ofReal_ne_zero.mpr hv.ne'
  unfold cubicThetaHyperbolicOperator
  simp only [deriv_const',deriv_const,zero_add]
  rw [cubicThetaHeightPower_second_deriv s hv,cubicThetaHeightPower_deriv s hv,
    Complex.cpow_sub s 2 hn,Complex.cpow_sub s 1 hn]
  norm_num only [Complex.cpow_one,Complex.cpow_ofNat]
  field_simp
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaKernelAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real analyticity of the coordinate slices of the kernel. This
supplies both differentiability levels needed by the spectral operator. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaHeightPower_analytic (s : ℂ) {v : ℝ} (hv : 0<v) :
    AnalyticAt ℝ (fun t : ℝ => (t:ℂ)^s) v := by
  have h : AnalyticAt ℂ (fun z : ℂ => z^s) (v:ℂ) :=
    analyticAt_id.cpow analyticAt_const (Complex.ofReal_mem_slitPlane.mpr hv)
  exact h.restrictScalars.comp (Complex.ofRealCLM.analyticAt v)

lemma cubicThetaQuadratic_analytic (s : ℂ) (b x : ℝ) (hx : 0<x^2+b) :
    AnalyticAt ℝ (cubicThetaQuadraticPower s b) x := by
  have hq : AnalyticAt ℝ (fun t : ℝ => t^2+b) x := by fun_prop
  exact (cubicThetaHeightPower_analytic s hx).comp (f:=fun t : ℝ => t^2+b) (x:=x) hq

lemma cubicThetaCartesian_x_analytic (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    AnalyticAt ℝ (fun t : ℝ => cubicThetaCartesianKernel s t y v) x := by
  have he : (fun t : ℝ => cubicThetaCartesianKernel s t y v)=
      (fun t : ℝ => (v:ℂ)^s*cubicThetaQuadraticPower (-s) (y^2+v^2) t) := by
    funext t
    unfold cubicThetaCartesianKernel cubicThetaQuadraticPower
    rw [add_assoc]
  rw [he]
  exact analyticAt_const.mul (cubicThetaQuadratic_analytic (-s) (y^2+v^2) x
    (by nlinarith [sq_nonneg x,sq_nonneg y,sq_pos_of_pos hv]))

lemma cubicThetaCartesian_y_analytic (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    AnalyticAt ℝ (fun t : ℝ => cubicThetaCartesianKernel s x t v) y := by
  have he : (fun t : ℝ => cubicThetaCartesianKernel s x t v)=
      (fun t : ℝ => cubicThetaCartesianKernel s t x v) := by
    funext t
    unfold cubicThetaCartesianKernel
    rw [add_comm (x^2) (t^2)]
  rw [he]
  exact cubicThetaCartesian_x_analytic s y x hv

lemma cubicThetaCartesian_v_analytic (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    AnalyticAt ℝ (fun t : ℝ => cubicThetaCartesianKernel s x y t) v := by
  rw [cubicThetaCartesian_vertical]
  exact (cubicThetaHeightPower_analytic s hv).mul
    (cubicThetaQuadratic_analytic (-s) (x^2+y^2) v
      (by nlinarith [sq_nonneg x,sq_nonneg y,sq_pos_of_pos hv]))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete cusp cutoff and compact support of its derivatives. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace CubicFirstMoment

def cubicThetaCuspCutoff (v : ℝ) : ℂ := Real.smoothTransition (v-1)

lemma cubicThetaCuspCutoff_zero {v : ℝ} (hv : v ≤ 1) : cubicThetaCuspCutoff v=0 := by
  simp only [cubicThetaCuspCutoff,Real.smoothTransition.zero_of_nonpos (by linarith : v-1 ≤ 0),
    Complex.ofReal_zero]

lemma cubicThetaCuspCutoff_one {v : ℝ} (hv : 2 ≤ v) : cubicThetaCuspCutoff v=1 := by
  simp only [cubicThetaCuspCutoff,Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ v-1),
    Complex.ofReal_one]

lemma cubicThetaCuspCutoff_smooth : ContDiff ℝ ∞ cubicThetaCuspCutoff :=
  Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop))

lemma cubicThetaCuspCutoff_derivatives_zero {v : ℝ} (hv : v<1 ∨ 2<v) :
    deriv cubicThetaCuspCutoff v=0 ∧ deriv (deriv cubicThetaCuspCutoff) v=0 := by
  have he : ∃ C : ℂ, cubicThetaCuspCutoff =ᶠ[𝓝 v] (fun _ => C) := by
    rcases hv with hv | hv
    · refine ⟨0,?_⟩
      filter_upwards [eventually_lt_nhds hv] with t ht
      exact cubicThetaCuspCutoff_zero ht.le
    · refine ⟨1,?_⟩
      filter_upwards [eventually_gt_nhds hv] with t ht
      exact cubicThetaCuspCutoff_one ht.le
  obtain ⟨C,hC⟩ := he
  refine ⟨?_,?_⟩
  · simpa only [deriv_const] using hC.deriv_eq
  · simpa only [deriv_const',deriv_const] using hC.deriv.deriv_eq

lemma cubicThetaCuspCutoff_deriv_compact : HasCompactSupport (deriv cubicThetaCuspCutoff) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro v hv
  by_contra h
  have he : v<1 ∨ 2<v := by simpa only [mem_Icc,not_and_or,not_le] using h
  exact hv (cubicThetaCuspCutoff_derivatives_zero he).1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspCutoffBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative bounds for the fixed cusp cutoff. Its radial derivative
is supported on the compact annulus with heights between one and two. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaCuspCutoff_norm (v : ℝ) : ‖cubicThetaCuspCutoff v‖≤1 := by
  rw [cubicThetaCuspCutoff,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

lemma cubicThetaCuspCutoff_deriv_bound :
    ∃ B≥0, ∀ v : ℝ, v^2*‖deriv cubicThetaCuspCutoff v‖^2≤
      (Icc (1:ℝ) 2).indicator (fun _ => B) v := by
  classical
  have hcont : Continuous (fun v : ℝ => v^2*‖deriv cubicThetaCuspCutoff v‖^2) :=
    (continuous_id.pow 2).mul ((cubicThetaCuspCutoff_smooth.continuous_deriv (by simp)).norm.pow 2)
  have hc : HasCompactSupport (fun v : ℝ => v^2*‖deriv cubicThetaCuspCutoff v‖^2) :=
    (cubicThetaCuspCutoff_deriv_compact.comp_left (g:=fun z : ℂ => ‖z‖^2) (by simp)).mul_left
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hcont
  refine ⟨max C 0,le_max_right _ _,fun v => ?_⟩
  by_cases hv : v∈Icc (1:ℝ) 2
  · rw [indicator_of_mem hv]
    exact (le_abs_self _).trans ((hC v).trans (le_max_left _ _))
  · have hv' : v<1 ∨ 2<v := by simpa only [mem_Icc,not_and_or,not_le] using hv
    rw [indicator_of_notMem hv,(cubicThetaCuspCutoff_derivatives_zero hv').1,
      norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero]

lemma cubicThetaComplex_norm_add_young (a b : ℂ) {ε : ℝ} (hε : 0<ε) :
    ‖a+b‖^2≤(1+ε)*‖b‖^2+(1+ε⁻¹)*‖a‖^2 := by
  have ht := norm_add_le a b
  have hs := mul_self_le_mul_self (_root_.norm_nonneg (a+b)) ht
  have hy := two_mul_le_add_mul_sq (a:=‖b‖) (b:=‖a‖) hε
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSiegelReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Siegel-set reduction for the full Eisenstein modular group, and
its finite translate cover of the actual principal level-three quotient. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

/-- A single full-group cusp chart with a uniform positive lower height. -/
def cubicThetaSiegelSet : Set (ℂ × ℝ) :=
  {p | 0<p.2 ∧ Complex.normSq p.1 ≤ 3/4 ∧ 1/2 ≤ p.2}

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactCoreCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite compact-core and cusp cover of the principal quotient. All
charts are actual hyperbolic transformations of the single Siegel set. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaSiegelCore (V : ℝ) : Set (ℂ × ℝ) :=
  Metric.closedBall (0:ℂ) 1 ×ˢ Icc (1/2:ℝ) V

lemma cubicThetaSiegelCore_compact (V : ℝ) : IsCompact (cubicThetaSiegelCore V) :=
  (isCompact_closedBall (0:ℂ) 1).prod isCompact_Icc

lemma cubicThetaSiegelCore_positive {V : ℝ} {p : ℂ × ℝ}
    (hp : p∈cubicThetaSiegelCore V) : 0<p.2 := by
  have h : (1/2:ℝ) ≤ p.2 := hp.2.1
  linarith

lemma cubicThetaSiegelSet_mem_core {V : ℝ} {q : ℂ × ℝ} (hq : q∈cubicThetaSiegelSet)
    (hV : q.2 ≤ V) : q∈cubicThetaSiegelCore V := by
  refine ⟨?_,hq.2.2,hV⟩
  rw [Metric.mem_closedBall,dist_zero_right]
  have hn := hq.2.1
  rw [Complex.normSq_eq_norm_sq] at hn
  nlinarith [_root_.norm_nonneg q.1]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaNormalizedJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative derivative formulas used to dominate the differentiated
Eisenstein summands by the original absolutely convergent series. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaQuadraticFirst_normalized (r : ℂ) (b x : ℝ) (hx : 0<x^2+b) :
    cubicThetaQuadraticFirst r b x=cubicThetaQuadraticPower r b x*
      (2*r*(x:ℂ)/((x^2+b:ℝ):ℂ)) := by
  have hn := Complex.ofReal_ne_zero.mpr hx.ne'
  unfold cubicThetaQuadraticFirst cubicThetaQuadraticPower
  rw [Complex.cpow_sub r 1 hn,Complex.cpow_one]
  ring

lemma cubicThetaQuadraticSecond_normalized (r : ℂ) (b x : ℝ) (hx : 0<x^2+b) :
    cubicThetaQuadraticSecond r b x=cubicThetaQuadraticPower r b x*
      (2*r/((x^2+b:ℝ):ℂ)+4*r*(r-1)*(x:ℂ)^2/((x^2+b:ℝ):ℂ)^2) := by
  have hn := Complex.ofReal_ne_zero.mpr hx.ne'
  unfold cubicThetaQuadraticSecond cubicThetaQuadraticPower
  rw [Complex.cpow_sub r 1 hn,Complex.cpow_sub r 2 hn]
  norm_num only [Complex.cpow_one,Complex.cpow_ofNat]
  ring

lemma cubicThetaVerticalFirst_normalized (s : ℂ) {b v : ℝ} (hb : 0 ≤ b) (hv : 0<v) :
    cubicThetaVerticalFirst s b v=cubicThetaVerticalKernel s b v*
      (s/(v:ℂ)-2*s*(v:ℂ)/((v^2+b:ℝ):ℂ)) := by
  have hR : 0<v^2+b := add_pos_of_pos_of_nonneg (sq_pos_of_pos hv) hb
  have hn := Complex.ofReal_ne_zero.mpr hv.ne'
  unfold cubicThetaVerticalFirst cubicThetaVerticalKernel
  rw [cubicThetaQuadraticFirst_normalized (-s) b v hR,
    Complex.cpow_sub s 1 hn,Complex.cpow_one]
  ring

lemma cubicThetaVerticalSecond_normalized (s : ℂ) {b v : ℝ} (hb : 0 ≤ b) (hv : 0<v) :
    cubicThetaVerticalSecond s b v=cubicThetaVerticalKernel s b v*
      (s*(s-1)/(v:ℂ)^2-(4*s^2+2*s)/((v^2+b:ℝ):ℂ)+
        4*s*(s+1)*(v:ℂ)^2/((v^2+b:ℝ):ℂ)^2) := by
  have hR : 0<v^2+b := add_pos_of_pos_of_nonneg (sq_pos_of_pos hv) hb
  have hRn := Complex.ofReal_ne_zero.mpr hR.ne'
  have hn := Complex.ofReal_ne_zero.mpr hv.ne'
  unfold cubicThetaVerticalSecond cubicThetaVerticalKernel
  rw [cubicThetaQuadraticFirst_normalized (-s) b v hR,
    cubicThetaQuadraticSecond_normalized (-s) b v hR,
    Complex.cpow_sub s 2 hn,Complex.cpow_sub s 1 hn]
  norm_num only [Complex.cpow_one,Complex.cpow_ofNat]
  field_simp
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaKernelRatios
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform coordinate ratios for differentiating the hyperbolic
kernel on a region with positive lower height. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaCartesian_radius_pos (x y : ℝ) {v : ℝ} (hv : 0<v) :
    0<x^2+y^2+v^2 := by
  nlinarith [sq_nonneg x,sq_nonneg y,sq_pos_of_pos hv]

lemma cubicTheta_horizontal_ratio (x y : ℝ) {v : ℝ} (hv : 0<v) :
    |x|/(x^2+y^2+v^2) ≤ 1/v := by
  apply (div_le_div_iff₀ (cubicThetaCartesian_radius_pos x y hv) hv).mpr
  nlinarith [sq_abs x,sq_nonneg (v-|x|),sq_nonneg y]

lemma cubicTheta_vertical_ratio (x y : ℝ) {v : ℝ} (hv : 0<v) :
    v/(x^2+y^2+v^2) ≤ 1/v := by
  apply (div_le_div_iff₀ (cubicThetaCartesian_radius_pos x y hv) hv).mpr
  nlinarith [sq_nonneg x,sq_nonneg y]

lemma cubicTheta_radius_inverse (x y : ℝ) {v : ℝ} (hv : 0<v) :
    1/(x^2+y^2+v^2) ≤ 1/v^2 :=
  one_div_le_one_div_of_le (sq_pos_of_pos hv) (by nlinarith [sq_nonneg x,sq_nonneg y])

lemma cubicTheta_horizontal_square_ratio (x y : ℝ) {v : ℝ} (hv : 0<v) :
    x^2/(x^2+y^2+v^2)^2 ≤ 1/v^2 := by
  have h := (sq_le_sq₀ (div_nonneg (abs_nonneg x) (cubicThetaCartesian_radius_pos x y hv).le)
    (one_div_pos.mpr hv).le).mpr (cubicTheta_horizontal_ratio x y hv)
  simpa only [div_pow,sq_abs,one_pow] using h

lemma cubicTheta_vertical_square_ratio (x y : ℝ) {v : ℝ} (hv : 0<v) :
    v^2/(x^2+y^2+v^2)^2 ≤ 1/v^2 := by
  have h := (sq_le_sq₀ (div_nonneg hv.le (cubicThetaCartesian_radius_pos x y hv).le)
    (one_div_pos.mpr hv).le).mpr (cubicTheta_vertical_ratio x y hv)
  simpa only [div_pow,one_pow] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaKernelFirstBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform first-coordinate derivative bounds for the kernel. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaCartesian_x_deriv (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    deriv (fun t : ℝ => cubicThetaCartesianKernel s t y v) x=
      cubicThetaCartesianKernel s x y v*
        (-2*s*(x:ℂ)/((x^2+y^2+v^2:ℝ):ℂ)) := by
  have hp : 0<x^2+(y^2+v^2) := by
    nlinarith [sq_nonneg x,sq_nonneg y,sq_pos_of_pos hv]
  have he : (fun t : ℝ => cubicThetaCartesianKernel s t y v)=
      (fun t : ℝ => (v:ℂ)^s*cubicThetaQuadraticPower (-s) (y^2+v^2) t) := by
    funext t
    unfold cubicThetaCartesianKernel cubicThetaQuadraticPower
    rw [add_assoc]
  rw [he,deriv_const_mul_field,cubicThetaQuadratic_deriv (-s) (y^2+v^2) x hp,
    cubicThetaQuadraticFirst_normalized (-s) (y^2+v^2) x hp]
  unfold cubicThetaQuadraticPower cubicThetaCartesianKernel
  rw [add_assoc]
  ring

theorem cubicThetaCartesian_x_deriv_bound (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ‖deriv (fun t : ℝ => cubicThetaCartesianKernel s t y v) x‖ ≤
      ‖cubicThetaCartesianKernel s x y v‖*(2*‖s‖/v) := by
  rw [cubicThetaCartesian_x_deriv s x y hv,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
  rw [norm_div,norm_mul,norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_real,
    Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_pos (cubicThetaCartesian_radius_pos x y hv)]
  calc
    _ = (2*‖s‖)*(|x|/(x^2+y^2+v^2)) := by ring
    _ ≤ (2*‖s‖)*(1/v) := mul_le_mul_of_nonneg_left
      (cubicTheta_horizontal_ratio x y hv) (by positivity)
    _ = _ := by ring

lemma cubicThetaCartesian_v_deriv (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    deriv (fun t : ℝ => cubicThetaCartesianKernel s x y t) v=
      cubicThetaCartesianKernel s x y v*
        (s/(v:ℂ)-2*s*(v:ℂ)/((x^2+y^2+v^2:ℝ):ℂ)) := by
  rw [cubicThetaCartesian_vertical,cubicThetaVertical_deriv s
    (add_nonneg (sq_nonneg x) (sq_nonneg y)) hv,
    cubicThetaVerticalFirst_normalized s (add_nonneg (sq_nonneg x) (sq_nonneg y)) hv]
  unfold cubicThetaVerticalKernel cubicThetaQuadraticPower cubicThetaCartesianKernel
  rw [add_comm (v^2) (x^2+y^2)]

theorem cubicThetaCartesian_v_deriv_bound (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ‖deriv (fun t : ℝ => cubicThetaCartesianKernel s x y t) v‖ ≤
      ‖cubicThetaCartesianKernel s x y v‖*(3*‖s‖/v) := by
  rw [cubicThetaCartesian_v_deriv s x y hv,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
  apply (norm_sub_le _ _).trans
  rw [norm_div,norm_div,norm_mul,norm_mul,Complex.norm_ofNat,Complex.norm_real,
    Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hv,
    abs_of_pos (cubicThetaCartesian_radius_pos x y hv)]
  calc
    _ = ‖s‖/v+(2*‖s‖)*(v/(x^2+y^2+v^2)) := by ring
    _ ≤ ‖s‖/v+(2*‖s‖)*(1/v) := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (cubicTheta_vertical_ratio x y hv)
        (show 0≤2*‖s‖ by positivity))
    _ = _ := by ring

lemma cubicThetaCartesian_swap (s : ℂ) (x y v : ℝ) :
    cubicThetaCartesianKernel s x y v=cubicThetaCartesianKernel s y x v := by
  unfold cubicThetaCartesianKernel
  rw [add_comm (x^2) (y^2)]

theorem cubicThetaCartesian_y_deriv_bound (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ‖deriv (fun t : ℝ => cubicThetaCartesianKernel s x t v) y‖ ≤
      ‖cubicThetaCartesianKernel s x y v‖*(2*‖s‖/v) := by
  simpa only [cubicThetaCartesian_swap s x] using cubicThetaCartesian_x_deriv_bound s y x hv

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaKernelSecondBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative bounds for the actual second coordinate derivatives. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaCartesian_x_second_normalized (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    deriv (deriv (fun t : ℝ => cubicThetaCartesianKernel s t y v)) x=
      cubicThetaCartesianKernel s x y v*
        (-2*s/((x^2+y^2+v^2:ℝ):ℂ)+
          4*s*(s+1)*(x:ℂ)^2/((x^2+y^2+v^2:ℝ):ℂ)^2) := by
  rw [cubicThetaCartesian_horizontal_second s x y hv,
    cubicThetaQuadraticSecond_normalized (-s) (y^2+v^2) x
      (by nlinarith [sq_nonneg x,sq_nonneg y,sq_pos_of_pos hv])]
  unfold cubicThetaCartesianKernel cubicThetaQuadraticPower
  rw [add_assoc]
  ring

theorem cubicThetaCartesian_x_second_bound (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ‖deriv (deriv (fun t : ℝ => cubicThetaCartesianKernel s t y v)) x‖ ≤
      ‖cubicThetaCartesianKernel s x y v‖*((2*‖s‖+4*‖s‖*‖s+1‖)/v^2) := by
  rw [cubicThetaCartesian_x_second_normalized s x y hv,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
  apply (norm_add_le _ _).trans
  rw [norm_div,norm_div,norm_mul,norm_mul,norm_mul,norm_mul,
    norm_neg,Complex.norm_ofNat,Complex.norm_ofNat,norm_pow,norm_pow,
    Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_pos (cubicThetaCartesian_radius_pos x y hv),sq_abs]
  calc
    _ = (2*‖s‖)*(1/(x^2+y^2+v^2))+
      (4*‖s‖*‖s+1‖)*(x^2/(x^2+y^2+v^2)^2) := by ring
    _ ≤ (2*‖s‖)*(1/v^2)+(4*‖s‖*‖s+1‖)*(1/v^2) :=
      add_le_add (mul_le_mul_of_nonneg_left (cubicTheta_radius_inverse x y hv) (by positivity))
        (mul_le_mul_of_nonneg_left (cubicTheta_horizontal_square_ratio x y hv) (by positivity))
    _ = _ := by ring

theorem cubicThetaCartesian_y_second_bound (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ‖deriv (deriv (fun t : ℝ => cubicThetaCartesianKernel s x t v)) y‖ ≤
      ‖cubicThetaCartesianKernel s x y v‖*((2*‖s‖+4*‖s‖*‖s+1‖)/v^2) := by
  simpa only [cubicThetaCartesian_swap s x] using cubicThetaCartesian_x_second_bound s y x hv

lemma cubicThetaCartesian_v_second_normalized (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    deriv (deriv (fun t : ℝ => cubicThetaCartesianKernel s x y t)) v=
      cubicThetaCartesianKernel s x y v*
        (s*(s-1)/(v:ℂ)^2-(4*s^2+2*s)/((x^2+y^2+v^2:ℝ):ℂ)+
          4*s*(s+1)*(v:ℂ)^2/((x^2+y^2+v^2:ℝ):ℂ)^2) := by
  rw [cubicThetaCartesian_vertical,cubicThetaVertical_second_deriv s
    (add_nonneg (sq_nonneg x) (sq_nonneg y)) hv,
    cubicThetaVerticalSecond_normalized s (add_nonneg (sq_nonneg x) (sq_nonneg y)) hv]
  unfold cubicThetaVerticalKernel cubicThetaQuadraticPower cubicThetaCartesianKernel
  rw [add_comm (v^2) (x^2+y^2)]

theorem cubicThetaCartesian_v_second_bound (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ‖deriv (deriv (fun t : ℝ => cubicThetaCartesianKernel s x y t)) v‖ ≤
      ‖cubicThetaCartesianKernel s x y v‖*
        ((‖s*(s-1)‖+‖4*s^2+2*s‖+4*‖s‖*‖s+1‖)/v^2) := by
  rw [cubicThetaCartesian_v_second_normalized s x y hv,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) le_rfl).trans
  simp only [norm_div,norm_mul,norm_pow,Complex.norm_ofNat,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hv,
    abs_of_pos (cubicThetaCartesian_radius_pos x y hv)]
  calc
    _ = (‖s‖*‖s-1‖)/v^2+‖4*s^2+2*s‖*(1/(x^2+y^2+v^2))+
      (4*‖s‖*‖s+1‖)*(v^2/(x^2+y^2+v^2)^2) := by ring
    _ ≤ (‖s‖*‖s-1‖)/v^2+‖4*s^2+2*s‖*(1/v^2)+
      (4*‖s‖*‖s+1‖)*(1/v^2) :=
      add_le_add (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (cubicTheta_radius_inverse x y hv) (_root_.norm_nonneg _)))
        (mul_le_mul_of_nonneg_left (cubicTheta_vertical_square_ratio x y hv) (by positivity))
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGridJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative bounds for all actual grid summands, with the zero row and
the inadmissible-pair extension included. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaHeightPower_first_norm (s : ℂ) {v : ℝ} (hv : 0<v) :
    ‖deriv (fun t : ℝ => (t:ℂ)^s) v‖=‖(v:ℂ)^s‖*(‖s‖/v) := by
  rw [cubicThetaHeightPower_deriv s hv,
    Complex.cpow_sub s 1 (Complex.ofReal_ne_zero.mpr hv.ne'),Complex.cpow_one]
  simp only [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hv]
  ring

lemma cubicThetaHeightPower_second_norm (s : ℂ) {v : ℝ} (hv : 0<v) :
    ‖deriv (deriv (fun t : ℝ => (t:ℂ)^s)) v‖=‖(v:ℂ)^s‖*(‖s*(s-1)‖/v^2) := by
  rw [cubicThetaHeightPower_second_deriv s hv,
    Complex.cpow_sub s 2 (Complex.ofReal_ne_zero.mpr hv.ne')]
  norm_num only [Complex.cpow_ofNat]
  simp only [norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hv]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGridLocalJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summable bounds for both derivatives on an actual coordinate
neighborhood. No derivative or normal-convergence assertion is assumed. -/
noncomputable section
namespace CubicFirstMoment

lemma uniform_ratio_bound {D F U K h a : ℝ} (hD : D ≤ F*(K/h))
    (hF : F ≤ U) (hF0 : 0 ≤ F) (hK : 0 ≤ K) (ha : 0<a) (hah : a ≤ h) :
    D ≤ U*(K/a) := by
  apply hD.trans
  exact mul_le_mul hF (div_le_div_of_nonneg_left hK ha hah)
    (div_nonneg hK (ha.trans_le hah).le) (hF0.trans hF)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTwiceDifferentiation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local twice differentiation for the complex coordinate series used
below. Both summable derivative bounds are supplied by actual grid estimates. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicTheta_twice_hasDerivAt_tsum {ι : Type*} {f : ι → ℝ → ℂ}
    {u₁ u₂ : ι → ℝ} (hu₁ : Summable u₁) (hu₂ : Summable u₂)
    {a b x : ℝ} (hx : x ∈ Set.Ioo a b)
    (hf : ∀ i t, t ∈ Set.Ioo a b → AnalyticAt ℝ (f i) t)
    (h₁ : ∀ i t, t ∈ Set.Ioo a b → ‖deriv (f i) t‖ ≤ u₁ i)
    (h₂ : ∀ i t, t ∈ Set.Ioo a b → ‖deriv (deriv (f i)) t‖ ≤ u₂ i)
    (h₀ : Summable (fun i => f i x)) :
    HasDerivAt (fun t => ∑' i, f i t) (∑' i, deriv (f i) x) x ∧
    HasDerivAt (deriv (fun t => ∑' i, f i t)) (∑' i, deriv (deriv (f i)) x) x ∧
    Summable (fun i => deriv (f i) x) ∧
    Summable (fun i => deriv (deriv (f i)) x) := by
  have hd₁ t (ht : t ∈ Set.Ioo a b) :
      HasDerivAt (fun w => ∑' i, f i w) (∑' i, deriv (f i) t) t :=
    hasDerivAt_tsum_of_isPreconnected hu₁ isOpen_Ioo (convex_Ioo a b).isPreconnected
      (fun i w hw => (hf i w hw).differentiableAt.hasDerivAt) h₁ hx h₀ ht
  have hs₁ : Summable (fun i => deriv (f i) x) :=
    hu₁.of_norm_bounded (fun i => h₁ i x hx)
  have hs₂ : Summable (fun i => deriv (deriv (f i)) x) :=
    hu₂.of_norm_bounded (fun i => h₂ i x hx)
  have hd₂ : HasDerivAt (fun t => ∑' i, deriv (f i) t)
      (∑' i, deriv (deriv (f i)) x) x :=
    hasDerivAt_tsum_of_isPreconnected hu₂ isOpen_Ioo (convex_Ioo a b).isPreconnected
      (fun i w hw => (hf i w hw).deriv.differentiableAt.hasDerivAt) h₂ hx hs₁ hx
  have he : deriv (fun t => ∑' i, f i t) =ᶠ[𝓝 x] (fun t => ∑' i, deriv (f i) t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    exact (hd₁ t ht).deriv
  exact ⟨hd₁ x hx,hd₂.congr_of_eventuallyEq he,hs₁,hs₂⟩

lemma cubicTheta_twice_deriv_tsum {ι : Type*} {f : ι → ℝ → ℂ}
    {u₁ u₂ : ι → ℝ} (hu₁ : Summable u₁) (hu₂ : Summable u₂)
    {a b x : ℝ} (hx : x ∈ Set.Ioo a b)
    (hf : ∀ i t, t ∈ Set.Ioo a b → AnalyticAt ℝ (f i) t)
    (h₁ : ∀ i t, t ∈ Set.Ioo a b → ‖deriv (f i) t‖ ≤ u₁ i)
    (h₂ : ∀ i t, t ∈ Set.Ioo a b → ‖deriv (deriv (f i)) t‖ ≤ u₂ i)
    (h₀ : Summable (fun i => f i x)) :
    deriv (fun t => ∑' i, f i t) x=(∑' i, deriv (f i) x) ∧
    deriv (deriv (fun t => ∑' i, f i t)) x=(∑' i, deriv (deriv (f i)) x) ∧
    Summable (fun i => deriv (f i) x) ∧
    Summable (fun i => deriv (deriv (f i)) x) := by
  obtain ⟨h,h',hs,hs'⟩ := cubicTheta_twice_hasDerivAt_tsum hu₁ hu₂ hx hf h₁ h₂ h₀
  exact ⟨h.deriv,h'.deriv,hs,hs'⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaVerticalProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The precise product error when a height-only eigenfunction is
multiplied by a smooth cusp cutoff. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicTheta_vertical_product_second {f g : ℝ → ℂ}
    (hf : ∀ t, 0<t → DifferentiableAt ℝ f t)
    (hg : ∀ t, 0<t → DifferentiableAt ℝ g t)
    (hf' : ∀ t, 0<t → DifferentiableAt ℝ (deriv f) t)
    (hg' : ∀ t, 0<t → DifferentiableAt ℝ (deriv g) t)
    {v : ℝ} (hv : 0<v) :
    deriv (deriv (fun t => f t*g t)) v=
      deriv (deriv f) v*g v+2*deriv f v*deriv g v+f v*deriv (deriv g) v := by
  have he : deriv (fun t => f t*g t) =ᶠ[𝓝 v]
      (fun t => deriv f t*g t+f t*deriv g t) := by
    filter_upwards [eventually_gt_nhds hv] with t ht
    have h := ((hf t ht).hasDerivAt.fun_mul (hg t ht).hasDerivAt).deriv
    exact h
  rw [he.deriv_eq]
  have h := (((hf' v hv).hasDerivAt.fun_mul (hg v hv).hasDerivAt).fun_add
    ((hf v hv).hasDerivAt.fun_mul (hg' v hv).hasDerivAt)).deriv
  rw [h]
  ring

theorem cubicThetaHyperbolicOperator_vertical_product {f g : ℝ → ℂ}
    (hf : ∀ t, 0<t → DifferentiableAt ℝ f t)
    (hg : ∀ t, 0<t → DifferentiableAt ℝ g t)
    (hf' : ∀ t, 0<t → DifferentiableAt ℝ (deriv f) t)
    (hg' : ∀ t, 0<t → DifferentiableAt ℝ (deriv g) t)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator (fun _ _ t => f t*g t) x y v=
      f v*cubicThetaHyperbolicOperator (fun _ _ t => g t) x y v+
      ((v:ℂ)^2*deriv (deriv f) v-(v:ℂ)*deriv f v)*g v+
      2*(v:ℂ)^2*deriv f v*deriv g v := by
  unfold cubicThetaHyperbolicOperator
  simp only [deriv_const',deriv_const,zero_add]
  rw [cubicTheta_vertical_product_second hf hg hf' hg' hv,
    ((hf v hv).hasDerivAt.fun_mul (hg v hv).hasDerivAt).deriv]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaIncomingForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The incoming height term gives an entire family of compact annular
forcing terms. This is the scalar term to be assembled in the arithmetic
cusps before applying the continued global resolvent. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

def cubicThetaIncomingForcing (s : ℂ) (v : ℝ) : ℂ :=
  ((v:ℂ)^2*deriv (deriv cubicThetaCuspCutoff) v-(v:ℂ)*deriv cubicThetaCuspCutoff v)*
      (v:ℂ)^s+
    2*(v:ℂ)^2*deriv cubicThetaCuspCutoff v*s*(v:ℂ)^(s-1)

theorem cubicThetaCutoffIncoming_equation (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun _ _ t => cubicThetaCuspCutoff t*(t:ℂ)^s) x y v=
      s*(s-2)*(cubicThetaCuspCutoff v*(v:ℂ)^s)+cubicThetaIncomingForcing s v := by
  have hc : Differentiable ℝ cubicThetaCuspCutoff :=
    cubicThetaCuspCutoff_smooth.differentiable (by simp)
  have hc' : Differentiable ℝ (deriv cubicThetaCuspCutoff) :=
    (cubicThetaCuspCutoff_smooth.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (2:ℕ∞ω)≤∞)).differentiable_deriv_two
  rw [cubicThetaHyperbolicOperator_vertical_product (fun t _ => hc t)
    (fun _ ht => (cubicThetaHeightPower_analytic s ht).differentiableAt)
    (fun t _ => hc' t)
    (fun _ ht => (cubicThetaHeightPower_analytic s ht).deriv.differentiableAt) x y hv,
    cubicThetaHyperbolicOperator_height s x y hv,cubicThetaHeightPower_deriv s hv]
  unfold cubicThetaIncomingForcing
  ring

lemma cubicThetaIncomingForcing_zero (s : ℂ) {v : ℝ} (hv : v<1 ∨ 2<v) :
    cubicThetaIncomingForcing s v=0 := by
  obtain ⟨h₁,h₂⟩ := cubicThetaCuspCutoff_derivatives_zero hv
  simp [cubicThetaIncomingForcing,h₁,h₂]

lemma cubicThetaIncomingForcing_compact (s : ℂ) :
    HasCompactSupport (cubicThetaIncomingForcing s) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro v hv
  by_contra h
  have he : v<1 ∨ 2<v := by simpa only [Set.mem_Icc,not_and_or,not_le] using h
  exact hv (cubicThetaIncomingForcing_zero s he)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Twice continuous coordinate differentiability of the literal
Eisenstein sum, from the existing local summable derivative bounds. -/
noncomputable section
open Set
open scoped Topology ContDiff
namespace CubicFirstMoment

lemma cubicTheta_twice_contDiffAt_tsum {ι : Type*} {f : ι → ℝ → ℂ}
    {u₁ u₂ : ι → ℝ} (hu₁ : Summable u₁) (hu₂ : Summable u₂)
    {a b x : ℝ} (hx : x∈Ioo a b)
    (hf : ∀ i t, t∈Ioo a b → AnalyticAt ℝ (f i) t)
    (h₁ : ∀ i t, t∈Ioo a b → ‖deriv (f i) t‖≤u₁ i)
    (h₂ : ∀ i t, t∈Ioo a b → ‖deriv (deriv (f i)) t‖≤u₂ i)
    (h₀ : ∀ t∈Ioo a b, Summable (fun i => f i t)) :
    ContDiffAt ℝ 2 (fun t => ∑' i, f i t) x := by
  have hd t (ht : t∈Ioo a b) := cubicTheta_twice_hasDerivAt_tsum hu₁ hu₂ ht hf h₁ h₂ (h₀ t ht)
  have hc₂ : ContinuousOn (fun t => ∑' i, deriv (deriv (f i)) t) (Ioo a b) :=
    continuousOn_tsum (fun i t ht => (hf i t ht).deriv.deriv.continuousAt.continuousWithinAt) hu₂ h₂
  have hc : ContinuousOn (deriv (deriv (fun t => ∑' i, f i t))) (Ioo a b) :=
    hc₂.congr (fun t ht => (hd t ht).2.1.deriv)
  have hcd₁ : ContDiffOn ℝ 1 (deriv (fun t => ∑' i, f i t)) (Ioo a b) := by
    rw [show (1 : ℕ∞ω)=0+1 from rfl,contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    exact ⟨fun t ht => (hd t ht).2.1.differentiableAt.differentiableWithinAt,
      by norm_num,contDiffOn_zero.mpr hc⟩
  have hcd₂ : ContDiffOn ℝ 2 (fun t => ∑' i, f i t) (Ioo a b) := by
    rw [show (2 : ℕ∞ω)=1+1 from rfl,contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    exact ⟨fun t ht => (hd t ht).1.differentiableAt.differentiableWithinAt,by norm_num,hcd₁⟩
  exact hcd₂.contDiffAt (isOpen_Ioo.mem_nhds hx)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaIncomingSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint spatial smoothness of the actual incoming arithmetic series.
The compact row bound makes the sum locally finite before differentiation. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaPositive_compact_neighborhood {p : ℂ × ℝ} (hp : 0<p.2) :
    ∃ K : Set (ℂ × ℝ), K∈𝓝 p ∧ IsCompact K ∧ ∀ q∈K, 0<q.2 := by
  refine ⟨Metric.closedBall p (p.2/2),Metric.closedBall_mem_nhds p (half_pos hp),
    isCompact_closedBall _ _,?_⟩
  intro q hq
  have hd : dist q.2 p.2≤dist q p := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have hb := hd.trans (Metric.mem_closedBall.mp hq)
  rw [Real.dist_eq] at hb
  have h := (abs_le.mp hb).1
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSecondChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real-to-complex second chain rule used for a smooth cutoff of
an arithmetic cusp height. -/
noncomputable section
open Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaSecondChain {f : ℝ → ℂ} {h : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f (h x)) (hh : ContDiffAt ℝ 2 h x) :
    deriv (deriv (f ∘ h)) x=(deriv h x)^2 • deriv (deriv f) (h x)+
      deriv (deriv h) x • deriv f (h x) := by
  have hf' : DifferentiableAt ℝ (deriv f) (h x) :=
    (hf.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hh' : DifferentiableAt ℝ (deriv h) x :=
    (hh.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hfe : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f (h y) :=
    hh.continuousAt.eventually ((hf.eventually (by norm_num)).mono
      (fun _ hy => hy.differentiableAt (by norm_num)))
  have hhe : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ h y :=
    (hh.eventually (by norm_num)).mono (fun _ hy => hy.differentiableAt (by norm_num))
  have he : deriv (f ∘ h) =ᶠ[𝓝 x] (fun y => deriv h y • deriv f (h y)) := by
    filter_upwards [hfe,hhe] with y hfy hhy
    exact deriv.scomp y hfy hhy
  rw [he.deriv_eq]
  have hd := hh'.hasDerivAt.smul
    (hf'.hasDerivAt.scomp x (hh.differentiableAt (by norm_num)).hasDerivAt)
  simpa only [Pi.smul_def',Function.comp_def,smul_smul,← pow_two,add_comm] using hd.deriv

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHyperbolicChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The hyperbolic chain rule, keeping the two coefficients explicit.
They will be identified for the actual arithmetic row height using its
already proved first and second power equations. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

def cubicThetaHeightChainQuadratic (h : ℝ → ℝ → ℝ → ℝ) (x y v : ℝ) : ℂ :=
  (v:ℂ)^2*(((deriv (fun t => h t y v) x:ℝ):ℂ)^2+
    ((deriv (fun t => h x t v) y:ℝ):ℂ)^2+
    ((deriv (fun t => h x y t) v:ℝ):ℂ)^2)

def cubicThetaHeightChainLinear (h : ℝ → ℝ → ℝ → ℝ) (x y v : ℝ) : ℂ :=
  (v:ℂ)^2*(((deriv (deriv (fun t => h t y v)) x:ℝ):ℂ)+
    ((deriv (deriv (fun t => h x t v)) y:ℝ):ℂ)+
    ((deriv (deriv (fun t => h x y t)) v:ℝ):ℂ))-
    (v:ℂ)*((deriv (fun t => h x y t) v:ℝ):ℂ)

theorem cubicThetaHyperbolic_chain {h : ℝ → ℝ → ℝ → ℝ} {f : ℝ → ℂ} {x y v : ℝ}
    (hx : ContDiffAt ℝ 2 (fun t => h t y v) x)
    (hy : ContDiffAt ℝ 2 (fun t => h x t v) y)
    (hv : ContDiffAt ℝ 2 (fun t => h x y t) v)
    (hf : ContDiffAt ℝ 2 f (h x y v)) :
    cubicThetaHyperbolicOperator (fun a b t => f (h a b t)) x y v=
      cubicThetaHeightChainQuadratic h x y v*deriv (deriv f) (h x y v)+
      cubicThetaHeightChainLinear h x y v*deriv f (h x y v) := by
  have hxx := cubicThetaSecondChain (h:=fun t => h t y v) (x:=x) hf hx
  have hyy := cubicThetaSecondChain (h:=fun t => h x t v) (x:=y) hf hy
  have hvv := cubicThetaSecondChain (h:=fun t => h x y t) (x:=v) hf hv
  have hdv := deriv.scomp v (hf.differentiableAt (by norm_num))
    (hv.differentiableAt (by norm_num))
  simp only [Function.comp_def] at hxx hyy hvv hdv
  unfold cubicThetaHyperbolicOperator cubicThetaHeightChainQuadratic cubicThetaHeightChainLinear
  dsimp only
  rw [hxx,hyy,hvv,hdv]
  simp only [Complex.real_smul,Complex.ofReal_pow]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowHeightEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every actual primitive row height, with arbitrary complex power,
satisfies the hyperbolic spectral equation. This removes the nonzero
cubic phase from the already proved literal grid equation. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaHyperbolicOperator_const_mul (F : ℝ → ℝ → ℝ → ℂ)
    (c : ℂ) (x y v : ℝ) :
    cubicThetaHyperbolicOperator (fun a b t => c*F a b t) x y v=
      c*cubicThetaHyperbolicOperator F x y v := by
  simpa only [add_zero] using cubicThetaHyperbolicOperator_translate F c 0 0 x y v

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Locality and finite additivity of the actual hyperbolic operator
for twice continuously differentiable functions. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace CubicFirstMoment

lemma cubicThetaHyperbolicOperator_finite {ι : Type*} (S : Finset ι)
    (F : ι → ℝ → ℝ → ℝ → ℂ) (x y v : ℝ)
    (hx : ∀ i∈S, ContDiffAt ℝ 2 (fun t => F i t y v) x)
    (hy : ∀ i∈S, ContDiffAt ℝ 2 (fun t => F i x t v) y)
    (ht : ∀ i∈S, ContDiffAt ℝ 2 (fun t => F i x y t) v) :
    cubicThetaHyperbolicOperator (fun a b t => ∑ i∈S, F i a b t) x y v=
      ∑ i∈S, cubicThetaHyperbolicOperator (F i) x y v := by
  have ex := iteratedDeriv_fun_sum (n:=2) hx
  have ey := iteratedDeriv_fun_sum (n:=2) hy
  have et := iteratedDeriv_fun_sum (n:=2) ht
  simp only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] at ex ey et
  have e₁ := deriv_fun_sum (fun i hi => (ht i hi).differentiableAt (by norm_num))
  unfold cubicThetaHyperbolicOperator
  rw [ex,ey,et,e₁]
  simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual arithmetic remainder satisfies the same forced spectral
operator as the continued global weak response. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace CubicFirstMoment

lemma second_sub {f g : ℝ → ℂ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (fun t => f t-g t)) x=deriv (deriv f) x-deriv (deriv g) x := by
  have he : deriv (fun t => f t-g t)=ᶠ[𝓝 x] (fun t => deriv f t-deriv g t) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with t ht hu
    exact deriv_sub (ht.differentiableAt (by norm_num)) (hu.differentiableAt (by norm_num))
  rw [he.deriv_eq]
  exact deriv_sub ((hf.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHermitianMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Determinant-one Hermitian coordinates and the invariant two-point
quantity underlying the hyperbolic metric. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaHyperbolicChord (p q : ℂ × ℝ) : ℝ :=
  (Complex.normSq (p.1-q.1)+(p.2-q.2)^2)/(p.2*q.2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaJacobian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Mobius Jacobian has absolute determinant equal to the cube
of the height ratio. Thus the hyperbolic volume density is invariant. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

abbrev TangentL2 := WithLp 2 (ℂ × ℝ)
def tangentCoordinates : TangentL2 ≃ₗ[ℝ] ℂ × ℝ := WithLp.linearEquiv 2 ℝ (ℂ × ℝ)

lemma tangent_finrank : Module.finrank ℝ TangentL2=3 := by
  rw [tangentCoordinates.finrank_eq,Module.finrank_prod,Complex.finrank_real_complex,
    Module.finrank_self]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHyperbolicMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual invariant hyperbolic measure on positive-height points.
Its density is v^-3, and arithmetic invariance follows from the proved
Jacobian, not from an assumed invariant measure. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ENNReal
namespace CubicFirstMoment

local instance cubicThetaHyperbolicMeasure_volumeHaar :
    (volume : Measure (ℂ × ℝ)).IsAddHaarMeasure := by
  change ((volume : Measure ℂ).prod (volume : Measure ℝ)).IsAddHaarMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactDensityBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On a fixed positive-height compact set, the hyperbolic L2 density
is bounded by a constant times the Euclidean L2 density. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaCompact_inverseCube_bound {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : K⊆{y : ℂ × ℝ | 0<y.2}) :
    ∃ C≥0, ∀ y∈K, (y.2^3)⁻¹≤C := by
  have hv : ContinuousOn (fun y : ℂ × ℝ => (y.2^3)⁻¹) K :=
    ((continuous_snd.pow 3).continuousOn).inv₀ (fun y hy => pow_ne_zero 3 (hpos hy).ne')
  obtain ⟨C₀,hC₀⟩ := hK.exists_bound_of_continuousOn hv
  refine ⟨max C₀ 0,le_max_right _ _,fun y hy => ?_⟩
  exact (le_abs_self _).trans ((hC₀ y hy).trans (le_max_left _ _))

lemma normSquare_integrable {f : ℂ × ℝ → ℂ}
    (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun y => ‖f y‖^2) (volume : Measure (ℂ × ℝ)) := by
  have hcont : Continuous (fun y => ‖f y‖^2) := hf.norm.pow 2
  have hs : HasCompactSupport (fun y => ‖f y‖^2) :=
    hc.comp_left (g:=fun z : ℂ => ‖z‖^2) (by simp)
  exact hcont.integrable_of_hasCompactSupport hs

lemma normSquare_divCube_integrableOn {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : K⊆{y : ℂ × ℝ | 0<y.2}) {f : ℂ × ℝ → ℂ} (hf : Continuous f) :
    IntegrableOn (fun y => ‖f y‖^2/y.2^3) K := by
  have hn : ContinuousOn (fun y => ‖f y‖^2) K := (hf.norm.pow 2).continuousOn
  have hd : ContinuousOn (fun y : ℂ × ℝ => y.2^3) K := (continuous_snd.pow 3).continuousOn
  have hdiv : ContinuousOn (fun y => ‖f y‖^2/y.2^3) K :=
    hn.div hd (fun y hy => pow_ne_zero 3 (hpos hy).ne')
  exact hdiv.integrableOn_compact hK

theorem cubicThetaCompactDensity_bound {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : K⊆{y : ℂ × ℝ | 0<y.2}) :
    ∃ C≥0, ∀ (f : ℂ × ℝ → ℂ), Continuous f → HasCompactSupport f → tsupport f⊆K →
      (∫ y, ‖f y‖^2/y.2^3)≤C*(∫ y, ‖f y‖^2) := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaCompact_inverseCube_bound hK hpos
  refine ⟨C,hC,fun f hf hc hs => ?_⟩
  have hnum := normSquare_integrable hf hc
  have hdiv := normSquare_divCube_integrableOn hK hpos hf
  have hmono : (∫ y in K, ‖f y‖^2/y.2^3)≤C*(∫ y in K, ‖f y‖^2) := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on hdiv (hnum.integrableOn.const_mul C) hK.measurableSet
    intro y hy
    simpa only [div_eq_mul_inv,mul_comm] using
      mul_le_mul_of_nonneg_right (hbound y hy) (sq_nonneg ‖f y‖)
  have hz : ∀ y, y∉K → f y=0 :=
    fun y hy => image_eq_zero_of_notMem_tsupport (fun ht => hy (hs ht))
  have h₁ : (∫ y in K, ‖f y‖^2/y.2^3)=∫ y, ‖f y‖^2/y.2^3 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [hz y hy,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_div]
  have h₂ : (∫ y in K, ‖f y‖^2)=∫ y, ‖f y‖^2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [hz y hy,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
  rwa [h₁,h₂] at hmono

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compactness transfer used to reconstruct global core values
from their compact coordinate localizations. -/
noncomputable section
open Set Topology
namespace CubicFirstMoment

theorem cubicThetaCompact_of_norm_domination
    {H K L : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    [NormedAddCommGroup L] [NormedSpace ℂ L] [CompleteSpace L]
    (A : H →L[ℂ] L) (B : H →L[ℂ] K) (hB : IsCompactOperator B)
    (hbound : ∃ C : ℝ, ∀ u, ‖A u‖≤C*‖B u‖) : IsCompactOperator A := by
  let V := B.toLinearMap.range.topologicalClosure
  let g : H →L[ℂ] V := B.codRestrict V
    (fun u => Submodule.le_topologicalClosure _ ⟨u,rfl⟩)
  have hd : DenseRange g := by
    intro v
    rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    have he : Subtype.val '' Set.range g=Set.range B := by
      ext y
      constructor
      · rintro ⟨w,⟨u,rfl⟩,rfl⟩
        exact ⟨u,rfl⟩
      · rintro ⟨u,rfl⟩
        exact ⟨g u,⟨u,rfl⟩,rfl⟩
    rw [he]
    exact v.property
  let T : V →L[ℂ] L := A.toLinearMap.extendOfNorm g.toLinearMap
  have hT (u : H) : T (g u)=A u :=
    LinearMap.extendOfNorm_eq hd hbound u
  have hg : IsCompactOperator g :=
    hB.codRestrict (V:=V) (fun u => Submodule.le_topologicalClosure B.toLinearMap.range ⟨u,rfl⟩)
      (Submodule.isClosed_topologicalClosure B.toLinearMap.range)
  have he : (A : H → L)=T ∘ g := funext (fun u => (hT u).symm)
  rw [he]
  exact hg.clm_comp T

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPoincareSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness of periodized compact seeds is proved locally by replacing
its locally finite arithmetic sum with an actual finite sum. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators CompactlySupported ContDiff
namespace CubicFirstMoment

lemma cubicTheta_locallyFinite_finsum {X ι A : Type*} [TopologicalSpace X]
    [AddCommMonoid A] (f : ι → X → A)
    (hf : LocallyFinite (fun i => Function.support (f i))) (x : X) :
    ∃ s : Finset ι, (fun y => ∑ᶠ i, f i y) =ᶠ[𝓝 x] fun y => ∑ i∈s, f i y := by
  classical
  obtain ⟨t,ht,hfin⟩ := hf x
  refine ⟨hfin.toFinset,?_⟩
  filter_upwards [ht] with y hy
  apply finsum_eq_sum_of_support_subset
  intro i hi
  exact hfin.mem_toFinset.mpr ⟨y,hi,hy⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLogHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic height conjugation of the radial hyperbolic
operator. The conjugated radial operator is d^2/dt^2 - 1. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

def cubicThetaLogLift (f : ℝ → ℂ) (v : ℝ) : ℂ := (v:ℂ)*f (Real.log v)

lemma cubicThetaLogLift_hasDerivAt {f : ℝ → ℂ} (hf : Differentiable ℝ f)
    {v : ℝ} (hv : 0<v) :
    HasDerivAt (cubicThetaLogLift f) (f (Real.log v)+deriv f (Real.log v)) v := by
  have h := Complex.ofRealCLM.hasDerivAt.fun_mul
    ((hf (Real.log v)).hasDerivAt.scomp v (Real.hasDerivAt_log hv.ne'))
  refine h.congr_deriv ?_
  · simp only [Function.comp_apply,Complex.ofRealCLM_apply,
      Complex.ofReal_one,one_mul,Complex.real_smul,Complex.ofReal_inv]
    have hn : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
    field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLogMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial L2 mass and energy after logarithmic height conjugation.
The measure factors are exactly those of hyperbolic three-space. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma integral_comp_exp_whole_aux (h : ℝ → ℝ) :
    ∫ x : ℝ, Real.exp x • h (Real.exp x) = ∫ y in Set.Ioi (0 : ℝ), h y := by
  have hh := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Set.univ)
    MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ hxy => Real.exp_injective hxy) h
  rw [Set.image_univ, Real.range_exp, MeasureTheory.setIntegral_univ] at hh
  simpa [abs_of_pos (Real.exp_pos _)] using hh.symm

lemma exp_smul_log_inv_mul (g : ℝ → ℝ) :
    (fun x : ℝ => Real.exp x • ((fun v : ℝ => v⁻¹ * g (Real.log v)) (Real.exp x))) = g := by
  funext x
  simp only [smul_eq_mul, Real.log_exp]
  rw [← mul_assoc, mul_inv_cancel₀ (Real.exp_pos x).ne', one_mul]

lemma integral_comp_log_Ioi_zero (g : ℝ → ℝ) :
    ∫ v in Set.Ioi (0 : ℝ), v⁻¹ * g (Real.log v) = ∫ t : ℝ, g t := by
  rw [← integral_comp_exp_whole_aux (fun v : ℝ => v⁻¹ * g (Real.log v)), exp_smul_log_inv_mul]

lemma cubicThetaLogLift_mass_integrand (f : ℝ → ℂ) {v : ℝ} (hv : 0<v) :
    ‖cubicThetaLogLift f v‖^2/v^3=v⁻¹*‖f (Real.log v)‖^2 := by
  rw [cubicThetaLogLift,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hv]
  field_simp

theorem cubicThetaLogLift_mass (f : ℝ → ℂ) :
    (∫ v in Ioi (0:ℝ), ‖cubicThetaLogLift f v‖^2/v^3)=
      ∫ t : ℝ, ‖f t‖^2 := by
  calc
    _ = ∫ v in Ioi (0:ℝ), v⁻¹*‖f (Real.log v)‖^2 :=
      setIntegral_congr_fun measurableSet_Ioi (fun v hv => cubicThetaLogLift_mass_integrand f hv)
    _ = _ := integral_comp_log_Ioi_zero (fun t : ℝ => ‖f t‖^2)

theorem cubicThetaLogLift_energy {f : ℝ → ℂ} (hf : Differentiable ℝ f) :
    (∫ v in Ioi (0:ℝ), ‖deriv (cubicThetaLogLift f) v‖^2/v)=
      ∫ t : ℝ, ‖f t+deriv f t‖^2 := by
  calc
    _ = ∫ v in Ioi (0:ℝ), v⁻¹*‖f (Real.log v)+deriv f (Real.log v)‖^2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      change ‖deriv (cubicThetaLogLift f) v‖^2/v=
        v⁻¹*‖f (Real.log v)+deriv f (Real.log v)‖^2
      rw [(cubicThetaLogLift_hasDerivAt hf hv).deriv]
      ring
    _ = _ := integral_comp_log_Ioi_zero (fun t : ℝ => ‖f t+deriv f t‖^2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspHardy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact radial energy identity and Hardy bound, with the
hyperbolic spectral threshold equal to one. -/
noncomputable section
open MeasureTheory Function
namespace CubicFirstMoment

lemma norm_square_integrable {f : ℝ → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) : Integrable (fun t : ℝ => ‖f t‖^2) := by
  have h : HasCompactSupport (fun t : ℝ => ‖f t‖^2) :=
    hc.comp_left (g:=fun z : ℂ => ‖z‖^2) (by simp)
  exact (hf.norm.pow 2).integrable_of_hasCompactSupport h

lemma cross_compact {f g : ℝ → ℂ} (hc : HasCompactSupport f) :
    HasCompactSupport (fun t : ℝ => 2*inner ℝ (f t) (g t)) := by
  apply hc.mono' (f':=fun t : ℝ => 2*inner ℝ (f t) (g t))
  intro t ht
  by_contra hn
  have hz : f t=0 := image_eq_zero_of_notMem_tsupport hn
  exact ht (by simp [hz])

lemma cross_integrable {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hc : HasCompactSupport f) : Integrable (fun t : ℝ => 2*inner ℝ (f t) (g t)) := by
  have hi : Continuous (fun t : ℝ => inner ℝ (f t) (g t)) := hf.inner hg
  exact (continuous_const.mul hi).integrable_of_hasCompactSupport (cross_compact hc)

lemma cubicTheta_log_cross_integral {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    (∫ t : ℝ, 2*inner ℝ (f t) (deriv f t))=0 := by
  have hdc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ‖f t‖^2) (2*inner ℝ (f t) (deriv f t)) t :=
    fun t => ((hf.differentiable (by norm_num)) t).hasDerivAt.norm_sq
  exact integral_eq_zero_of_hasDerivAt_of_integrable hd
    (cross_integrable hf.continuous hdc hc) (norm_square_integrable hf.continuous hc)

theorem cubicTheta_log_energy_identity {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    (∫ t : ℝ, ‖f t+deriv f t‖^2)=
      (∫ t : ℝ, ‖f t‖^2)+(∫ t : ℝ, ‖deriv f t‖^2) := by
  have hdc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have h₀ := norm_square_integrable hf.continuous hc
  have h₁ := norm_square_integrable hdc hc.deriv
  have hcross := cross_integrable hf.continuous hdc hc
  simp_rw [norm_add_sq_real]
  have hi := integral_add (h₀.add hcross) h₁
  simp only [Pi.add_apply] at hi
  rw [hi,integral_add h₀ hcross,
    cubicTheta_log_cross_integral hf hc,add_zero]

theorem cubicTheta_radial_energy_identity {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    (∫ v in Set.Ioi (0:ℝ), ‖deriv (cubicThetaLogLift f) v‖^2/v)=
      (∫ v in Set.Ioi (0:ℝ), ‖cubicThetaLogLift f v‖^2/v^3)+
        ∫ t : ℝ, ‖deriv f t‖^2 := by
  rw [cubicThetaLogLift_energy (hf.differentiable (by norm_num)),
    cubicThetaLogLift_mass,cubicTheta_log_energy_identity hf hc]

theorem cubicTheta_radial_hardy {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    (∫ v in Set.Ioi (0:ℝ), ‖cubicThetaLogLift f v‖^2/v^3) ≤
      (∫ v in Set.Ioi (0:ℝ), ‖deriv (cubicThetaLogLift f) v‖^2/v) := by
  rw [cubicTheta_radial_energy_identity hf hc]
  exact le_add_of_nonneg_right (integral_nonneg (fun _ => sq_nonneg _))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspStrip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A half-open three-Eisenstein period cell gives a genuinely injective
high cusp strip in the arithmetic quotient. Boundary points retain their
unique representatives. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma halfOpen_integer_unique {x y : ℝ} {n : ℤ}
    (hx : x∈Ico (0:ℝ) 1) (hy : y∈Ico (0:ℝ) 1) (he : x=y+n) : x=y := by
  have hlow : (-1:ℝ)<(n:ℝ) := by linarith [hx.1,hy.2]
  have hhigh : (n:ℝ)<1 := by linarith [hx.2,hy.1]
  have hlow' : (-1:ℤ)<n := by exact_mod_cast hlow
  have hhigh' : n<1 := by exact_mod_cast hhigh
  have hn : n=0 := by omega
  simpa only [hn,Int.cast_zero,add_zero] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The slit resolvent of a positive Hilbert-space contraction. This
common argument is used for the constant block and the full cusp operator;
it does not require compactness of the constant block. -/
noncomputable section
namespace CubicFirstMoment
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma cubicThetaPositiveContraction_unit (G : H →L[ℂ] H)
    (hG : G.IsPositive) (hGnorm : ‖G‖ ≤ 1) {z : ℂ} (hz : z.im≠0 ∨ z.re<1) :
    IsUnit (1-z • G) := by
  by_cases hz0 : z=0
  · subst z
    have he : (0:ℂ) • G=0 := by ext F; simp
    rw [he,sub_zero]
    exact isUnit_one
  have hn : z⁻¹ ∉ spectrum ℂ (G) := by
    intro hm
    have hi : (z⁻¹).im=0 := hG.isSelfAdjoint.im_eq_zero_of_mem_spectrum hm
    have hr : 0 ≤ (z⁻¹).re := by
      apply SpectrumRestricts.nnreal_iff.mp hG.spectrumRestricts
      apply spectrum.of_algebraMap_mem (S:=ℂ)
      convert hm using 1
      all_goals try with_reducible_and_instances rfl
      exact (hG.isSelfAdjoint.mem_spectrum_eq_re hm).symm
    have hb : (z⁻¹).re ≤ 1 := by
      apply (Complex.re_le_norm _).trans
      apply (spectrum.norm_le_norm_mul_of_mem hm).trans
      exact (mul_le_mul hGnorm
        (ContinuousLinearMap.norm_id_le (𝕜:=ℂ) (E:=H))
        (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have he := congrArg Complex.re (mul_inv_cancel₀ hz0)
    have he' := congrArg Complex.im (mul_inv_cancel₀ hz0)
    simp only [Complex.mul_re,Complex.mul_im,hi,mul_zero,sub_zero,zero_add,Complex.one_re,Complex.one_im] at he he'
    rcases hz with hz | hz
    · have hzre : (z⁻¹).re=0 := (mul_eq_zero.mp he').resolve_left hz
      rw [hzre,mul_zero] at he
      exact zero_ne_one he
    · have hrpos : 0<(z⁻¹).re := lt_of_le_of_ne hr (by
        intro hh
        rw [← hh,mul_zero] at he
        exact zero_ne_one he)
      have hprod := mul_pos (sub_pos.mpr hz) hrpos
      nlinarith
  have hu := spectrum.notMem_iff.mp hn
  have hs := hu.smul (Units.mk0 z hz0)
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  all_goals
    simp [Units.smul_def,smul_sub,Algebra.algebraMap_eq_smul_one,smul_smul,hz0]


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary Fredholm alternative needed for the compactly
corrected energy pencil: injectivity upgrades to invertibility. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaCompactPerturbation_unit
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (A K : H →L[ℂ] H) (hK : IsCompactOperator K) (hU : IsUnit (A+K))
    (hinj : Function.Injective A) : IsUnit A := by
  let U := A+K
  let L : H →L[ℂ] H := (Ring.inverse U).comp K
  have hL : IsCompactOperator L := hK.clm_comp (Ring.inverse U)
  have hfactor : U*(1-L)=A := by
    change U*(1-Ring.inverse U*K)=A
    rw [mul_sub,mul_one,← mul_assoc,Ring.mul_inverse_cancel _ hU,one_mul]
    dsimp [U]
    abel
  have hn : ¬Module.End.HasEigenvalue (L : Module.End ℂ H) 1 := by
    intro he
    obtain ⟨v,hv,hv0⟩ := he.exists_hasEigenvector
    have heq : L v=v := by
      have hh := Module.End.mem_eigenspace_iff.mp hv
      change L v=(1:ℂ) • v at hh
      simpa only [one_smul] using hh
    have hav : A v=0 := by
      rw [← hfactor]
      change U (v-L v)=0
      rw [heq,sub_self,map_zero]
    exact hv0 (hinj (hav.trans (map_zero A).symm))
  have hu : IsUnit (1-L) := by
    have hr := (hL.hasEigenvalue_or_mem_resolventSet (one_ne_zero : (1:ℂ)≠0)).resolve_left hn
    simpa only [spectrum.mem_resolventSet_iff,map_one] using hr
  rw [← hfactor]
  exact hU.mul hu

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSpatialDerivativeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A joint Frechet derivative bound for the actual Eisenstein summands.
The three proved coordinate bounds control the product-space operator norm. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaComplexProduct_opNorm_le (L : (ℂ × ℝ) →L[ℝ] ℂ) {B : ℝ}
    (hB : 0≤B) (hx : ‖L (1,0)‖≤B) (hy : ‖L (Complex.I,0)‖≤B)
    (hv : ‖L (0,1)‖≤B) : ‖L‖≤3*B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  have hu : u=u.1.re • ((1:ℂ),(0:ℝ))+u.1.im • ((Complex.I:ℂ),(0:ℝ))+u.2 • ((0:ℂ),(1:ℝ)) := by
    apply Prod.ext
    · change u.1=(u.1.re:ℂ)*1+(u.1.im:ℂ)*Complex.I+(u.2:ℂ)*0
      simpa only [mul_one,mul_zero,add_zero] using (Complex.re_add_im u.1).symm
    · simp
  have hr : ‖u.1.re‖≤‖u‖ := (Complex.abs_re_le_norm u.1).trans (norm_fst_le u)
  have hi : ‖u.1.im‖≤‖u‖ := (Complex.abs_im_le_norm u.1).trans (norm_fst_le u)
  have ht : ‖u.2‖≤‖u‖ := norm_snd_le u
  calc
    ‖L u‖=‖u.1.re • L (1,0)+u.1.im • L (Complex.I,0)+u.2 • L (0,1)‖ := by
      conv_lhs => rw [hu,map_add,map_add,map_smul,map_smul,map_smul]
    _ ≤ ‖u.1.re • L (1,0)‖+‖u.1.im • L (Complex.I,0)‖+‖u.2 • L (0,1)‖ := norm_add₃_le
    _ ≤ ‖u‖*B+‖u‖*B+‖u‖*B := by
      simp only [norm_smul]
      exact add_le_add (add_le_add (mul_le_mul hr hx (_root_.norm_nonneg _) (_root_.norm_nonneg _))
        (mul_le_mul hi hy (_root_.norm_nonneg _) (_root_.norm_nonneg _)))
        (mul_le_mul ht hv (_root_.norm_nonneg _) (_root_.norm_nonneg _))
    _ = (3*B)*‖u‖ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Products supported inside positive height extend continuously and
smoothly across the unused boundary, regardless of the other factor there. -/
noncomputable section
open Set Filter Topology MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPositiveProduct_continuous {φ f : ℂ × ℝ → ℂ}
    (hφ : Continuous φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})
    (hf : ContinuousOn f {y : ℂ × ℝ | 0<y.2}) : Continuous (φ*f) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases h : 0<p.2
  · exact hφ.continuousAt.mul (hf.continuousAt ((isOpen_lt continuous_const continuous_snd).mem_nhds h))
  · have hout : p∉tsupport (φ*f) := fun hq => h (hp (tsupport_mul_subset_left hq))
    exact (continuousAt_const : ContinuousAt (fun _ : ℂ × ℝ => (0:ℂ)) p).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hout)

lemma cubicThetaPositiveProduct_integrable {φ f : ℂ × ℝ → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})
    (hf : ContinuousOn f {y : ℂ × ℝ | 0<y.2}) : Integrable (φ*f) :=
  (cubicThetaPositiveProduct_continuous hφ hp hf).integrable_of_hasCompactSupport hc.mul_right

lemma cubicThetaPositiveProduct_contDiff {φ f : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})
    (hf : ContDiffOn ℝ 1 f {y : ℂ × ℝ | 0<y.2}) : ContDiff ℝ 1 (φ*f) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases h : 0<p.2
  · exact (hφ.contDiffOn.mul hf).contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds h)
  · have hout : p∉tsupport (φ*f) := fun hq => h (hp (tsupport_mul_subset_left hq))
    exact (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : ℂ × ℝ => (0:ℂ)) p).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hout)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateIntegrationByParts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integration by parts for the pure coordinate derivatives, with
compact positive-height tests and no assumption on mixed derivatives. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

local instance instIsAddHaarMeasureProdComplexRealVolume_solutions : (volume : Measure (ℂ × ℝ)).IsAddHaarMeasure := by
  change ((volume : Measure ℂ).prod (volume : Measure ℝ)).IsAddHaarMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaWeightedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact tests with the hyperbolic first-derivative weight v^-1.
The support stays away from the singular boundary v=0. -/
noncomputable section
open Set
namespace CubicFirstMoment

def cubicThetaHeightInverse (p : ℂ × ℝ) : ℂ := (p.2⁻¹ : ℝ)

def cubicThetaWeightedTest (φ : ℂ × ℝ → ℂ) (p : ℂ × ℝ) : ℂ :=
  star (φ p)*cubicThetaHeightInverse p

lemma cubicThetaHeightInverse_regular :
    ContDiffOn ℝ 1 cubicThetaHeightInverse {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  have h : ContDiffAt ℝ 1 cubicThetaHeightInverse p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p (contDiffAt_snd.inv hp.ne')
  exact h.contDiffWithinAt

lemma cubicThetaWeightedTest_support (φ : ℂ × ℝ → ℂ) :
    tsupport (cubicThetaWeightedTest φ)⊆tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro p hp
  apply subset_tsupport
  intro h
  exact hp (by simp [cubicThetaWeightedTest,h])

lemma cubicThetaWeightedTest_regular {φ : ℂ × ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hp : tsupport φ⊆{p : ℂ × ℝ | 0<p.2}) : ContDiff ℝ 1 (cubicThetaWeightedTest φ) := by
  have hbar : ContDiff ℝ 1 (fun p => star (φ p)) := by
    exact Complex.conjCLE.contDiff.comp hφ
  have hsupport : tsupport (fun p => star (φ p))⊆tsupport φ := by
    apply closure_minimal _ (isClosed_tsupport φ)
    intro p hp
    apply subset_tsupport
    intro h
    exact hp (by simp [h])
  exact cubicThetaPositiveProduct_contDiff hbar (hsupport.trans hp) cubicThetaHeightInverse_regular

lemma cubicThetaWeightedTest_compact {φ : ℂ × ℝ → ℂ} (hc : HasCompactSupport φ) :
    HasCompactSupport (cubicThetaWeightedTest φ) :=
  hc.of_isClosed_subset isClosed_closure (cubicThetaWeightedTest_support φ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinatePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The intrinsic tangent inner product is the literal three-coordinate
sesquilinear sum. This fixes the local normalization of the weak form. -/
noncomputable section
open scoped Matrix
namespace CubicFirstMoment

lemma cubicThetaLinear_inner_of_norm_eq
    {V E G : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (L : V →ₗ[ℂ] E) (M : V →ₗ[ℂ] G) (h : ∀ v, ‖L v‖=‖M v‖) (v w : V) :
    inner ℂ (L v) (L w)=inner ℂ (M v) (M w) := by
  rw [inner_eq_sum_norm_sq_div_four,inner_eq_sum_norm_sq_div_four]
  simp only [← map_add,← map_sub,← map_smul]
  simp only [h]

def cubicThetaCoordinateValues : ((ℂ × ℝ) →L[ℝ] ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3) where
  toFun L := WithLp.toLp 2 ![L (1,0),L (Complex.I,0),L (0,1)]
  map_add' L M := by ext i; fin_cases i <;> rfl
  map_smul' c L := by ext i; fin_cases i <;> rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFourierNonzero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered Eisenstein expansion on the original half-plane,
with the continued constant coefficient separated from the actual
nonzero arithmetic Fourier coefficients. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicTheta_zero_mode_archimedean {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 1 < s.re)
    (D : ℂ) :
    ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s)*
      (D*(∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s 0 t))=
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)/(s-1))*(v:ℂ)^(2-s)*D := by
  have hs0 : s-1≠0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.sub_re,Complex.one_re,Complex.zero_re] at he
    linarith
  have hg := Complex.Gamma_add_one (s-1) hs0
  rw [sub_add_cancel] at hg
  have hG := Complex.Gamma_ne_zero_of_re_pos
    (show 0<(s-1).re by simp only [Complex.sub_re,Complex.one_re]; linarith)
  have hf := cubicTheta_zero_height_factor hv (by norm_num : (0:ℝ)<1) s
  simp only [div_one,Complex.ofReal_one,Complex.one_cpow,mul_one] at hf
  rw [cubicThetaDualHeat_zero_integral hv hs,hg]
  calc
    _ = ((2*Real.pi/(9*Real.sqrt 3):ℂ)/(s-1))*
        ((v:ℂ)^s*((v^2:ℝ):ℂ)^(1-s))*D := by field_simp
    _ = _ := by rw [hf]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEisensteinTorus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nonconstant Eisenstein Fourier series is a continuous
function on its period torus. Its coefficients retain the arithmetic
Dirichlet series and heat integral, including the zero-mode exclusion. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

local instance instMeasureSpaceUnitAddCircle_solutions_4 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
attribute [local instance] Classical.propDecidable

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMeromorphicLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded linear transport preserves the finite pole order. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaMeromorphic_clm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E →L[ℂ] F) {f : ℂ → E} {z : ℂ} (hf : MeromorphicAt f z) :
    MeromorphicAt (fun w => L (f w)) z := by
  obtain ⟨n,hn⟩ := hf
  refine ⟨n,?_⟩
  have h := (L.analyticAt _).comp (f:=fun w : ℂ => (w-z)^n • f w) (x:=z) hn
  simpa only [Function.comp_def, L.map_smul] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFinitePoleInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Algebra of the finite exceptional block. An invertible correction by
an idempotent gives the exact inverse off its scalar exceptional value. -/
noncomputable section
namespace CubicFirstMoment

variable {A : Type*} [Ring A] [Algebra ℂ A]

omit [Algebra ℂ A] in
lemma energy_commute_inverse
    {T P : A}
    (hT : IsUnit T) (h : Commute T P) : Commute (Ring.inverse T) P := by
  rw [← hT.unit_spec,Ring.inverse_unit]
  have hh : Commute (↑hT.unit) P := by simpa only [hT.unit_spec] using h
  exact hh.units_inv_left

lemma cubicThetaProjection_inverse_data
    (T P : A) (c : ℂ)
    (hPP : P*P=P) (hTP : T*P=c • P) (hPT : P*T=c • P)
    (hunit : IsUnit (T+P)) (hc : c≠0) :
    IsUnit T ∧ Ring.inverse T=Ring.inverse (T+P)*(1-P)+c⁻¹ • P := by
  let V := Ring.inverse (T+P)
  let L := V*(1-P)+c⁻¹ • P
  have hcomm : Commute T P := hTP.trans hPT.symm
  have hVP : Commute V P := energy_commute_inverse hunit
    (hcomm.add_left (Commute.refl P))
  have hVT : Commute V T := energy_commute_inverse hunit
    ((Commute.refl T).add_left hcomm.symm)
  have hvanish : P*V*(1-P)=0 := by
    rw [← hVP.eq,mul_assoc,mul_sub,mul_one,hPP,sub_self,mul_zero]
  have hTV : T*V=1-P*V := by
    calc
      _ = ((T+P)-P)*V := by congr 1; abel
      _ = (T+P)*V-P*V := sub_mul _ _ _
      _ = _ := by rw [Ring.mul_inverse_cancel _ hunit]
  have hscalar : T*(c⁻¹ • P)=P := by
    rw [mul_smul_comm,hTP,smul_smul,inv_mul_cancel₀ hc,one_smul]
  have hright : T*L=1 := by
    calc
      T*L = T*(V*(1-P))+T*(c⁻¹ • P) := mul_add _ _ _
      _ = (T*V)*(1-P)+P := by rw [← mul_assoc,hscalar]
      _ = (1-P*V)*(1-P)+P := by rw [hTV]
      _ = (1-P)-(P*V)*(1-P)+P := by rw [sub_mul,one_mul]
      _ = 1 := by rw [hvanish]; abel
  have hLT : Commute L T := by
    have ha := hVT.mul_left ((Commute.one_left T).sub_left hcomm.symm)
    have hb : Commute (c⁻¹ • P) T := by
      change (c⁻¹ • P)*T=T*(c⁻¹ • P)
      rw [smul_mul_assoc,mul_smul_comm,hPT,hTP]
    exact ha.add_left hb
  have hleft : L*T=1 := hLT.eq.trans hright
  have hT : IsUnit T := ⟨⟨T,L,hright,hleft⟩,rfl⟩
  refine ⟨hT,?_⟩
  change Ring.inverse T=L
  calc
    _ = Ring.inverse T*(T*L) := by rw [hright,mul_one]
    _ = L := by rw [← mul_assoc,Ring.inverse_mul_cancel _ hT,one_mul]

lemma cubicThetaProjection_inverse
    (T P : A) (c : ℂ)
    (hPP : P*P=P) (hTP : T*P=c • P) (hPT : P*T=c • P)
    (hunit : IsUnit (T+P)) (hc : c≠0) :
    Ring.inverse T=Ring.inverse (T+P)*(1-P)+c⁻¹ • P :=
  (cubicThetaProjection_inverse_data T P c hPP hTP hPT hunit hc).2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEnergySimplePole
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact residue of the actual energy inverse. The complementary
inverse is analytic and the exceptional projection gives a simple pole. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

lemma scale_pole {E : Type*} [AddCommGroup E] [Module ℂ E]
    {z w : ℂ} (hw : w≠z) (u v : E) :
    (w-z) • (u+(z/(z-w)) • v)=(w-z) • u+(-z) • v := by
  have hc : (w-z)*(z/(z-w))=-z := by
    field_simp [sub_ne_zero.mpr hw.symm]
    ring
  rw [smul_add,smul_smul,hc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEuclideanSmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth approximation of compact C1 coordinate functions, controlling
both the value and the actual first derivative. -/
noncomputable section
open Set MeasureTheory Metric
open scoped Convolution Pointwise ContDiff
namespace CubicFirstMoment

local instance cubicThetaSmoothing_haar :
    (volume : Measure (ℂ × ℝ)).IsAddHaarMeasure := by
  change ((volume : Measure ℂ).prod (volume : Measure ℝ)).IsAddHaarMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def cubicThetaCoordinateSmooth (φ : ContDiffBump (0 : ℂ × ℝ))
    (g : ℂ × ℝ → ℂ) : ℂ × ℝ → ℂ :=
  φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g

lemma cubicThetaCoordinateSmooth_contDiff (φ : ContDiffBump (0 : ℂ × ℝ))
    {g : ℂ × ℝ → ℂ} (hg : Continuous g) :
    ContDiff ℝ ∞ (cubicThetaCoordinateSmooth φ g) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hg.locallyIntegrable

lemma cubicThetaCoordinateSmooth_compact (φ : ContDiffBump (0 : ℂ × ℝ))
    {g : ℂ × ℝ → ℂ} (hg : HasCompactSupport g) :
    HasCompactSupport (cubicThetaCoordinateSmooth φ g) :=
  φ.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hg

lemma cubicThetaCoordinateSmooth_support (φ : ContDiffBump (0 : ℂ × ℝ))
    {g : ℂ × ℝ → ℂ} (hg : HasCompactSupport g) :
    tsupport (cubicThetaCoordinateSmooth φ g) ⊆
      closedBall (0 : ℂ × ℝ) φ.rOut + tsupport g := by
  apply closure_minimal
  · exact (support_convolution_subset _).trans
      (add_subset_add (by rw [φ.support_normed_eq]; exact ball_subset_closedBall) subset_closure)
  · exact (isCompact_closedBall _ _ |>.add hg).isClosed

lemma cubicThetaCoordinateSmooth_fderiv (φ : ContDiffBump (0 : ℂ × ℝ))
    {g : ℂ × ℝ → ℂ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (x : ℂ × ℝ) :
    fderiv ℝ (cubicThetaCoordinateSmooth φ g) x =
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fderiv ℝ g) x := by
  have h := hc.hasFDerivAt_convolution_right (μ:=volume) (ContinuousLinearMap.lsmul ℝ ℝ)
    ((φ.continuous_normed (μ:=volume)).locallyIntegrable (μ:=volume)) hg x
  unfold cubicThetaCoordinateSmooth
  rw [h.fderiv]
  congr 1

lemma cubicThetaCoordinateSmooth_exists {g : ℂ × ℝ → ℂ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) {ε ρ : ℝ}
    (hε : 0<ε) (hρ : 0<ρ) :
    ∃ φ : ContDiffBump (0 : ℂ × ℝ), φ.rOut<ρ ∧
      (∀ x, ‖cubicThetaCoordinateSmooth φ g x-g x‖≤ε) ∧
      (∀ x, ‖fderiv ℝ (cubicThetaCoordinateSmooth φ g) x-fderiv ℝ g x‖≤ε) := by
  have hu := hc.uniformContinuous_of_continuous hg.continuous
  have hdu := (hc.fderiv ℝ).uniformContinuous_of_continuous (hg.continuous_fderiv one_ne_zero)
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  obtain ⟨δ',hδ',hd'⟩ := Metric.uniformContinuous_iff.mp hdu ε hε
  let r := min ρ (min δ δ') / 2
  have hr : 0 < r := half_pos (lt_min hρ (lt_min hδ hδ'))
  let φ : ContDiffBump (0 : ℂ × ℝ) := ⟨r/2,r,half_pos hr,half_lt_self hr⟩
  have hrρ : r<ρ := (half_lt_self (lt_min hρ (lt_min hδ hδ'))).trans_le (min_le_left _ _)
  have hrδ : r<δ := (half_lt_self (lt_min hρ (lt_min hδ hδ'))).trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have hrδ' : r<δ' := (half_lt_self (lt_min hρ (lt_min hδ hδ'))).trans_le
    ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨φ,hrρ,?_,?_⟩
  · intro x
    rw [← dist_eq_norm]
    exact φ.dist_normed_convolution_le (μ:=volume) (g:=g) hg.continuous.aestronglyMeasurable
      (fun y hy => (hd ((mem_ball.mp hy).trans hrδ)).le)
  · intro x
    rw [cubicThetaCoordinateSmooth_fderiv φ hg hc]
    rw [← dist_eq_norm]
    exact φ.dist_normed_convolution_le (μ:=volume) (g:=fderiv ℝ g)
      (hg.continuous_fderiv one_ne_zero).aestronglyMeasurable
      (fun y hy => (hd' ((mem_ball.mp hy).trans hrδ')).le)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteInflation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact multiplicity in a finite residue-ring inflation. The
surjective reduction is used directly, so no choice of residue representatives
enters the resulting sum identity. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma finite_sum_surjective_addHom {R S : Type*} [AddCommGroup R] [AddCommGroup S]
    [Fintype R] [Fintype S] (r : R →+ S) (hr : Function.Surjective r) (f : S → ℂ) :
    (∑ x : R, f (r x))=(Fintype.card R:ℂ)/(Fintype.card S:ℂ)*∑ y : S, f y := by
  have hshift (y : S) : (∑ x : R, f (r x+y))=∑ x : R, f (r x) := by
    obtain ⟨b,rfl⟩ := hr y
    have he := Equiv.sum_comp (Equiv.addRight b) (fun x => f (r x))
    change (∑ x : R, f (r (x+b)))=∑ x : R, f (r x) at he
    simpa only [map_add] using he
  have he : (Fintype.card S:ℂ)*(∑ x : R, f (r x))=
      (Fintype.card R:ℂ)*(∑ y : S, f y) := by
    calc
      _ = ∑ y : S, ∑ x : R, f (r x+y) := by simp_rw [hshift]; simp
      _ = ∑ x : R, ∑ y : S, f (r x+y) := Finset.sum_comm
      _ = ∑ _x : R, ∑ y : S, f y := by
        apply Finset.sum_congr rfl
        intro x _
        exact Equiv.sum_comp (Equiv.addLeft (r x)) f
      _ = _ := by simp
  have hcard : (Fintype.card S:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  apply (mul_left_cancel₀ hcard)
  calc
    _ = (Fintype.card R:ℂ)*(∑ y : S, f y) := he
    _ = _ := by field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaForcingSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness of the actual forcing follows from the compact cutoff
and the locally finite arithmetic row expansion. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaIncomingForcing_contDiffAt (s : ℂ) {v : ℝ} (hv : 0<v) :
    ContDiffAt ℝ ∞ (cubicThetaIncomingForcing s) v := by
  have hd := (contDiff_infty_iff_deriv.mp cubicThetaCuspCutoff_smooth).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  have hc : ContDiffAt ℝ ∞ (fun t : ℝ => (t:ℂ)) v := Complex.ofRealCLM.contDiff.contDiffAt
  have hp := (cubicThetaHeightPower_analytic s hv).contDiffAt (n:=∞)
  have hp' := (cubicThetaHeightPower_analytic (s-1) hv).contDiffAt (n:=∞)
  exact (((hc.pow 2).mul hdd.contDiffAt).sub (hc.mul hd.contDiffAt)).mul hp |>.add
    (((((contDiffAt_const.mul (hc.pow 2)).mul hd.contDiffAt).mul
      contDiffAt_const).mul hp'))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaForcingBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness makes both cutoff derivatives vanish at the two endpoints,
so the forcing can be reconstructed from the open annulus. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma cubicThetaCuspCutoff_derivatives_zero_closed {v : ℝ} (hv : v≤1 ∨ 2≤v) :
    deriv cubicThetaCuspCutoff v=0 ∧ deriv (deriv cubicThetaCuspCutoff) v=0 := by
  have hd := (contDiff_infty_iff_deriv.mp cubicThetaCuspCutoff_smooth).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  rcases hv with hv | hv
  · have h₁ : EqOn (deriv cubicThetaCuspCutoff) (fun _ => 0) (Iio (1:ℝ)) :=
      fun t ht => (cubicThetaCuspCutoff_derivatives_zero (Or.inl ht)).1
    have h₂ : EqOn (deriv (deriv cubicThetaCuspCutoff)) (fun _ => 0) (Iio (1:ℝ)) :=
      fun t ht => (cubicThetaCuspCutoff_derivatives_zero (Or.inl ht)).2
    have hm : v∈closure (Iio (1:ℝ)) := by simpa only [closure_Iio,mem_Iic] using hv
    exact ⟨h₁.closure hd.continuous continuous_const hm,
      h₂.closure hdd.continuous continuous_const hm⟩
  · have h₁ : EqOn (deriv cubicThetaCuspCutoff) (fun _ => 0) (Ioi (2:ℝ)) :=
      fun t ht => (cubicThetaCuspCutoff_derivatives_zero (Or.inr ht)).1
    have h₂ : EqOn (deriv (deriv cubicThetaCuspCutoff)) (fun _ => 0) (Ioi (2:ℝ)) :=
      fun t ht => (cubicThetaCuspCutoff_derivatives_zero (Or.inr ht)).2
    have hm : v∈closure (Ioi (2:ℝ)) := by simpa only [closure_Ioi,mem_Ici] using hv
    exact ⟨h₁.closure hd.continuous continuous_const hm,
      h₂.closure hdd.continuous continuous_const hm⟩

lemma cubicThetaIncomingForcing_zero_closed (s : ℂ) {v : ℝ} (hv : v≤1 ∨ 2≤v) :
    cubicThetaIncomingForcing s v=0 := by
  obtain ⟨h₁,h₂⟩ := cubicThetaCuspCutoff_derivatives_zero_closed hv
  simp [cubicThetaIncomingForcing,h₁,h₂]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGlobalSpectralResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed global Green operator gives the actual Eisenstein
spectral resolvent initially in Re(s)>2 and at nonreal points of Re(s)>1.
Real poles in (1,2] still require meromorphic continuation. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaGlobalSpectralParameter (s : ℂ) : ℂ := 1-s*(s-2)

lemma cubicThetaGlobalSpectralParameter_regular {s : ℂ} (hs : 1 < s.re)
    (h : s.im≠0 ∨ 2 < s.re) :
    (cubicThetaGlobalSpectralParameter s).im≠0 ∨
      (cubicThetaGlobalSpectralParameter s).re<1 := by
  by_cases hi : s.im=0
  · right
    have hs2 := h.resolve_left (not_not_intro hi)
    simp only [cubicThetaGlobalSpectralParameter,Complex.sub_re,Complex.one_re,
      Complex.mul_re,Complex.sub_im,hi]
    norm_num
    nlinarith [mul_pos (by linarith : 0 < s.re) (by linarith : 0 < s.re-2)]
  · left
    simp only [cubicThetaGlobalSpectralParameter,Complex.sub_im,Complex.one_im,
      Complex.mul_im,Complex.sub_re]
    norm_num
    intro he
    have hp : (2*(s.re-1))*s.im=0 := by nlinarith
    exact hi ((mul_eq_zero.mp hp).resolve_left (by linarith))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGlobalMeromorphic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Meromorphic continuation of the actual global weak resolvent past
the finite exceptional spectrum, throughout the Eisenstein half-plane. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

lemma cubicThetaGlobalSpectralParameter_below_threshold {s : ℂ} (hs : 1 < s.re) :
    (cubicThetaGlobalSpectralParameter s).im≠0 ∨
      (cubicThetaGlobalSpectralParameter s).re<2 := by
  by_cases hi : s.im=0
  · right
    simp only [cubicThetaGlobalSpectralParameter,Complex.sub_re,Complex.one_re,
      Complex.mul_re,Complex.sub_im,hi]
    norm_num
    nlinarith [sq_pos_of_pos (sub_pos.mpr hs)]
  · rcases cubicThetaGlobalSpectralParameter_regular hs (Or.inl hi) with h|h
    · exact Or.inl h
    · exact Or.inr (h.trans (by norm_num))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaWindowProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact radial defect of the compact incoming window. Its difference
from the original forcing is a continuous weight supported in [2,4]. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaIncomingForcing_continuous (s : ℂ) : Continuous (cubicThetaIncomingForcing s) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  by_cases hv : 0<v
  · exact (cubicThetaIncomingForcing_contDiffAt s hv).continuousAt
  · have he : cubicThetaIncomingForcing s =ᶠ[𝓝 v] (fun _ => 0) := by
      filter_upwards [eventually_lt_nhds (show v<1 by linarith)] with t ht
      exact cubicThetaIncomingForcing_zero s (Or.inl ht)
    exact continuousAt_const.congr_of_eventuallyEq he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveStarProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact conjugated test factors preserve integrability in the
positive-height chart. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaStar_support (φ : ℂ × ℝ → ℂ) :
    tsupport (fun p => star (φ p))⊆tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro p hp
  apply subset_tsupport
  intro h
  exact hp (by simp [h])

lemma cubicThetaPositiveStarProduct_integrable {φ f : ℂ × ℝ → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ⊆{p : ℂ × ℝ | 0<p.2})
    (hf : ContinuousOn f {p : ℂ × ℝ | 0<p.2}) :
    Integrable (fun p => star (φ p)*f p) := by
  have hbar : Continuous (fun p => star (φ p)) := continuous_star.comp hφ
  have hcbar : HasCompactSupport (fun p => star (φ p)) :=
    hc.of_isClosed_subset isClosed_closure (cubicThetaStar_support φ)
  exact cubicThetaPositiveProduct_integrable hbar hcbar ((cubicThetaStar_support φ).trans hp) hf

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSmoothingSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate smoothing can keep all supports inside one compact
subset of the chosen open chart. -/
noncomputable section
open Set Metric
open scoped Pointwise ContDiff
namespace CubicFirstMoment

lemma cubicThetaSmoothing_compact_chart {g : ℂ × ℝ → ℂ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {U : Set (ℂ × ℝ)} (hU : IsOpen U) (hs : tsupport g⊆U) :
    ∃ K : Set (ℂ × ℝ), IsCompact K ∧ tsupport g⊆K ∧ K⊆U ∧
      ∀ ε : ℝ, 0<ε → ∃ h : ℂ × ℝ → ℂ,
        ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ tsupport h⊆K ∧
        (∀ x, ‖h x-g x‖≤ε) ∧ (∀ x, ‖fderiv ℝ h x-fderiv ℝ g x‖≤ε) := by
  obtain ⟨ρ,hρ,hsub⟩ := hc.exists_cthickening_subset_open hU hs
  refine ⟨cthickening ρ (tsupport g),hc.cthickening,
    self_subset_cthickening _,hsub,?_⟩
  intro ε hε
  obtain ⟨φ,hφ,hv,hd⟩ := cubicThetaCoordinateSmooth_exists hg hc hε hρ
  refine ⟨cubicThetaCoordinateSmooth φ g,
    cubicThetaCoordinateSmooth_contDiff φ hg.continuous,
    cubicThetaCoordinateSmooth_compact φ hc,?_,hv,hd⟩
  intro x hx
  obtain ⟨a,ha,b,hb,rfl⟩ := cubicThetaCoordinateSmooth_support φ hc hx
  apply mem_cthickening_of_dist_le (a+b) b ρ (tsupport g) hb
  have ha' : ‖a‖≤φ.rOut := by simpa only [mem_closedBall,dist_zero_right] using ha
  simpa only [dist_eq_norm,add_sub_cancel_right] using ha'.trans hφ.le

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarCuspEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scaled cusp cutoffs have uniformly bounded hyperbolic gradient.
The bound uses the unique high primitive row and exact Mobius transport. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

lemma cubicThetaCuspCutoff_scaled_energy (N v : ℝ) :
    v^2*‖deriv (fun t => cubicThetaCuspCutoff (t/N)) v‖^2=
      (v/N)^2*‖deriv cubicThetaCuspCutoff (v/N)‖^2 := by
  have hd := (cubicThetaCuspCutoff_smooth.differentiable (by simp) (v/N)).hasDerivAt.scomp v
    ((hasDerivAt_id v).div_const N)
  have he : deriv (fun t => cubicThetaCuspCutoff (t/N)) v=
      (1/N) • deriv cubicThetaCuspCutoff (v/N) := hd.deriv
  rw [he]
  simp only [one_div,norm_smul,norm_inv,Real.norm_eq_abs,sq_abs,mul_pow,inv_pow,div_pow]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTorusCellIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Haar integration on the cusp torus agrees with the actual half-open
level-three cell, including its boundary convention and Jacobian. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

local instance cubicThetaTorusCellMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMeromorphicApply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Applying a meromorphic operator to an analytic vector preserves its
finite pole order. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaMeromorphic_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {A : ℂ → E →L[ℂ] F} {u : ℂ → E} {z : ℂ}
    (hA : MeromorphicAt A z) (hu : AnalyticAt ℂ u z) :
    MeromorphicAt (fun w => A w (u w)) z := by
  obtain ⟨n,hn⟩ := hA
  refine ⟨n,?_⟩
  have hb := (ContinuousLinearMap.id ℂ (E →L[ℂ] F)).analyticAt_bilinear
    ((z-z)^n • A z,u z)
  have h := hb.comp (f:=fun w => ((w-z)^n • A w,u w)) (x:=z) (hn.prod hu)
  simpa only [Function.comp_def,ContinuousLinearMap.id_apply,
    smul_apply] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSpectralSimplePole
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer of the simple energy pole to the Eisenstein parameter.
The derivative factor is explicit and nonzero on the real interval (1,2). -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

lemma cubicThetaSpectralParameter_gap (a b : ℂ) :
    cubicThetaGlobalSpectralParameter a-cubicThetaGlobalSpectralParameter b=
      (b-a)*(b+a-2) := by
  unfold cubicThetaGlobalSpectralParameter
  ring

lemma cubicThetaSpectralParameter_punctured {σ : ℝ} (hσ : 1<σ) :
    Tendsto cubicThetaGlobalSpectralParameter (𝓝[≠] (σ:ℂ))
      (𝓝[≠] (cubicThetaGlobalSpectralParameter (σ:ℂ))) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact ((continuous_const.sub (continuous_id.mul (continuous_id.sub continuous_const))).tendsto _).mono_left
      nhdsWithin_le_nhds
  · have hnear : ∀ᶠ s : ℂ in 𝓝 (σ:ℂ), 1 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simpa using hσ)
    filter_upwards [nhdsWithin_le_nhds hnear,self_mem_nhdsWithin] with s hs hne
    change cubicThetaGlobalSpectralParameter s≠cubicThetaGlobalSpectralParameter (σ:ℂ)
    intro he
    have hprod : (s-(σ:ℂ))*(s+(σ:ℂ)-2)=0 := by
      rw [← cubicThetaSpectralParameter_gap,he,sub_self]
    have hsum : s+(σ:ℂ)-2≠0 := by
      intro hz
      have hre := congrArg Complex.re hz
      simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.zero_re] at hre
      norm_num at hre
      linarith
    exact hne (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hsum))

lemma cubicThetaRealSpectralParameter_closedRange {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2) :
    0<1-σ*(σ-2) ∧ 1-σ*(σ-2)<2 := by
  constructor
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : 0≤σ) (by linarith : σ-2≤0)]
  · nlinarith [sq_pos_of_pos (by linarith : 0<σ-1)]

lemma spectral_rescale {E : Type*} [AddCommGroup E] [Module ℂ E]
    (a b : ℂ) (hb : b+a-2≠0) (u : E) :
    -(b+a-2)⁻¹ • ((cubicThetaGlobalSpectralParameter b-cubicThetaGlobalSpectralParameter a) • u)=
      (b-a) • u := by
  rw [smul_smul,cubicThetaSpectralParameter_gap]
  have he : -(b+a-2)⁻¹*((a-b)*(a+b-2))=b-a := by
    have hba : a+b-2=b+a-2 := by ring
    rw [hba]
    field_simp [hb]
    ring
  rw [he]

lemma rescale_associative {E : Type*} [AddCommGroup E] [Module ℂ E]
    (a b : ℂ) (u : E) : a • (b • u)=(a*b) • u := smul_smul a b u

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialTent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete nonnegative radial test supported in [2,4]. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaRadialTent (v : ℝ) : ℝ := max 0 (1-|v-3|)

lemma cubicThetaRadialTent_continuous : Continuous cubicThetaRadialTent := by
  unfold cubicThetaRadialTent
  fun_prop

lemma cubicThetaRadialTent_compact : HasCompactSupport cubicThetaRadialTent := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (2:ℝ) 4))
  intro v hv
  have hp : 0<1-|v-3| := by
    by_contra hn
    exact hv (max_eq_left (le_of_not_gt hn))
  have h := abs_lt.mp (show |v-3|<1 by linarith)
  constructor <;> linarith

def cubicThetaRadialTestWeight : C_c(ℝ,ℂ) where
  toFun v := (cubicThetaRadialTent v:ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp cubicThetaRadialTent_continuous
  hasCompactSupport' := cubicThetaRadialTent_compact.comp_left
    (g:=fun x : ℝ => (x:ℂ)) (by simp)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaZeroObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The genuine zero-frequency observation retains the explicit
arithmetic scattering coefficient. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaZeroRadialTest (W : C_c(ℝ,ℂ)) (s : ℂ) : ℂ :=
  ∫ v in Ioi (2:ℝ), star (W v)*(v:ℂ)^(2-s)/(v:ℂ)^3

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScatteringMeromorphic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit scattering coefficient and actual constant observation
agree meromorphically, without assuming nonvanishing of a zeta factor. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

lemma cubicThetaRamifiedPower_analytic (b s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => (3:ℂ)^(b-3*z)) s := by
  let _ : NeZero (3:ℂ) := ⟨by norm_num⟩
  exact
    ((differentiable_const_cpow_of_neZero (3:ℂ)).analyticAt _).comp
      (f:=fun z : ℂ => b-3*z) (x:=s) (by fun_prop)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaZeroWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact radial windows supported above height two retain the exact
constant-mode continuation. They will test the high annular forcing. -/
noncomputable section
open Set Filter MeasureTheory Topology
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaZeroRadialWindow_mellin (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ), W v=0) (s : ℂ) :
    cubicThetaZeroRadialTest W s=
      mellin (star W) (-s) := by
  have he : (∫ v in Ioi (2:ℝ), star (W v)*(v:ℂ)^(2-s)/(v:ℂ)^3)=
      ∫ v in Ioi (2:ℝ), (v:ℂ)^(-s-1)*star (W v) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    change 2<v at hv
    dsimp only
    have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have hp : (v:ℂ)^(2-s)/(v:ℂ)^3=(v:ℂ)^(-s-1) := by
      rw [← Complex.cpow_natCast,← Complex.cpow_sub _ _ hv0]
      congr 1
      norm_num
      ring
    calc
      _ = ((v:ℂ)^(2-s)/(v:ℂ)^3)*star (W v) := by ring
      _ = _ := by rw [hp]
  unfold cubicThetaZeroRadialTest
  rw [he]
  have h₂ : (∫ v in Ioi (2:ℝ), (v:ℂ)^(-s-1)*star (W v))=
      ∫ v : ℝ, (v:ℂ)^(-s-1)*star (W v) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [hW v (le_of_not_gt hv),star_zero,mul_zero]
  have h₀ : (∫ v in Ioi (0:ℝ), (v:ℂ)^(-s-1)*star (W v))=
      ∫ v : ℝ, (v:ℂ)^(-s-1)*star (W v) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [hW v (le_trans (le_of_not_gt hv) (by norm_num)),star_zero,mul_zero]
  rw [h₂,← h₀]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialWeightScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact radial test functions under positive dilations. These are the
literal tests induced by the Hecke constant-mode identity. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaRadialWeightScale (r : ℝ) (hr : 0 < r) (W : C_c(ℝ,ℂ)) : C_c(ℝ,ℂ) :=
  W.comp (Homeomorph.mulLeft₀ r hr.ne').toCocompactMap

lemma cubicThetaRadialWeightScale_apply (r : ℝ) (hr : 0 < r) (W : C_c(ℝ,ℂ)) (v : ℝ) :
    cubicThetaRadialWeightScale r hr W v=W (r*v) := rfl

lemma cubicThetaRadialWeightScale_mellin (r : ℝ) (hr : 0 < r) (W : C_c(ℝ,ℂ)) (s : ℂ) :
    mellin (star (cubicThetaRadialWeightScale r hr W)) s=
      (r:ℂ)^(-s)*mellin (star W) s := by
  have he : (star (cubicThetaRadialWeightScale r hr W) : ℝ → ℂ)=
      fun v => (star W : ℝ → ℂ) (r*v) := rfl
  rw [he,mellin_comp_mul_left _ _ hr]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLongWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact incoming window between heights one and H. Its defect is
exactly the difference of the original and dilated annular forcing. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff CompactlySupported
namespace CubicFirstMoment

def cubicThetaIncomingForcingWeight (s : ℂ) : C_c(ℝ,ℂ) where
  toFun := cubicThetaIncomingForcing s
  continuous_toFun := cubicThetaIncomingForcing_continuous s
  hasCompactSupport' := cubicThetaIncomingForcing_compact s

def cubicThetaLongForcingWeight (H : ℝ) (hH : 0<H) (s : ℂ) : C_c(ℝ,ℂ) :=
  (H:ℂ)^s • cubicThetaRadialWeightScale H⁻¹ (inv_pos.mpr hH) (cubicThetaIncomingForcingWeight s)

lemma cubicThetaLongForcingWeight_apply (H : ℝ) (hH : 0<H) (s : ℂ) (v : ℝ) :
    cubicThetaLongForcingWeight H hH s v=(H:ℂ)^s*cubicThetaIncomingForcing s (v/H) := by
  change (H:ℂ)^s*cubicThetaIncomingForcing s (H⁻¹*v)=_
  rw [div_eq_mul_inv,mul_comm H⁻¹ v]

lemma cubicThetaLongForcingWeight_low {H : ℝ} (hH : 0<H) (s : ℂ)
    {v : ℝ} (hv : v≤H) : cubicThetaLongForcingWeight H hH s v=0 := by
  rw [cubicThetaLongForcingWeight_apply,cubicThetaIncomingForcing_zero_closed s
    (Or.inl ((div_le_one hH).mpr hv)),mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialMeanIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Change of height in the literal v^-3 radial mean integral. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRadialIntegral_zero_extension (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ), W v=0) (f : ℝ → ℂ) :
    (∫ v in Ioi (2:ℝ),star (W v)/(v:ℂ)^3*f v)=
      ∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*f v := by
  have h (a : ℝ) (ha : a≤2) :
      (∫ v in Ioi a,star (W v)/(v:ℂ)^3*f v)=
        ∫ v : ℝ,star (W v)/(v:ℂ)^3*f v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [hW v ((le_of_not_gt hv).trans ha),star_zero,zero_div,zero_mul]
  rw [h 2 le_rfl,h 0 (by norm_num)]

lemma cubicThetaRadialIntegral_dilate (r : ℝ) (hr : 0 < r)
    (W : C_c(ℝ,ℂ)) (f : ℝ → ℂ) :
    (∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*f (r*v))=
      (r:ℂ)^2*∫ v in Ioi (0:ℝ),star (W (v/r))/(v:ℂ)^3*f v := by
  let g : ℝ → ℂ := fun v => star (W (v/r))/(v:ℂ)^3*f v
  have he : (fun v => star (W v)/(v:ℂ)^3*f (r*v))=
      (fun v => (r:ℂ)^3*g (r*v)) := by
    funext v
    dsimp only [g]
    rw [mul_div_cancel_left₀ v hr.ne',Complex.ofReal_mul,mul_pow]
    by_cases hv : v=0
    · simp [hv]
    · have hr0 : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
      have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv
      field_simp
  rw [he,integral_const_mul,integral_comp_mul_left_Ioi g 0 hr,mul_zero]
  simp only [Complex.real_smul,Complex.ofReal_inv]
  have hr0 : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  dsimp only [g]
  field_simp

lemma cubicThetaRadialIntegral_integrable_zero_extension (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ), W v=0) (f : ℝ → ℂ)
    (hf : IntegrableOn (fun v => star (W v)/(v:ℂ)^3*f v) (Ioi (2:ℝ))) :
    IntegrableOn (fun v => star (W v)/(v:ℂ)^3*f v) (Ioi (0:ℝ)) := by
  let g : ℝ → ℂ := fun v => star (W v)/(v:ℂ)^3*f v
  have he : (Ioi (0:ℝ)).indicator g=(Ioi (2:ℝ)).indicator g := by
    funext v
    change (if 0<v then g v else 0)=(if 2<v then g v else 0)
    split_ifs with h0 h2 h2
    · rfl
    · dsimp only [g]
      rw [hW v (le_of_not_gt h2),star_zero,zero_div,zero_mul]
    · have : False := h0 (lt_trans (by norm_num) h2)
      exact this.elim
    · rfl
  rw [←integrable_indicator_iff measurableSet_Ioi] at hf ⊢
  change Integrable ((Ioi (0:ℝ)).indicator g)
  rw [he]
  exact hf

lemma cubicThetaRadialIntegral_dilate_integrable (r : ℝ) (hr : 0 < r)
    (W : C_c(ℝ,ℂ)) (f : ℝ → ℂ)
    (hf : IntegrableOn (fun v => star (W (v/r))/(v:ℂ)^3*f v) (Ioi (0:ℝ))) :
    IntegrableOn (fun v => star (W v)/(v:ℂ)^3*f (r*v)) (Ioi (0:ℝ)) := by
  let g : ℝ → ℂ := fun v => star (W (v/r))/(v:ℂ)^3*f v
  have hg : IntegrableOn (fun v => g (r*v)) (Ioi (0:ℝ)) :=
    (integrableOn_Ioi_comp_mul_left_iff g 0 hr).mpr (by simpa only [mul_zero] using (show IntegrableOn g (Ioi (0:ℝ)) from hf))
  apply (hg.const_mul ((r:ℂ)^3)).congr
  filter_upwards with v
  dsimp only [g]
  rw [mul_div_cancel_left₀ v hr.ne',Complex.ofReal_mul,mul_pow]
  by_cases hv : v=0
  · simp [hv]
  · have hr0 : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv
    field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialHeckeWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact radial test dual to the two surviving Hecke height branches. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaRadialHeckeWeight (r : ℝ) (hr : 0 < r) (W : C_c(ℝ,ℂ)) : C_c(ℝ,ℂ) :=
  (r:ℂ)^2 • cubicThetaRadialWeightScale r⁻¹ (inv_pos.mpr hr) W+
    cubicThetaRadialWeightScale r hr W

lemma cubicThetaRadialHeckeWeight_apply (r : ℝ) (hr : 0 < r) (W : C_c(ℝ,ℂ)) (v : ℝ) :
    cubicThetaRadialHeckeWeight r hr W v=(r:ℂ)^2*W (v/r)+W (r*v) := by
  change (r:ℂ)^2*W (r⁻¹*v)+W (r*v)=_
  rw [div_eq_mul_inv,mul_comm r⁻¹ v]

lemma cubicThetaRadialHeckeWeight_low {r H : ℝ} (hr : 1 ≤ r) (hH : 0≤H) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤H*r,W v=0) :
    ∀ v≤H, cubicThetaRadialHeckeWeight r (by linarith) W v=0 := by
  intro v hv
  rw [cubicThetaRadialHeckeWeight_apply]
  have hratio : v/r≤H*r := by
    rw [div_le_iff₀ (by linarith : 0 < r)]
    have : 1 ≤ r*r := by nlinarith
    nlinarith
  rw [hW _ hratio,hW _ (by nlinarith),mul_zero,zero_add]

lemma cubicThetaRadialIntegral_hecke (r : ℝ) (hr : 0 < r) (W : C_c(ℝ,ℂ))
    (f : ℝ → ℂ)
    (ha : IntegrableOn (fun v => star (W (v/r))/(v:ℂ)^3*f v) (Ioi (0:ℝ)))
    (hb : IntegrableOn (fun v => star (W (r*v))/(v:ℂ)^3*f v) (Ioi (0:ℝ))) :
    (∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*(f (r*v)+(r:ℂ)^2*f (v/r)))=
      (r:ℂ)^2*(∫ v in Ioi (0:ℝ),star (W (v/r))/(v:ℂ)^3*f v)+
        ∫ v in Ioi (0:ℝ),star (W (r*v))/(v:ℂ)^3*f v := by
  have harg (v : ℝ) : v/r⁻¹=r*v := by simp [div_eq_mul_inv,mul_comm]
  have harg' (v : ℝ) : r⁻¹*v=v/r := by simp [div_eq_mul_inv,mul_comm]
  have hb' : IntegrableOn (fun v => star (W (v/r⁻¹))/(v:ℂ)^3*f v) (Ioi (0:ℝ)) := by
    simpa only [harg] using hb
  have hA := cubicThetaRadialIntegral_dilate_integrable r hr W f ha
  have hB := cubicThetaRadialIntegral_dilate_integrable r⁻¹ (inv_pos.mpr hr) W f hb'
  simp only [harg'] at hB
  have he := cubicThetaRadialIntegral_dilate r⁻¹ (inv_pos.mpr hr) W f
  simp only [harg,harg',Complex.ofReal_inv] at he
  calc
    _ = (∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*f (r*v))+
        (r:ℂ)^2*(∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*f (v/r)) := by
      rw [←integral_const_mul,←integral_add hA (hB.const_mul _)]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v _
      ring
    _ = _ := by
      rw [cubicThetaRadialIntegral_dilate r hr W f,he]
      have hr0 : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
      field_simp

lemma cubicThetaRadialHeckeWeight_integral (r : ℝ) (hr : 0 < r) (W : C_c(ℝ,ℂ))
    (f : ℝ → ℂ)
    (ha : IntegrableOn (fun v => star (W (v/r))/(v:ℂ)^3*f v) (Ioi (0:ℝ)))
    (hb : IntegrableOn (fun v => star (W (r*v))/(v:ℂ)^3*f v) (Ioi (0:ℝ))) :
    (∫ v in Ioi (0:ℝ),star (cubicThetaRadialHeckeWeight r hr W v)/(v:ℂ)^3*f v)=
      (r:ℂ)^2*(∫ v in Ioi (0:ℝ),star (W (v/r))/(v:ℂ)^3*f v)+
        ∫ v in Ioi (0:ℝ),star (W (r*v))/(v:ℂ)^3*f v := by
  rw [←integral_const_mul,←integral_add (ha.const_mul _) hb]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  dsimp only
  rw [cubicThetaRadialHeckeWeight_apply]
  simp only [star_add,star_mul,star_pow,Complex.star_def,Complex.conj_ofReal]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialMellin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mellin identities of the actual compact radial tests. -/
noncomputable section
open Set
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRadialWeight_mellinConvergent (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ),W v=0) (s : ℂ) : MellinConvergent (star W : ℝ → ℂ) s := by
  have hs : tsupport (star W)⊆Ici (2:ℝ) := by
    apply closure_minimal ?_ isClosed_Ici
    intro v hv
    by_contra hn
    apply hv
    change star (W v)=0
    rw [hW v (le_of_not_ge hn),star_zero]
  exact smooth_mellin_convergent (star W) (star W).hasCompactSupport
    (fun v hv => lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (hs hv)) (star W).continuous s

lemma cubicThetaZeroRadialTest_add (W V : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ),W v=0) (hV : ∀ v≤(2:ℝ),V v=0) (s : ℂ) :
    cubicThetaZeroRadialTest (W+V) s=cubicThetaZeroRadialTest W s+cubicThetaZeroRadialTest V s := by
  have hsum : ∀ v≤(2:ℝ),(W+V) v=0 := by
    intro v hv
    change W v+V v=0
    rw [hW v hv,hV v hv,add_zero]
  rw [cubicThetaZeroRadialWindow_mellin _ hsum,cubicThetaZeroRadialWindow_mellin W hW,
    cubicThetaZeroRadialWindow_mellin V hV]
  have he : star (↑(W+V) : ℝ → ℂ)=(fun v => (star W : ℝ → ℂ) v+(star V : ℝ → ℂ) v) := by
    funext v
    change star (W v+V v)=star (W v)+star (V v)
    exact star_add _ _
  rw [he]
  exact (hasMellin_add (cubicThetaRadialWeight_mellinConvergent W hW (-s))
    (cubicThetaRadialWeight_mellinConvergent V hV (-s))).2

lemma cubicThetaZeroRadialTest_smul (c : ℂ) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ),W v=0) (s : ℂ) :
    cubicThetaZeroRadialTest (c • W) s=star c*cubicThetaZeroRadialTest W s := by
  have hc : ∀ v≤(2:ℝ),(c • W) v=0 := by
    intro v hv
    change c*W v=0
    rw [hW v hv,mul_zero]
  rw [cubicThetaZeroRadialWindow_mellin _ hc,cubicThetaZeroRadialWindow_mellin W hW]
  have he : star (↑(c • W) : ℝ → ℂ)=(fun v => star c • (star W : ℝ → ℂ) v) := by
    funext v
    change star (c*W v)=star c*star (W v)
    rw [star_mul,mul_comm]
  rw [he,mellin_const_smul]
  rfl

lemma cubicThetaZeroRadialTest_scale (r : ℝ) (hr : 0 < r) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ),W v=0)
    (hS : ∀ v≤(2:ℝ),cubicThetaRadialWeightScale r hr W v=0) (s : ℂ) :
    cubicThetaZeroRadialTest (cubicThetaRadialWeightScale r hr W) s=
      (r:ℂ)^s*cubicThetaZeroRadialTest W s := by
  rw [cubicThetaZeroRadialWindow_mellin _ hS,cubicThetaZeroRadialWindow_mellin W hW,
    cubicThetaRadialWeightScale_mellin,neg_neg]

lemma cubicThetaZeroRadialTest_hecke (r : ℝ) (hr : 0 < r) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ),W v=0)
    (hA : ∀ v≤(2:ℝ),cubicThetaRadialWeightScale r⁻¹ (inv_pos.mpr hr) W v=0)
    (hB : ∀ v≤(2:ℝ),cubicThetaRadialWeightScale r hr W v=0) (s : ℂ) :
    cubicThetaZeroRadialTest (cubicThetaRadialHeckeWeight r hr W) s=
      ((r:ℂ)^2*(r⁻¹:ℝ)^s+(r:ℂ)^s)*cubicThetaZeroRadialTest W s := by
  unfold cubicThetaRadialHeckeWeight
  rw [cubicThetaZeroRadialTest_add _ _ (by
    intro v hv
    change (r:ℂ)^2*cubicThetaRadialWeightScale r⁻¹ (inv_pos.mpr hr) W v=0
    rw [hA v hv,mul_zero]) hB,
    cubicThetaZeroRadialTest_smul _ _ hA,
    cubicThetaZeroRadialTest_scale _ _ W hW hA,
    cubicThetaZeroRadialTest_scale _ _ W hW hB]
  simp only [star_pow,Complex.star_def,Complex.conj_ofReal]
  ring

end CubicFirstMoment

end

end OAI
end


