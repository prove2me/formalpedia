-- Prove2me | Definitions.Def_OAIQ237Ny001
-- name    : OAIQ237Ny001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T00:02:50.49297+00:00
-- url     : https://prove2.me/theorems/4444ef54-bf83-4f30-808b-fb4b1a4ae4f2
-- title:
--   Definitions bundle OAIQ237Ny001 of the split of OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 270 declarations of OpenAI's Lean: 123 definitions, 8 instances and 139 theorems. The definitions and types are `OAI.Yau.Geometry.planeRadialCovector`, `OAI.Yau.Geometry.radialComponent`, `OAI.Yau.Geometry.realCutoffRadius`, `OAI.Yau.Geometry.realFinCube`, `OAI.Yau.Geometry.realJetErrorTerms`, `OAI.Yau.Geometry.realScaledCube`, `OAI.Yau.Jets.Poly`, `OAI.Yau.Jets.direction`, `OAI.Yau.Jets.original`, `OAI.Yau.Jets.transverse`, `OAI.Yau.Probability.covarianceFactor`, `OAI.Yau.Probability.covarianceMatrix`, `OAI.Yau.Probability.gaussianPairs`, `OAI.Yau.Probability.pairJetMap`, `OAI.Yau.RealEuclideanL2`, `OAI.Yau.Target.Ambient`, `OAI.Yau.Target.AmbientBase`, `OAI.Yau.Target.BaseModel`, `OAI.Yau.Target.CircleModel`, `OAI.Yau.Target.CotangentModel`, `OAI.Yau.Target.IntrinsicTensor`, `OAI.Yau.Target.IntrinsicTensorSmooth`, `OAI.Yau.Target.SeedAmbient`, `OAI.Yau.Target.SphereChartCubeL2`, `OAI.Yau.Target.SphereCotangent`, `OAI.Yau.Target.ambientCircleWeight`, `OAI.Yau.Target.ambientComplexSeed`, `OAI.Yau.Target.ambientFormMatrix`, `OAI.Yau.Target.ambientMatrixForm`, `OAI.Yau.Target.ambientRealSeed`, `OAI.Yau.Target.ambientRoundBilinear`, `OAI.Yau.Target.baseChartDensity`, `OAI.Yau.Target.baseCovectorCoordinates`, `OAI.Yau.Target.centeredSphereIsometry`, `OAI.Yau.Target.chartBilinearForm`, `OAI.Yau.Target.circleChartDerivative`, `OAI.Yau.Target.circleChartFactor`, `OAI.Yau.Target.circleLift`, `OAI.Yau.Target.indexedProductFrame`, `OAI.Yau.Target.instAddCommGroupContinuousLinearMapRealIdSphereCotangent` and 83 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `NodalSets_Charts_BaseChartFlux`, `NodalSets_Charts_CenteredSphereChart`, `NodalSets_Charts_CenteredSphereMetricLemmas`, `NodalSets_Charts_CenteredSphereSecondJet`, `NodalSets_Charts_ChartFrameSmooth`, `NodalSets_Charts_CircleChartFactor`, `NodalSets_Charts_CircleInvariantDerivative`, `NodalSets_Charts_IndependentAmbientMetric`, `NodalSets_Charts_ProductChartPullback`, `NodalSets_Charts_RadialMetricIdentification`, `NodalSets_Charts_RoundChartConnection`, `NodalSets_Charts_RoundCotangentSmooth`, `NodalSets_Charts_RoundCotangentTensor`, `NodalSets_Charts_SmoothBundleInverse`, `NodalSets_Charts_SphereChartDerivativeMap`, `NodalSets_Charts_SphereChartOpenMap`, `NodalSets_Charts_SphereChartTangentTrace`, `NodalSets_Charts_SphereChartVolume`, `NodalSets_Charts_SphereContravariant`, `NodalSets_Charts_SphereCovectorRestriction`, `NodalSets_Charts_SphereMeasureChartGeometry`, `NodalSets_Charts_SphereReferenceMeasure`, `NodalSets_Charts_SphereReferenceMeasureFinite`, `NodalSets_Charts_SphereReferenceMeasureInvariance`, `NodalSets_Charts_SphereReferenceMeasurePositive`, `NodalSets_Charts_SphereUniformDensityPairingLimit`, `NodalSets_Charts_SphereWeightedL2`, `NodalSets_Charts_SphereWeightedPairingLimit`, `NodalSets_Charts_TangentialMatrixInverse`, `NodalSets_Charts_TargetChartBasis`, `NodalSets_Coefficients_CoefficientAmbientReconstruction`, `NodalSets_Coefficients_GaussianCoefficientVariance`, `NodalSets_Coefficients_MatrixCoefficientMap`, `NodalSets_Elliptic_AmbientFormMatrix`, `NodalSets_Elliptic_AmbientMatrixForm`, `NodalSets_Elliptic_CorrugationDiskJets`, `NodalSets_Elliptic_CorrugationRadialJetsLemmas`, `NodalSets_Elliptic_DirectionalJet`, `NodalSets_Elliptic_FiniteCertificateWeight`, `NodalSets_Elliptic_IntrinsicAmbientExtension`, `NodalSets_Elliptic_IntrinsicAmbientSmooth`, `NodalSets_Elliptic_IntrinsicRoundPerturbation`, `NodalSets_Elliptic_PolynomialJet`, `NodalSets_Elliptic_PositiveContravariant`, `NodalSets_Elliptic_RealBallCutoffChain`, `NodalSets_Elliptic_RealCompactL2`, `NodalSets_Elliptic_RealCompactL2MapLemmas`, `NodalSets_Elliptic_RealCompactL2Product`, `NodalSets_Elliptic_RealCompactMultiplierLemmas`, `NodalSets_Elliptic_RealCubeL2EmbeddingLemmas`, `NodalSets_Elliptic_RealFinCubeFubini`, `NodalSets_Elliptic_RealGlobalL2Multiplier`, `NodalSets_Elliptic_RealJetProductExpansion`, `NodalSets_Elliptic_RealL2DifferenceLimit`, `NodalSets_Elliptic_RealL2DifferenceQuotient`, `NodalSets_Elliptic_RealPositiveNestedRadii`, `NodalSets_Elliptic_RealScaledCubeIntegration`, `NodalSets_Elliptic_SeedConcretePoint`, `NodalSets_Elliptic_SeedCoordinateCube`, `NodalSets_Elliptic_SeedLogConcreteJets`, `NodalSets_Elliptic_SeedLogNonvanishing`, `NodalSets_Elliptic_SeedLogarithmicBranch`, `NodalSets_Elliptic_SeedPatchTopology`, `NodalSets_Elliptic_SeedPolynomialDerivatives`, `NodalSets_Elliptic_SeedRoundAdmissibility`, `NodalSets_Elliptic_SeedRoundPatch`, `NodalSets_Elliptic_SphericalSeed`, `NodalSets_Elliptic_StereographicSecondDerivative`, `NodalSets_Elliptic_TargetEmbedding`, `NodalSets_Hausdorff_NodalProjection`, `NodalSets_Spectral_SphereRadialProjection`, `NodalSets_Waves_FiniteGaussianMap`, `NodalSets_Waves_GaussianFactor`.
--
--   **Imports.** It imports the published bundle `Def_YauCounterexample`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ237Ny002` and `OAIQ237Ny003`; the statements `OAI.Yau.Geometry.LocalCompactWaveData.actual_lattice_gaussian_small_ball`, `OAI.Yau.Geometry.LocalCompactWaveData.lattice_good_event_probability` and `OAI.Yau.Geometry.lattice_physical_sign_subballs_fixed_domain`; the proof of `OAI.Yau.Geometry.LocalCompactWaveData.lattice_good_event_probability`.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.UniformConvergence
import Definitions.Def_YauCounterexample

section
-- module Solutions.OAIQ237_NY.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PolynomialJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MvPolynomial Finsupp
noncomputable section

def primitive {σ K : Type*} [Field K] (i : σ) (p : MvPolynomial σ K) :
    MvPolynomial σ K :=
  ∑ s ∈ p.support, monomial (s + single i 1) (p.coeff s / ((s i : K) + 1))

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_DirectionalJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
namespace Jets
open MvPolynomial
noncomputable section
variable {σ K : Type*} [Field K] [DecidableEq σ]
abbrev Poly (σ K : Type*) [CommSemiring K] := MvPolynomial σ K

def direction (v : σ → K) : Derivation K (Poly σ K) (Poly σ K) :=
  mkDerivation K (fun j ↦ C (v j))

def transverse (v : σ → K) (i j : σ) : Poly σ K :=
  if j = i then C ((v i)⁻¹) * X i
  else X j + C (-(v j / v i)) * X i

def original (v : σ → K) (i j : σ) : Poly σ K :=
  if j = i then C (v i) * X i else X j + C (v j) * X i

end
end Jets
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_TargetEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff
noncomputable section
abbrev AmbientBase := EuclideanSpace ℝ (Fin 5)
abbrev Ambient := AmbientBase × ℂ
attribute [local instance] finrank_real_complex_fact'
local instance instFactEqNatFinrankRealAmbientBaseHAddOfNat : Fact (Module.finrank ℝ AmbientBase = 4 + 1) := ⟨by simp [AmbientBase]⟩

def targetEmbedding (x : Manifold5) : Ambient := ((x.1 : AmbientBase),(x.2 : ℂ))

lemma targetEmbedding_smooth : ContMDiff modelWithCorners 𝓘(ℝ,Ambient) ∞ targetEmbedding := by
  rw [show 𝓘(ℝ,Ambient) = 𝓘(ℝ,AmbientBase).prod 𝓘(ℝ,ℂ) from modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact (contMDiff_coe_sphere (E := AmbientBase) (n := 4)).prodMap
    (contMDiff_coe_sphere (E := ℂ) (n := 1))

lemma targetEmbedding_derivative (x : Manifold5) :
    mfderiv modelWithCorners 𝓘(ℝ,Ambient) targetEmbedding x =
      (mfderiv (𝓡 4) 𝓘(ℝ,AmbientBase) (Subtype.val : Base → AmbientBase) x.1).prodMap
      (mfderiv (𝓡 1) 𝓘(ℝ,ℂ) (fun z : Circle ↦ (z : ℂ)) x.2) := by
  rw [show 𝓘(ℝ,Ambient) = 𝓘(ℝ,AmbientBase).prod 𝓘(ℝ,ℂ) from modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mfderiv_prodMap
    ((contMDiff_coe_sphere (E := AmbientBase) (n := 4) (m := ∞)).mdifferentiable (by simp) x.1)
    ((contMDiff_coe_sphere (E := ℂ) (n := 1) (m := ∞)).mdifferentiable (by simp) x.2)

lemma targetEmbedding_immersion (x : Manifold5) :
    Function.Injective (mfderiv modelWithCorners 𝓘(ℝ,Ambient) targetEmbedding x) := by
  rw [targetEmbedding_derivative]
  intro v w he
  apply Prod.ext
  · apply injective_mvfderiv_subtypeVal_sphere (n := 4) x.1
    exact congrArg Prod.fst he
  · apply injective_mvfderiv_subtypeVal_sphere (n := 1) x.2
    exact congrArg Prod.snd he

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_AmbientMatrixForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix ContinuousLinearMap
open scoped ContDiff
noncomputable section

def ambientMatrixForm (A : Matrix (Fin 5) (Fin 5) ℝ) :
    AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ :=
  ∑ i, ∑ j, A i j • ((innerSL ℝ (EuclideanSpace.basisFun (Fin 5) ℝ i)).smulRight
    (innerSL ℝ (EuclideanSpace.basisFun (Fin 5) ℝ j)))

lemma ambientMatrixForm_apply (A : Matrix (Fin 5) (Fin 5) ℝ) (v w : AmbientBase) :
    ambientMatrixForm A v w = ∑ i, ∑ j, v i * A i j * w j := by
  simp [ambientMatrixForm, EuclideanSpace.inner_single_left,mul_comm,mul_assoc]

lemma ambientMatrixForm_symm (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.IsHermitian)
    (v w : AmbientBase) : ambientMatrixForm A v w = ambientMatrixForm A w v := by
  rw [ambientMatrixForm_apply,ambientMatrixForm_apply,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h := hA.apply i j
  simp only [star_trivial] at h
  rw [h]
  ring

lemma ambientMatrixForm_pos (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    (v : AmbientBase) (hv : v ≠ 0) : 0 < ambientMatrixForm A v v := by
  have hn : (fun i ↦ v i) ≠ 0 := by
    intro he
    apply hv
    ext i
    exact congrFun he i
  have hh := hA.dotProduct_mulVec_pos hn
  rw [ambientMatrixForm_apply]
  simpa [dotProduct,mulVec,Finset.mul_sum,mul_assoc] using hh

lemma ambientMatrixForm_smooth (A : Base → Matrix (Fin 5) (Fin 5) ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j)) :
    ContMDiff (𝓡 4) 𝓘(ℝ,AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ) ∞
      (fun x ↦ ambientMatrixForm (A x)) := by
  unfold ambientMatrixForm
  apply ContMDiff.sum
  intro i _
  apply ContMDiff.sum
  intro j _
  exact (hA i j).smul contMDiff_const

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_IndependentAmbientMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix
open scoped ContDiff
noncomputable section

def ambientCircleWeight (A : Matrix (Fin 5) (Fin 5) ℝ) (rho : ℝ) : ℝ :=
  Real.sqrt A.det / rho

lemma ambientCircleWeight_pos (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    {rho : ℝ} (hr : 0 < rho) : 0 < ambientCircleWeight A rho :=
  div_pos (Real.sqrt_pos.mpr hA.det_pos) hr

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_TangentialMatrixInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma symmetric_dot_mulVec (A : Matrix n n ℝ) (hA : A.IsHermitian) (x v : n → ℝ) :
    x ⬝ᵥ (A *ᵥ v) = (A *ᵥ x) ⬝ᵥ v := by
  simp only [dotProduct,mulVec,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h := hA.apply i j
  simp only [star_trivial] at h
  rw [h]
  ring

omit [DecidableEq n] in
lemma radial_orthogonal_preserved (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (x v : n → ℝ) (hx : A *ᵥ x = x) (hv : x ⬝ᵥ v = 0) :
    x ⬝ᵥ (A *ᵥ v) = 0 := by
  rw [symmetric_dot_mulVec A hA,hx,hv]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_RadialMetricIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section
local instance instFactEqNatFinrankRealAmbientBaseHAddOfNat_1 : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩

def sphereAmbientDerivative (x : Base) : TangentSpace (𝓡 4) x →L[ℝ] AmbientBase :=
  mfderiv (𝓡 4) 𝓘(ℝ,AmbientBase) (Subtype.val : Base → AmbientBase) x

lemma sphere_derivative_radial_orthogonal (x : Base) (v : TangentSpace (𝓡 4) x) :
    (fun i ↦ (x : AmbientBase) i) ⬝ᵥ
      (fun i ↦ (sphereAmbientDerivative x v) i) = 0 := by
  have hm : (sphereAmbientDerivative x v) ∈
      (ℝ ∙ (x : AmbientBase))ᗮ := by
    rw [← range_mvfderiv_subtypeVal (n := 4) x]
    exact ⟨v,rfl⟩
  have hi := (Submodule.mem_orthogonal_singleton_iff_inner_left (𝕜 := ℝ) (E := AmbientBase)).mp hm
  simpa [PiLp.inner_apply,dotProduct,mul_comm] using hi

lemma ambientMatrixForm_dot (A : Matrix (Fin 5) (Fin 5) ℝ) (v w : AmbientBase) :
    ambientMatrixForm A v w = (fun i ↦ v i) ⬝ᵥ (A *ᵥ (fun i ↦ w i)) := by
  rw [ambientMatrixForm_apply]
  simp [dotProduct,mulVec,Finset.mul_sum,mul_assoc]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
noncomputable section
local instance instFactEqNatFinrankRealAmbientBaseHAddOfNat_2 : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩
abbrev BaseModel := EuclideanSpace ℝ (Fin 4)

def sphereChartDerivative (p : Base) (y : BaseModel) : BaseModel →L[ℝ] AmbientBase :=
  (sphereAmbientDerivative ((extChartAt (𝓡 4) p).symm y)).comp
    (mfderiv 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p).symm y)

def sphereChartFrame (p : Base) (y : BaseModel) : Matrix (Fin 5) (Fin 4) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis (sphereChartDerivative p y).toLinearMap

lemma sphereChartFrame_apply (p : Base) (y : BaseModel) (i : Fin 5) (j : Fin 4) :
    sphereChartFrame p y i j =
      sphereChartDerivative p y (EuclideanSpace.basisFun (Fin 4) ℝ j) i := by
  simp [sphereChartFrame,LinearMap.toMatrix_apply]

lemma sphereChartFrame_mulVec (p : Base) (y : BaseModel) (v : Fin 4 → ℝ) :
    sphereChartFrame p y *ᵥ v =
      (fun i ↦ sphereChartDerivative p y (WithLp.toLp 2 v) i) := by
  exact LinearMap.toMatrix_mulVec_repr (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis (sphereChartDerivative p y).toLinearMap
      (WithLp.toLp 2 v)

lemma sphereChartDerivative_injective (p : Base) {y : BaseModel}
    (hy : y ∈ (extChartAt (𝓡 4) p).target) :
    Function.Injective (sphereChartDerivative p y) := by
  apply (injective_mvfderiv_subtypeVal_sphere (n := 4) ((extChartAt (𝓡 4) p).symm y)).comp
  have h := (isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 4) hy).injective
  rw [ModelWithCorners.range_eq_univ,mfderivWithin_univ] at h
  convert! h using 1
  all_goals try with_reducible_and_instances rfl

lemma sphereChartFrame_injective (p : Base) {y : BaseModel}
    (hy : y ∈ (extChartAt (𝓡 4) p).target) :
    Function.Injective (sphereChartFrame p y).mulVec := by
  intro v w h
  rw [sphereChartFrame_mulVec,sphereChartFrame_mulVec] at h
  have he : sphereChartDerivative p y (WithLp.toLp 2 v) =
      sphereChartDerivative p y (WithLp.toLp 2 w) := by ext i; exact congrFun h i
  exact congrArg WithLp.ofLp (sphereChartDerivative_injective p hy he)

lemma sphereChartFrame_orthogonal (p : Base) (y : BaseModel) :
    (sphereChartFrame p y).transpose *ᵥ
      (fun i ↦ ((extChartAt (𝓡 4) p).symm y : AmbientBase) i) = 0 := by
  ext j
  have h := sphere_derivative_radial_orthogonal ((extChartAt (𝓡 4) p).symm y)
    (mfderiv 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p).symm y
      (EuclideanSpace.basisFun (Fin 4) ℝ j))
  simp only [mulVec,transpose_apply,sphereChartFrame_apply,sphereChartDerivative,
    Pi.zero_apply]
  rw [dotProduct_comm]
  convert! h using 1
  all_goals try with_reducible_and_instances rfl

def sphereRoundChartMatrix (p : Base) (y : BaseModel) : Matrix (Fin 4) (Fin 4) ℝ :=
  (sphereChartFrame p y).transpose * sphereChartFrame p y

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CircleChartFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
noncomputable section
attribute [local instance] finrank_real_complex_fact'
abbrev CircleModel := EuclideanSpace ℝ (Fin 1)

def circleChartDerivative (p : Circle) (y : CircleModel) : CircleModel →L[ℝ] ℂ :=
  (show TangentSpace (𝓡 1) ((extChartAt (𝓡 1) p).symm y) →L[ℝ] ℂ from
    mfderiv (𝓡 1) 𝓘(ℝ,ℂ) (fun z : Circle ↦ (z : ℂ)) ((extChartAt (𝓡 1) p).symm y)).comp
    (mfderiv 𝓘(ℝ,CircleModel) (𝓡 1) (extChartAt (𝓡 1) p).symm y)

def circleChartFactor (p : Circle) (y : CircleModel) : ℝ :=
  ‖circleChartDerivative p y (EuclideanSpace.basisFun (Fin 1) ℝ 0)‖^2

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ChartFrameSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff Topology
noncomputable section
attribute [local instance] finrank_real_complex_fact'
local instance instFactEqNatFinrankRealAmbientBaseHAddOfNat_3 : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ProductChartPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

def productFrame : Module.Basis (Fin 4 ⊕ Fin 1) ℝ Model :=
  (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.prod
    (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis

def productMetricMatrix (g : SmoothMetric) (p : Manifold5) (y : Model) :
    Matrix (Fin 4 ⊕ Fin 1) (Fin 4 ⊕ Fin 1) ℝ := fun i j ↦
  g.inner ((extChartAt modelWithCorners p).symm y)
    (mfderiv 𝓘(ℝ,Model) modelWithCorners (extChartAt modelWithCorners p).symm y (productFrame i))
    (mfderiv 𝓘(ℝ,Model) modelWithCorners (extChartAt modelWithCorners p).symm y (productFrame j))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_BaseChartFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

def roundChartDensity (p : Base) (z : BaseModel) : ℝ :=
  Real.sqrt (sphereRoundChartMatrix p z).det

def baseChartDensity (rho : Base → ℝ) (p : Base) (z : BaseModel) : ℝ :=
  rho ((extChartAt (𝓡 4) p).symm z) * roundChartDensity p z

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_StereographicSecondDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open scoped ContDiff RealInnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def stereoReciprocal (x : E) : ℝ := (‖x‖^2+4)⁻¹

def stereoNumerator (v x : E) : E := (4:ℝ) • x + (‖x‖^2-4) • v

lemma stereoReciprocal_hasFDerivAt (x : E) :
    HasFDerivAt stereoReciprocal
      (-(stereoReciprocal x)^2 • ((2:ℝ) • innerSL ℝ x)) x := by
  have hd := (hasFDerivAt_inv (by positivity : ‖x‖^2+4 ≠ 0)).comp x
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const (4:ℝ))
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  ext w
  simp [stereoReciprocal,inv_pow,smul_eq_mul,nsmul_eq_mul]
  ring

lemma stereoNumerator_hasFDerivAt (v x : E) :
    HasFDerivAt (stereoNumerator v)
      ((4:ℝ) • ContinuousLinearMap.id ℝ E + ((2:ℝ) • innerSL ℝ x).smulRight v) x := by
  convert! ((hasFDerivAt_id x).const_smul (4:ℝ)).add
    (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub_const (4:ℝ)).smul_const v) using 1
  all_goals try with_reducible_and_instances rfl
  ext w
  simp [nsmul_eq_mul]

lemma stereoInvFunAux_fderiv (v x w : E) :
    fderiv ℝ (stereoInvFunAux v) x w =
      (-2 * stereoReciprocal x^2 * ⟪x,w⟫) • stereoNumerator v x +
      stereoReciprocal x • ((4:ℝ) • w + (2*⟪x,w⟫) • v) := by
  have hd := (stereoReciprocal_hasFDerivAt x).smul (stereoNumerator_hasFDerivAt v x)
  change HasFDerivAt (stereoInvFunAux v) _ x at hd
  rw [hd.fderiv]
  simp only [smul_apply,add_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply,innerSL_apply_apply,smul_eq_mul]
  rw [add_comm]
  congr 1
  congr 1
  ring

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CenteredSphereChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff RealInnerProductSpace
noncomputable section

local instance localInst_r069c8e_1 : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩
def centeredSphereIsometry (p : Base) : BaseModel →ₗᵢ[ℝ] AmbientBase :=
  (ℝ ∙ ((-p : Base) : AmbientBase))ᗮ.subtypeₗᵢ.comp
    (OrthonormalBasis.fromOrthogonalSpanSingleton 4 (ne_zero_of_mem_unit_sphere (-p))).repr.symm.toLinearIsometry

lemma centeredSphereIsometry_orthogonal (p : Base) (v : BaseModel) :
    ⟪(p : AmbientBase),centeredSphereIsometry p v⟫ = (0:ℝ) := by
  have h := ((OrthonormalBasis.fromOrthogonalSpanSingleton 4
    (ne_zero_of_mem_unit_sphere (-p))).repr.symm v).property
  have he := (Submodule.mem_orthogonal_singleton_iff_inner_left
    (𝕜 := ℝ) (E := AmbientBase)).mp h
  change ⟪(p : AmbientBase),
    ((OrthonormalBasis.fromOrthogonalSpanSingleton 4
      (ne_zero_of_mem_unit_sphere (-p))).repr.symm v : AmbientBase)⟫ = 0
  simpa [real_inner_comm] using he

lemma centeredSphereChart_target (p : Base) : (extChartAt (𝓡 4) p).target = Set.univ := by
  rw [extChartAt_target]
  change id ⁻¹' (stereographic' 4 (-p)).target ∩ Set.range (id : BaseModel → BaseModel) = Set.univ
  simp

lemma centeredSphereChart_inverse (p : Base) :
    ((Subtype.val : Base → AmbientBase) ∘ (extChartAt (𝓡 4) p).symm) =
      stereoInvFunAux (-(p : AmbientBase)) ∘ (centeredSphereIsometry p) := by
  funext y
  change ((stereographic' 4 (-p)).symm y : AmbientBase) = _
  rw [stereographic'_symm_apply]
  change _ = stereoInvFunAux (-(p : AmbientBase))
    ((OrthonormalBasis.fromOrthogonalSpanSingleton 4
      (ne_zero_of_mem_unit_sphere (-p))).repr.symm y : AmbientBase)
  simp only [stereoInvFunAux, smul_add, smul_smul]
  rfl

lemma centeredSphereChart_inverse_zero (p : Base) : (extChartAt (𝓡 4) p).symm 0 = p := by
  apply Subtype.ext
  have h := congrFun (centeredSphereChart_inverse p) 0
  simpa [stereoInvFunAux] using h

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CenteredSphereSecondJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff RealInnerProductSpace
noncomputable section

local instance instContinuousSMulRealAmbientBase : ContinuousSMul ℝ AmbientBase := IsBoundedSMul.continuousSMul

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CenteredSphereMetricLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Target

open Manifold Matrix
open scoped ContDiff RealInnerProductSpace

lemma sphereRoundChartMatrix_inner (p : Base) (y : BaseModel) (i j : Fin 4) :
    sphereRoundChartMatrix p y i j =
      ⟪sphereChartDerivative p y (EuclideanSpace.basisFun (Fin 4) ℝ i),
        sphereChartDerivative p y (EuclideanSpace.basisFun (Fin 4) ℝ j)⟫ := by
  simp [sphereRoundChartMatrix,Matrix.mul_apply,Matrix.transpose_apply,
    sphereChartFrame_apply,PiLp.inner_apply,mul_comm]

open Manifold Filter
open scoped Topology

open Manifold

end Yau.Target

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CircleInvariantDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

def circleLift (f : Base → ℝ) (x : Manifold5) : ℝ := f x.1

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_RoundChartConnection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff RealInnerProductSpace
noncomputable section

local instance instFactEqNatFinrankRealAmbientBaseHAddOfNat_5_r069c8e_1 : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩
def ambientRoundBilinear : AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ := innerSL ℝ

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereCovectorRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Bundle Manifold ContinuousLinearMap
open scoped ContDiff RealInnerProductSpace
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

abbrev SphereCotangent (x : Base) := TangentSpace (𝓡 4) x →L[ℝ] ℝ
abbrev CotangentModel := BaseModel →L[ℝ] ℝ

def sphereCovectorRestriction (x : Base) : AmbientBase →L[ℝ] SphereCotangent x :=
  ((sphereAmbientDerivative x).precomp ℝ).comp (innerSL ℝ)

lemma sphereCovectorRestriction_apply (x : Base) (v : AmbientBase)
    (u : TangentSpace (𝓡 4) x) :
    sphereCovectorRestriction x v u = ⟪v, sphereAmbientDerivative x u⟫ := rfl

lemma sphereCovectorRestriction_radial (x : Base) :
    sphereCovectorRestriction x (x : AmbientBase) = 0 := by
  ext u
  have h := sphere_derivative_radial_orthogonal x u
  simpa [sphereCovectorRestriction_apply, PiLp.inner_apply, dotProduct, mul_comm] using h

local instance localInst_r069c8e_2 : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩
lemma sphereCovectorRestriction_separates (x : Base) (v : AmbientBase)
    (hv : sphereCovectorRestriction x v = 0) (hr : ⟪(x : AmbientBase),v⟫ = 0) : v = 0 := by
  have hm : v ∈ (ℝ ∙ (x : AmbientBase))ᗮ := by
    exact (Submodule.mem_orthogonal_singleton_iff_inner_left (𝕜 := ℝ) (E := AmbientBase)).mpr (by simpa only [real_inner_comm] using hr)
  rw [← range_mvfderiv_subtypeVal (n := 4)] at hm
  obtain ⟨u,hu⟩ := hm
  have h := congrArg (fun f : SphereCotangent x ↦ f u) hv
  change ⟪v,sphereAmbientDerivative x u⟫ = 0 at h
  change sphereAmbientDerivative x u = v at hu
  rw [hu, real_inner_self_eq_norm_sq] at h
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp h)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_AmbientFormMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Matrix
noncomputable section

def ambientFormMatrix (B : AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ) :
    Matrix (Fin 5) (Fin 5) ℝ := fun i j ↦
  B (EuclideanSpace.basisFun (Fin 5) ℝ i) (EuclideanSpace.basisFun (Fin 5) ℝ j)

lemma ambientFormMatrix_form (B : AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ)
    (v w : AmbientBase) : ambientMatrixForm (ambientFormMatrix B) v w = B v w := by
  have hv := (EuclideanSpace.basisFun (Fin 5) ℝ).sum_repr v
  have hw := (EuclideanSpace.basisFun (Fin 5) ℝ).sum_repr w
  conv_rhs => rw [← hv, ← hw]
  simp [ambientMatrixForm_apply, ambientFormMatrix, map_sum, map_smul, mul_assoc, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma ambientFormMatrix_posDef (B : AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ)
    (hs : ∀ v w, B v w = B w v) (hp : ∀ v, v ≠ 0 → 0 < B v v) :
    (ambientFormMatrix B).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp [ambientFormMatrix, hs]
  · intro v hv
    have hn : WithLp.toLp 2 v ≠ (0 : AmbientBase) := by
      intro h
      apply hv
      exact congrArg WithLp.ofLp h
    simpa only [← ambientFormMatrix_form B, ambientMatrixForm_dot, star_trivial] using
      hp (WithLp.toLp 2 v) hn

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicAmbientExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Bundle Manifold ContinuousLinearMap Matrix
open scoped ContDiff RealInnerProductSpace
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

abbrev IntrinsicTensor := ∀ x : Base, SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ

def intrinsicAmbientForm (A : IntrinsicTensor) (x : Base) :
    AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ :=
  ((sphereCovectorRestriction x).precomp ℝ).comp ((A x).comp (sphereCovectorRestriction x)) +
    (innerSL ℝ (x : AmbientBase)).smulRight (innerSL ℝ (x : AmbientBase))

def intrinsicAmbientMatrix (A : IntrinsicTensor) (x : Base) : Matrix (Fin 5) (Fin 5) ℝ :=
  ambientFormMatrix (intrinsicAmbientForm A x)

lemma intrinsicAmbientForm_apply (A : IntrinsicTensor) (x : Base) (v w : AmbientBase) :
    intrinsicAmbientForm A x v w =
      A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) +
        ⟪(x : AmbientBase),v⟫ * ⟪(x : AmbientBase),w⟫ := rfl

lemma intrinsicAmbientMatrix_pairing (A : IntrinsicTensor) (x : Base) (v w : AmbientBase) :
    ambientMatrixForm (intrinsicAmbientMatrix A x) v w =
      A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) +
        ⟪(x : AmbientBase),v⟫ * ⟪(x : AmbientBase),w⟫ := by
  rw [intrinsicAmbientMatrix, ambientFormMatrix_form, intrinsicAmbientForm_apply]

lemma intrinsicAmbientMatrix_tangent (A : IntrinsicTensor) (x : Base) (v w : AmbientBase)
    (hv : ⟪(x : AmbientBase),v⟫ = 0) :
    ambientMatrixForm (intrinsicAmbientMatrix A x) v w =
      A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) := by
  rw [intrinsicAmbientMatrix_pairing,hv,zero_mul,add_zero]

lemma intrinsicAmbientMatrix_posDef (A : IntrinsicTensor)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v) (x : Base) :
    (intrinsicAmbientMatrix A x).PosDef := by
  apply ambientFormMatrix_posDef
  · intro v w
    simp only [intrinsicAmbientForm_apply, mul_comm]
    rw [hs]
  · intro v hv
    rw [intrinsicAmbientForm_apply]
    by_cases hz : sphereCovectorRestriction x v = 0
    · have hn : ⟪(x : AmbientBase),v⟫ ≠ 0 := by
        intro h
        exact hv (sphereCovectorRestriction_separates x v hz h)
      rw [hz, map_zero (A x 0), zero_add]
      exact mul_self_pos.mpr hn
    · exact add_pos_of_pos_of_nonneg (hp x _ hz) (mul_self_nonneg _)

lemma intrinsicAmbientMatrix_radial (A : IntrinsicTensor) (x : Base) :
    intrinsicAmbientMatrix A x *ᵥ (fun i ↦ (x : AmbientBase) i) =
      (fun i ↦ (x : AmbientBase) i) := by
  have hx : ⟪(x : AmbientBase),(x : AmbientBase)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq]
    have hn : ‖(x : AmbientBase)‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using x.property
    rw [hn,one_pow]
  ext i
  have h := intrinsicAmbientMatrix_pairing A x (EuclideanSpace.basisFun (Fin 5) ℝ i)
    (x : AmbientBase)
  rw [sphereCovectorRestriction_radial,map_zero,hx,mul_one,zero_add] at h
  simpa [ambientMatrixForm_dot,dotProduct,EuclideanSpace.basisFun_inner,
    EuclideanSpace.inner_single_right] using h

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereRadialProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped RealInnerProductSpace
noncomputable section

def sphereTangentProjection (x : Base) (v : AmbientBase) : AmbientBase :=
  v - ⟪(x : AmbientBase),v⟫ • (x : AmbientBase)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_RoundCotangentTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped RealInnerProductSpace
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

local instance roundCotangentTensorLocalInst1 : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩
local instance roundCotangentTensorLocalInst2 (x : Base) : NormedAddCommGroup (TangentSpace (𝓡 4) x) := inferInstanceAs (NormedAddCommGroup BaseModel)
local instance roundCotangentTensorLocalInst3 (x : Base) : NormedSpace ℝ (TangentSpace (𝓡 4) x) := inferInstanceAs (NormedSpace ℝ BaseModel)
local instance roundCotangentTensorLocalInst4 (x : Base) : FiniteDimensional ℝ (TangentSpace (𝓡 4) x) := inferInstanceAs (FiniteDimensional ℝ BaseModel)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SmoothBundleInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Bundle Manifold ContinuousLinearMap
open scoped ContDiff Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {V W : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, NormedSpace ℝ (W x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle ℝ G W]

lemma smooth_bundle_inverse (T : ∀ x, V x ≃L[ℝ] W x)
    (hT : ContMDiff I (I.prod 𝓘(ℝ,F →L[ℝ] G)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] G) (E := fun x ↦ V x →L[ℝ] W x) x
        (T x).toContinuousLinearMap)) :
    ContMDiff I (I.prod 𝓘(ℝ,G →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (G →L[ℝ] F) (E := fun x ↦ W x →L[ℝ] V x) x
        (T x).symm.toContinuousLinearMap) := by
  intro x
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id,?_⟩
  have ht := ((contMDiffAt_hom_bundle _).mp (hT x)).2
  let t := fun y ↦ inCoordinates F V G W x y x y (T y).toContinuousLinearMap
  have ht' : ContMDiffAt I 𝓘(ℝ,F →L[ℝ] G) ∞ t x := ht
  have hi : (t x).IsInvertible := by
    dsimp only [t]
    rw [inCoordinates_eq (mem_baseSet_trivializationAt F V x)
      (mem_baseSet_trivializationAt G W x)]
    exact ⟨(((trivializationAt F V x).continuousLinearEquivAt ℝ x
      (mem_baseSet_trivializationAt F V x)).symm.trans (T x)).trans
      ((trivializationAt G W x).continuousLinearEquivAt ℝ x
      (mem_baseSet_trivializationAt G W x)),rfl⟩
  apply (hi.contDiffAt_map_inverse.comp_contMDiffAt ht').congr_of_eventuallyEq
  filter_upwards [(trivializationAt F V x).open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V x),
    (trivializationAt G W x).open_baseSet.mem_nhds (mem_baseSet_trivializationAt G W x)] with y hy hz
  dsimp only [Function.comp_def]
  dsimp only [t]
  rw [inCoordinates_eq hy hz,inCoordinates_eq hz hy]
  simp only [inverse_equiv_comp,inverse_comp_equiv,inverse_equiv,ContinuousLinearEquiv.symm_symm]
  rfl

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicAmbientSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Bundle Manifold ContinuousLinearMap
open scoped ContDiff RealInnerProductSpace
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

local instance instNormedAddCommGroupCotangentModel : NormedAddCommGroup CotangentModel := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealCotangentModel : NormedSpace ℝ CotangentModel := ContinuousLinearMap.toNormedSpace

local instance instNormedAddCommGroupContinuousLinearMapRealIdCotangentModel : NormedAddCommGroup (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapIdCotangentModel : NormedSpace ℝ (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

local instance instAddCommGroupSphereCotangent (x : Base) : AddCommGroup (SphereCotangent x) := ContinuousLinearMap.addCommGroup
local instance instModuleRealSphereCotangent (x : Base) : Module ℝ (SphereCotangent x) := ContinuousLinearMap.module
local instance instAddCommGroupContinuousLinearMapRealIdSphereCotangent (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance instModuleRealContinuousLinearMapIdSphereCotangent (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
local instance instTopologicalSpaceContinuousLinearMapRealIdSphereCotangent (x : Base) : TopologicalSpace (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.topologicalSpace
local instance instIsTopologicalAddGroupContinuousLinearMapRealIdSphereCotangent (x : Base) : IsTopologicalAddGroup (SphereCotangent x →L[ℝ] ℝ) := inferInstance
local instance instContinuousSMulRealContinuousLinearMapIdSphereCotangent (x : Base) : ContinuousSMul ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.continuousSMul
local instance instTopologicalSpaceTotalSpaceElemEuclideanSpaceRealFinOfNatNatBaseContinuousLinearMapIdCotangentModelSphereCotangent : TopologicalSpace (TotalSpace (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
    (fun x : Base ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ)) :=
  ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) CotangentModel SphereCotangent
    (CotangentModel →L[ℝ] ℝ) (fun x : Base ↦ SphereCotangent x →L[ℝ] ℝ)

abbrev IntrinsicTensorSmooth (A : IntrinsicTensor) : Prop :=
  ContMDiff (𝓡 4) ((𝓡 4).prod 𝓘(ℝ,CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)) ∞
    (fun x ↦ TotalSpace.mk' (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
      (E := fun x ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) x (A x))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_RoundCotangentSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Bundle Manifold ContinuousLinearMap Yau.Geometry
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
local instance roundCotangentSmoothLocalInst1 : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩
local instance roundCotangentSmoothLocalInst2 (x : Base) : NormedAddCommGroup (TangentSpace (𝓡 4) x) := inferInstanceAs (NormedAddCommGroup BaseModel)
local instance roundCotangentSmoothLocalInst3 (x : Base) : NormedSpace ℝ (TangentSpace (𝓡 4) x) := inferInstanceAs (NormedSpace ℝ BaseModel)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_TargetChartBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
noncomputable section

def productIndexEquiv : (Fin 4 ⊕ Fin 1) ≃ Index :=
  finSumFinEquiv.trans (finCongr (by simp [Model]))

def indexedProductFrame : Module.Basis Index ℝ Model :=
  productFrame.reindex productIndexEquiv

def chartBilinearForm (g : SmoothMetric) (c : PartialEquiv Manifold5 Model) (y : Model) :
    LinearMap.BilinForm ℝ Model :=
  ((g.inner (c.symm y)).toBilinForm).compl₁₂
    (mfderiv 𝓘(ℝ,Model) modelWithCorners c.symm y).toLinearMap
    (mfderiv 𝓘(ℝ,Model) modelWithCorners c.symm y).toLinearMap

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereContravariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
noncomputable section
local instance instFactEqNatFinrankRealAmbientBaseHAddOfNat_4 : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩

lemma sphereChartFrame_spans (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) (v : Fin 5 → ℝ)
    (hv : (fun i ↦ ((extChartAt (𝓡 4) p).symm z : AmbientBase) i) ⬝ᵥ v = 0) :
    ∃ w : Fin 4 → ℝ, sphereChartFrame p z *ᵥ w = v := by
  have hm : WithLp.toLp 2 v ∈
      (ℝ ∙ (((extChartAt (𝓡 4) p).symm z : Base) : AmbientBase))ᗮ := by
    apply (Submodule.mem_orthogonal_singleton_iff_inner_left (𝕜 := ℝ) (E := AmbientBase)).mpr
    simpa [PiLp.inner_apply,dotProduct,mul_comm] using hv
  rw [← range_mvfderiv_subtypeVal (n := 4)] at hm
  obtain ⟨u,hu⟩ := hm
  have hs := (isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 4) hz).surjective
  rw [ModelWithCorners.range_eq_univ,mfderivWithin_univ] at hs
  obtain ⟨w,hw⟩ := hs u
  refine ⟨WithLp.ofLp w,?_⟩
  rw [sphereChartFrame_mulVec]
  change (fun i ↦ (sphereAmbientDerivative _
    (mfderiv 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p).symm z w)) i) = v
  rw [hw]
  exact congrArg WithLp.ofLp hu

lemma sphereChartFrame_invariant (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    (p : Base) {z : BaseModel} (hz : z ∈ (extChartAt (𝓡 4) p).target)
    (hrad : A *ᵥ (fun i ↦ ((extChartAt (𝓡 4) p).symm z : AmbientBase) i) =
      (fun i ↦ ((extChartAt (𝓡 4) p).symm z : AmbientBase) i)) :
    ∃ T : Matrix (Fin 4) (Fin 4) ℝ, A * sphereChartFrame p z = sphereChartFrame p z * T := by
  have he (j : Fin 4) : ∃ w : Fin 4 → ℝ,
      sphereChartFrame p z *ᵥ w = A *ᵥ (fun i ↦ sphereChartFrame p z i j) := by
    apply sphereChartFrame_spans p hz
    apply radial_orthogonal_preserved A hA.1 _ _ hrad
    have h := congrFun (sphereChartFrame_orthogonal p z) j
    simpa [mulVec,transpose_apply,dotProduct,mul_comm] using h
  choose t ht using he
  refine ⟨fun i j ↦ t j i,?_⟩
  ext i j
  exact (congrFun (ht j) i).symm

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PositiveContravariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma positiveContravariant_injective (A : (E →L[ℝ] ℝ) →L[ℝ] E)
    (hp : ∀ α : E →L[ℝ] ℝ, α ≠ 0 → 0 < α (A α)) : Function.Injective A := by
  intro α β h
  apply sub_eq_zero.mp
  by_contra hn
  have hz : A (α-β) = 0 := by rw [map_sub,h,sub_self]
  have hh := hp (α-β) hn
  rw [hz,map_zero] at hh
  exact (lt_irrefl 0 hh)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_MatrixCoefficientMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Matrix Yau.Geometry
open scoped RealInnerProductSpace ContDiff
noncomputable section

def baseCovectorCoordinates (α : BaseModel →L[ℝ] ℝ) : Fin 4 → ℝ :=
  fun i ↦ α (EuclideanSpace.basisFun (Fin 4) ℝ i)

def matrixContravariant (A : Matrix (Fin 4) (Fin 4) ℝ) :
    (BaseModel →L[ℝ] ℝ) →L[ℝ] BaseModel :=
  ∑ i, ∑ j, A i j • (ContinuousLinearMap.apply ℝ ℝ
    (EuclideanSpace.basisFun (Fin 4) ℝ j)).smulRight (EuclideanSpace.basisFun (Fin 4) ℝ i)

def matrixCovariant (B : Matrix (Fin 4) (Fin 4) ℝ) :
    BaseModel →L[ℝ] BaseModel →L[ℝ] ℝ :=
  ∑ i, ∑ j, B i j • (innerSL ℝ (EuclideanSpace.basisFun (Fin 4) ℝ j)).smulRight
    (innerSL ℝ (EuclideanSpace.basisFun (Fin 4) ℝ i))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SphericalSeed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff
noncomputable section

abbrev SeedAmbient := EuclideanSpace ℝ (Fin 5)

local instance instFactEqNatFinrankRealSeedAmbientHAddOfNat_r069c8e_1 : Fact (Module.finrank ℝ SeedAmbient = 4+1) := ⟨by simp [SeedAmbient]⟩
def seedCoordinate (i : Fin 5) : SeedAmbient →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (EuclideanSpace.proj i)

def seedZ1 : SeedAmbient →L[ℝ] ℂ := seedCoordinate 0 + Complex.I • seedCoordinate 1

def seedZ2 : SeedAmbient →L[ℝ] ℂ := seedCoordinate 2 + Complex.I • seedCoordinate 3

def seedQuadratic (x : SeedAmbient) : ℂ := seedZ1 x * seedZ2 x

def ambientComplexSeed (N : ℕ) (x : SeedAmbient) : ℂ := seedQuadratic x ^ N

def ambientRealSeed (N : ℕ) (x : SeedAmbient) : ℝ := (ambientComplexSeed N x).re

def sphericalSeed (N : ℕ) (x : Base) : ℝ := ambientRealSeed N x

def seedEigenvalue (N : ℕ) : ℝ := 4*(N:ℝ)^2 + 6*(N:ℝ)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedConcretePoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff RealInnerProductSpace
noncomputable section

def seedPointVector : SeedAmbient := WithLp.toLp 2 ![1/3,0,2/3,0,2/3]

lemma seedPointVector_norm : ‖seedPointVector‖ = 1 := by
  have h : ⟪seedPointVector,seedPointVector⟫ = (1:ℝ) := by
    rw [PiLp.inner_apply]
    first | (simp [seedPointVector,Fin.sum_univ_succ,Matrix.cons_val_succ]; all_goals first | (norm_num [seedPointVector,Fin.sum_univ_succ,Matrix.cons_val_succ]; done) | rfl | decide) | (norm_num [seedPointVector,Fin.sum_univ_succ,Matrix.cons_val_succ]; done) | norm_num [seedPointVector,Fin.sum_univ_succ,Matrix.cons_val_succ]
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg seedPointVector]

def seedPoint : Base := ⟨seedPointVector,mem_sphere_zero_iff_norm.mpr seedPointVector_norm⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedPolynomialDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open scoped ContDiff
noncomputable section

def seedQuadraticDerivative (x : SeedAmbient) : SeedAmbient →L[ℝ] ℂ :=
  seedZ1 x • seedZ2 + seedZ2 x • seedZ1

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedLogarithmicBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set
open scoped ContDiff
noncomputable section

local instance instFactEqNatFinrankRealSeedAmbientHAddOfNat_1_r069c8e_1 : Fact (Module.finrank ℝ SeedAmbient = 4+1) := ⟨by simp [SeedAmbient]⟩
def seedLogDomain : Set SeedAmbient := seedQuadratic ⁻¹' Complex.slitPlane

def seedLog (x : SeedAmbient) : ℂ := Complex.log (seedQuadratic x)

def seedLogReal (x : SeedAmbient) : ℝ := (seedLog x).re

def seedLogImag (x : SeedAmbient) : ℝ := (seedLog x).im

def sphereSeedLogReal (x : Base) : ℝ := seedLogReal x

def sphereSeedLogImag (x : Base) : ℝ := seedLogImag x

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedLogNonvanishing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set
open scoped ContDiff RealInnerProductSpace
noncomputable section
local instance instFactEqNatFinrankRealSeedAmbientHAddOfNat_2_r069c8e_1 : Fact (Module.finrank ℝ SeedAmbient = 4+1) := ⟨by simp [SeedAmbient]⟩
def seedImagTestVector : SeedAmbient := WithLp.toLp 2 ![0,1,0,0,0]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedLogConcreteJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open scoped ContDiff RealInnerProductSpace
noncomputable section

def seedRealGradient : SeedAmbient := WithLp.toLp 2 ![7/3,0,1/6,0,-4/3]
def seedImagGradient : SeedAmbient := WithLp.toLp 2 ![0,3,0,3/2,0]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedRoundAdmissibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff RealInnerProductSpace
noncomputable section

def seedRealChart : BaseModel → ℝ := sphereSeedLogReal ∘ (extChartAt (𝓡 4) seedPoint).symm
def seedImagChart : BaseModel → ℝ := sphereSeedLogImag ∘ (extChartAt (𝓡 4) seedPoint).symm

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedRoundPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter Set Metric
open scoped ContDiff RealInnerProductSpace Topology
noncomputable section

def seedChartAmbient : BaseModel → SeedAmbient := (Subtype.val : Base → SeedAmbient) ∘
  (extChartAt (𝓡 4) seedPoint).symm

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedCoordinateCube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter Set Metric
open scoped ContDiff RealInnerProductSpace Topology
noncomputable section

def seedCoordinateCube (a : ℝ) : Set BaseModel := {y | ∀ i, |y i| ≤ a}

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_GaussianCoefficientVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory
noncomputable section
variable {ι : Type*} [Fintype ι]

def gaussianPairs : Measure (ι × Fin 2 → ℝ) := Measure.pi (fun _ ↦ gaussianReal 0 1)

end
end Yau.Probability

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedPatchTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Metric
open scoped ContDiff Topology
noncomputable section

def seedSpherePatch (r : ℝ) : Set Base :=
  (extChartAt (𝓡 4) seedPoint).symm '' ball (0 : BaseModel) r

lemma seedSphereChart_inverse_continuous : Continuous (extChartAt (𝓡 4) seedPoint).symm := by
  apply continuousOn_univ.mp
  simpa only [centeredSphereChart_target] using continuousOn_extChartAt_symm (I := 𝓡 4) seedPoint

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicRoundPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Bundle Manifold Matrix Yau.Geometry
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
local instance intrinsicRoundPerturbationLocalInst1 (x : Base) : NormedAddCommGroup (TangentSpace (𝓡 4) x) := inferInstanceAs (NormedAddCommGroup BaseModel)
local instance intrinsicRoundPerturbationLocalInst2 (x : Base) : NormedSpace ℝ (TangentSpace (𝓡 4) x) := inferInstanceAs (NormedSpace ℝ BaseModel)

local instance intrinsicRoundPerturbationLocalInst3 : NormedAddCommGroup CotangentModel := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicRoundPerturbationLocalInst4 : NormedSpace ℝ CotangentModel := ContinuousLinearMap.toNormedSpace
local instance intrinsicRoundPerturbationLocalInst9 (x : Base) : AddCommGroup (SphereCotangent x) := ContinuousLinearMap.addCommGroup
local instance intrinsicRoundPerturbationLocalInst10 (x : Base) : Module ℝ (SphereCotangent x) := ContinuousLinearMap.module

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_GaussianFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace MatrixOrder
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

local notation "E" => EuclideanSpace ℝ ι

def covarianceMatrix (T : F →L[ℝ] E) : Matrix ι ι ℝ :=
  (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)).symm (T ∘L T.adjoint)

def covarianceFactor (T : F →L[ℝ] E) : E →L[ℝ] E :=
  (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) (CFC.sqrt (covarianceMatrix T))

end
end Yau.Probability

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_FiniteGaussianMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def pairJetMap (z : κ → ι → ℂ) :
    EuclideanSpace ℝ (ι × Fin 2) →L[ℝ] EuclideanSpace ℝ κ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ ↦ ℝ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun k ↦ ∑ p : ι × Fin 2,
      (if p.2 = 0 then (z k p.1).re else -(z k p.1).im) • EuclideanSpace.proj p)

end
end Yau.Probability

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealFinCubeFubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set Function
noncomputable section

def realFinCube (n : ℕ) : Set (Fin n → ℝ) := univ.pi (fun _ ↦ Icc (-1:ℝ) 1)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCubeL2EmbeddingLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open MeasureTheory Set Function Metric
open scoped ContDiff

open MeasureTheory Set Function

lemma realFinCube_isCompact (n : ℕ) : IsCompact (realFinCube n) :=
  isCompact_univ_pi (fun _ ↦ isCompact_Icc)

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereMeasureChartGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff
noncomputable section

local instance : Fact (Module.finrank ℝ AmbientBase = 4 + 1) := ⟨by simp [AmbientBase]⟩

lemma centeredSphereChart_source (p : Base) :
    (extChartAt (𝓡 4) p).source = {-p}ᶜ := by
  rw [extChartAt_source]
  exact stereographic'_source (-p)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartOpenMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set Topology
noncomputable section
local instance sphereChartOpenMapLocal1 : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereReferenceMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set MeasureTheory
open scoped ENNReal
noncomputable section

local instance sphereReferenceMeasureLocal1 : MeasurableSpace Base := borel Base
local instance sphereReferenceMeasureLocal2 : BorelSpace Base := ⟨rfl⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereReferenceMeasureInvariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section
local instance sphereReferenceMeasureInvarianceLocal1 : MeasurableSpace Base := borel Base
local instance sphereReferenceMeasureInvarianceLocal2 : BorelSpace Base := ⟨rfl⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereReferenceMeasureFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set MeasureTheory Metric
open scoped ENNReal Topology
noncomputable section
local instance sphereReferenceMeasureFiniteLocal1 : MeasurableSpace Base := borel Base
local instance sphereReferenceMeasureFiniteLocal2 : BorelSpace Base := ⟨rfl⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereReferenceMeasurePositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set MeasureTheory
open scoped ENNReal
noncomputable section
local instance sphereReferenceMeasurePositiveLocal1 : MeasurableSpace Base := borel Base
local instance sphereReferenceMeasurePositiveLocal2 : BorelSpace Base := ⟨rfl⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereWeightedL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory
open scoped ENNReal
noncomputable section
local instance sphereWeightedL2Measurable : MeasurableSpace Base := borel Base
local instance sphereWeightedL2Borel : BorelSpace Base := ⟨rfl⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCompactL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
noncomputable section

theorem real_continuous_memLp_compact {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) : MemLp f 2 (volume.restrict K) :=
  (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
    ((hf.pow 2).continuousOn.integrableOn_compact hK)

theorem real_toLp_norm_sq {X : Type*} [MeasurableSpace X] {m : Measure X}
    (f : X → ℝ) (hf : MemLp f 2 m) : ‖hf.toLp f‖^2 = ∫ x, (f x)^2 ∂m := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartDerivativeMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry
noncomputable section

abbrev SphereChartCubeL2 := Lp ℝ 2 (volume.restrict (realFinCube 4))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartTangentTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold InnerProductSpace Laplacian
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma sphereChartDerivative_normal (p : Base) (y v : BaseModel) :
    ⟪((extChartAt (𝓡 4) p).symm y : AmbientBase), sphereChartDerivative p y v⟫ = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct_comm]
  exact sphere_derivative_radial_orthogonal ((extChartAt (𝓡 4) p).symm y)
    (mfderiv 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p).symm y v)

def sphereConformalFrame (p : Base) (y : BaseModel) : Fin 4 ⊕ Fin 1 → AmbientBase :=
  Sum.elim (fun i ↦ ((‖y‖^2+4)/4) •
    sphereChartDerivative p y (EuclideanSpace.basisFun (Fin 4) ℝ i))
    (fun _ ↦ (extChartAt (𝓡 4) p).symm y)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereWeightedPairingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
local instance sphereWeightedPairingLimitMeasurable : MeasurableSpace Base := borel Base

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereUniformDensityPairingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
local instance sphereUniformDensityMeasurable : MeasurableSpace Base := borel Base

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CoefficientAmbientReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

local instance coefficientReconstructionDimension_r069c8e_1 : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩
def sphereChartAmbientCovector (p : Base) (v : AmbientBase) (z : BaseModel) :
    BaseModel →L[ℝ] ℝ := (innerSL ℝ v).comp (sphereChartDerivative p z)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationDiskJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real Set
open scoped ContDiff
noncomputable section

def planeRadialCovector (z : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  z.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + z.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationRadialJetsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open Real

def radialComponent (z v : ℝ × ℝ) (r : ℝ) : ℝ := (z.1*v.1+z.2*v.2)/r

open Real Set
open scoped ContDiff

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FiniteCertificateWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
noncomputable section
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

def successfulTestWeight (w : ι → ℝ) (A : ι → Set Ω) (a : Ω) : ℝ :=
  ∑ i, (A i).indicator (fun _ ↦ w i) a

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealJetProductExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section

def realJetErrorTerms (extra : List (Fin 4)) :
    List (Fin 4) → List (List (Fin 4) × List (Fin 4))
  | [] => []
  | l::ds =>
    (realJetErrorTerms extra ds).map (fun t ↦ (l::t.1,t.2)) ++
    (realJetErrorTerms extra ds).map (fun t ↦ (t.1,l::t.2)) ++ [([l],extra++ds)]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealBallCutoffChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Metric
open scoped ContDiff
noncomputable section

def realCutoffRadius (r R : ℝ) (n : ℕ) : ℝ := r+(R-r)/(2:ℝ)^n

lemma realCutoffRadius_gt (r R : ℝ) (hR : r < R) (n : ℕ) :
    r < realCutoffRadius r R n := by
  have h := div_pos (sub_pos.mpr hR) (pow_pos (by norm_num : (0:ℝ)<2) n)
  dsimp [realCutoffRadius] <;> linarith

lemma realCutoffRadius_succ_lt (r R : ℝ) (hR : r < R) (n : ℕ) :
    realCutoffRadius r R (n+1) < realCutoffRadius r R n := by
  have h := div_pos (sub_pos.mpr hR) (pow_pos (by norm_num : (0:ℝ)<2) n)
  dsimp [realCutoffRadius]
  rw [pow_succ,div_mul_eq_div_div]
  linarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCompactMultiplierLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau

open MeasureTheory Set

theorem real_compact_multiplier_bound {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (a : (Fin n → ℝ) → ℝ) (ha : Continuous a) :
    ∃ C > 0, ∀ u : (Fin n → ℝ) → ℝ, MemLp u 2 (volume.restrict K) →
      MemLp (fun x ↦ a x*u x) 2 (volume.restrict K) ∧
      (∫ x in K, (a x*u x)^2) ≤ C*(∫ x in K, (u x)^2) := by
  obtain ⟨B,hB,hb⟩ := (hK.image ha).isBounded.exists_pos_norm_le
  refine ⟨B^2,sq_pos_of_pos hB,?_⟩
  intro u hu
  have hmul : MemLp (fun x ↦ a x*u x) 2 (volume.restrict K) :=
    hu.of_le_mul (ha.aestronglyMeasurable.mul hu.aestronglyMeasurable) (by
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb _ ⟨x,hx,rfl⟩) (norm_nonneg _))
  refine ⟨hmul,?_⟩
  calc
    _ ≤ ∫ x in K, B^2*(u x)^2 := by
      apply setIntegral_mono_on hmul.integrable_sq (hu.integrable_sq.const_mul _) hK.measurableSet
      intro x hx
      have hab : (a x)^2 ≤ B^2 := by
        have h := hb _ ⟨x,hx,rfl⟩
        rw [Real.norm_eq_abs] at h
        nlinarith [sq_abs (a x),abs_nonneg (a x)]
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hab (sq_nonneg _)
    _ = _ := integral_const_mul _ _

end Yau

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCompactL2Product
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
noncomputable section

theorem real_compact_localL2_product {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (eta u : (Fin n → ℝ) → ℝ) (he : Continuous eta) (hs : tsupport eta ⊆ K)
    (hu : MemLp u 2 (volume.restrict K)) : MemLp (fun x ↦ eta x*u x) 2 volume := by
  obtain ⟨_,_,hb⟩ := real_compact_multiplier_bound hK eta he
  have hlocal := (hb u hu).1
  have hglobal := (memLp_indicator_iff_restrict hK.measurableSet).mpr hlocal
  have heq : K.indicator (fun x ↦ eta x*u x) = fun x ↦ eta x*u x := by
    funext x
    by_cases hx : x ∈ K
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx,image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h)),zero_mul]
  rwa [heq] at hglobal

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCompactL2MapLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau

open MeasureTheory Set

theorem real_compact_mul_ae {n : ℕ} {K : Set (Fin n → ℝ)} (hK : MeasurableSet K)
    (eta u v : (Fin n → ℝ) → ℝ) (hs : tsupport eta ⊆ K)
    (huv : u =ᵐ[volume.restrict K] v) :
    (fun x ↦ eta x*u x) =ᵐ[volume] (fun x ↦ eta x*v x) := by
  have h := (ae_restrict_iff' hK).mp huv
  filter_upwards [h] with x hx
  by_cases hm : x ∈ K
  · rw [hx hm]
  · rw [image_eq_zero_of_notMem_tsupport (fun he ↦ hm (hs he)),zero_mul,zero_mul]

def realCompactL2Linear {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (eta : (Fin n → ℝ) → ℝ) (he : Continuous eta) (hs : tsupport eta ⊆ K) :
    Lp ℝ 2 (volume.restrict K) →ₗ[ℝ] Lp ℝ 2 (volume : Measure (Fin n → ℝ)) where
  toFun u := (real_compact_localL2_product hK eta u he hs (Lp.memLp u)).toLp (fun x ↦ eta x*u x)
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(real_compact_localL2_product hK eta ((u+v : Lp ℝ 2 (volume.restrict K)) : (Fin n → ℝ) → ℝ) he hs (Lp.memLp _)).coeFn_toLp,
      Lp.coeFn_add
        ((real_compact_localL2_product hK eta u he hs (Lp.memLp _)).toLp (fun x ↦ eta x*u x))
        ((real_compact_localL2_product hK eta v he hs (Lp.memLp _)).toLp (fun x ↦ eta x*v x)),
      (real_compact_localL2_product hK eta u he hs (Lp.memLp _)).coeFn_toLp,
      (real_compact_localL2_product hK eta v he hs (Lp.memLp _)).coeFn_toLp,
      real_compact_mul_ae hK.measurableSet eta ((u+v : Lp ℝ 2 (volume.restrict K)) : (Fin n → ℝ) → ℝ) (fun x ↦ u x+v x) hs (Lp.coeFn_add u v)]
      with x h1 h2 h3 h4 h5
    rw [h1,h2,Pi.add_apply,h3,h4,h5,mul_add]
  map_smul' t u := by
    apply Lp.ext
    filter_upwards [(real_compact_localL2_product hK eta ((t • u : Lp ℝ 2 (volume.restrict K)) : (Fin n → ℝ) → ℝ) he hs (Lp.memLp _)).coeFn_toLp,
      Lp.coeFn_smul t
        ((real_compact_localL2_product hK eta u he hs (Lp.memLp _)).toLp (fun x ↦ eta x*u x)),
      (real_compact_localL2_product hK eta u he hs (Lp.memLp _)).coeFn_toLp,
      real_compact_mul_ae hK.measurableSet eta ((t • u : Lp ℝ 2 (volume.restrict K)) : (Fin n → ℝ) → ℝ) (fun x ↦ t*u x) hs (Lp.coeFn_smul t u)]
      with x h1 h2 h3 h4
    simp only [RingHom.id_apply]
    rw [h1,h2,Pi.smul_apply,h3,h4]
    change eta x*(t*u x)=t*(eta x*u x)
    ring

theorem realCompactL2Linear_bound {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (eta : (Fin n → ℝ) → ℝ) (he : Continuous eta) (hs : tsupport eta ⊆ K) :
    ∃ C > 0, ∀ u : Lp ℝ 2 (volume.restrict K), ‖realCompactL2Linear hK eta he hs u‖ ≤ C*‖u‖ := by
  obtain ⟨C,hC,hb⟩ := real_compact_multiplier_bound hK eta he
  refine ⟨Real.sqrt C,Real.sqrt_pos.mpr hC,fun u ↦ ?_⟩
  have hn : ‖realCompactL2Linear hK eta he hs u‖^2 = ∫ x, (eta x*u x)^2 :=
    real_toLp_norm_sq _ (real_compact_localL2_product hK eta u he hs (Lp.memLp u))
  have hz : (∫ x, (eta x*u x)^2) = ∫ x in K, (eta x*u x)^2 := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h)),zero_mul,zero_pow (by decide)]
  have hu : ‖u‖^2 = ∫ x in K, (u x)^2 := by
    simpa only [Lp.toLp_coeFn] using real_toLp_norm_sq _ (Lp.memLp u)
  have hb' := (hb u (Lp.memLp u)).2
  rw [← hz,← hn,← hu] at hb'
  have hr : (Real.sqrt C*‖u‖)^2=C*‖u‖^2 := by rw [mul_pow,Real.sq_sqrt hC.le]
  nlinarith [norm_nonneg (realCompactL2Linear hK eta he hs u),
    mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg u)]

def realCompactL2Map {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (eta : (Fin n → ℝ) → ℝ) (he : Continuous eta) (hs : tsupport eta ⊆ K) :
    Lp ℝ 2 (volume.restrict K) →L[ℝ] Lp ℝ 2 (volume : Measure (Fin n → ℝ)) :=
  (realCompactL2Linear hK eta he hs).mkContinuous
    (realCompactL2Linear_bound hK eta he hs).choose
    (realCompactL2Linear_bound hK eta he hs).choose_spec.2

end Yau

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealL2DifferenceQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory
noncomputable section

abbrev RealEuclideanL2 (n : ℕ) := Lp ℝ 2 (volume : Measure (Fin n → ℝ))

def realL2Translate {n : ℕ} (v : Fin n → ℝ) (f : RealEuclideanL2 n) : RealEuclideanL2 n :=
  Lp.compMeasurePreserving (fun x ↦ x+v) (measurePreserving_add_right volume v) f

def realDifferenceQuotient {n : ℕ} (i : Fin n) (h : ℝ) (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : ℝ := h⁻¹*(u (x+(Pi.single i h : Fin n → ℝ))-u x)

def realL2DifferenceQuotient {n : ℕ} (i : Fin n) (h : ℝ) (f : RealEuclideanL2 n) :
    RealEuclideanL2 n := h⁻¹ • (realL2Translate ((Pi.single i h : Fin n → ℝ)) f-f)

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealL2DifferenceLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Filter
open scoped Topology
noncomputable section

def realL2DifferenceMap {n : ℕ} (i : Fin n) (h : ℝ) :
    RealEuclideanL2 n →L[ℝ] RealEuclideanL2 n :=
  h⁻¹ • ((Lp.compMeasurePreservingₗᵢ ℝ (fun x : (Fin n → ℝ) ↦ x+Pi.single i h)
    (measurePreserving_add_right (G := Fin n → ℝ) volume (Pi.single i h : Fin n → ℝ))).toContinuousLinearMap -
      ContinuousLinearMap.id ℝ (RealEuclideanL2 n))

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealGlobalL2Multiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
noncomputable section

def realL2RestrictLinear {n : ℕ} (K : Set (Fin n → ℝ)) :
    RealEuclideanL2 n →ₗ[ℝ] Lp ℝ 2 (volume.restrict K) where
  toFun u := ((Lp.memLp u).mono_measure Measure.restrict_le_self).toLp u
  map_add' u v :=
    (MemLp.toLp_congr _ _ (ae_restrict_of_ae (Lp.coeFn_add u v))).trans
      (MemLp.toLp_add ((Lp.memLp u).mono_measure Measure.restrict_le_self)
        ((Lp.memLp v).mono_measure Measure.restrict_le_self))
  map_smul' t u :=
    (MemLp.toLp_congr _ _ (ae_restrict_of_ae (Lp.coeFn_smul t u))).trans
      (MemLp.toLp_const_smul t ((Lp.memLp u).mono_measure Measure.restrict_le_self))

theorem realL2RestrictLinear_bound {n : ℕ} (K : Set (Fin n → ℝ)) (u : RealEuclideanL2 n) :
    ‖realL2RestrictLinear K u‖ ≤ 1*‖u‖ := by
  change ‖((Lp.memLp u).mono_measure Measure.restrict_le_self).toLp u‖ ≤ _
  rw [one_mul,Lp.norm_toLp,Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp u).2.ne (eLpNorm_mono_measure u Measure.restrict_le_self)

def realL2RestrictMap {n : ℕ} (K : Set (Fin n → ℝ)) :
    RealEuclideanL2 n →L[ℝ] Lp ℝ 2 (volume.restrict K) :=
  (realL2RestrictLinear K).mkContinuous 1 (realL2RestrictLinear_bound K)

def realGlobalCompactMap {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (eta : (Fin n → ℝ) → ℝ) (he : Continuous eta) (hs : tsupport eta ⊆ K) :
    RealEuclideanL2 n →L[ℝ] RealEuclideanL2 n :=
  (realCompactL2Map hK eta he hs).comp (realL2RestrictMap K)

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealPositiveNestedRadii
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
noncomputable section

def realWeakJetRadius (m : ℕ) : ℝ := 1/16+1/(16*((m:ℝ)+1))

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealScaledCubeIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set Function Metric
noncomputable section

def realScaledCube (n : ℕ) (c : Fin n → ℝ) (r : ℝ) : Set (Fin n → ℝ) :=
  (fun x ↦ c+r • x) '' realFinCube n

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Hausdorff_NodalProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def segmentPoint (a b : E) (t : ℝ) : E := (1 - t) • a + t • b

end
end Yau

end OAI
end


