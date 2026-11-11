-- Prove2me | Definitions.Def_OAIQ239Tc004
-- name    : OAIQ239Tc004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:09:30.258271+00:00
-- url     : https://prove2.me/theorems/818588fe-e269-4e52-b462-a118f5a2a754
-- title:
--   Definitions bundle OAIQ239Tc004 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 222 declarations of OpenAI's Lean: 104 definitions, 8 instances and 110 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricHilbert.HodgeKernelBounds.gammaKernel`, `OAI.TamingCompatibility.GeometricHilbert.HodgeKernelBounds.gammaTail`, `OAI.TamingCompatibility.GeometricHilbert.HodgeKernelBounds.leading`, `OAI.TamingCompatibility.GeometricHilbert.HodgeKernelBounds.leadingConstant`, `OAI.TamingCompatibility.GeometricHilbert.HodgeKernelBounds.moment`, `OAI.TamingCompatibility.GeometricHilbert.HodgeKernelBounds.profile`, `OAI.TamingCompatibility.GeometricHilbert.HodgeKernelBounds.rapidConstant`, `OAI.TamingCompatibility.GeometricHilbert.HodgeKernelBounds.truncatedProfile`, `OAI.TamingCompatibility.GeometricHilbert.KernelL2.action`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.instNormedAddCommGroupContinuousLinearMapRealId_solutions`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.instNormedSpaceRealContinuousLinearMapId_solutions`, `OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.differential`, `OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.secondOrder`, `OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.weightedAdjoint`, `OAI.TamingCompatibility.GeometricHilbert.VolterraBounds.weight`, `OAI.TamingCompatibility.GeometricHilbert.hodgeGammaWeight`, `OAI.TamingCompatibility.GeometricHilbert.hodgeHeatMultiplier`, `OAI.TamingCompatibility.GeometricHilbert.hodgeSpectralRate`, `OAI.TamingCompatibility.GeometricHilbert.isometryFromCompletion`, `OAI.TamingCompatibility.GeometricHilbert.lpEncode`, `OAI.TamingCompatibility.GeometricHilbert.lpEncodeIsometry`, `OAI.TamingCompatibility.GeometricHilbert.unitSymbol`, `OAI.TamingCompatibility.HermitianRadial.cutoffLogError`, `OAI.TamingCompatibility.HermitianRadial.cutoffLogPotential`, `OAI.TamingCompatibility.HermitianRadial.cutoffSqrtError`, `OAI.TamingCompatibility.HermitianRadial.cutoffSqrtPotential`, `OAI.TamingCompatibility.HermitianRadial.logInnerSchwartz`, `OAI.TamingCompatibility.HermitianRadial.logInnerSupported`, `OAI.TamingCompatibility.HermitianRadial.logShellSchwartz`, `OAI.TamingCompatibility.HermitianRadial.logShellSupported`, `OAI.TamingCompatibility.HermitianRadial.logSingularSource`, `OAI.TamingCompatibility.HermitianRadial.logSourceSchwartz`, `OAI.TamingCompatibility.HermitianRadial.logSourceSupported`, `OAI.TamingCompatibility.HermitianRadial.shiftedLogError`, `OAI.TamingCompatibility.HermitianRadial.shiftedLogInner`, `OAI.TamingCompatibility.HermitianRadial.shiftedLogShell`, `OAI.TamingCompatibility.HermitianRadial.shiftedLogSource`, `OAI.TamingCompatibility.HermitianRadial.shiftedSqrtError`, `OAI.TamingCompatibility.HermitianRadial.shiftedSqrtInner`, `OAI.TamingCompatibility.HermitianRadial.shiftedSqrtShell` and 64 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_Charts_HermitianBundleSources`, `TamingCompatibility_Charts_HermitianCutoffErrors`, `TamingCompatibility_Charts_HermitianCutoffProfiles`, `TamingCompatibility_Charts_HermitianCutoffSupported`, `TamingCompatibility_Charts_LocalInverse`, `TamingCompatibility_Charts_LocalSmooth`, `TamingCompatibility_Charts_RadialBundleSources`, `TamingCompatibility_Charts_RadialCutoffErrors`, `TamingCompatibility_Charts_RadialOperatorCutoffs`, `TamingCompatibility_Charts_SlowLogCutoff`, `TamingCompatibility_Charts_SummableCutoff`, `TamingCompatibility_Concentration_RadialDefect`, `TamingCompatibility_Currents_LocalMeasure`, `TamingCompatibility_DifferentialForms_AntiDdcBound`, `TamingCompatibility_DifferentialForms_Bessel`, `TamingCompatibility_DifferentialForms_ComplexEquiv`, `TamingCompatibility_DifferentialForms_CriticalRescale`, `TamingCompatibility_DifferentialForms_Dpos2`, `TamingCompatibility_DifferentialForms_GeometricFrameTest`, `TamingCompatibility_DifferentialForms_HermitianCoefficientBounds`, `TamingCompatibility_DifferentialForms_HermitianErrorSources`, `TamingCompatibility_DifferentialForms_HermitianPhysicalJets`, `TamingCompatibility_DifferentialForms_HermitianShiftedSources`, `TamingCompatibility_DifferentialForms_HermitianSupportedSources`, `TamingCompatibility_DifferentialForms_HermitianVariableProfiles`, `TamingCompatibility_DifferentialForms_JAction`, `TamingCompatibility_DifferentialForms_JetBasis`, `TamingCompatibility_DifferentialForms_JetOperator`, `TamingCompatibility_DifferentialForms_ParameterCoefficients`, `TamingCompatibility_DifferentialForms_PositiveFunctions`, `TamingCompatibility_DifferentialForms_RadialErrorSources`, `TamingCompatibility_DifferentialForms_RadialGradientBridge`, `TamingCompatibility_DifferentialForms_RadialObserverScale`, `TamingCompatibility_DifferentialForms_RadialScalarOff`, `TamingCompatibility_DifferentialForms_RationalKernelCompare`, `TamingCompatibility_DifferentialForms_SmoothingKernel`, `TamingCompatibility_DifferentialForms_TwoDirection`, `TamingCompatibility_DifferentialForms_UniformInterior`, `TamingCompatibility_Elliptic_BilinearCoercivePos`, `TamingCompatibility_Elliptic_DerivativeIndex`, `TamingCompatibility_Elliptic_OperatorCalculus`, `TamingCompatibility_Elliptic_RealSobolevLift`, `TamingCompatibility_Functional_CompactCutoff`, `TamingCompatibility_Functional_ContinuousBundleNorm`, `TamingCompatibility_Functional_HermitianRadialProfiles`, `TamingCompatibility_Functional_NormalChart`, `TamingCompatibility_HeatFlow_HodgeHeatIdentification`, `TamingCompatibility_HeatFlow_HodgeHeatSmoothing`, `TamingCompatibility_HeatFlow_HodgeSpectralHeat`, `TamingCompatibility_HeatFlow_ResolventGammaScalar`, `TamingCompatibility_HeatFlow_VariationalResolvent`, `TamingCompatibility_Hodge_HodgeGammaLinearTransfer`, `TamingCompatibility_Hodge_HodgeGammaSplit`, `TamingCompatibility_Hodge_HodgeGeometricDistance`, `TamingCompatibility_Hodge_HodgeKernelAction`, `TamingCompatibility_Hodge_HodgeKernelGammaBounds`, `TamingCompatibility_Hodge_HodgeL2Coefficients`, `TamingCompatibility_Hodge_HodgeLocalCoefficients`, `TamingCompatibility_Hodge_HodgeManifoldKernelExtension`, `TamingCompatibility_Hodge_HodgeScalarJet`, `TamingCompatibility_Hodge_HodgeVolterraKernel`.
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ239Tc008`; the statement `OAI.TamingCompatibility.HilbertSobolev.parameter_energy_two_jet`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility

section
-- module Solutions.OAIQ239_TC.Compat
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
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
/-- d13f23b's `BorelSpace Circle`, for `circleMeasurableSpace`. -/
theorem circleBorelSpace : @BorelSpace Circle _ circleMeasurableSpace :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_JAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
namespace TamingCompatibility

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

omit [IsManifold Model ∞ X] in
lemma IsSmooth.zero : IsSmooth (0 : TwoForm X) := by
  intro f U hU hf
  change ContDiffOn ℝ ∞ (fun _ : Space => (0 : Space [⋀^Fin 2]→L[ℝ] ℝ)) U
  exact contDiffOn_const

omit [IsManifold Model ∞ X] in
lemma IsClosed.zero : IsClosed (0 : TwoForm X) := by
  intro f U hU hf y hy
  change extDerivWithin (fun _ => (0 : Space [⋀^Fin 2]→L[ℝ] ℝ)) U y = 0
  rw [extDerivWithin, fderivWithin_fun_const]
  change ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ Space ℝ 0 = 0
  exact map_zero _

end TamingCompatibility

open scoped Manifold ContDiff Topology
open Filter Set

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_BilinearCoercivePos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
namespace TamingCompatibility

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

theorem bilinear_coercive_of_pos (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v, v ≠ 0 → 0 < B v v) : IsCoercive B := by
  have hc : Continuous (fun v : E => B v v) := B.continuous.clm_apply continuous_id
  obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hc.continuousOn
  have hv₀norm : ‖v₀‖ = 1 := by simpa using hv₀
  have hv₀ne : v₀ ≠ 0 := by intro h; simp [h] at hv₀norm
  refine ⟨B v₀ v₀, hB v₀ hv₀ne, ?_⟩
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u : E := ‖v‖⁻¹ • v
  have hun : ‖u‖ = 1 := by simp [u, norm_smul, hn.ne']
  have hu : u ∈ Metric.sphere (0 : E) 1 := by simpa using hun
  have hm := hmin hu
  have heq : B v v = ‖v‖ ^ 2 * B u u := by
    dsimp [u]
    simp only [map_smul, _root_.smul_apply, smul_eq_mul]
    field_simp
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_left hm (sq_nonneg ‖v‖)]

theorem bilinear_unitBall_isVonNBounded (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v, v ≠ 0 → 0 < B v v) :
    Bornology.IsVonNBounded ℝ {v | B v v < 1} := by
  obtain ⟨c, hc, hco⟩ := bilinear_coercive_of_pos B hB
  apply (NormedSpace.isVonNBounded_ball ℝ E (1 / c + 1)).subset
  intro v hv
  rw [Metric.mem_ball, dist_zero_right]
  have hmul : c * (1 / c) = 1 := by field_simp
  by_contra! hn
  have hrec : 0 < 1 / c := one_div_pos.mpr hc
  have hn1 : 1 < ‖v‖ := by linarith
  have hnpos : 0 < ‖v‖ := hn1.trans' zero_lt_one
  have hcn : 1 < c * ‖v‖ := by nlinarith
  have hsq : c * ‖v‖ ≤ c * ‖v‖ ^ 2 := by nlinarith
  have hco' := hco v
  change B v v < 1 at hv
  linarith

end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ComplexEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.MetricForms
open ContinuousAlternatingMap
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def complexEquiv (J : E →L[ℝ] E) (hJ : ∀ u, J (J u) = -u) : E ≃L[ℝ] E where
  toLinearEquiv := {
    toLinearMap := J.toLinearMap
    invFun := fun u => -(J u)
    left_inv := fun u => by change -J (J u) = u; rw [hJ,neg_neg]
    right_inv := fun u => by change J (-J u) = u; rw [map_neg,hJ,neg_neg] }
  continuous_toFun := J.continuous
  continuous_invFun := J.continuous.neg
end TamingCompatibility.MetricForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_GeometricFrameTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.ScalarPair
open _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv ContDiff

lemma postcomp_derivative {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (L : G →L[ℝ] H) (u : 𝓢(E,G)) (v : E) :
    ∂_{v} (SchwartzMap.postcompCLM L u) = SchwartzMap.postcompCLM L (∂_{v} u) := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (L ∘ u) x v = L (fderiv ℝ u x v)
  rw [(L.hasFDerivAt.comp x (u.differentiableAt (x := x)).hasFDerivAt).fderiv]
  rfl

end TamingCompatibility.ScalarPair

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_AntiDdcBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.RadialPotential
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def logPotential (s : ℝ) (z : E) : ℝ := (1/2:ℝ)*Real.log (s^2+‖z‖^2)
def sqrtPotential (s : ℝ) (z : E) : ℝ := Real.sqrt (s^2+‖z‖^2)

omit [InnerProductSpace ℝ E] in
lemma radial_sq_pos {s : ℝ} (hs : 0 < s) (z : E) : 0 < s^2+‖z‖^2 := by positivity

lemma logPotential_fderiv {s : ℝ} (hs : 0 < s) (z : E) :
    fderiv ℝ (logPotential s) z = (s^2+‖z‖^2)⁻¹ • innerSL ℝ z := by
  have h := (((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add (s^2)).log
    (ne_of_gt (radial_sq_pos hs z))).const_mul (1/2:ℝ)
  rw [show logPotential s = (fun z : E => (1/2:ℝ)*Real.log (s^2+‖z‖^2)) from rfl,h.fderiv]
  ext v
  simp only [_root_.smul_apply,smul_eq_mul,innerSL_apply_apply]
  ring

lemma sqrtPotential_fderiv {s : ℝ} (hs : 0 < s) (z : E) :
    fderiv ℝ (sqrtPotential s) z = (Real.sqrt (s^2+‖z‖^2))⁻¹ • innerSL ℝ z := by
  have h := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add (s^2)).sqrt
    (ne_of_gt (radial_sq_pos hs z))
  rw [show sqrtPotential s = (fun z : E => Real.sqrt (s^2+‖z‖^2)) from rfl,h.fderiv]
  ext v
  simp only [_root_.smul_apply,smul_eq_mul,innerSL_apply_apply]
  ring

end TamingCompatibility.RadialPotential

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_TwoDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open ContinuousAlternatingMap
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma logPotential_smooth {s : ℝ} (hs : 0 < s) : ContDiff ℝ ∞ (logPotential (E := E) s) := by
  have h : ContDiff ℝ ∞ (fun z : E => Real.log (s^2+‖z‖^2)) :=
    (contDiff_const.add (contDiff_norm_sq ℝ)).log (fun z => ne_of_gt (radial_sq_pos hs z))
  exact contDiff_const.mul h

lemma sqrtPotential_smooth {s : ℝ} (hs : 0 < s) : ContDiff ℝ ∞ (sqrtPotential (E := E) s) := by
  exact (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun z => ne_of_gt (radial_sq_pos hs z))

end TamingCompatibility.RadialPotential

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialGradientBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

section
noncomputable section
namespace TamingCompatibility.RadialPotential
open Set
open scoped ContDiff RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def logGradientProfile (s : ℝ) (z v : E) : ℝ :=
  (s^2+‖z‖^2)⁻¹ * ⟪z,v⟫
def sqrtGradientProfile (s : ℝ) (z v : E) : ℝ :=
  (Real.sqrt (s^2+‖z‖^2))⁻¹ * ⟪z,v⟫

lemma logGradientProfile_eq_fderiv {s : ℝ} (hs : 0 < s) (z v : E) :
    logGradientProfile s z v = fderiv ℝ (logPotential s) z v := by
  rw [logPotential_fderiv hs]
  rfl
lemma sqrtGradientProfile_eq_fderiv {s : ℝ} (hs : 0 < s) (z v : E) :
    sqrtGradientProfile s z v = fderiv ℝ (sqrtPotential s) z v := by
  rw [sqrtPotential_fderiv hs]
  rfl

end TamingCompatibility.RadialPotential
end
end

end

section

noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter Function Metric
open scoped ContDiff Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]

def unitCutoff : E → ℝ := (⟨1, 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : E))

def scaledCutoff (r : ℝ) (z : E) : ℝ := unitCutoff (r⁻¹ • z)

def shellCutoff (r : ℝ) (z : E) : ℝ := scaledCutoff (2*r) z - scaledCutoff r z

lemma unitCutoff_smooth : ContDiff ℝ ∞ (unitCutoff : E → ℝ) :=
  ContDiffBump.contDiff _

lemma unitCutoff_one {z : E} (hz : ‖z‖ ≤ 1) : unitCutoff z = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, dist_zero_right] using hz

lemma unitCutoff_zero {z : E} (hz : 2 ≤ ‖z‖) : unitCutoff z = 0 := by
  apply ContDiffBump.zero_of_le_dist
  simpa only [dist_zero_right] using hz

lemma scaledCutoff_smooth (r : ℝ) : ContDiff ℝ ∞ (scaledCutoff r : E → ℝ) :=
  unitCutoff_smooth.comp (contDiff_const.smul contDiff_id)

lemma scaledCutoff_one {r : ℝ} (hr : 0 < r) {z : E} (hz : ‖z‖ ≤ r) :
    scaledCutoff r z = 1 := by
  apply unitCutoff_one
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  exact (inv_mul_le_iff₀ hr).mpr (by simpa using hz)

lemma scaledCutoff_zero {r : ℝ} (hr : 0 < r) {z : E} (hz : 2*r ≤ ‖z‖) :
    scaledCutoff r z = 0 := by
  apply unitCutoff_zero
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  exact (le_inv_mul_iff₀ hr).mpr (by simpa [mul_comm] using hz)

lemma scaledCutoff_tsupport {r : ℝ} (hr : 0 < r) :
    tsupport (scaledCutoff r : E → ℝ) ⊆ Metric.closedBall 0 (2*r) := by
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  simp only [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  exact hz (scaledCutoff_zero hr (le_of_lt (lt_of_not_ge h)))

lemma scaledCutoff_compact [ProperSpace E] {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (scaledCutoff r : E → ℝ) :=
  (isCompact_closedBall (0:E) (2*r)).of_isClosed_subset (isClosed_tsupport _) (scaledCutoff_tsupport hr)

lemma shellCutoff_smooth (r : ℝ) : ContDiff ℝ ∞ (shellCutoff r : E → ℝ) :=
  (scaledCutoff_smooth _).sub (scaledCutoff_smooth _)

lemma shellCutoff_zero_inner {r : ℝ} (hr : 0 < r) {z : E} (hz : ‖z‖ ≤ r) :
    shellCutoff r z = 0 := by
  rw [shellCutoff, scaledCutoff_one (by positivity : 0 < 2*r) (by linarith),
    scaledCutoff_one hr hz, sub_self]

lemma shellCutoff_tsupport {r : ℝ} (hr : 0 < r) :
    tsupport (shellCutoff r : E → ℝ) ⊆ Metric.closedBall 0 (4*r) \ Metric.ball 0 r := by
  apply closure_minimal _ (isClosed_closedBall.sdiff isOpen_ball)
  intro z hz
  constructor
  · simp only [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    have hz2 : 2*r ≤ ‖z‖ := by linarith [lt_of_not_ge h]
    have hz4 : 2*(2*r) ≤ ‖z‖ := by linarith [lt_of_not_ge h]
    apply hz
    rw [shellCutoff, scaledCutoff_zero (by positivity : 0 < 2*r) hz4,
      scaledCutoff_zero hr hz2, sub_self]
  · simp only [Metric.mem_ball, dist_zero_right, not_lt]
    by_contra h
    exact hz (shellCutoff_zero_inner hr (le_of_lt (lt_of_not_ge h)))

end TamingCompatibility.RadialPotential

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_RadialCutoffErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [HasContDiffBump E]

lemma fderiv_scaledCutoff_zero_inner {R : ℝ} (hR : 0 < R) {z : E} (hz : ‖z‖ < R) :
    fderiv ℝ (scaledCutoff R : E → ℝ) z = 0 := by
  have he : (scaledCutoff R : E → ℝ) =ᶠ[𝓝 z] fun _ => 1 := by
    filter_upwards [isOpen_ball.mem_nhds (by simpa using hz : z ∈ ball (0:E) R)] with w hw
    exact scaledCutoff_one hR (by simpa using (le_of_lt (show ‖w‖ < R by simpa using hw)))
  rw [he.fderiv_eq]
  simp

end TamingCompatibility.RadialPotential

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_RadialBundleSources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]

omit [InnerProductSpace ℝ E] [HasContDiffBump E] [ProperSpace E] in
lemma tsupport_translated_mul_subset {a : E → ℝ} (f : E → ℝ) (b : E) (R : ℝ)
    (ha : tsupport a ⊆ closedBall 0 R) :
    tsupport (fun z => a (z-b) * f z) ⊆ closedBall b R := by
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  have hn : a (z-b) ≠ 0 := fun h => hz (by simp [h])
  have hb := ha (subset_tsupport a hn)
  simpa only [mem_closedBall,dist_zero_right,dist_eq_norm,sub_zero] using hb

end TamingCompatibility.RadialPotential

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_LocalMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.MeasureTheory
open scoped ENNReal
namespace TamingCompatibility.LocalRestriction

variable {E F : Type*} [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def localMeasure (μ : Measure E) (K : Set E) : Measure K := μ.comap Subtype.val

def restrict (μ : Measure E) (K : Set E) (hK : MeasurableSet K) :
    Lp F 2 μ →L[ℝ] Lp F 2 (localMeasure μ K) :=
  (Lp.compMeasurePreservingₗᵢ ℝ ((↑) : K → E)
    (measurePreserving_subtype_coe hK)).toContinuousLinearMap ∘L
      Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using μ.restrict_le_self (s := K))

lemma restrict_coe (μ : Measure E) (K : Set E) (hK : MeasurableSet K)
    (u : Lp F 2 μ) : restrict μ K hK u =ᵐ[localMeasure μ K] (fun x : K => u x) := by
  apply (Lp.coeFn_compMeasurePreserving _ (measurePreserving_subtype_coe hK)).trans
  exact (measurePreserving_subtype_coe hK).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by simp)
      (by simpa using μ.restrict_le_self (s := K)) u)

lemma restrict_norm_le (μ : Measure E) (K : Set E) (hK : MeasurableSet K)
    (u : Lp F 2 μ) : ‖restrict μ K hK u‖ ≤ ‖u‖ := by
  change ‖Lp.compMeasurePreserving ((↑) : K → E) (measurePreserving_subtype_coe hK)
    (Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
      (by simpa using μ.restrict_le_self (s := K)) u)‖ ≤ _
  rw [Lp.norm_compMeasurePreserving]
  have hb := Lp.norm_LpToLpOfMeasureLeSMul_le (p := (2 : ℝ≥0∞)) (E := F)
    (c := 1) (by simp) (by simpa using μ.restrict_le_self (s := K))
  have hn : ‖(Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
      (by simpa using μ.restrict_le_self (s := K)) : Lp F 2 μ →L[ℝ] Lp F 2 (μ.restrict K))‖ ≤ 1 := by
    simpa using hb
  exact ContinuousLinearMap.le_of_opNorm_le _ hn u |>.trans_eq (one_mul _)

lemma finite_localMeasure (μ : Measure E) (K : Set E) (hK : MeasurableSet K)
    (hm : μ K < ∞) : IsFiniteMeasure (localMeasure μ K) := by
  constructor
  have h := (measurePreserving_subtype_coe (μa := μ) hK).measure_preimage MeasurableSet.univ
  change (μ.comap ((↑) : K → E)) Set.univ < ∞
  have h' : (μ.comap ((↑) : K → E)) Set.univ = (μ.restrict K) Set.univ := h
  exact h'.trans_lt (by rw [Measure.restrict_apply_univ]; exact hm)

end TamingCompatibility.LocalRestriction

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_LocalInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section

noncomputable section
open _root_.MeasureTheory Filter
open scoped ENNReal BoundedContinuousFunction

namespace TamingCompatibility.RellichTail
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def cutoff (g : E →ᵇ ℂ) (R : ℝ) : E → ℂ := (Metric.closedBall 0 R).indicator g

lemma cutoff_memLp_top (g : E →ᵇ ℂ) (R : ℝ) :
    MemLp (cutoff g R) ∞ (volume : Measure E) :=
  g.memLp_top.indicator measurableSet_closedBall

lemma cutoff_memLp_two (g : E →ᵇ ℂ) (R : ℝ) :
    MemLp (cutoff g R) 2 (volume : Measure E) := by
  apply (memLp_indicator_iff_restrict measurableSet_closedBall).mpr
  let : IsFiniteMeasure ((volume : Measure E).restrict (Metric.closedBall 0 R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall (0 : E) R).measure_lt_top⟩
  exact MemLp.of_bound (g.continuous.aestronglyMeasurable) ‖g‖
    (Eventually.of_forall g.norm_coe_le_norm)

lemma cutoff_support (g : E →ᵇ ℂ) (R : ℝ) :
    ∀ᵐ ξ ∂(volume : Measure E), R < ‖ξ‖ → (cutoff_memLp_two g R).toLp (cutoff g R) ξ = 0 := by
  filter_upwards [(cutoff_memLp_two g R).coeFn_toLp] with ξ hξ h
  rw [hξ]
  exact Set.indicator_of_notMem (by simpa [Metric.mem_closedBall, dist_zero_right] using not_le.mpr h) _

lemma cutoff_lp_eq (g : E →ᵇ ℂ) (R : ℝ) :
    (cutoff_memLp_two g R).toLp (cutoff g R) =ᵐ[volume]
      (cutoff_memLp_top g R).toLp (cutoff g R) :=
  (cutoff_memLp_two g R).coeFn_toLp.trans (cutoff_memLp_top g R).coeFn_toLp.symm

lemma tail_norm_le {g : E →ᵇ ℂ} {R ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ ξ, R < ‖ξ‖ → ‖g ξ‖ ≤ ε) :
    ‖(g.memLp_top (μ := (volume : Measure E))).toLp g -
      (cutoff_memLp_top g R).toLp (cutoff g R)‖ ≤ ε := by
  rw [← MemLp.toLp_sub, Lp.norm_toLp,
    eLpNorm_exponent_top]
  have hb : ∀ ξ, ‖g ξ - cutoff g R ξ‖ ≤ ε := by
    intro ξ
    by_cases hm : ξ ∈ Metric.closedBall (0 : E) R
    · simp [cutoff, Set.indicator_of_mem hm, hε]
    · simpa [cutoff, Set.indicator_of_notMem hm] using
        h ξ (lt_of_not_ge (by simpa [Metric.mem_closedBall, dist_zero_right] using hm))
  have he := eLpNormEssSup_le_of_ae_bound (μ := (volume : Measure E))
    (Eventually.of_forall hb)
  exact (ENNReal.toReal_mono (by finiteness) he).trans_eq (ENNReal.toReal_ofReal hε)

end TamingCompatibility.RellichTail

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Bessel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.LocalRestriction
open _root_.MeasureTheory Set
open scoped RealInnerProductSpace
variable {E F : Type*} [MeasurableSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def restore (μ : Measure E) (K : Set E) (hK : MeasurableSet K) :
    Lp F 2 (localMeasure μ K) →L[ℝ] Lp F 2 μ :=
  ContinuousLinearMap.adjoint (restrict μ K hK)

lemma restore_restrict (μ : Measure E) (K : Set E) (hK : MeasurableSet K)
    (u : Lp F 2 μ) (hu : ∀ᵐ x ∂μ, x ∉ K → u x = 0) :
    restore μ K hK (restrict μ K hK u) = u := by
  apply ext_inner_left ℝ
  intro v
  rw [restore, ContinuousLinearMap.adjoint_inner_right, L2.inner_def, L2.inner_def]
  calc
    (∫ x : K, ⟪restrict μ K hK v x, restrict μ K hK u x⟫ ∂localMeasure μ K) =
        ∫ x : K, ⟪v x, u x⟫ ∂localMeasure μ K := by
      apply integral_congr_ae
      filter_upwards [restrict_coe μ K hK v, restrict_coe μ K hK u] with x hv hx
      rw [hv, hx]
    _ = ∫ x in K, ⟪v x, u x⟫ ∂μ := integral_subtype_comap (μ := μ) hK (fun x => ⟪v x, u x⟫)
    _ = ∫ x, ⟪v x, u x⟫ ∂μ := by
      rw [← integral_indicator hK]
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      by_cases h : x ∈ K
      · exact indicator_of_mem h _
      · rw [indicator_of_notMem h, hx h, inner_zero_right]

end TamingCompatibility.LocalRestriction


end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_CriticalRescale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in

def rescaleSchwartz (p : E) (r : ℝ) (hr : r ≠ 0) : 𝓢(E,F) →L[ℂ] 𝓢(E,F) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := E) (Units.mk0 r hr))).comp
      (SchwartzMap.compSubConstCLM ℂ (-p))

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UniformInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap LineDeriv Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def scaledCoefficient (k : ℕ) (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (p : E) (r : ℝ) : 𝓢(E,ℂ) :=
  (hχ.mul_right (f' := fun x => (r:ℂ)^k * f (p + r • x))).toSchwartzMap
    ((χ.smooth ⊤).mul (contDiff_const.mul
      (hf.comp (contDiff_const.add (contDiff_const.smul contDiff_id)))))

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_DerivativeIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap Laplacian ENNReal
open scoped BigOperators
namespace TamingCompatibility.ManifoldLocalization
open _root_.MeasureTheory Set Function LineDeriv
open scoped Topology Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
variable (k : ℕ)

abbrev DerivativeIndex := Option (Fin (Module.finrank ℝ Space))

end TamingCompatibility.ManifoldLocalization

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_VariationalResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped RealInnerProductSpace

namespace TamingCompatibility.Variational
open scoped RealInnerProductSpace
variable {V H Z : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

def energy (i : V →L[ℝ] H) (D : V →L[ℝ] Z) : V →L[ℝ] V →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp i i + (innerSL ℝ).bilinearComp D D

omit [CompleteSpace V] [CompleteSpace H] in
@[simp] lemma energy_apply (i : V →L[ℝ] H) (D : V →L[ℝ] Z) (u v : V) :
    energy i D u v = ⟪i u, i v⟫ + ⟪D u, D v⟫ := rfl

def weakSolution (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (hc : IsCoercive (energy i D)) : H →L[ℝ] V :=
  hc.continuousLinearEquivOfBilin.symm.toContinuousLinearMap ∘L i.adjoint

lemma weakSolution_identity (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (hc : IsCoercive (energy i D)) (f : H) (v : V) :
    ⟪i (weakSolution i D hc f), i v⟫ + ⟪D (weakSolution i D hc f), D v⟫ = ⟪f, i v⟫ := by
  rw [← energy_apply, ← hc.continuousLinearEquivOfBilin_apply]
  simp only [weakSolution, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  exact i.adjoint_inner_left v f

def resolvent (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (hc : IsCoercive (energy i D)) : H →L[ℝ] H := i ∘L weakSolution i D hc

lemma resolvent_symmetric (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (hc : IsCoercive (energy i D)) : (resolvent i D hc).toLinearMap.IsSymmetric := by
  intro f g
  have hfg := weakSolution_identity i D hc f (weakSolution i D hc g)
  have hgf := weakSolution_identity i D hc g (weakSolution i D hc f)
  change ⟪i (weakSolution i D hc f), g⟫ = ⟪f, i (weakSolution i D hc g)⟫
  calc
    _ = ⟪g, i (weakSolution i D hc f)⟫ := real_inner_comm _ _
    _ = _ := by
      rw [← hgf, ← hfg]
      congr 1 <;> exact real_inner_comm _ _

lemma resolvent_norm_le (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (hc : IsCoercive (energy i D)) (f : H) : ‖resolvent i D hc f‖ ≤ ‖f‖ := by
  have h := weakSolution_identity i D hc f (weakSolution i D hc f)
  have hle := real_inner_le_norm f (i (weakSolution i D hc f))
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  change ‖i (weakSolution i D hc f)‖ ≤ ‖f‖
  by_cases hz : i (weakSolution i D hc f) = 0
  · simp [hz]
  · have hp : 0 < ‖i (weakSolution i D hc f)‖ := norm_pos_iff.mpr hz
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith [sq_nonneg ‖D (weakSolution i D hc f)‖]

end TamingCompatibility.Variational

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_CompactCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.SchwartzCutoff
open Set Filter
open scoped ContDiff Topology SchwartzMap Manifold
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma exists_one_on_compact {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ φ : 𝓢(E,ℝ), HasCompactSupport (φ : E → ℝ) ∧ tsupport φ ⊆ U ∧ ∀ x ∈ K, φ x = 1 := by
  obtain ⟨L,hL,hKL,hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨b,hbone,hbzero,-⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    𝓘(ℝ,E) (n := (⊤ : ℕ∞)) hK.isClosed hKL
  have hbs : tsupport b ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro y hy
    by_contra hn
    exact hy (hbzero y hn)
  have hbc : HasCompactSupport (b : E → ℝ) := hL.of_isClosed_subset (isClosed_tsupport b) hbs
  exact ⟨hbc.toSchwartzMap b.contMDiff.contDiff,hbc,hbs.trans hLU,hbone.self_of_nhdsSet⟩
end TamingCompatibility.SchwartzCutoff

namespace TamingCompatibility.HilbertSobolev
open Set TemperedDistribution
open scoped SchwartzMap
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma tests_eq_of_localize {U : Set E} (hU : IsOpen U) {u v : 𝓢'(E,F)}
    (h : ∀ χ : 𝓢(E,ℂ), HasCompactSupport (χ : E → ℂ) → tsupport χ ⊆ U →
      smulLeftCLM F χ u = smulLeftCLM F χ v)
    (φ : 𝓢(E,ℂ)) (hc : HasCompactSupport (φ : E → ℂ)) (hφU : tsupport φ ⊆ U) :
    u φ = v φ := by
  obtain ⟨χ,hχ,hχU,hχone⟩ := SchwartzCutoff.exists_one_on_compact hc hU hφU
  let ψ : 𝓢(E,ℂ) := SchwartzMap.postcompCLM Complex.ofRealCLM χ
  have hs : tsupport ψ ⊆ tsupport χ := tsupport_comp_subset (map_zero Complex.ofRealCLM) χ
  have he := congrArg (fun w : 𝓢'(E,F) => w φ) (h ψ
    (hχ.of_isClosed_subset (isClosed_tsupport ψ) hs) (hs.trans hχU))
  have hp : SchwartzMap.smulLeftCLM ℂ ψ φ = φ := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply ψ.hasTemperateGrowth]
    by_cases hx : x ∈ tsupport φ
    · change (χ x : ℂ) * φ x = φ x
      rw [hχone x hx,Complex.ofReal_one,one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx,smul_zero]
  change u (SchwartzMap.smulLeftCLM ℂ ψ φ) = v (SchwartzMap.smulLeftCLM ℂ ψ φ) at he
  rwa [hp] at he
end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_LocalSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open TemperedDistribution _root_.MeasureTheory Set Filter
open scoped SchwartzMap Topology ContDiff BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma postcomp_real_tsupport (φ : 𝓢(E,ℝ)) :
    tsupport (SchwartzMap.postcompCLM Complex.ofRealCLM φ) ⊆ tsupport φ := by
  apply closure_mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support,not_not] at hx ⊢
  change (φ x : ℂ) = 0
  rw [hx,Complex.ofReal_zero]

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ParameterCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution Filter LineDeriv Set
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

section
omit [MeasurableSpace E] [BorelSpace E]

def movingFrozenCoefficient (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (p₀ : E) (t : ℝ × E) : 𝓢(E,ℂ) :=
  (hχ.mul_right (f' := fun x => f (t.2 + t.1 • x) - f p₀)).toSchwartzMap
    ((χ.smooth ⊤).mul ((hf.comp (contDiff_const.add (contDiff_const.smul contDiff_id))).sub
      contDiff_const))

end

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_ContinuousBundleNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
namespace TamingCompatibility
variable {B F : Type*} [TopologicalSpace B] [CompactSpace B] [T2Space B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]

omit [CompactSpace B] [T2Space B] [ProperSpace F] in
lemma continuous_bundle_norm : Continuous (fun p : TotalSpace F E => ‖p.2‖) := by
  have h : Continuous (fun p : TotalSpace F E => inner ℝ p.2 p.2) :=
    continuous_id.inner_bundle continuous_id
  convert h.sqrt using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  simp

theorem isCompact_bundle_closedBall (r : ℝ) :
    IsCompact {p : TotalSpace F E | ‖p.2‖ ≤ r} := by
  have hlocal (x : B) : ∃ K : Set B, ∃ C : ℝ,
      IsCompact K ∧ x ∈ interior K ∧
      (K ⊆ (trivializationAt F E x).baseSet) ∧
      ∀ y ∈ K, ∀ v : E y, ‖v‖ ≤ r →
        ‖(trivializationAt F E x).continuousLinearMapAt ℝ y v‖ ≤ C := by
    obtain ⟨C, hC, hevent⟩ := eventually_norm_trivializationAt_lt F E x
    have hn : {y | ‖(trivializationAt F E x).continuousLinearMapAt ℝ y‖ < C} ∩
        (trivializationAt F E x).baseSet ∈ 𝓝 x :=
      inter_mem hevent ((trivializationAt F E x).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F E x))
    obtain ⟨U, hUs, hUo, hxU⟩ := mem_nhds_iff.mp hn
    obtain ⟨K, hKc, hxK, hKU⟩ := exists_compact_subset hUo hxU
    refine ⟨K, C * max r 0, hKc, hxK, fun y hy => (hUs (hKU hy)).2, ?_⟩
    intro y hy v hv
    exact (ContinuousLinearMap.le_opNorm _ v).trans
      (mul_le_mul ((hUs (hKU hy)).1.le) (hv.trans (le_max_left _ _))
        (norm_nonneg _) hC.le)
  choose K C hK hxK hKb hbound using hlocal
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => interior (K x))
    (fun _ => isOpen_interior) (fun x _ => mem_iUnion.mpr ⟨x, hxK x⟩)
  let A (x : B) : Set (TotalSpace F E) :=
    (trivializationAt F E x).toOpenPartialHomeomorph.symm ''
      (K x ×ˢ Metric.closedBall (0 : F) (C x))
  have hAc (x : B) : IsCompact (A x) := by
    apply ((hK x).prod (isCompact_closedBall (0 : F) (C x))).image_of_continuousOn
    apply (trivializationAt F E x).toOpenPartialHomeomorph.continuousOn_symm.mono
    intro q hq
    exact (trivializationAt F E x).mem_target.mpr (hKb x hq.1)
  have hsc : IsCompact (⋃ x ∈ t, A x) := t.isCompact_biUnion (fun x _ => hAc x)
  apply hsc.of_isClosed_subset
    (isClosed_le continuous_bundle_norm continuous_const)
  intro p hp
  obtain ⟨x, hxt, hx⟩ := mem_iUnion₂.mp (ht (mem_univ p.proj))
  have hpk : p.proj ∈ K x := interior_subset hx
  have hpb : p.proj ∈ (trivializationAt F E x).baseSet := hKb x hpk
  apply mem_iUnion₂.mpr
  refine ⟨x, hxt, ?_⟩
  refine ⟨(trivializationAt F E x) p, ?_, ?_⟩
  · constructor
    · simpa only [(trivializationAt F E x).coe_fst' hpb] using hpk
    · rw [Metric.mem_closedBall, dist_zero_right]
      rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hpb p.2]
      exact hbound x _ hpk _ hp
  · exact (trivializationAt F E x).toOpenPartialHomeomorph.left_inv
      ((trivializationAt F E x).mem_source.mpr hpb)

theorem isCompact_bundle_unitSphere :
    IsCompact {p : TotalSpace F E | ‖p.2‖ = 1} :=
  (isCompact_bundle_closedBall (E := E) 1).of_isClosed_subset
    (isClosed_eq continuous_bundle_norm continuous_const) (fun _ h => h.le)

end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PositiveFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility

section CompactFunctions

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]

def positiveFunctions : Set C(K, ℝ) := {f | ∀ x, 0 < f x}

end CompactFunctions

open Bundle Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

lemma isCompact_metricUnit [CompactSpace X] [T2Space X]
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type)) :
    IsCompact {p : TangentBundle Model X | g.inner p.proj p.2 p.2 = 1} := by
  let : RiemannianBundle (TangentSpace Model : X → Type) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  have heq : {p : TangentBundle Model X | g.inner p.proj p.2 p.2 = 1} =
      {p : TangentBundle Model X | ‖p.2‖ = 1} := by
    ext p
    change inner ℝ p.2 p.2 = 1 ↔ ‖p.2‖ = 1
    rw [real_inner_self_eq_norm_sq]
    constructor
    · intro h
      nlinarith [norm_nonneg p.2]
    · intro h
      rw [h]
      norm_num
  rw [heq]
  exact isCompact_bundle_unitSphere

end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_JetOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.JetOperator
open ContinuousAlternatingMap
open scoped SchwartzMap ContDiff LineDeriv
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

abbrev Jet (F : Type*) := F × (Fin 4 → F) × (Fin 4 → Fin 4 → F)

def projZero : Jet F →L[ℝ] F := ContinuousLinearMap.fst ℝ F _
def projOne (i : Fin 4) : Jet F →L[ℝ] F :=
  (ContinuousLinearMap.proj i).comp ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ F _))
def projTwo (i j : Fin 4) : Jet F →L[ℝ] F :=
  ((ContinuousLinearMap.proj j) : (Fin 4 → F) →L[ℝ] F).comp
    (((ContinuousLinearMap.proj i) : (Fin 4 → Fin 4 → F) →L[ℝ] (Fin 4 → F)).comp
    ((ContinuousLinearMap.snd ℝ (Fin 4 → F) (Fin 4 → Fin 4 → F)).comp
      (ContinuousLinearMap.snd ℝ F _)))

end TamingCompatibility.JetOperator

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_JetBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.JetOperator
open ContinuousAlternatingMap Set LineDeriv
open scoped SchwartzMap ContDiff LineDeriv
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type*} [Fintype ι]
abbrev BasisJet (ι F : Type*) := F × (ι → F) × (ι → ι → F)
def basisProjZero : BasisJet ι F →L[ℝ] F := ContinuousLinearMap.fst ℝ F _
def basisProjOne (i : ι) : BasisJet ι F →L[ℝ] F :=
  (ContinuousLinearMap.proj i).comp ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ F _))
def basisProjTwo (i j : ι) : BasisJet ι F →L[ℝ] F :=
  ((ContinuousLinearMap.proj j) : (ι → F) →L[ℝ] F).comp
    (((ContinuousLinearMap.proj i) : (ι → ι → F) →L[ℝ] (ι → F)).comp
    ((ContinuousLinearMap.snd ℝ (ι → F) (ι → ι → F)).comp
      (ContinuousLinearMap.snd ℝ F _)))
end TamingCompatibility.JetOperator

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialScalarOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility
open Set
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def supportedSchwartz (K : Set E) : Submodule ℝ 𝓢(E,ℝ) where
  carrier := {f | tsupport f ⊆ K}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    exact (tsupport_add (f : E → ℝ) g).trans (union_subset hf hg)
  smul_mem' := by
    intro c f hf
    exact (tsupport_smul_subset_right (fun _ : E => c) (f : E → ℝ)).trans hf

lemma supportedSchwartz_compact {K : Set E} (hK : IsCompact K)
    (f : supportedSchwartz K) : HasCompactSupport (f.val : E → ℝ) :=
  hK.of_isClosed_subset (isClosed_tsupport _) f.property

end TamingCompatibility

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialErrorSources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]

omit [InnerProductSpace ℝ E] [HasContDiffBump E] [ProperSpace E] in
lemma tsupport_translated_subset {f : E → ℝ} (b : E) (R : ℝ)
    (hf : tsupport f ⊆ closedBall 0 R) :
    tsupport (fun z => f (z-b)) ⊆ closedBall b R := by
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  have hb := hf (subset_tsupport f hz)
  simpa only [mem_closedBall,dist_zero_right,dist_eq_norm,sub_zero] using hb

end TamingCompatibility.RadialPotential

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_RadialOperatorCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter Metric
open scoped ContDiff Topology SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]

def complexScaledCutoff (r : ℝ) (hr : 0 < r) : 𝓢(E,ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM
    ((scaledCutoff_compact hr).toSchwartzMap (scaledCutoff_smooth r))

end TamingCompatibility.RadialPotential

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialObserverScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential

def observerScale (δ c d : ℝ) : ℝ := min (δ/2) (d/(5+c))

end TamingCompatibility.RadialPotential


end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_HermitianRadialProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter ContinuousAlternatingMap
open scoped ContDiff Topology RealInnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def hermitianGraph (K : E →L[ℝ] E) : E →L[ℝ] WithLp 2 (E × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℝ E).prod K)

lemma hermitianGraph_apply (K : E →L[ℝ] E) (z : E) :
    hermitianGraph K z = WithLp.toLp 2 (z,K z) := rfl

lemma hermitianGraph_norm_sq (K : E →L[ℝ] E) (z : E) :
    ‖hermitianGraph K z‖^2 = ‖z‖^2 + ‖K z‖^2 := by
  simp [hermitianGraph_apply,WithLp.prod_norm_sq_eq_of_L2]

lemma hermitianGraph_inner (K : E →L[ℝ] E) (z v : E) :
    ⟪hermitianGraph K z,hermitianGraph K v⟫ = ⟪z,v⟫ + ⟪K z,K v⟫ := rfl

def hermitianLogPotential (K : E →L[ℝ] E) (s : ℝ) (z : E) : ℝ :=
  logPotential s (hermitianGraph K z)

def hermitianSqrtPotential (K : E →L[ℝ] E) (s : ℝ) (z : E) : ℝ :=
  sqrtPotential s (hermitianGraph K z)

lemma hermitianLogPotential_smooth (K : E →L[ℝ] E) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (hermitianLogPotential K s) :=
  (logPotential_smooth hs).comp (hermitianGraph K).contDiff

lemma hermitianSqrtPotential_smooth (K : E →L[ℝ] E) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (hermitianSqrtPotential K s) :=
  (sqrtPotential_smooth hs).comp (hermitianGraph K).contDiff

end TamingCompatibility.RadialPotential

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianCoefficientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def hermitianLogGradientProfile (K : E →L[ℝ] E) (s : ℝ) (z v : E) : ℝ :=
  (s^2+‖z‖^2+‖K z‖^2)⁻¹ * (⟪z,v⟫+⟪K z,K v⟫)
def hermitianSqrtGradientProfile (K : E →L[ℝ] E) (s : ℝ) (z v : E) : ℝ :=
  (Real.sqrt (s^2+‖z‖^2+‖K z‖^2))⁻¹ * (⟪z,v⟫+⟪K z,K v⟫)

lemma hermitianLogGradient_eq (K : E →L[ℝ] E) (s : ℝ) (z v : E) :
    hermitianLogGradientProfile K s z v =
      logGradientProfile s (hermitianGraph K z) (hermitianGraph K v) := by
  simp only [hermitianLogGradientProfile,logGradientProfile,hermitianGraph_norm_sq,
    hermitianGraph_inner,add_assoc]

lemma hermitianSqrtGradient_eq (K : E →L[ℝ] E) (s : ℝ) (z v : E) :
    hermitianSqrtGradientProfile K s z v =
      sqrtGradientProfile s (hermitianGraph K z) (hermitianGraph K v) := by
  simp only [hermitianSqrtGradientProfile,sqrtGradientProfile,hermitianGraph_norm_sq,
    hermitianGraph_inner,add_assoc]

lemma hermitianLogGradient_eq_fderiv (K : E →L[ℝ] E) {s : ℝ} (hs : 0 < s) (z v : E) :
    hermitianLogGradientProfile K s z v = fderiv ℝ (hermitianLogPotential K s) z v := by
  rw [hermitianLogGradient_eq,logGradientProfile_eq_fderiv hs]
  change _ = fderiv ℝ (fun x => logPotential s (hermitianGraph K x)) z v
  rw [fderiv_fun_comp z ((logPotential_smooth hs).differentiable (by simp) _)
    (hermitianGraph K).differentiableAt,(hermitianGraph K).fderiv]
  rfl

lemma hermitianSqrtGradient_eq_fderiv (K : E →L[ℝ] E) {s : ℝ} (hs : 0 < s) (z v : E) :
    hermitianSqrtGradientProfile K s z v = fderiv ℝ (hermitianSqrtPotential K s) z v := by
  rw [hermitianSqrtGradient_eq,sqrtGradientProfile_eq_fderiv hs]
  change _ = fderiv ℝ (fun x => sqrtPotential s (hermitianGraph K x)) z v
  rw [fderiv_fun_comp z ((sqrtPotential_smooth hs).differentiable (by simp) _)
    (hermitianGraph K).differentiableAt,(hermitianGraph K).fderiv]
  rfl

end TamingCompatibility.RadialPotential

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianVariableProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def variableLogProfile (W : E → E →L[ℝ] E) (χ a : E → ℝ) (V : E → E)
    (p : ℝ × ℝ × E) (z : E) : ℝ :=
  χ z * (a (p.2.1 • z) * hermitianLogGradientProfile (W p.2.2) p.1 z (V (p.2.2+p.2.1•z)))

def variableSqrtProfile (W : E → E →L[ℝ] E) (χ a : E → ℝ) (V : E → E)
    (p : ℝ × ℝ × E) (z : E) : ℝ :=
  χ z * (a (p.2.1 • z) * hermitianSqrtGradientProfile (W p.2.2) p.1 z (V (p.2.2+p.2.1•z)))

end TamingCompatibility.HermitianRadial

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianPhysicalJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]

def logSingularSource (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (s : ℝ) (b z : E) : ℝ :=
  a z * hermitianLogGradientProfile (W b) s z (V (b+z))
def sqrtSingularSource (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (s : ℝ) (b z : E) : ℝ :=
  a z * hermitianSqrtGradientProfile (W b) s z (V (b+z))

end TamingCompatibility.HermitianRadial

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianShiftedSources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]

def shiftedLogSource (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (s : ℝ) (b z : E) : ℝ :=
  logSingularSource W a V s b (z-b)
def shiftedSqrtSource (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (s : ℝ) (b z : E) : ℝ :=
  sqrtSingularSource W a V s b (z-b)

def shiftedLogShell (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (r s : ℝ) (b z : E) : ℝ :=
  shellCutoff r (z-b) * shiftedLogSource W a V s b z
def shiftedSqrtShell (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (r s : ℝ) (b z : E) : ℝ :=
  shellCutoff r (z-b) * shiftedSqrtSource W a V s b z

def shiftedLogInner (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (s : ℝ) (b z : E) : ℝ :=
  scaledCutoff s (z-b) * shiftedLogSource W a V s b z
def shiftedSqrtInner (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (s : ℝ) (b z : E) : ℝ :=
  scaledCutoff s (z-b) * shiftedSqrtSource W a V s b z

omit [HasContDiffBump E] [ProperSpace E] in
lemma shiftedLogSource_smooth (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (shiftedLogSource W a V s b) := by
  have hd : ContDiff ℝ ∞ (fun z => fderiv ℝ (hermitianLogPotential (W b) s) (z-b) (V z)) :=
    (((hermitianLogPotential_smooth (W b) hs).fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp
      (contDiff_id.sub contDiff_const)).clm_apply hV
  have he : shiftedLogSource W a V s b =
      fun z => a (z-b) * fderiv ℝ (hermitianLogPotential (W b) s) (z-b) (V z) := by
    funext z
    simp [shiftedLogSource,logSingularSource,hermitianLogGradient_eq_fderiv (W b) hs]
  rw [he]
  exact (ha.comp (contDiff_id.sub contDiff_const)).mul hd

omit [HasContDiffBump E] [ProperSpace E] in
lemma shiftedSqrtSource_smooth (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (shiftedSqrtSource W a V s b) := by
  have hd : ContDiff ℝ ∞ (fun z => fderiv ℝ (hermitianSqrtPotential (W b) s) (z-b) (V z)) :=
    (((hermitianSqrtPotential_smooth (W b) hs).fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp
      (contDiff_id.sub contDiff_const)).clm_apply hV
  have he : shiftedSqrtSource W a V s b =
      fun z => a (z-b) * fderiv ℝ (hermitianSqrtPotential (W b) s) (z-b) (V z) := by
    funext z
    simp [shiftedSqrtSource,sqrtSingularSource,hermitianSqrtGradient_eq_fderiv (W b) hs]
  rw [he]
  exact (ha.comp (contDiff_id.sub contDiff_const)).mul hd

omit [ProperSpace E] in
lemma shiftedLogShell_smooth (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) (r : ℝ) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (shiftedLogShell W a V r s b) :=
  ((shellCutoff_smooth r).comp (contDiff_id.sub contDiff_const)).mul
    (shiftedLogSource_smooth W a V ha hV hs b)
omit [ProperSpace E] in
lemma shiftedSqrtShell_smooth (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) (r : ℝ) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (shiftedSqrtShell W a V r s b) :=
  ((shellCutoff_smooth r).comp (contDiff_id.sub contDiff_const)).mul
    (shiftedSqrtSource_smooth W a V ha hV hs b)
omit [ProperSpace E] in
lemma shiftedLogInner_smooth (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (shiftedLogInner W a V s b) :=
  ((scaledCutoff_smooth s).comp (contDiff_id.sub contDiff_const)).mul
    (shiftedLogSource_smooth W a V ha hV hs b)
omit [ProperSpace E] in
lemma shiftedSqrtInner_smooth (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (shiftedSqrtInner W a V s b) :=
  ((scaledCutoff_smooth s).comp (contDiff_id.sub contDiff_const)).mul
    (shiftedSqrtSource_smooth W a V ha hV hs b)

end TamingCompatibility.HermitianRadial

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_HermitianBundleSources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]

omit [ProperSpace E] in
lemma shiftedLogShell_support (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    {r : ℝ} (hr : 0 < r) (s : ℝ) (b : E) :
    tsupport (shiftedLogShell W a V r s b) ⊆ closedBall b (4*r) :=
  tsupport_translated_mul_subset _ b _ (fun _ hz => (shellCutoff_tsupport hr hz).1)
omit [ProperSpace E] in
lemma shiftedSqrtShell_support (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    {r : ℝ} (hr : 0 < r) (s : ℝ) (b : E) :
    tsupport (shiftedSqrtShell W a V r s b) ⊆ closedBall b (4*r) :=
  tsupport_translated_mul_subset _ b _ (fun _ hz => (shellCutoff_tsupport hr hz).1)
omit [ProperSpace E] in
lemma shiftedLogInner_support (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    {s : ℝ} (hs : 0 < s) (b : E) :
    tsupport (shiftedLogInner W a V s b) ⊆ closedBall b (2*s) :=
  tsupport_translated_mul_subset _ b _ (scaledCutoff_tsupport hs)
omit [ProperSpace E] in
lemma shiftedSqrtInner_support (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    {s : ℝ} (hs : 0 < s) (b : E) :
    tsupport (shiftedSqrtInner W a V s b) ⊆ closedBall b (2*s) :=
  tsupport_translated_mul_subset _ b _ (scaledCutoff_tsupport hs)

omit [HasContDiffBump E] [ProperSpace E] in
lemma shiftedLogSource_support (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (s : ℝ) (b : E)
    (R : ℝ) (ha : tsupport a ⊆ closedBall 0 R) :
    tsupport (shiftedLogSource W a V s b) ⊆ closedBall b R :=
  tsupport_translated_mul_subset _ b R ha
omit [HasContDiffBump E] [ProperSpace E] in
lemma shiftedSqrtSource_support (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (s : ℝ) (b : E)
    (R : ℝ) (ha : tsupport a ⊆ closedBall 0 R) :
    tsupport (shiftedSqrtSource W a V s b) ⊆ closedBall b R :=
  tsupport_translated_mul_subset _ b R ha

variable (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)

def logShellSchwartz {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedLogShell W a V r s b) :=
    (isCompact_closedBall b (4*r)).of_isClosed_subset (isClosed_tsupport _)
      (shiftedLogShell_support W a V hr s b)
  exact hc.toSchwartzMap (shiftedLogShell_smooth W a V ha hV r hs b)
def sqrtShellSchwartz {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedSqrtShell W a V r s b) :=
    (isCompact_closedBall b (4*r)).of_isClosed_subset (isClosed_tsupport _)
      (shiftedSqrtShell_support W a V hr s b)
  exact hc.toSchwartzMap (shiftedSqrtShell_smooth W a V ha hV r hs b)
def logInnerSchwartz {s : ℝ} (hs : 0 < s) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedLogInner W a V s b) :=
    (isCompact_closedBall b (2*s)).of_isClosed_subset (isClosed_tsupport _)
      (shiftedLogInner_support W a V hs b)
  exact hc.toSchwartzMap (shiftedLogInner_smooth W a V ha hV hs b)
def sqrtInnerSchwartz {s : ℝ} (hs : 0 < s) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedSqrtInner W a V s b) :=
    (isCompact_closedBall b (2*s)).of_isClosed_subset (isClosed_tsupport _)
      (shiftedSqrtInner_support W a V hs b)
  exact hc.toSchwartzMap (shiftedSqrtInner_smooth W a V ha hV hs b)

lemma logShellSchwartz_fixedSupport {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (b : E)
    (R : ℝ) (haR : tsupport a ⊆ closedBall 0 R) :
    tsupport (logShellSchwartz W a V ha hV hr hs b) ⊆ closedBall b R :=
  tsupport_mul_subset_right.trans (shiftedLogSource_support W a V s b R haR)

lemma logInnerSchwartz_fixedSupport {s : ℝ} (hs : 0 < s) (b : E)
    (R : ℝ) (haR : tsupport a ⊆ closedBall 0 R) :
    tsupport (logInnerSchwartz W a V ha hV hs b) ⊆ closedBall b R :=
  tsupport_mul_subset_right.trans (shiftedLogSource_support W a V s b R haR)

lemma sqrtShellSchwartz_fixedSupport {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (b : E)
    (R : ℝ) (haR : tsupport a ⊆ closedBall 0 R) :
    tsupport (sqrtShellSchwartz W a V ha hV hr hs b) ⊆ closedBall b R :=
  tsupport_mul_subset_right.trans (shiftedSqrtSource_support W a V s b R haR)

lemma sqrtInnerSchwartz_fixedSupport {s : ℝ} (hs : 0 < s) (b : E)
    (R : ℝ) (haR : tsupport a ⊆ closedBall 0 R) :
    tsupport (sqrtInnerSchwartz W a V ha hV hs b) ⊆ closedBall b R :=
  tsupport_mul_subset_right.trans (shiftedSqrtSource_support W a V s b R haR)

end TamingCompatibility.HermitianRadial

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_HermitianCutoffErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [HasContDiffBump E]

def cutoffLogError (W : E → E →L[ℝ] E) (V : E → E) (R : ℝ) (p : ℝ × E) (z : E) : ℝ :=
  hermitianLogPotential (W p.2) p.1 z * fderiv ℝ (scaledCutoff R) z (V (p.2+z))

def cutoffSqrtError (W : E → E →L[ℝ] E) (V : E → E) (R : ℝ) (p : ℝ × E) (z : E) : ℝ :=
  hermitianSqrtPotential (W p.2) p.1 z * fderiv ℝ (scaledCutoff R) z (V (p.2+z))

lemma cutoffLogError_smooth (W : E → E →L[ℝ] E) (V : E → E) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ ∞ (fun q : (ℝ × E) × E => cutoffLogError W V R q.1 q.2) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hz : q.2 = 0
  · have he : (fun q : (ℝ × E) × E => cutoffLogError W V R q.1 q.2) =ᶠ[𝓝 q] fun _ => 0 := by
      have hb : q.2 ∈ ball (0:E) R := by simp [hz,hR]
      filter_upwards [(continuous_snd.tendsto q).eventually (isOpen_ball.mem_nhds hb)] with p hp
      simp [cutoffLogError,fderiv_scaledCutoff_zero_inner hR (by simpa using hp)]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hpos : 0 < q.1.1^2 + ‖q.2‖^2 + ‖W q.1.2 q.2‖^2 := by
      have hn := norm_pos_iff.mpr hz
      nlinarith [sq_nonneg q.1.1,sq_nonneg ‖W q.1.2 q.2‖]
    have hden : ContDiff ℝ ∞ (fun q : (ℝ × E) × E => q.1.1^2 + ‖q.2‖^2 + ‖W q.1.2 q.2‖^2) :=
      ((contDiff_fst.fst.pow 2).add ((contDiff_norm_sq ℝ).comp contDiff_snd)).add
        ((contDiff_norm_sq ℝ).comp ((hW.comp contDiff_fst.snd).clm_apply contDiff_snd))
    have hl : ContDiffAt ℝ ∞ (fun q : (ℝ × E) × E => hermitianLogPotential (W q.1.2) q.1.1 q.2) q := by
      simp only [hermitianLogPotential,logPotential,hermitianGraph_norm_sq,← add_assoc]
      exact contDiffAt_const.mul (hden.contDiffAt.log hpos.ne')
    have hd : ContDiff ℝ ∞ (fun q : (ℝ × E) × E => fderiv ℝ (scaledCutoff R) q.2) :=
      ((scaledCutoff_smooth R).fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp contDiff_snd
    have hv : ContDiff ℝ ∞ (fun q : (ℝ × E) × E => V (q.1.2+q.2)) :=
      hV.comp (contDiff_fst.snd.add contDiff_snd)
    exact hl.mul (hd.clm_apply hv).contDiffAt

lemma cutoffSqrtError_smooth (W : E → E →L[ℝ] E) (V : E → E) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ ∞ (fun q : (ℝ × E) × E => cutoffSqrtError W V R q.1 q.2) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hz : q.2 = 0
  · have he : (fun q : (ℝ × E) × E => cutoffSqrtError W V R q.1 q.2) =ᶠ[𝓝 q] fun _ => 0 := by
      have hb : q.2 ∈ ball (0:E) R := by simp [hz,hR]
      filter_upwards [(continuous_snd.tendsto q).eventually (isOpen_ball.mem_nhds hb)] with p hp
      simp [cutoffSqrtError,fderiv_scaledCutoff_zero_inner hR (by simpa using hp)]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hpos : 0 < q.1.1^2 + ‖q.2‖^2 + ‖W q.1.2 q.2‖^2 := by
      have hn := norm_pos_iff.mpr hz
      nlinarith [sq_nonneg q.1.1,sq_nonneg ‖W q.1.2 q.2‖]
    have hden : ContDiff ℝ ∞ (fun q : (ℝ × E) × E => q.1.1^2 + ‖q.2‖^2 + ‖W q.1.2 q.2‖^2) :=
      ((contDiff_fst.fst.pow 2).add ((contDiff_norm_sq ℝ).comp contDiff_snd)).add
        ((contDiff_norm_sq ℝ).comp ((hW.comp contDiff_fst.snd).clm_apply contDiff_snd))
    have hl : ContDiffAt ℝ ∞ (fun q : (ℝ × E) × E => hermitianSqrtPotential (W q.1.2) q.1.1 q.2) q := by
      simp only [hermitianSqrtPotential,sqrtPotential,hermitianGraph_norm_sq,← add_assoc]
      exact hden.contDiffAt.sqrt hpos.ne'
    have hd : ContDiff ℝ ∞ (fun q : (ℝ × E) × E => fderiv ℝ (scaledCutoff R) q.2) :=
      ((scaledCutoff_smooth R).fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp contDiff_snd
    have hv : ContDiff ℝ ∞ (fun q : (ℝ × E) × E => V (q.1.2+q.2)) :=
      hV.comp (contDiff_fst.snd.add contDiff_snd)
    exact hl.mul (hd.clm_apply hv).contDiffAt

end TamingCompatibility.HermitianRadial

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_HermitianCutoffProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E]
variable (K : E →L[ℝ] E)

def cutoffLogPotential (R s : ℝ) (z : E) : ℝ :=
  scaledCutoff R z * hermitianLogPotential K s z

def cutoffSqrtPotential (R s : ℝ) (z : E) : ℝ :=
  scaledCutoff R z * hermitianSqrtPotential K s z

lemma cutoffLogPotential_smooth (R : ℝ) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (cutoffLogPotential K R s : E → ℝ) :=
  (scaledCutoff_smooth R).mul (hermitianLogPotential_smooth K hs)

lemma cutoffSqrtPotential_smooth (R : ℝ) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (cutoffSqrtPotential K R s : E → ℝ) :=
  (scaledCutoff_smooth R).mul (hermitianSqrtPotential_smooth K hs)

lemma cutoffLogPotential_tsupport {R : ℝ} (hR : 0 < R) (s : ℝ) :
    tsupport (cutoffLogPotential K R s : E → ℝ) ⊆ closedBall 0 (2*R) :=
  tsupport_mul_subset_left.trans (scaledCutoff_tsupport hR)

lemma cutoffSqrtPotential_tsupport {R : ℝ} (hR : 0 < R) (s : ℝ) :
    tsupport (cutoffSqrtPotential K R s : E → ℝ) ⊆ closedBall 0 (2*R) :=
  tsupport_mul_subset_left.trans (scaledCutoff_tsupport hR)

end TamingCompatibility.HermitianRadial

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianErrorSources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]

def shiftedLogError (W : E → E →L[ℝ] E) (V : E → E) (R s : ℝ) (b z : E) : ℝ :=
  cutoffLogError W V R (s,b) (z-b)
def shiftedSqrtError (W : E → E →L[ℝ] E) (V : E → E) (R s : ℝ) (b z : E) : ℝ :=
  cutoffSqrtError W V R (s,b) (z-b)

omit [ProperSpace E] in
lemma shiftedLogError_smooth (W : E → E →L[ℝ] E) (V : E → E) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    ContDiff ℝ ∞ (shiftedLogError W V R s b) :=
  (cutoffLogError_smooth W V hW hV hR).comp
    (contDiff_const.prodMk (contDiff_id.sub contDiff_const))
omit [ProperSpace E] in
lemma shiftedSqrtError_smooth (W : E → E →L[ℝ] E) (V : E → E) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    ContDiff ℝ ∞ (shiftedSqrtError W V R s b) :=
  (cutoffSqrtError_smooth W V hW hV hR).comp
    (contDiff_const.prodMk (contDiff_id.sub contDiff_const))

end TamingCompatibility.HermitianRadial

end
end

section

noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]
variable (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
  (R : ℝ) (haR : tsupport a ⊆ closedBall 0 R)

def logSourceSchwartz {s : ℝ} (hs : 0 < s) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedLogSource W a V s b) :=
    (isCompact_closedBall b R).of_isClosed_subset (isClosed_tsupport _)
      (shiftedLogSource_support W a V s b R haR)
  exact hc.toSchwartzMap (shiftedLogSource_smooth W a V ha hV hs b)

def sqrtSourceSchwartz {s : ℝ} (hs : 0 < s) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedSqrtSource W a V s b) :=
    (isCompact_closedBall b R).of_isClosed_subset (isClosed_tsupport _)
      (shiftedSqrtSource_support W a V s b R haR)
  exact hc.toSchwartzMap (shiftedSqrtSource_smooth W a V ha hV hs b)

end TamingCompatibility.HermitianRadial

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianSupportedSources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]
variable (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
  (R : ℝ) (haR : tsupport a ⊆ closedBall 0 R) (K : Set E)

def logShellSupported {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K) :
    supportedSchwartz K :=
  ⟨logShellSchwartz W a V ha hV hr hs b,(logShellSchwartz_fixedSupport W a V ha hV hr hs b R haR).trans hb⟩

def logInnerSupported {s : ℝ} (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K) :
    supportedSchwartz K :=
  ⟨logInnerSchwartz W a V ha hV hs b,(logInnerSchwartz_fixedSupport W a V ha hV hs b R haR).trans hb⟩

def logSourceSupported {s : ℝ} (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K) :
    supportedSchwartz K :=
  ⟨logSourceSchwartz W a V ha hV R haR hs b,(shiftedLogSource_support W a V s b R haR).trans hb⟩

def sqrtShellSupported {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K) :
    supportedSchwartz K :=
  ⟨sqrtShellSchwartz W a V ha hV hr hs b,(sqrtShellSchwartz_fixedSupport W a V ha hV hr hs b R haR).trans hb⟩

def sqrtInnerSupported {s : ℝ} (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K) :
    supportedSchwartz K :=
  ⟨sqrtInnerSchwartz W a V ha hV hs b,(sqrtInnerSchwartz_fixedSupport W a V ha hV hs b R haR).trans hb⟩

def sqrtSourceSupported {s : ℝ} (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K) :
    supportedSchwartz K :=
  ⟨sqrtSourceSchwartz W a V ha hV R haR hs b,(shiftedSqrtSource_support W a V s b R haR).trans hb⟩

end TamingCompatibility.HermitianRadial

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_HermitianCutoffSupported
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]
variable (W : E → E →L[ℝ] E)

def translatedCutoffLog (R s : ℝ) (b z : E) : ℝ := cutoffLogPotential (W b) R s (z-b)
def translatedCutoffSqrt (R s : ℝ) (b z : E) : ℝ := cutoffSqrtPotential (W b) R s (z-b)

omit [ProperSpace E] in
lemma translatedCutoffLog_smooth (R : ℝ) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (translatedCutoffLog W R s b) :=
  (cutoffLogPotential_smooth (W b) R hs).comp (contDiff_id.sub contDiff_const)
omit [ProperSpace E] in
lemma translatedCutoffSqrt_smooth (R : ℝ) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (translatedCutoffSqrt W R s b) :=
  (cutoffSqrtPotential_smooth (W b) R hs).comp (contDiff_id.sub contDiff_const)
omit [ProperSpace E] in
lemma translatedCutoffLog_support {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    tsupport (translatedCutoffLog W R s b) ⊆ closedBall b (2*R) :=
  tsupport_translated_subset b _ (cutoffLogPotential_tsupport (W b) hR s)
omit [ProperSpace E] in
lemma translatedCutoffSqrt_support {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    tsupport (translatedCutoffSqrt W R s b) ⊆ closedBall b (2*R) :=
  tsupport_translated_subset b _ (cutoffSqrtPotential_tsupport (W b) hR s)

lemma translatedCutoffLog_compact {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    HasCompactSupport (translatedCutoffLog W R s b) :=
  (isCompact_closedBall b (2*R)).of_isClosed_subset (isClosed_tsupport _)
    (translatedCutoffLog_support W hR s b)
lemma translatedCutoffSqrt_compact {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    HasCompactSupport (translatedCutoffSqrt W R s b) :=
  (isCompact_closedBall b (2*R)).of_isClosed_subset (isClosed_tsupport _)
    (translatedCutoffSqrt_support W hR s b)

end TamingCompatibility.HermitianRadial

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_SlowLogCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology
namespace TamingCompatibility.SummableCutoff

def logActivation (ε δ t : ℝ) : ℝ := ε * Real.log (1+t/δ)

end TamingCompatibility.SummableCutoff

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_SummableCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter _root_.MeasureTheory Finset
open scoped Topology ENNReal
namespace TamingCompatibility.SummableCutoff
variable {X : Type*}

def saturation (c : ℕ → X → ℝ) (n N : ℕ) (x : X) : ℝ :=
  1 - Real.exp (-(∑ k ∈ Finset.range N, c (k+n) x))

def tailLimit (c : ℕ → X → ℝ) (n : ℕ) (x : X) : ℝ := by
  classical
  exact if Summable (fun k => c k x) then
    1 - Real.exp (-(∑' k, c (k+n) x)) else 1

end TamingCompatibility.SummableCutoff

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_RadialDefect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter ContinuousAlternatingMap
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def hermitianDefect (K : E →L[ℝ] E) (z v : E) : ℝ :=
  ‖hermitianGraph K z‖^2 * ‖hermitianGraph K v‖^2 -
    ⟪hermitianGraph K z,hermitianGraph K v⟫^2 -
    ⟪hermitianGraph K z,hermitianGraph K (K v)⟫^2

end TamingCompatibility.RadialPotential

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_NormalChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalJets
open scoped RealInnerProductSpace ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions : NormedAddCommGroup (V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions : NormedSpace ℝ (V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

end TamingCompatibility.GeometricHilbert.NormalJets

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Dpos2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.UniformJets

section FiniteDimensionalDirections
open Set Metric Filter
open scoped ContDiff Topology
variable {P V W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [FiniteDimensional ℝ V] [NormedSpace ℝ P] [NormedSpace ℝ V] in
lemma compact_tube (K : Set P) (hK : IsCompact K) (O : Set (P × V)) (hO : IsOpen O)
    (hKO : K ×ˢ {(0 : V)} ⊆ O) :
    ∃ r : ℝ, 0 < r ∧ K ×ˢ closedBall (0 : V) r ⊆ O := by
  obtain ⟨r,hr,hsub⟩ := (hK.prod isCompact_singleton).exists_cthickening_subset_open hO hKO
  refine ⟨r,hr,?_⟩
  rintro ⟨p,z⟩ ⟨hp,hz⟩
  apply hsub
  apply mem_cthickening_of_dist_le (p,z) (p,0) r (K ×ˢ {(0 : V)}) ⟨hp,rfl⟩
  simpa [Prod.dist_eq] using hz

end FiniteDimensionalDirections
open Filter
open scoped ContDiff Topology
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

end TamingCompatibility.GeometricHilbert.UniformJets

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RationalKernelCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.PlaneVariation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def skew (a b w : V) : V := ⟪b,w⟫ • a - ⟪a,w⟫ • b

def transverse (u v z : V) : V := z - ⟪u,z⟫ • u - ⟪v,z⟫ • v

def detInner (u v a b : V) : ℝ := ⟪u,a⟫*⟪v,b⟫-⟪u,b⟫*⟪v,a⟫

end TamingCompatibility.PlaneVariation

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SmoothingKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertKernel
open _root_.MeasureTheory
open scoped RealInnerProductSpace
variable {H F G A B : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

def kernel (E : A → H →L[ℝ] F) (D : B → H →L[ℝ] G) (x : A) (y : B) : G →L[ℝ] F :=
  (E x).comp (D y).adjoint

def regularize [MeasurableSpace A] (μ : Measure A)
    (E : A → H →L[ℝ] F) (v : A → F) : H := ∫ x, (E x).adjoint (v x) ∂μ

end TamingCompatibility.HilbertKernel

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_OperatorCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open scoped ContDiff
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

def differential (e : ι → V) (a : ι → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (u : V → W) (x : V) : Q := ∑ i, a i x (fderiv ℝ u x (e i)) + b x (u x)

def weightedAdjoint (e : ι → V) (a : ι → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (ρ : V → ℝ) (v : V → Q) (x : V) : W :=
  -(ρ x)⁻¹ • (∑ i, fderiv ℝ (fun y => (ρ y • a i y).adjoint (v y)) x (e i)) +
    (b x).adjoint (v x)

def secondOrder (e : ι → V) (a : ι → ι → V → ℝ)
    (b : ι → V → W →L[ℝ] W) (c : V → W →L[ℝ] W) (u : V → W) (x : V) : W :=
  -(∑ i, ∑ j, a i j x • fderiv ℝ (fun y => fderiv ℝ u y (e j)) x (e i)) +
    (∑ i, b i x (fderiv ℝ u x (e i))) + c x (u x)

end TamingCompatibility.GeometricHilbert.OperatorCalculus


end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_RealSobolevLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution Set
open scoped SchwartzMap ENNReal LineDeriv Topology BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma schwartz_bessel_surjective (s : ℝ) : Function.Surjective
    (SchwartzMap.fourierMultiplierCLM F (fun x : E => (((1+‖x‖^2)^(s/2) : ℝ) : ℂ))) := by
  intro f
  refine ⟨SchwartzMap.fourierMultiplierCLM F (fun x : E => (((1+‖x‖^2)^(-s/2) : ℝ) : ℂ)) f,?_⟩
  rw [SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  have he : ((fun x : E => (((1+‖x‖^2)^(s/2) : ℝ) : ℂ)) *
      (fun x : E => (((1+‖x‖^2)^(-s/2) : ℝ) : ℂ))) = fun _ => (1:ℂ) := by
    ext x
    simp only [Pi.mul_apply,← Complex.ofReal_mul]
    rw [← Real.rpow_add (by positivity)]
    have hz : s/2 + -s/2 = 0 := by ring
    rw [hz,Real.rpow_zero,Complex.ofReal_one]
  rw [he,SchwartzMap.fourierMultiplierCLM_const]
  simp

omit [CompleteSpace F] in
lemma schwartzLp_dense : DenseRange (fun f : 𝓢(E,F) => f.toLp 2 (volume : Measure E)) :=
  SchwartzMap.denseRange_toLpCLM (E := E) (F := F)
    (μ := (volume : Measure E)) (p := 2) (by norm_num)

end TamingCompatibility.HilbertSobolev

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeScalarJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeScalar
open _root_.MeasureTheory LineDeriv ManifoldLocalization
open scoped SchwartzMap LineDeriv ContDiff
abbrev F := EuclideanSpace ℂ (Fin 6)
def inject (j : Fin 6) : ℝ →L[ℝ] F :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 6 => ℂ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℝ (fun _ : Fin 6 => ℂ) j ∘L Complex.ofRealCLM
lemma inject_apply (j i : Fin 6) (s : ℝ) : inject j s i = if i=j then (s : ℂ) else 0 := by
  simp [inject]
end TamingCompatibility.HodgeScalar

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeSpectralHeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (J : AlmostComplexStructure X)
  (α : TwoForm X)
  (hs : IsSmooth α)
  (ht : Tames α J)

def hodgeSpectralRate (x : ℝ) : ℝ := max 0 (x⁻¹-1)

def hodgeHeatMultiplier (t x : ℝ) : ℝ := Real.exp (-(max t 0) * hodgeSpectralRate x)

lemma hodgeHeatMultiplier_pos (t x : ℝ) : 0 < hodgeHeatMultiplier t x := Real.exp_pos _
lemma hodgeHeatMultiplier_le_one (t x : ℝ) : hodgeHeatMultiplier t x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_max_right _ _)) (le_max_left _ _)

end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldLocalization Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (J : AlmostComplexStructure X)
  (α : TwoForm X)
  (hs : IsSmooth α)
  (ht : Tames α J)

lemma hodgeHeatMultiplier_continuous (x : ℝ) : Continuous (fun t => hodgeHeatMultiplier t x) := by
  exact ((continuous_id.max continuous_const).neg.mul continuous_const).rexp

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeHeatSmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldLocalization Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (J : AlmostComplexStructure X)
  (α : TwoForm X)
  (hs : IsSmooth α)
  (ht : Tames α J)

lemma heat_boost_bound (y : ℝ) (hy : 0 ≤ y) :
    |(1+y)^3 * Real.exp (-y)| ≤ 6 * Real.exp 1 := by
  have hp : 0 ≤ 1+y := by linarith
  have he := Real.pow_div_factorial_le_exp (1+y) hp 3
  norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at he
  have he' : (1+y)^3 ≤ 6 * Real.exp (1+y) := by linarith
  rw [abs_of_nonneg (mul_nonneg (pow_nonneg hp _) (Real.exp_pos _).le)]
  calc
    _ ≤ (6 * Real.exp (1+y)) * Real.exp (-y) :=
      mul_le_mul_of_nonneg_right he' (Real.exp_pos _).le
    _ = 6 * Real.exp 1 := by rw [mul_assoc, ← Real.exp_add]; ring_nf

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeHeatIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldLocalization Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (J : AlmostComplexStructure X)
  (α : TwoForm X)
  (hs : IsSmooth α)
  (ht : Tames α J)

def unitSymbol (x : ℝ) : ℝ := min 1 (max 0 x)
lemma unitSymbol_bound (x : ℝ) : |unitSymbol x| ≤ 1 := by
  rw [abs_of_nonneg (le_min zero_le_one (le_max_left _ _))]
  exact min_le_left _ _

end TamingCompatibility.GeometricHilbert
end

end
end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_ResolventGammaScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldLocalization _root_.MeasureTheory Set
open scoped Manifold ContDiff RealInnerProductSpace

def hodgeGammaWeight (s : ℝ) : ℝ := Real.exp (-s) * s^5

lemma hodgeGammaWeight_continuous : Continuous hodgeGammaWeight :=
  continuous_id.neg.rexp.mul (continuous_id.pow 5)

lemma hodgeGammaWeight_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ hodgeGammaWeight s := by
  exact mul_nonneg (Real.exp_pos _).le (pow_nonneg hs _)

lemma hodgeGammaWeight_integrable : IntegrableOn hodgeGammaWeight (Ioi 0) := by
  convert Real.GammaIntegral_convergent (s := 6) (by norm_num) using 1
  all_goals try with_reducible_and_instances rfl
  funext s
  simp only [hodgeGammaWeight, show (6:ℝ)-1 = 5 by norm_num, Real.rpow_ofNat]

lemma hodgeGammaWeight_laplace (r z : ℝ) (hz : 0 ≤ z) :
    ∫ s : ℝ in Ioi 0, hodgeGammaWeight s * Real.exp (-(r^2*s)*z) =
      120 * (1/(1+r^2*z))^6 := by
  have hp : 0 < 1+r^2*z := by positivity
  have hg : Real.Gamma 6 = 120 := by norm_num
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a:=6) (r:=1+r^2*z) (by norm_num) hp
  have he : (fun s : ℝ => hodgeGammaWeight s * Real.exp (-(r^2*s)*z)) =
      (fun s : ℝ => s^(5:ℕ) * Real.exp (-((1+r^2*z)*s))) := by
    funext s
    unfold hodgeGammaWeight
    rw [mul_comm (Real.exp (-s)) (s^5), mul_assoc, ← Real.exp_add]
    congr 1
    ring_nf
  rw [he]
  norm_num only [show (6:ℝ)-1 = 5 by norm_num, Real.rpow_ofNat, hg] at h
  exact h.trans (mul_comm _ _)

lemma hodgeGammaWeight_integral : ∫ s : ℝ in Ioi 0, hodgeGammaWeight s = 120 := by
  simpa only [mul_zero, Real.exp_zero, mul_one, add_zero, div_one, one_pow] using
    hodgeGammaWeight_laplace 0 0 le_rfl

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeKernelGammaBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.HodgeKernelBounds
open _root_.MeasureTheory Set

def rapidConstant (c : ℝ) (N : ℕ) : ℝ :=
  (N.factorial : ℝ) * Real.exp c / c^N

def moment (n : ℕ) (b : ℝ) : ℝ := (1/b)^(n+1) * (n.factorial : ℝ)

def profile (n : ℕ) (c a s : ℝ) : ℝ :=
  Real.exp (-s) * s^n * Real.exp (-c*a^2/s)

def truncatedProfile (n : ℕ) (c a T : ℝ) : ℝ :=
  ∫ s : ℝ in Ioc 0 T, profile n c a s

def leading (r t₀ d : ℝ) : ℝ :=
  (1 / (120*(4*Real.pi)^2)) * (r⁻¹)^4 *
    truncatedProfile 3 (1/4) (d/r) (t₀/r^2)

def leadingConstant (N : ℕ) : ℝ :=
  (1 / (120*(4*Real.pi)^2)) * moment 3 (1/2) * rapidConstant (1/2) N

def gammaTail (T : ℝ) : ℝ := ∫ s : ℝ in Ioi T, Real.exp (-s) * s^5

end TamingCompatibility.GeometricHilbert.HodgeKernelBounds

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeVolterraKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.VolterraBounds
open _root_.MeasureTheory Set Metric
open scoped Topology
variable {X B : Type*} [PseudoMetricSpace X]

def weight (N : ℕ) (t : ℝ) (x y : X) : ℝ := (1 + dist x y / Real.sqrt t)^N

end TamingCompatibility.GeometricHilbert.VolterraBounds

end
end

end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGammaSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.HodgeKernelBounds
open Set _root_.MeasureTheory

variable {X : Type*} [PseudoMetricSpace X]

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

def gammaKernel (K : ℝ → X → X → B) (T r : ℝ) (x y : X) : B :=
  (1/120 : ℝ) • ∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s • K (r^2*s) x y

end TamingCompatibility.GeometricHilbert.HodgeKernelBounds

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeManifoldKernelExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.ManifoldKernelExtension
open Set Filter
open scoped Manifold Topology
variable {E X G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace E X]
  [NormedAddCommGroup G]
attribute [local instance] Classical.propDecidable
local notation "I" => 𝓘(ℝ,E)

def liftSet (p : X) (K : Set (E × E)) : Set (X × X) :=
  (fun z : E × E => ((extChartAt I p).symm z.1,(extChartAt I p).symm z.2)) '' K

end TamingCompatibility.ManifoldKernelExtension

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGammaLinearTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open _root_.MeasureTheory
variable {ι E F : Type*} [MeasurableSpace ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
namespace TamingCompatibility.KernelTransfer

def sandwich (L : E →L[ℝ] F) (R : F →L[ℝ] E) :
    (E →L[ℝ] E) →L[ℝ] (F →L[ℝ] F) :=
  (ContinuousLinearMap.compL ℝ F E F).flip R ∘L
    (ContinuousLinearMap.compL ℝ E E F L)

end TamingCompatibility.KernelTransfer

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGeometricDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.RiemannianChartDistance
open Bundle Manifold Set Metric _root_.MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ,E) 1 X]
  [RiemannianBundle (fun x : X => TangentSpace 𝓘(ℝ,E) x)]
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
  ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

local instance inverseChartNormedAddCommGroup (z : E) (x : X) :
    NormedAddCommGroup (TangentSpace 𝓘(ℝ,E) z →L[ℝ] TangentSpace 𝓘(ℝ,E) x) :=
  ContinuousLinearMap.toNormedAddCommGroup

end TamingCompatibility.RiemannianChartDistance

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeKernelAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.KernelL2
open Set Filter _root_.MeasureTheory
open scoped Topology
variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]
variable (μ : Measure X) [IsFiniteMeasure μ]

def action (K : X → X → F →L[ℝ] F) (v : X → F) (x : X) : F := ∫ y, K x y (v y) ∂μ

omit [CompleteSpace F] in
lemma applied_measurable (K : X → X → F →L[ℝ] F)
    (hK : StronglyMeasurable (Function.uncurry K)) (v : X → F) (hv : StronglyMeasurable v) :
    StronglyMeasurable (fun p : X × X => K p.1 p.2 (v p.2)) :=
  (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
    (hK.prodMk (hv.comp_measurable measurable_snd))

omit [CompleteSpace F] in
lemma action_measurable (K : X → X → F →L[ℝ] F)
    (hK : StronglyMeasurable (Function.uncurry K)) (v : X → F) (hv : StronglyMeasurable v) :
    StronglyMeasurable (action μ K v) := (applied_measurable K hK v hv).integral_prod_right

omit [CompleteSpace F] [IsFiniteMeasure μ] in
lemma action_norm (K : X → X → F →L[ℝ] F) (v : X → F) {V H : ℝ} (hV : 0 ≤ V)
    (hv : ∀ y, ‖v y‖ ≤ V) (x : X) (hKi : Integrable (fun y => ‖K x y‖) μ)
    (hKb : (∫ y, ‖K x y‖ ∂μ) ≤ H) : ‖action μ K v x‖ ≤ H*V := by
  calc
    _ ≤ ∫ y, ‖K x y‖*V ∂μ := by
      apply norm_integral_le_of_norm_le (hKi.mul_const _) (Eventually.of_forall _)
      intro y
      exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left (hv y) (norm_nonneg _))
    _ = (∫ y, ‖K x y‖ ∂μ)*V := integral_mul_const _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hKb hV

end TamingCompatibility.GeometricHilbert.KernelL2

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeL2Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open _root_.MeasureTheory
open scoped RealInnerProductSpace
namespace TamingCompatibility.GeometricHilbert
variable {V E X : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace X]
  {μ : Measure X}

def lpEncode (φ : V →ₗ[ℝ] (X → E)) (hm : ∀ v, MemLp (φ v) 2 μ) :
    V →ₗ[ℝ] Lp E 2 μ where
  toFun v := (hm v).toLp (φ v)
  map_add' v w := by
    apply Lp.ext
    filter_upwards [(hm (v+w)).coeFn_toLp,(hm v).coeFn_toLp,(hm w).coeFn_toLp,
      Lp.coeFn_add ((hm v).toLp (φ v)) ((hm w).toLp (φ w))] with x hx hv hw ha
    rw [hx,ha,Pi.add_apply,hv,hw]
    exact congrFun (φ.map_add v w) x
  map_smul' c v := by
    apply Lp.ext
    filter_upwards [(hm (c • v)).coeFn_toLp,(hm v).coeFn_toLp,
      Lp.coeFn_smul c ((hm v).toLp (φ v))] with x hx hv ha
    simp only [RingHom.id_apply] at *
    rw [hx,ha,Pi.smul_apply,hv]
    exact congrFun (φ.map_smul c v) x

lemma lpEncode_inner (φ : V →ₗ[ℝ] (X → E)) (hm : ∀ v, MemLp (φ v) 2 μ)
    (v w : V) :
    ⟪lpEncode φ hm v,lpEncode φ hm w⟫ = ∫ x, ⟪φ v x,φ w x⟫ ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hm v).coeFn_toLp,(hm w).coeFn_toLp] with x hv hw
  change ⟪(hm v).toLp (φ v) x,(hm w).toLp (φ w) x⟫ = _
  rw [hv,hw]

def lpEncodeIsometry (φ : V →ₗ[ℝ] (X → E)) (hm : ∀ v, MemLp (φ v) 2 μ)
    (hi : ∀ v w, (∫ x, ⟪φ v x,φ w x⟫ ∂μ) = ⟪v,w⟫) : V →ₗᵢ[ℝ] Lp E 2 μ where
  __ := lpEncode φ hm
  norm_map' v := by
    have h : ‖lpEncode φ hm v‖^2 = ‖v‖^2 := by
      rw [← real_inner_self_eq_norm_sq,lpEncode_inner,hi,real_inner_self_eq_norm_sq]
    nlinarith [norm_nonneg (lpEncode φ hm v),norm_nonneg v]

variable [CompleteSpace E]
def isometryFromCompletion (f : V →ₗᵢ[ℝ] E) : UniformSpace.Completion V →ₗᵢ[ℝ] E where
  __ := f.toContinuousLinearMap.fromCompletion.toLinearMap
  norm_map' v := by
    induction v using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (f.toContinuousLinearMap.fromCompletion.continuous.norm) continuous_norm
    | ih v =>
      change ‖f.toContinuousLinearMap.fromCompletion (v : UniformSpace.Completion V)‖ = _
      rw [ContinuousLinearMap.fromCompletion_apply_coe,UniformSpace.Completion.norm_coe]
      exact f.norm_map v

end TamingCompatibility.GeometricHilbert

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeLocalCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility
lemma bounded_triple_composition {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : G →L[ℝ] H) (N : F →L[ℝ] G) (L : E →L[ℝ] F) (B t : ℝ)
    (h : ∀ v, ‖L v‖ ≤ B*t*‖v‖) (v : E) :
    ‖(P.comp (N.comp L)) v‖ ≤ ‖P‖*‖N‖*B*t*‖v‖ := by
  calc
    _ ≤ ‖P‖*‖N (L v)‖ := P.le_opNorm _
    _ ≤ ‖P‖*(‖N‖*‖L v‖) := mul_le_mul_of_nonneg_left (N.le_opNorm _) (norm_nonneg _)
    _ ≤ ‖P‖*(‖N‖*(B*t*‖v‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h v) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring
end TamingCompatibility

end
end

end
end

end OAI
end


