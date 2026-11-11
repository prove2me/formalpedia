-- Prove2me | Definitions.Def_OAIQ241TT002
-- name    : OAIQ241TT002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:47:32.474096+00:00
-- url     : https://prove2.me/theorems/11a1162c-5a58-41b8-be7e-ec60286f90d5
-- title:
--   Definitions bundle OAIQ241TT002 of the split of OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 650 declarations of OpenAI's Lean: 531 definitions, 17 inductive types or structures, 16 instances and 86 theorems. The definitions and types are `OAI.AlgorithmicThinTrees.GraphicHalf.countError`, `OAI.AlgorithmicThinTrees.GraphicHalf.nextCount`, `OAI.AlgorithmicThinTrees.InputStack.B`, `OAI.AlgorithmicThinTrees.InputStack.E`, `OAI.AlgorithmicThinTrees.InputStack.Good`, `OAI.AlgorithmicThinTrees.InputStack.Large`, `OAI.AlgorithmicThinTrees.InputStack.bFields`, `OAI.AlgorithmicThinTrees.Iteration.initialCount`, `OAI.AlgorithmicThinTrees.Iteration.lossB`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedBag`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedBag.InteriorMove`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedBag.SameOwnerSeparated`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedBag.input`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedBag.neighbor`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedBag.weaken`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedFamily`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedFamily.BoundaryRatio`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedFamily.ProtectedFrom`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedFamily.badCenters`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedFamily.badCount`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedFamily.boundaryCount`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedFamily.goodCenters`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedFamily.mass`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedFamily.owners`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedFamily.predecessors`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedFamily.weaken`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedSequence.Family`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedSequence.Fresh`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedSequence.Geometric`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedSequence.GeometricAt`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedSequence.Ratios`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedSequence.Ready`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedSequence.initialRadius`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedSequence.mass`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.CapturedFamily`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.CapturedFamily.Ratio`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.CapturedFamily.mass`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.CapturedFamily.owners`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.CapturedFamily.radius`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.CapturedFamily.upper` and 508 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `MatrixSigning_Arithmetic_Alpha`, `MatrixSigning_Arithmetic_Alpha2`, `MatrixSigning_Arithmetic_Kappa₁`, `MatrixSigning_Arithmetic_ScalarPsi`, `MatrixSigning_Calculus_JetBound`, `MatrixSigning_Calculus_NormSmulRightId`, `MatrixSigning_Complexity_BitSupport`, `MatrixSigning_Complexity_GlobalCounts`, `MatrixSigning_Complexity_PolynomialMatrixFold`, `MatrixSigning_Complexity_RationalGridBits`, `MatrixSigning_Complexity_StoredBits`, `MatrixSigning_Encoding_BinaryEncoding`, `MatrixSigning_Encoding_FlattenLookup`, `MatrixSigning_Machines_ComplexBridge`, `MatrixSigning_Machines_Realification`, `MatrixSigning_Machines_RealificationSPD`, `MatrixSigning_Matrices_DerivInvHPath`, `MatrixSigning_Matrices_FDerivTightPart`, `MatrixSigning_Matrices_FinPivot`, `MatrixSigning_Matrices_HermitianMat`, `MatrixSigning_Matrices_InnerRight`, `MatrixSigning_Matrices_InvH`, `MatrixSigning_Matrices_JetBoundTightPart`, `MatrixSigning_Matrices_JordanCLM`, `MatrixSigning_Matrices_OperatorNorm`, `MatrixSigning_Matrices_PSDSeparation`, `MatrixSigning_Matrices_Pivot`, `MatrixSigning_Matrices_RealTrace`, `MatrixSigning_Matrices_RetractH`, `MatrixSigning_Matrices_Sandwich`, `MatrixSigning_Matrices_SandwichCLM`, `MatrixSigning_Matrices_Space`, `MatrixSigning_Matrices_TraceCLM`, `MatrixSigning_Model`, `MatrixSigning_Optimization_Affine`, `MatrixSigning_Optimization_ComplexValueProgram`, `MatrixSigning_Optimization_FinRealify`, `MatrixSigning_Optimization_ObjectiveCLM`, `MatrixSigning_Optimization_RationalAtoms`, `MatrixSigning_Optimization_RealVector`, `MatrixSigning_Optimization_ShiftedHessian`, `MatrixSigning_Optimization_SqSum`, `MatrixSigning_Optimization_Transition`, `MatrixSigning_Optimization_Variables`, `MatrixSigning_Potential_CoarseBudget`, `MatrixSigning_Potential_Column`, `MatrixSigning_Potential_Coordinates`, `MatrixSigning_Potential_CovarianceE`, `MatrixSigning_Potential_DerivPathObjective`, `MatrixSigning_Potential_DiagBlock`, `MatrixSigning_Potential_Drift`, `MatrixSigning_Potential_Energy`, `MatrixSigning_Potential_EnergyMatrix`, `MatrixSigning_Potential_EuclideanForget`, `MatrixSigning_Potential_FacePotential`, `MatrixSigning_Potential_FaceValueDirectionVariations`, `MatrixSigning_Potential_Hessian`, `MatrixSigning_Potential_Interaction`, `MatrixSigning_Potential_JetBoundProjection`, `MatrixSigning_Potential_Lagrangian`, `MatrixSigning_Potential_LightPoint`, `MatrixSigning_Potential_Line`, `MatrixSigning_Potential_MovementMat`, `MatrixSigning_Potential_NegativeWeight`, `MatrixSigning_Potential_NormCoordinate`, `MatrixSigning_Potential_Normalizer`, `MatrixSigning_Potential_ObjectiveVarsCLM`, `MatrixSigning_Potential_Pack`, `MatrixSigning_Potential_Pair`, `MatrixSigning_Potential_PairCone`, `MatrixSigning_Potential_PairHilbert`, `MatrixSigning_Potential_PairIndex`, `MatrixSigning_Potential_PairVec`, `MatrixSigning_Potential_ParameterCube`, `MatrixSigning_Potential_Parameters`, `MatrixSigning_Potential_Point`, `MatrixSigning_Potential_Potential`, `MatrixSigning_Potential_QuadGram`, `MatrixSigning_Potential_RationalBasis`, `MatrixSigning_Potential_ResponseMatrix`, `MatrixSigning_Potential_SchurBlock`, `MatrixSigning_Potential_StateIA`, `MatrixSigning_Potential_StatePsi`, `MatrixSigning_Potential_StateR`, `MatrixSigning_Potential_StrictEpigraph`, `MatrixSigning_Potential_SymmetricMap`, `MatrixSigning_Potential_TightSystem`, `MatrixSigning_Potential_Value`, `MatrixSigning_Potential_ValueFeasible`, `MatrixSigning_Potential_VarianceH`, `MatrixSigning_Potential_Vars`, `MatrixSigning_Potential_WhitenWeighted`, `MatrixSigning_Realization_CurvatureRealization`, `MatrixSigning_Realization_FaceArrayRealization`, `MatrixSigning_Realization_FaceQueryRealization`, `MatrixSigning_Realization_MatrixStructureRealization`, `MatrixSigning_Realization_PotentialRealization`, `MatrixSigning_Realization_StencilRealization`, `MatrixSigning_Realization_ValueDataRealization`, `MatrixSigning_Realization_ValueEvalRealization`, `MatrixSigning_Realization_ValueQueryRealization`, `ThinTrees_Arithmetic_ScalarRealization`, `ThinTrees_BasePacking`, `ThinTrees_ChainEdges`, `ThinTrees_Coarea`, `ThinTrees_Continuation_Domain`, `ThinTrees_Continuation_Gains`, `ThinTrees_Continuation_PartitionGeometry`, `ThinTrees_Continuation_PartitionLattice`, `ThinTrees_Continuation_PartitionLocalConnectivity`, `ThinTrees_Continuation_PartitionUncrossing`, `ThinTrees_Continuation_Ramp`, `ThinTrees_Duality`, `ThinTrees_DyadicSelection`, `ThinTrees_Encoding_InputArrays`, `ThinTrees_Encoding_InputDispatch`, `ThinTrees_Encoding_OrderedGraph`, `ThinTrees_Encoding_SelectionRealization`, `ThinTrees_Flow_ParallelCopies`, `ThinTrees_GraphMatrix`, `ThinTrees_Hierarchy`, `ThinTrees_HierarchyBounds`, `ThinTrees_HierarchyBuilder`, `ThinTrees_Matrix`, `ThinTrees_MatrixDomain`, `ThinTrees_Metric_AssignedCharging`, `ThinTrees_Metric_CompactCharging`, `ThinTrees_Metric_CompactDuality`, `ThinTrees_Metric_ConeRepresentation`, `ThinTrees_Metric_ConicDuality`, `ThinTrees_Metric_MatrixBound`, `ThinTrees_Metric_Profiles`, `ThinTrees_Metric_ScaleCharging`, `ThinTrees_Metric_ShellCharging`, `ThinTrees_Metric_SpectralMetricBridge`, `ThinTrees_Normalization_Algorithm`, `ThinTrees_Normalization_Descent`, `ThinTrees_Normalization_Packing`, `ThinTrees_PartitionRank`, `ThinTrees_Records`, `ThinTrees_Representation`, `ThinTrees_ResponseBounds`, `ThinTrees_Restriction`, `ThinTrees_Selection`, `ThinTrees_ShortcutDuality`, `ThinTrees_Signing_RationalSigning`, `ThinTrees_Signing_RealMatrixBridge`, `ThinTrees_Signing_StackedSigning`, `ThinTrees_Sparsification_GraphicNormalization`, `ThinTrees_Sparsification_HalfNumeric`, `ThinTrees_Sparsification_IterationPotential`, `ThinTrees_Sparsification_IterationRealization`, `ThinTrees_Sparsification_RationalIteration`, `ThinTrees_SpectralPacking`, `ThinTrees_Truncation`.
--
--   **Imports.** It imports the published bundle `Def_AlgorithmicThinTrees`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ241TT006`; the statements `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedSequence.ordered_bound`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.capturePackage`, `OAI.CurrentKS.Interaction.state_energy_ensemble`, `OAI.CurrentKS.RationalFace.normalizedRun_spec`, `OAI.CurrentKS.RationalFace.transition_spec`, `OAI.CurrentKS.State.LightPoint.Psi_driftCurvature`, `OAI.CurrentKS.State.LightPoint.computed_candidates_progress`, `OAI.CurrentKS.State.LightPoint.covariance_movement_bounds`, `OAI.CurrentKS.State.LightPoint.exists_descent_ensemble`, `OAI.CurrentKS.State.LightPoint.shifted_hessian_not_psd`, `OAI.CurrentKS.State.etaTheta_minimizer`, `OAI.CurrentKS.State.face_value_direction_variations`, `OAI.CurrentKS.State.value_strip_derivatives`, `OAI.CurrentKS.Variational.exists_smooth_kkt_branch`, `OAI.CurrentKS.Variational.kkt` and `OAI.CurrentKS.Variational.value_derivatives_majorant`; the proofs of `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedSequence.ordered_bound`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.capturePackage`, `OAI.CurrentKS.Interaction.state_energy_ensemble`, `OAI.CurrentKS.State.LightPoint.covariance_movement_bounds`, `OAI.CurrentKS.State.LightPoint.exists_descent_ensemble`, `OAI.CurrentKS.State.etaTheta_minimizer` and `OAI.CurrentKS.Variational.kkt`.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_AlgorithmicThinTrees

section
-- module Solutions.OAIQ241_TT.Compat
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_ScalarPsi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Scalar
noncomputable section
open scoped ContDiff

def psi (x : ℝ) : ℝ := (1-x^2) ^ (1/3 : ℝ)
def psi₁ (x : ℝ) : ℝ := -2*x / (3*psi x^2)
def kappa (x : ℝ) : ℝ := 2*(3+x^2) / (9*psi x^5)

end
end CurrentKS.Scalar

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_Alpha
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Scalar
noncomputable section

def alpha (x _A B : ℝ) : ℝ := 1 - 2*x*B/(3*(1-x^2))
def beta (x A _B : ℝ) : ℝ := 1 + 2*x*A/(3*(1-x^2))

end
end CurrentKS.Scalar

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_Alpha2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Scalar
noncomputable section

def Alpha (c x a b : ℝ) : ℝ := alpha x (c*psi x*a) (c*psi x*b)
def Beta (c x a b : ℝ) : ℝ := beta x (c*psi x*a) (c*psi x*b)
def scaleT (c x a b : ℝ) : ℝ := Real.sqrt (Alpha c x a b*Beta c x a b/psi x)
def scaleL (c x a b : ℝ) : ℝ := Alpha c x a b/scaleT c x a b
def scaleM (c x a b : ℝ) : ℝ := Beta c x a b/scaleT c x a b

end
end CurrentKS.Scalar

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_Kappa₁
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Scalar
noncomputable section
open scoped ContDiff

def kappa₁ (x : ℝ) : ℝ :=
  4*x/(9*psi x^5)+20*x*(3+x^2)/(27*psi x^8)

end
end CurrentKS.Scalar

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Calculus_JetBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Calculus
noncomputable section
open Set

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

def JetBound (f : E → F) (x : E) (B : ℝ) : Prop :=
  ∀ n : ℕ, n ≤ 3 → ‖iteratedFDeriv ℝ n f x‖ ≤ B

end
end CurrentKS.Calculus

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Calculus_NormSmulRightId
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Calculus
noncomputable section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions : NormedAddCommGroup (G →L[ℝ] F) := inferInstance
local instance instNormedSpaceRealContinuousLinearMapId_solutions : NormedSpace ℝ (G →L[ℝ] F) := inferInstance
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_1_r914c68_1 : NormedAddCommGroup ((G →L[ℝ] F) →L[ℝ] F) := inferInstance
local instance instNormedSpaceRealContinuousLinearMapId_solutions_1 : NormedSpace ℝ ((G →L[ℝ] F) →L[ℝ] F) := inferInstance
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_2 : NormedAddCommGroup (F →L[ℝ] G) := inferInstance
local instance instNormedSpaceRealContinuousLinearMapId_solutions_2 : NormedSpace ℝ (F →L[ℝ] G) := inferInstance
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_3_r914c68_1 : NormedAddCommGroup ((F →L[ℝ] G) →L[ℝ] G) := inferInstance
local instance instNormedSpaceRealContinuousLinearMapId_solutions_3 : NormedSpace ℝ ((F →L[ℝ] G) →L[ℝ] G) := inferInstance

end
end CurrentKS.Calculus

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_HermitianMat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

def hermitianSubmodule (d : ℕ) : Submodule ℝ (Mat d) where
  carrier := {A | A.IsHermitian}
  zero_mem' := Matrix.isHermitian_zero
  add_mem' hA hB := hA.add hB
  smul_mem' r A hA := by
    change ((r : ℂ) • A).IsHermitian
    exact hA.smul (by change star (r : ℂ) = (r : ℂ); simp)

abbrev H (d : ℕ) := hermitianSubmodule d

variable {d : ℕ}

instance instFiniteDimensionalRealSubtypeMatMemSubmoduleH : FiniteDimensional ℝ (H d) := inferInstance

instance instIsUniformAddGroupSubtypeMatMemSubmoduleRealH : IsUniformAddGroup (H d) := (H d).toAddSubgroup.isUniformAddGroup

instance instCompleteSpaceSubtypeMatMemSubmoduleRealH : CompleteSpace (H d) := FiniteDimensional.complete ℝ (H d)

@[simp] theorem matrix_hermitian (A : H d) : (A : Mat d).IsHermitian := A.property

def one : H d := ⟨1, Matrix.isHermitian_one⟩

@[simp] theorem one_val : ((one : H d) : Mat d) = 1 := rfl

def realTrace (A : H d) : ℝ := (A.val.trace).re

def psdCone (d : ℕ) : ConvexCone ℝ (H d) where
  carrier := {A | (A : Mat d).PosSemidef}
  smul_mem' r hr A hA := by
    change ((r : ℂ) • (A : Mat d)).PosSemidef
    exact hA.smul (by simpa using hr.le)
  add_mem' A hA B hB := hA.add hB

@[simp] theorem mem_psdCone (A : H d) : A ∈ psdCone d ↔ (A : Mat d).PosSemidef := Iff.rfl

@[simp] theorem zero_mem_psdCone : (0 : H d) ∈ psdCone d := Matrix.PosSemidef.zero

@[simp] theorem one_mem_psdCone : (one : H d) ∈ psdCone d := Matrix.PosSemidef.one

open scoped Matrix.Norms.Frobenius

def asL2 {d : ℕ} (A : Mat d) : PiLp 2 (fun _ : Fin d => EuclideanSpace ℂ (Fin d)) :=
  WithLp.toLp 2 (fun i => WithLp.toLp 2 (A i))

instance matrixInnerProduct (d : ℕ) : InnerProductSpace ℂ (Mat d) where
  inner A B := inner ℂ (asL2 A) (asL2 B)
  norm_sq_eq_re_inner A := norm_sq_eq_re_inner (asL2 A)
  conj_inner_symm A B := inner_conj_symm (asL2 A) (asL2 B)
  add_left A B C := by
    change inner ℂ (asL2 A + asL2 B) (asL2 C) = _
    exact inner_add_left _ _ _
  smul_left A B r := by
    change inner ℂ (r • asL2 A) (asL2 B) = _
    exact inner_smul_left _ _ _

instance matrixRealInnerProduct (d : ℕ) : InnerProductSpace ℝ (Mat d) :=
  InnerProductSpace.complexToReal

def rankOne (v : Fin d → ℂ) : H d :=
  ⟨Matrix.vecMulVec v (star v), (Matrix.posSemidef_vecMulVec_self_star v).isHermitian⟩

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.HermitianCoordinates
noncomputable section
open CurrentKS.Hermitian Matrix
open scoped BigOperators Matrix.Norms.Frobenius

variable {d : ℕ}
local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH : NormedAddCommGroup (H d) := inferInstance

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d × Fin d)

local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_r914c68_1 : NormedSpace ℝ (H d) := inferInstance
def decode (x : Fin d × Fin d → ℝ) : Mat d := fun i j =>
  ⟨x (min i j,max i j),if i < j then x (j,i) else if j < i then -x (i,j) else 0⟩

def encode (A : H d) : Fin d × Fin d → ℝ := fun p =>
  if p.1 ≤ p.2 then (A.val p.1 p.2).re else (A.val p.2 p.1).im

lemma decode_hermitian (x : Fin d × Fin d → ℝ) : (decode x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  apply Complex.ext
  · simp [decode,min_comm,max_comm]
  · simp only [decode,Complex.star_def,Complex.conj_im]
    rcases lt_trichotomy i j with hij | hij | hji
    · simp [hij,not_lt.mpr hij.le]
    · subst j; simp
    · simp [hji,not_lt.mpr hji.le]

local instance instNormedAddCommGroupSpace_r914c68_1 : NormedAddCommGroup (Space d) := inferInstance
local instance instNormedSpaceRealSpace_r914c68_1 : NormedSpace ℝ (Space d) := inferInstance
def assemble (x : Space d) : H d := ⟨decode x,decode_hermitian x⟩
def extract (A : H d) : Space d := WithLp.toLp 2 (encode A)

lemma decode_add (x y : Fin d × Fin d → ℝ) : decode (x+y)=decode x+decode y := by
  ext i j
  apply Complex.ext
  · simp [decode,Matrix.add_apply]
  · simp only [decode,Matrix.add_apply,Pi.add_apply,Complex.add_im]
    split_ifs <;> ring

lemma decode_smul (r : ℝ) (x : Fin d × Fin d → ℝ) : decode (r • x)=r • decode x := by
  ext i j
  apply Complex.ext
  · simp [decode,Matrix.smul_apply]
  · simp only [decode,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,Complex.real_smul,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul]
    split_ifs <;> ring

def assembleLinear (d : ℕ) : Space d →ₗ[ℝ] H d where
  toFun := assemble
  map_add' x y := Subtype.ext (decode_add x y)
  map_smul' r x := Subtype.ext (decode_smul r x)

end
end CurrentKS.HermitianCoordinates

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS

noncomputable def opNorm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖

def signValue (b : Bool) : ℝ := if b then 1 else -1

end CurrentKS

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RealTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS
noncomputable section
open scoped BigOperators ComplexOrder

variable {d : ℕ}

def realTrace (A : Matrix (Fin d) (Fin d) ℂ) : ℝ := A.trace.re

def traceSign (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  if 0 ≤ realTrace A then 1 else -1

end
end CurrentKS

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Normalizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS
noncomputable section
open scoped BigOperators ComplexOrder

variable {d N : ℕ}

def normalizer (H : Fin N → Matrix (Fin d) (Fin d) ℂ) : ℝ := ∑ i, |realTrace (H i)|

def normalizedMatrix (H : Fin N → Matrix (Fin d) (Fin d) ℂ) (i : Fin N) :
    Matrix (Fin d) (Fin d) ℂ := (normalizer H)⁻¹ • (traceSign (H i) • H i)

end
end CurrentKS

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_BitSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.RationalBits

def Parts (b : ℕ) (q : ℚ) : Prop := q.num.natAbs ≤ 2^b ∧ q.den ≤ 2^b

variable {ι : Type*}

def LinearBits (f : (ι → ℚ) → ℚ) : Prop :=
  ∃ C:ℕ, 0<C ∧ ∀ b x, (∀i,Parts b (x i)) → Parts (C*(b+1)) (f x)

end CurrentKS.RationalBits

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Drift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Progress
noncomputable section
open scoped BigOperators

variable {n : ℕ}

def drift (T a b ω : ℝ) : ℝ := -24/T*(a-b)*ω

end
end CurrentKS.Progress

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_InvH
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder

variable {d : ℕ}

def invH (A : H d) : H d := ⟨(A : Mat d)⁻¹, A.property.inv⟩

@[simp] theorem invH_val (A : H d) : (invH A : Mat d) = (A : Mat d)⁻¹ := rfl

def pd (d : ℕ) : Set (H d) := {A | (A : Mat d).PosDef}

lemma psd_smul {A : H d} (hA : A ∈ psdCone d) {a : ℝ} (ha : 0 ≤ a) :
    a • A ∈ psdCone d := by
  change ((a : ℂ) • (A : Mat d)).PosSemidef
  exact hA.smul (by exact_mod_cast ha)

open scoped Matrix.Norms.L2Operator

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_Sandwich
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian

section L2Operator

open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {d : ℕ}

def sandwich (A U : H d) : H d :=
  ⟨(A : Mat d) * (U : Mat d) * (A : Mat d), by
    have hh := Matrix.isHermitian_mul_mul_conjTranspose (A : Mat d) U.property
    rw [A.property.eq] at hh
    exact hh⟩

@[simp] lemma sandwich_val (A U : H d) :
    (sandwich A U : Mat d) = (A : Mat d) * (U : Mat d) * (A : Mat d) := rfl

def matrixTraceCLM : Mat d →L[ℝ] ℝ :=
  Complex.reCLM.comp (Matrix.traceLinearMap (Fin d) ℝ ℂ).toContinuousLinearMap

@[simp] lemma matrixTraceCLM_apply (A : Mat d) : matrixTraceCLM A = A.trace.re := rfl

end L2Operator

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_TraceCLM
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

@[simp] lemma realTrace_zero : realTrace (0 : H d) = 0 := by
  simp [realTrace]

@[simp] lemma realTrace_add (A B : H d) : realTrace (A+B) = realTrace A + realTrace B := by
  change ((A : Mat d) + (B : Mat d)).trace.re = _
  simp [Matrix.trace_add, realTrace]

@[simp] lemma realTrace_sub (A B : H d) : realTrace (A-B) = realTrace A - realTrace B := by
  change ((A : Mat d) - (B : Mat d)).trace.re = _
  simp [Matrix.trace_sub, realTrace]

@[simp] lemma realTrace_smul (r : ℝ) (A : H d) : realTrace (r • A) = r * realTrace A := by
  change ((r : ℂ) • (A : Mat d)).trace.re = _
  rw [Matrix.trace_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, realTrace]

@[simp] lemma realTrace_one : realTrace (one : H d) = d := by
  simp [realTrace]

def traceCLM : H d →L[ℝ] ℝ := innerSL ℝ one

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_InnerRight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma sandwich_add (A U V : H d) : sandwich A (U+V) = sandwich A U + sandwich A V := by
  apply Subtype.ext
  change (A : Mat d) * ((U : Mat d)+(V : Mat d)) * (A : Mat d) = _
  simp only [mul_add, add_mul]
  rfl

lemma sandwich_smul (r : ℝ) (A U : H d) : sandwich A (r • U) = r • sandwich A U := by
  apply Subtype.ext
  change (A : Mat d) * (r • (U : Mat d)) * (A : Mat d) = r • _
  simp only [mul_smul_comm, smul_mul_assoc]
  rfl

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_SandwichCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p7 : NormedAddCommGroup (H d) := inferInstance
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_r914c68_2 : NormedSpace ℝ (H d) := inferInstance
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p7 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

def sandwichCLM (A : H d) : H d →L[ℝ] H d :=
  ({ toFun := sandwich A
     map_add' := sandwich_add A
     map_smul' := fun r U => sandwich_smul r A U } : H d →ₗ[ℝ] H d).toContinuousLinearMap

@[simp] lemma sandwichCLM_apply (A U : H d) : sandwichCLM A U = sandwich A U := rfl

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_JordanCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p4 : NormedAddCommGroup (H d) := inferInstance
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_r914c68_3 : NormedSpace ℝ (H d) := inferInstance
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p4 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

def jordanCLM (A B : H d) : H d →L[ℝ] H d :=
  sandwichCLM (A+B) - sandwichCLM A - sandwichCLM B

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RetractH
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

local instance instNormedAddCommGroupMat_p2 : NormedAddCommGroup (Mat d) := inferInstance
local instance instNormedSpaceRealMat_p2 : NormedSpace ℝ (Mat d) := inferInstance
local instance instTopologicalSpaceMat_p2 : TopologicalSpace (Mat d) :=
  (inferInstance : NormedAddCommGroup (Mat d)).toUniformSpace.toTopologicalSpace

local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p6 : NormedAddCommGroup (H d) := inferInstance
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_r914c68_4 : NormedSpace ℝ (H d) := inferInstance
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p6 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

def retractH : Mat d →L[ℝ] H d := (hermitianSubmodule d).orthogonalProjectionOnto

@[simp] lemma retractH_coe (A : H d) : retractH (A : Mat d) = A :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self A

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_DerivInvHPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian
open Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

variable {d : ℕ}

local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p0 : NormedAddCommGroup (H d) := inferInstance
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_p0 : NormedSpace ℝ (H d) := inferInstance
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p0 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

local instance derivInvHPathNormedAddCommGroup : NormedAddCommGroup (H d →L[ℝ] H d) := inferInstance
local instance derivInvHPathNormedSpace : NormedSpace ℝ (H d →L[ℝ] H d) := inferInstance
local instance instTopologicalSpaceContinuousLinearMapRealIdSubtypeMatMemSubmoduleH : TopologicalSpace (H d →L[ℝ] H d) :=
  (inferInstance : NormedAddCommGroup (H d →L[ℝ] H d)).toUniformSpace.toTopologicalSpace

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Point
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

abbrev Point (d : ℕ) := ℝ × H d × H d

def domain (d : ℕ) : Set (Point d) := {z | z.2.1 ∈ pd d ∧ z.2.2 ∈ pd d}

def objective (ε : ℝ) (z : Point d) : ℝ := z.1 + ε * _root_.OAI.CurrentKS.Hermitian.realTrace (z.2.1 + z.2.2)

def residual (S : H d) (η : H d →L[ℝ] H d) (z : Point d) : H d × H d :=
  (invH z.2.1 + S + η z.2.2 - z.1 • (Hermitian.one : H d),
    invH z.2.2 - S + η z.2.1 - z.1 • (Hermitian.one : H d))

def feasible (S : H d) (η : H d →L[ℝ] H d) : Set (Point d) :=
  {z | z ∈ domain d ∧ (residual S η z).1 ≤ 0 ∧ (residual S η z).2 ≤ 0}

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_PairCone
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

def pairCone (d : ℕ) : ConvexCone ℝ (H d × H d) where
  carrier := {z | z.1 ∈ psdCone d ∧ z.2 ∈ psdCone d}
  smul_mem' _ hr _ hz := ⟨psd_smul hz.1 hr.le, psd_smul hz.2 hr.le⟩
  add_mem' _ hx _ hy := ⟨(psdCone d).add_mem hx.1 hy.1, (psdCone d).add_mem hx.2 hy.2⟩

@[simp] lemma mem_pairCone (z : H d × H d) :
    z ∈ pairCone d ↔ z.1 ∈ psdCone d ∧ z.2 ∈ psdCone d := Iff.rfl

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_StrictEpigraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Conic
noncomputable section
open Set
open scoped Topology

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

def strictEpigraph (K : ConvexCone ℝ F) (D : Set E) (g : E → F) (f : E → ℝ) :
    Set (F × ℝ) :=
  {z | ∃ x ∈ D, z.1 - g x ∈ interior (K : Set F) ∧ f x < z.2}

end
end CurrentKS.Conic

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Lagrangian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

def lagrangian (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d) (P Q : H d) (z : Point d) : ℝ :=
  objective ε z + inner ℝ P (residual S η z).1 + inner ℝ Q (residual S η z).2

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_SymmetricMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

def SymmetricMap (η : H d →L[ℝ] H d) : Prop :=
  ∀ A B, inner ℝ A (η B) = inner ℝ (η A) B

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p1 : NormedAddCommGroup (H d) := inferInstance
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_r914c68_5 : NormedSpace ℝ (H d) := inferInstance
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p1 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

abbrev Coordinates (N : ℕ) := Fin N → ℝ

def Cube (x : Coordinates N) : Prop := ∀ i, |x i| ≤ 1

def S (A : Fin N → H d) (x : Coordinates N) : H d := ∑ i, x i • A i

def eta (c : ℝ) (A : Fin N → H d) (x : Coordinates N) : H d →L[ℝ] H d :=
  ∑ i, (c * psi (x i)) • sandwichCLM (A i)

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_NormCoordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Calculus Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p5 : NormedAddCommGroup (H d) := inferInstance
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_p5 : NormedSpace ℝ (H d) := inferInstance
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p5 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

local instance normCoordinateOperatorNormedAddCommGroup : NormedAddCommGroup (H d →L[ℝ] H d) := inferInstance
local instance normCoordinateOperatorNormedSpace : NormedSpace ℝ (H d →L[ℝ] H d) := inferInstance

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Variables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.KKT
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev Variables (E : Type*) := ℝ × E × E

def jacobian (e : E) (L H : E →L[ℝ] E) : Variables E →L[ℝ] Variables E :=
  ({ toFun := fun z => (inner ℝ e z.2.2, L z.2.1 + z.1 • e, L z.2.2 - H z.2.1)
     map_add' := by
       intro z w
       apply Prod.ext
       · simp [inner_add_right]
       · apply Prod.ext
         · simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul]
           module
         · simp only [Prod.fst_add, Prod.snd_add, map_add]
           module
     map_smul' := by
       intro r z
       apply Prod.ext
       · simp [real_inner_smul_right]
       · apply Prod.ext <;> simp [smul_add, smul_sub, smul_smul] } :
    Variables E →ₗ[ℝ] Variables E).toContinuousLinearMap

@[simp] lemma jacobian_apply (e : E) (L H : E →L[ℝ] E) (z : Variables E) :
    jacobian e L H z = (inner ℝ e z.2.2, L z.2.1 + z.1 • e, L z.2.2 - H z.2.1) := rfl

end
end CurrentKS.KKT

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_FDerivTightPart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius ContDiff

variable {d : ℕ}

local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p1 : NormedAddCommGroup (H d) := inferInstance

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Pair
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.retractH_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p3 : NormedAddCommGroup (H d) := inferInstance
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_p3 : NormedSpace ℝ (H d) := inferInstance
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p3 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

abbrev Pair (d : ℕ) := H d × H d

def linConstraint (X Y : H d) (η : H d →L[ℝ] H d) : Pair d →L[ℝ] Pair d :=
  ((sandwichCLM (invH X)).comp (ContinuousLinearMap.fst ℝ (H d) (H d)) -
    η.comp (ContinuousLinearMap.snd ℝ (H d) (H d))).prod
  ((sandwichCLM (invH Y)).comp (ContinuousLinearMap.snd ℝ (H d) (H d)) -
    η.comp (ContinuousLinearMap.fst ℝ (H d) (H d)))

def linPositive (X Y : H d) (η : H d →L[ℝ] H d) : Pair d →L[ℝ] Pair d :=
  ((sandwichCLM X).comp (η.comp (ContinuousLinearMap.snd ℝ (H d) (H d)))).prod
    ((sandwichCLM Y).comp (η.comp (ContinuousLinearMap.fst ℝ (H d) (H d))))

def linCongruence (X Y : H d) : Pair d →L[ℝ] Pair d :=
  ((sandwichCLM X).comp (ContinuousLinearMap.fst ℝ (H d) (H d))).prod
    ((sandwichCLM Y).comp (ContinuousLinearMap.snd ℝ (H d) (H d)))

@[simp] lemma linConstraint_apply (X Y : H d) (η : H d →L[ℝ] H d) (z : Pair d) :
    linConstraint X Y η z = (sandwich (invH X) z.1 - η z.2,
      sandwich (invH Y) z.2 - η z.1) := rfl

@[simp] lemma linPositive_apply (X Y : H d) (η : H d →L[ℝ] H d) (z : Pair d) :
    linPositive X Y η z = (sandwich X (η z.2), sandwich Y (η z.1)) := rfl

@[simp] lemma linCongruence_apply (X Y : H d) (z : Pair d) :
    linCongruence X Y z = (sandwich X z.1, sandwich Y z.2) := rfl

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_PairHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

abbrev PairHilbert (d : ℕ) := WithLp 2 (H d × H d)

local instance instTopologicalSpacePairHilbert_p4 : TopologicalSpace (PairHilbert d) :=
  (inferInstance : NormedAddCommGroup (PairHilbert d)).toUniformSpace.toTopologicalSpace

def pairEquiv (d : ℕ) : PairHilbert d ≃L[ℝ] Pair d :=
  WithLp.prodContinuousLinearEquiv 2 ℝ (H d) (H d)

def pairHilbertCone (d : ℕ) : ConvexCone ℝ (PairHilbert d) where
  carrier := {z | pairEquiv d z ∈ pairCone d}
  smul_mem' a ha z hz := by
    change pairEquiv d (a • z) ∈ pairCone d
    rw [map_smul]
    exact (pairCone d).smul_mem ha hz
  add_mem' z hz w hw := by
    change pairEquiv d (z+w) ∈ pairCone d
    rw [map_add]
    exact (pairCone d).add_mem hz hw

def onPairHilbert (T : Pair d →L[ℝ] Pair d) : PairHilbert d →L[ℝ] PairHilbert d :=
  (pairEquiv d).symm.toContinuousLinearMap.comp (T.comp (pairEquiv d).toContinuousLinearMap)

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Hessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

local instance instTopologicalSpacePairHilbert_p0 : TopologicalSpace (PairHilbert d) :=
  (inferInstance : NormedAddCommGroup (PairHilbert d)).toUniformSpace.toTopologicalSpace

def hessian (X Y P Q : H d) : PairHilbert d →L[ℝ] PairHilbert d :=
  onPairHilbert ((jordanCLM (invH X) (sandwich (invH X) P)).prodMap
    (jordanCLM (invH Y) (sandwich (invH Y) Q)))

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Vars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

abbrev Vars (d : ℕ) := CurrentKS.KKT.Variables (PairHilbert d)

local instance instNormedAddCommGroupVars : NormedAddCommGroup (Vars d) := inferInstance
local instance instNormedSpaceRealVars : NormedSpace ℝ (Vars d) := inferInstance

def identityPair (d : ℕ) : PairHilbert d := (pairEquiv d).symm (Hermitian.one,Hermitian.one)

def tCoord (d : ℕ) : Vars d →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (PairHilbert d × PairHilbert d)
def uCoord (d : ℕ) : Vars d →L[ℝ] PairHilbert d :=
  (ContinuousLinearMap.fst ℝ (PairHilbert d) (PairHilbert d)).comp
    (ContinuousLinearMap.snd ℝ ℝ (PairHilbert d × PairHilbert d))
def pCoord (d : ℕ) : Vars d →L[ℝ] PairHilbert d :=
  (ContinuousLinearMap.snd ℝ (PairHilbert d) (PairHilbert d)).comp
    (ContinuousLinearMap.snd ℝ ℝ (PairHilbert d × PairHilbert d))
def xCoord (d : ℕ) : Vars d →L[ℝ] H d := (WithLp.fstL 2 ℝ (H d) (H d)).comp (uCoord d)
def yCoord (d : ℕ) : Vars d →L[ℝ] H d := (WithLp.sndL 2 ℝ (H d) (H d)).comp (uCoord d)
def mCoord (d : ℕ) : Vars d →L[ℝ] H d := (WithLp.fstL 2 ℝ (H d) (H d)).comp (pCoord d)
def nCoord (d : ℕ) : Vars d →L[ℝ] H d := (WithLp.sndL 2 ℝ (H d) (H d)).comp (pCoord d)

def kktSystem (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d) (z : Vars d) : Vars d :=
  (inner ℝ (identityPair d) (pCoord d z) - 1,
   (pairEquiv d).symm
    (tCoord d z • (Hermitian.one : H d) - invH (xCoord d z) - S - η (yCoord d z),
     tCoord d z • (Hermitian.one : H d) - invH (yCoord d z) + S - η (xCoord d z)),
   (pairEquiv d).symm
    (sandwich (invH (xCoord d z)) (mCoord d z) - η (nCoord d z) - ε • (Hermitian.one : H d),
     sandwich (invH (yCoord d z)) (nCoord d z) - η (mCoord d z) - ε • (Hermitian.one : H d)))

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Pack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

variable {d : ℕ}

def pack (z : Point d) (P Q : H d) : Vars d :=
  (z.1, (pairEquiv d).symm z.2, (pairEquiv d).symm (P,Q))

def unpack (z : Vars d) : Point d := (tCoord d z, xCoord d z, yCoord d z)

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_JetBoundTightPart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open CurrentKS.Calculus Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p3 : NormedAddCommGroup (H d) := inferInstance
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_p3 : NormedSpace ℝ (H d) := inferInstance
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p3 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

local instance instNormedAddCommGroupContinuousLinearMapRealIdSubtypeMatMemSubmoduleH : NormedAddCommGroup (H d →L[ℝ] H d) := inferInstance
local instance instNormedSpaceRealContinuousLinearMapIdSubtypeMatMemSubmoduleH : NormedSpace ℝ (H d →L[ℝ] H d) := inferInstance
end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Variational
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ}

section

local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p4 : NormedAddCommGroup (H d) := inferInstance
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_p4 : NormedSpace ℝ (H d) := inferInstance
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p4 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

abbrev Parameters (d : ℕ) := H d × (H d →L[ℝ] H d)

local instance instNormedAddCommGroupContinuousLinearMapRealIdSubtypeMatMemSubmoduleH : NormedAddCommGroup (H d →L[ℝ] H d) := inferInstance
local instance instNormedSpaceRealContinuousLinearMapIdSubtypeMatMemSubmoduleH : NormedSpace ℝ (H d →L[ℝ] H d) := inferInstance
local instance instNormedAddCommGroupParameters : NormedAddCommGroup (Parameters d) := inferInstance
local instance instNormedSpaceRealParameters : NormedSpace ℝ (Parameters d) := inferInstance
local instance instNormedAddCommGroupVars_1 : NormedAddCommGroup (Vars d) := inferInstance
local instance instNormedSpaceRealVars_1 : NormedSpace ℝ (Vars d) := inferInstance
local instance instNormedAddCommGroupProdParametersVars : NormedAddCommGroup (Parameters d × Vars d) := inferInstance
local instance instNormedSpaceRealProdParametersVars : NormedSpace ℝ (Parameters d × Vars d) := inferInstance

def kktJoint (ε : ℝ) (u : Parameters d × Vars d) : Vars d :=
  kktSystem ε u.1.1 u.1.2 u.2

end

end CurrentKS.Variational

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_JetBoundProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian CurrentKS.Calculus Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p0 : NormedAddCommGroup (H d) := inferInstance
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_p0 : NormedSpace ℝ (H d) := inferInstance
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p0 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace
local instance instNormedAddCommGroupContinuousLinearMapRealIdSubtypeMatMemSubmoduleH_1 : NormedAddCommGroup (H d →L[ℝ] H d) := inferInstance
local instance instNormedSpaceRealContinuousLinearMapIdSubtypeMatMemSubmoduleH_1 : NormedSpace ℝ (H d →L[ℝ] H d) := inferInstance
local instance instNormedAddCommGroupPairHilbert : NormedAddCommGroup (PairHilbert d) := inferInstance
local instance instNormedSpaceRealPairHilbert : NormedSpace ℝ (PairHilbert d) := inferInstance
local instance instNormedAddCommGroupProdSubtypeMatMemSubmoduleRealH : NormedAddCommGroup (H d × H d) := inferInstance
local instance instNormedSpaceRealProdSubtypeMatMemSubmoduleH : NormedSpace ℝ (H d × H d) := inferInstance
local instance instNormedAddCommGroupProdPairHilbert : NormedAddCommGroup (PairHilbert d × PairHilbert d) := inferInstance
local instance instNormedSpaceRealProdPairHilbert : NormedSpace ℝ (PairHilbert d × PairHilbert d) := inferInstance
local instance instNormedAddCommGroupVars_2 : NormedAddCommGroup (Vars d) := inferInstance
local instance instNormedSpaceRealVars_2 : NormedSpace ℝ (Vars d) := inferInstance
end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

def value (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d) : ℝ :=
  sInf (objective ε '' feasible S η)

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ObjectiveVarsCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p2 : NormedAddCommGroup (H d) := inferInstance
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_p2 : NormedSpace ℝ (H d) := inferInstance
private local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_r914c68_1 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace
local instance instNormedAddCommGroupPairHilbert_1 : NormedAddCommGroup (PairHilbert d) := inferInstance
local instance instNormedSpaceRealPairHilbert_1 : NormedSpace ℝ (PairHilbert d) := inferInstance
private local instance instTopologicalSpacePairHilbert_r914c68_1 : TopologicalSpace (PairHilbert d) :=
  (inferInstance : NormedAddCommGroup (PairHilbert d)).toUniformSpace.toTopologicalSpace
local instance instNormedAddCommGroupVars_3 : NormedAddCommGroup (Vars d) := inferInstance
local instance instNormedSpaceRealVars_3 : NormedSpace ℝ (Vars d) := inferInstance
local instance instTopologicalSpaceVars_p4 : TopologicalSpace (Vars d) :=
  (inferInstance : NormedAddCommGroup (Vars d)).toUniformSpace.toTopologicalSpace

def objectiveVarsCLM (ε : ℝ) : Vars d →L[ℝ] ℝ :=
  tCoord d+ε • (innerSL ℝ (identityPair d)).comp (uCoord d)

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_CoarseBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d N : ℕ}
local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p0 : NormedAddCommGroup (H d) := inferInstance
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_p0 : NormedSpace ℝ (H d) := inferInstance
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p0 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace
private local instance instNormedAddCommGroupVars_r914c68_1 : NormedAddCommGroup (Vars d) := inferInstance
private local instance instNormedSpaceRealVars_r914c68_1 : NormedSpace ℝ (Vars d) := inferInstance
private local instance instTopologicalSpaceVars_r914c68_1 : TopologicalSpace (Vars d) :=
  (inferInstance : NormedAddCommGroup (Vars d)).toUniformSpace.toTopologicalSpace
local instance instNormedAddCommGroupContinuousLinearMapRealIdSubtypeMatMemSubmoduleH : NormedAddCommGroup (H d →L[ℝ] H d) := inferInstance
local instance instNormedSpaceRealContinuousLinearMapIdSubtypeMatMemSubmoduleH : NormedSpace ℝ (H d →L[ℝ] H d) := inferInstance

def coarseBudget (d N : ℕ) (ε σ : ℝ) : ℝ :=
  200+((d:ℝ)+1)+|ε|+(200/ε)*((d:ℝ)+1)+200*((d:ℝ)+1)+
    (((d:ℝ)+1)+N)+384*N*(1+800/σ^3)

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Energy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

def energy (X Y P Q U V : H d) : ℝ :=
  inner ℝ P (sandwich (invH X) (sandwich U (invH X))) +
  inner ℝ Q (sandwich (invH Y) (sandwich V (invH Y)))

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Line
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Scalar Filter
open scoped BigOperators Topology

variable {N : ℕ}
def line (x h : Coordinates N) (s : ℝ) : Coordinates N := fun i => x i+s*h i

@[simp] lemma line_zero (x h : Coordinates N) : line x h 0 = x := by funext i; simp [line]

def penalty (x : Coordinates N) : ℝ := ∑ i, psi (x i)

def penalty₁ (x h : Coordinates N) : ℝ := ∑ i, psi₁ (x i)*h i

def penalty₂ (x h : Coordinates N) : ℝ := ∑ i, -kappa (x i)*(h i)^2

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_NegativeWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

variable {d N : ℕ}

local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p4 : NormedAddCommGroup (H d) := inferInstance
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_p4 : NormedSpace ℝ (H d) := inferInstance
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p4 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

def negativeWeight (A : Fin N → H d) (x h : Coordinates N) (X Y P Q : H d) : ℝ :=
  ∑ i, kappa (x i)*(h i)^2*(inner ℝ (A i) Y*inner ℝ (A i) P + inner ℝ (A i) X*inner ℝ (A i) Q)

def mixedTerm (c : ℝ) (A : Fin N → H d) (x h : Coordinates N) (P Q U V : H d) : ℝ :=
  ∑ i, 2*c*psi₁ (x i)*h i*(inner ℝ (A i) P*inner ℝ (A i) V + inner ℝ (A i) Q*inner ℝ (A i) U)

local instance negativeWeightNormedAddCommGroup : NormedAddCommGroup (H d →L[ℝ] H d) :=
  inferInstance
local instance negativeWeightNormedSpace : NormedSpace ℝ (H d →L[ℝ] H d) := inferInstance

private local instance instTopologicalSpaceContinuousLinearMapRealIdSubtypeMatMemSubmoduleH_r914c68_1 : TopologicalSpace (H d →L[ℝ] H d) :=
  (inferInstance : NormedAddCommGroup (H d →L[ℝ] H d)).toUniformSpace.toTopologicalSpace
def eta₁ (c : ℝ) (A : Fin N → H d) (x h : Coordinates N) : H d →L[ℝ] H d :=
  ∑ i, (c*psi₁ (x i)*h i) • sandwichCLM (A i)

def eta₂ (c : ℝ) (A : Fin N → H d) (x h : Coordinates N) : H d →L[ℝ] H d :=
  ∑ i, (-c*kappa (x i)*(h i)^2) • sandwichCLM (A i)

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_DerivPathObjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

variable {d N : ℕ}
local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p2 : NormedAddCommGroup (H d) := inferInstance
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_p2 : NormedSpace ℝ (H d) := inferInstance
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p2 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace
local instance derivPathObjectiveNormedAddCommGroup : NormedAddCommGroup (H d →L[ℝ] H d) :=
  inferInstance
local instance derivPathObjectiveNormedSpace : NormedSpace ℝ (H d →L[ℝ] H d) := inferInstance

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_TightSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ}

local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p5 : NormedAddCommGroup (H d) := inferInstance
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_p5 : NormedSpace ℝ (H d) := inferInstance
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p5 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

def tightSystem (t : ℝ) (S : H d) (η : H d →L[ℝ] H d) (z : Pair d) : Pair d :=
  (t • (Hermitian.one : H d) - invH z.1 - S - η z.2,
   t • (Hermitian.one : H d) - invH z.2 + S - η z.1)

local instance tightSystemOperatorNormedAddCommGroup : NormedAddCommGroup (H d →L[ℝ] H d) :=
  inferInstance
local instance tightSystemOperatorNormedSpace : NormedSpace ℝ (H d →L[ℝ] H d) := inferInstance
local instance tightSystemPairNormedAddCommGroup : NormedAddCommGroup (Pair d) := inferInstance
local instance tightSystemPairNormedSpace : NormedSpace ℝ (Pair d) := inferInstance
local instance tightSystemParametersNormedAddCommGroup : NormedAddCommGroup (Parameters d) :=
  inferInstance
local instance tightSystemParametersNormedSpace : NormedSpace ℝ (Parameters d) := inferInstance
local instance tightSystemProductNormedAddCommGroup : NormedAddCommGroup (Parameters d × Pair d) :=
  inferInstance
local instance tightSystemProductNormedSpace : NormedSpace ℝ (Parameters d × Pair d) := inferInstance

def tightJoint (t : ℝ) (v : Parameters d × Pair d) : Pair d :=
  tightSystem t v.1.1 v.1.2 v.2

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ValueFeasible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ}

local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p8 : NormedAddCommGroup (H d) := inferInstance
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_p8 : NormedSpace ℝ (H d) := inferInstance
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p8 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

local instance valueFeasibleOperatorNormedAddCommGroup :
    NormedAddCommGroup (H d →L[ℝ] H d) := inferInstance
local instance valueFeasibleOperatorNormedSpace : NormedSpace ℝ (H d →L[ℝ] H d) := inferInstance
local instance valueFeasiblePairNormedAddCommGroup : NormedAddCommGroup (Pair d) := inferInstance
local instance valueFeasiblePairNormedSpace : NormedSpace ℝ (Pair d) := inferInstance

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_FaceValueDirectionVariations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d N : ℕ}
local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p3 : NormedAddCommGroup (H d) := inferInstance
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_p3 : NormedSpace ℝ (H d) := inferInstance
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p3 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace
local instance faceValueDirectionNormedAddCommGroup : NormedAddCommGroup (H d →L[ℝ] H d) := inferInstance
local instance faceValueDirectionNormedSpace : NormedSpace ℝ (H d →L[ℝ] H d) := inferInstance

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Interaction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Interaction
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.State Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

def interaction (c : ℝ) (A : Fin N → H d) (l : Fin N → ℝ) (X : H d) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => c*l i*l j*inner ℝ (A i) (sandwich X (A j))

def responseInput (A : Fin N → H d) (l F : Fin N → ℝ) : H d :=
  ∑ i, (l i*F i) • A i

end
end CurrentKS.Interaction

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_MovementMat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Movement
noncomputable section
open Matrix WithLp
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

variable {n : ℕ}
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

end
end CurrentKS.Movement

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_EnergyMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Interaction
noncomputable section
open CurrentKS.Hermitian CurrentKS.State Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

def energyMatrix (A : Fin N → H d) (l : Fin N → ℝ) (X P : H d) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (l i*l j/2)*inner ℝ (A i) (jordanCLM X P (A j))

end
end CurrentKS.Interaction

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_CovarianceE
attribute [-instance] _root_.OAI.CurrentKS.Hermitian.instFiniteDimensionalRealSubtypeMatMemSubmoduleH
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Covariance
noncomputable section
open scoped BigOperators
open Matrix

local instance instInnerProductSpaceReal_solutions : InnerProductSpace ℝ ℝ := RCLike.innerProductSpace

abbrev E (m : ℕ) := EuclideanSpace ℝ (Fin m)
abbrev Mat (m : ℕ) := Matrix (Fin m) (Fin m) ℝ

variable {m : ℕ}

local instance instLocallyConvexSpaceRealMat_r914c68_1 : LocallyConvexSpace ℝ (Mat m) :=
  inferInstanceAs (LocallyConvexSpace ℝ (Fin m → Fin m → ℝ))
def projectionMatrix (G : Submodule ℝ (E m)) : Mat m :=
  LinearMap.toMatrix (EuclideanSpace.basisFun _ ℝ).toBasis
    (EuclideanSpace.basisFun _ ℝ).toBasis G.starProjection.toLinearMap

def psdTraceBound (B : ℝ) : Set (Mat m) :=
  {A | A.PosSemidef ∧ A.trace ≤ B}

def Supported (G : Submodule ℝ (E m)) (A : Mat m) : Prop :=
  ∀ x, Matrix.toEuclideanLin A x ∈ G

def feasible (G : Submodule ℝ (E m)) : Set (Mat m) :=
  {A | A.PosSemidef ∧ Supported G A ∧ ∀ i, A i i ≤ 1}

def sqrtDiagonal (A : Mat m) : Mat m := Matrix.diagonal fun i => Real.sqrt (A i i)

def whiten (A : Mat m) : Mat m :=
  let D := Matrix.diagonal fun i => (Real.sqrt (A i i))⁻¹
  D * A * D

def quad (A : Mat m) (x : E m) : ℝ := inner ℝ x (Matrix.toEuclideanLin A x)

abbrev High {A : Mat m} (hA : A.IsHermitian) (κ : ℝ) :=
  {i : Fin m // κ < hA.eigenvalues i}

def highCoordinates {A : Mat m} (hA : A.IsHermitian) (κ : ℝ) :
    E m →ₗ[ℝ] (High hA κ → ℝ) where
  toFun x i := inner ℝ (hA.eigenvectorBasis i) x
  map_add' x y := by ext i; exact inner_add_right _ _ _
  map_smul' r x := by ext i; exact real_inner_smul_right _ _ _

def rawDualMatrix (f : Mat m →ₗ[ℝ] ℝ) : Mat m := fun i j => f (Matrix.single j i 1)

def dualMatrix (f : Mat m →ₗ[ℝ] ℝ) : Mat m :=
  (1 / 2 : ℝ) • (rawDualMatrix f + (rawDualMatrix f).transpose)

def slack (κ : ℝ) (A : Mat m) : Mat m := κ • Matrix.diagonal (Matrix.diag A) - A

def constraintMap (κ : ℝ) : Mat m →ₗ[ℝ] Mat m × ℝ where
  toFun A := (slack κ A, A.trace)
  map_add' A B := by
    apply Prod.ext
    · change slack κ (A + B) = slack κ A + slack κ B
      ext i j
      by_cases hij : i = j <;>
        simp [slack, Matrix.diagonal, hij, mul_add, sub_add_sub_comm, add_comm]
    · change (A + B).trace = A.trace + B.trace
      exact Matrix.trace_add _ _
  map_smul' r A := by
    apply Prod.ext
    · simp [slack, Matrix.diag_smul, Matrix.diagonal_smul, smul_sub, smul_smul, mul_comm]
    · change (r • A).trace = r • A.trace
      exact Matrix.trace_smul _ _

end
end CurrentKS.Covariance

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Column
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Covariance
noncomputable section
open Matrix WithLp
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

local instance columnInnerProductSpace : InnerProductSpace ℝ ℝ := RCLike.innerProductSpace
variable {m n : ℕ}

def column (A : Mat m) (j : Fin m) : E m := toLp 2 (fun i => A i j)

end
end CurrentKS.Covariance

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_QuadGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Covariance

section
open scoped BigOperators
open Matrix

local instance instInnerProductSpaceReal_solutions_1 : InnerProductSpace ℝ ℝ := RCLike.innerProductSpace

end

open scoped BigOperators
open Matrix

local instance instInnerProductSpaceReal_solutions_2 : InnerProductSpace ℝ ℝ := RCLike.innerProductSpace

end CurrentKS.Covariance

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_WhitenWeighted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Covariance
noncomputable section
open Matrix
open scoped BigOperators

variable {n : ℕ}

def whitenWeighted (a b : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => Real.sqrt (b i)*M i j/Real.sqrt (a j)

end
end CurrentKS.Covariance

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_PairIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Covariance

section
open Matrix WithLp
open scoped BigOperators

variable {n m : ℕ}

def pairIndex (n : ℕ) : Fin n ⊕ Fin n ≃ Fin (2*n) :=
  finSumFinEquiv.trans (finCongr (by omega))

def offBlock (A B : Mat n) : Mat (2*n) :=
  Matrix.reindex (pairIndex n) (pairIndex n) (Matrix.fromBlocks 0 B A 0)

def weightEquiv (a : Fin m → ℝ) (ha : ∀ i, 0 < a i) : E m ≃ₗ[ℝ] E m :=
  (EuclideanSpace.equiv (Fin m) ℝ).toLinearEquiv |>.trans
    (LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfNeZero ℝ ℝ (Real.sqrt (a i))
      (ne_of_gt (Real.sqrt_pos.mpr (ha i)))) |>.trans
        (EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearEquiv

end

open Matrix WithLp
open scoped BigOperators

local instance instInnerProductSpaceReal_solutions_3 : InnerProductSpace ℝ ℝ := RCLike.innerProductSpace
variable {n : ℕ}

def pairWeight (a b : Fin n → ℝ) : Fin (2*n) → ℝ :=
  Sum.elim a b ∘ (pairIndex n).symm

lemma pairWeight_pos (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    ∀ i, 0 < pairWeight a b i := by
  intro i
  dsimp only [pairWeight,Function.comp_apply]
  cases (pairIndex n).symm i with
  | inl j => exact ha j
  | inr j => exact hb j

end CurrentKS.Covariance

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_PairVec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Covariance
noncomputable section
open Matrix WithLp
open scoped BigOperators Matrix.Norms.L2Operator

local instance instInnerProductSpaceReal_solutions_4 : InnerProductSpace ℝ ℝ := RCLike.innerProductSpace
variable {n : ℕ}

def pairVec (F G : E n) : E (2*n) :=
  toLp 2 (fun i => Sum.elim F G ((pairIndex n).symm i))

def fstVec (v : E (2*n)) : E n := toLp 2 (fun i => v (pairIndex n (.inl i)))
def sndVec (v : E (2*n)) : E n := toLp 2 (fun i => v (pairIndex n (.inr i)))

def fstLin : E (2*n) →ₗ[ℝ] E n where
  toFun := fstVec
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def sndLin : E (2*n) →ₗ[ℝ] E n where
  toFun := sndVec
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def responseLin (B : Mat n) : E (2*n) →ₗ[ℝ] E n := fstLin-B.toEuclideanLin.comp sndLin

def constraintLin (A B : Mat n) : E (2*n) →ₗ[ℝ] E n :=
  responseLin B-(A.toEuclideanLin.comp fstLin-sndLin)

end
end CurrentKS.Covariance

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_DiagBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Covariance
open Matrix WithLp
open scoped BigOperators Matrix.Norms.L2Operator

variable {n : ℕ}

def diagBlock (A B : Mat n) : Mat (2*n) :=
  Matrix.reindex (pairIndex n) (pairIndex n) (Matrix.fromBlocks A 0 0 B)

end CurrentKS.Covariance

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_LightPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Interaction
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

structure LightPoint (d N : ℕ) where
  A : Fin N → H d
  x : Coordinates N
  fixedPart : H d
  ε : ℝ
  ε_pos : 0 < ε
  ε_le_one : ε ≤ 1
  A_pos : ∀ i, A i ∈ psdCone d
  A_ne_zero : ∀ i, A i ≠ 0
  A_rank : ∀ i, (A i : Hermitian.Mat d).rank ≤ 1
  interior : ∀ i, |x i| < 1
  lower : -(100 : ℝ) • (Hermitian.one : H d) ≤ fixedPart+S A x
  upper : fixedPart+S A x ≤ (100 : ℝ) • (Hermitian.one : H d)
  primal : Point d
  feasible : primal ∈ Variational.feasible (fixedPart+S A x) (eta 384 A x)
  sublevel : objective ε primal ≤ 100
  minimal : ∀ w ∈ Variational.feasible (fixedPart+S A x) (eta 384 A x),
    objective ε primal ≤ objective ε w
  P : H d
  Q : H d
  P_pos : P ∈ pd d
  Q_pos : Q ∈ pd d
  P_le : P ≤ (Hermitian.one : H d)
  Q_le : Q ≤ (Hermitian.one : H d)
  trace_eq : Hermitian.realTrace P+Hermitian.realTrace Q = 1
  tight : residual (fixedPart+S A x) (eta 384 A x) primal = 0
  stationary_X : sandwich (invH primal.2.1) P = eta 384 A x Q+ε • (Hermitian.one : H d)
  stationary_Y : sandwich (invH primal.2.2) Q = eta 384 A x P+ε • (Hermitian.one : H d)
  lightA : ∀ i, 384*psi (x i)*inner ℝ (A i) primal.2.1 < 1+x i
  lightB : ∀ i, 384*psi (x i)*inner ℝ (A i) primal.2.2 < 1-x i

variable {d N : ℕ}

namespace LightPoint
variable (p : LightPoint d N)

def X : H d := p.primal.2.1
def Y : H d := p.primal.2.2
def a (i : Fin N) : ℝ := inner ℝ (p.A i) p.X
def b (i : Fin N) : ℝ := inner ℝ (p.A i) p.Y
def pp (i : Fin N) : ℝ := inner ℝ (p.A i) p.P
def qq (i : Fin N) : ℝ := inner ℝ (p.A i) p.Q
def T (i : Fin N) : ℝ := scaleT 384 (p.x i) (p.a i) (p.b i)
def l (i : Fin N) : ℝ := scaleL 384 (p.x i) (p.a i) (p.b i)
def m (i : Fin N) : ℝ := scaleM 384 (p.x i) (p.a i) (p.b i)

end LightPoint
end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ResponseMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Covariance
noncomputable section
open Matrix WithLp
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

variable {n : ℕ}

def responseMatrix (B : Mat n) : Matrix (Fin n) (Fin (2*n)) ℝ :=
  fun i j => Sum.elim (fun k => (1 : Mat n) i k) (fun k => -B i k) ((pairIndex n).symm j)

end
end CurrentKS.Covariance

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_StateIA
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State.LightPoint
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Interaction
open CurrentKS.Covariance CurrentKS.Movement Matrix WithLp
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {d N : ℕ} (p : LightPoint d N)

def IA : Covariance.Mat N := interaction 384 p.A p.l p.X
def IB : Covariance.Mat N := interaction 384 p.A p.m p.Y
def wP (i : Fin N) : ℝ := p.l i*p.pp i
def wQ (i : Fin N) : ℝ := p.m i*p.qq i
def s0 : ℝ := p.ε/40000
def J : ℝ := 1+(3*(N : ℝ))^2/p.s0
def E0 : ℝ := 2*p.J^2*(1+3*(N : ℝ))^2
def C1 : ℝ := max 1 (max (48*p.E0/23) (4*(1+9*(N : ℝ)^2)))

end
end CurrentKS.State.LightPoint

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_StateR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State.LightPoint
noncomputable section
open Matrix CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Interaction CurrentKS.Covariance
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ} (p : LightPoint d N)

def R (y : Coordinates N) : ℝ := value p.ε (p.fixedPart+S p.A y) (eta 384 p.A y)
def tildeA (i : Fin N) : ℝ := p.l i*p.a i
def tildeB (i : Fin N) : ℝ := p.m i*p.b i
def resp (v : Covariance.E (2*N)) : Coordinates N := fun i => responseLin p.IB v i
def direction (v : Covariance.E (2*N)) : Coordinates N := fun i => p.resp v i/p.T i
def invEnergy (v : Covariance.E (2*N)) : ℝ := energy p.X p.Y p.P p.Q
  (sandwich p.X (responseInput p.A p.l (fstVec v)))
  (sandwich p.Y (responseInput p.A p.m (sndVec v)))

end
end CurrentKS.State.LightPoint

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_StatePsi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State.LightPoint
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Interaction CurrentKS.Covariance
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d N : ℕ} (p : LightPoint d N)

def Psi (lam : ℝ) (y : Coordinates N) : ℝ := p.R y+lam*penalty y

def omega (Γ : Covariance.Mat (2*N)) (i : Fin N) : ℝ :=
  ∑ j, (p.resp (column (CFC.sqrt Γ) j) i)^2

def mu (Γ : Covariance.Mat (2*N)) : Coordinates N :=
  fun i => Progress.drift (p.T i) (p.tildeA i) (p.tildeB i) (p.omega Γ i)

def dirs (Γ : Covariance.Mat (2*N)) (j : Fin (2*N)) : Coordinates N :=
  p.direction (column (CFC.sqrt Γ) j)

def driftCurvature (f : Coordinates N → ℝ) (Γ : Covariance.Mat (2*N)) : ℝ :=
  deriv (fun s => f (line p.x (p.mu Γ) s)) 0+
    (1/2 : ℝ)*(∑ j,deriv (deriv (fun s => f (line p.x (p.dirs Γ j) s))) 0)

end
end CurrentKS.State.LightPoint

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_Pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Matrix

namespace KS.W07

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

def pivotRow (b : n → K) : Matrix Unit n K := fun _ j => b j

def pivotSchur (a : K) (b : n → K) (D : Matrix n n K) : Matrix n n K :=
  fun i j => D i j - b i * b j / a

def pivotWitnessLift (a : K) (b y : n → K) : Unit ⊕ n → K :=
  Sum.elim (fun _ => -(a⁻¹ * ∑ j, b j * y j)) y

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_FinPivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Matrix

namespace KS.W07

def pivotIndexEquiv (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n + 1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (Sum.inl ()) Sum.inr
  left_inv := by
    intro i
    cases i with
    | inl i => cases i; rfl
    | inr i => rfl
  right_inv := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PSDSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

open Matrix

noncomputable def psdCutEvalReal {n : ℕ} (q : Fin n → ℚ) (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  -((fun i => (q i : ℝ)) ⬝ᵥ (M *ᵥ (fun i => (q i : ℝ))))

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_SqSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalRoot
open scoped BigOperators

variable {N : ℕ}

noncomputable def realVector (v : Fin N → ℚ) : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 fun i => (v i:ℝ)

end CurrentKS.RationalRoot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_ShiftedHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalRoot
open Matrix
open scoped BigOperators

variable {N : ℕ}

noncomputable def realQuadratic (H : Matrix (Fin N) (Fin N) ℚ)
    (u : EuclideanSpace ℝ (Fin N)) : ℝ :=
  u ⬝ᵥ ((H.map fun t : ℚ => (t:ℝ)) *ᵥ u)

end CurrentKS.RationalRoot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_RationalBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Difference
open Set Matrix
open scoped BigOperators ContDiff

variable {N : ℕ}

noncomputable def realBasis (i : Fin N) : Fin N → ℝ := Pi.single i 1

def pointCast (x : Fin N → ℚ) : Fin N → ℝ := fun i => (x i:ℝ)

end CurrentKS.Difference

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_EuclideanForget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Difference
open scoped ContDiff

variable {N : ℕ}

noncomputable def euclideanForget : EuclideanSpace ℝ (Fin N) →L[ℝ] (Fin N → ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)).toContinuousLinearMap

noncomputable def euclideanBilinear
    (B : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ :=
  (B.flip.comp euclideanForget).flip.comp euclideanForget

open CurrentKS.RationalRoot Matrix Set

end CurrentKS.Difference

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_FacePotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Scalar CurrentKS.Calculus
open scoped BigOperators ContDiff

variable {d N : ℕ}

open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff


def facePotential (ε lam : ℝ) (S₀ : H d) (A : Fin N → H d) (x : Coordinates N) : ℝ :=
  value ε (S₀+S A x) (eta 384 A x)+lam*penalty x

def valueCurve2Bound (d N : ℕ) (ε σ : ℝ) : ℝ :=
  let B := coarseBudget d N ε σ
  let Jb := 10^18*((d:ℝ)+1)*(1+ε⁻¹)^4
  let D := 300*B^5
  (1+|ε| *(2*((d:ℝ)+1)))*(Jb*D*(1+Jb*D)^2)

def valueCurve3Bound (d N : ℕ) (ε σ : ℝ) : ℝ :=
  let B := coarseBudget d N ε σ
  let Jb := 10^18*((d:ℝ)+1)*(1+ε⁻¹)^4
  let D := 300*B^5
  (1+|ε| *(2*((d:ℝ)+1)))*
    (Jb*D*((1+Jb*D)^3+3*(1+Jb*D)*(Jb*D*(1+Jb*D)^2)))

def potentialCurveBound (d N : ℕ) (ε σ lam : ℝ) : ℝ :=
  1+valueCurve2Bound d N ε σ+valueCurve3Bound d N ε σ+|lam| *(N:ℝ)*(1+800/σ^3)

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Potential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

def potential (c ε lam : ℝ) (A : Fin N → H d) (x : Coordinates N) : ℝ :=
  value ε (S A x) (eta c A x)+lam*∑ i,psi (x i)

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_RealVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open scoped BigOperators RealInnerProductSpace
open Set

variable {n m : ℕ}

noncomputable def realVector (y : Fin n → ℚ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => (y i : ℝ))

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_ObjectiveCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Set

variable {n m : ℕ}

def objectiveCLM (f : Fin n → ℚ) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  innerSL ℝ (realVector f)

end
end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_BinaryEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W01

abbrev RationalComplex := ℚ × ℚ

end KS.W01

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_ComplexBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W01

def toComplex (z : RationalComplex) : ℂ := ⟨(z.1 : ℝ), (z.2 : ℝ)⟩

@[simp] theorem toComplex_re (z : RationalComplex) : (toComplex z).re = (z.1 : ℝ) := rfl
@[simp] theorem toComplex_im (z : RationalComplex) : (toComplex z).im = (z.2 : ℝ) := rfl

end KS.W01

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_Realification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08

open Matrix
open scoped BigOperators

def embedComplexMatrix {m n : Type*} (A : Matrix m n KS.W01.RationalComplex) : Matrix m n ℂ :=
  Matrix.of (fun i j => KS.W01.toComplex (A i j))

@[simp] theorem embedComplexMatrix_apply {m n : Type*}
    (A : Matrix m n KS.W01.RationalComplex) (i : m) (j : n) :
    embedComplexMatrix A i j = KS.W01.toComplex (A i j) := rfl

def realify {m n : Type*} (A : Matrix m n ℂ) : Matrix (m ⊕ m) (n ⊕ n) ℝ :=
  Matrix.fromBlocks (fun i j => (A i j).re) (fun i j => -(A i j).im)
    (fun i j => (A i j).im) (fun i j => (A i j).re)

@[simp] theorem realify_one {n : Type*} [DecidableEq n] :
    realify (1 : Matrix n n ℂ) = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [realify, Matrix.fromBlocks, Matrix.one_apply] <;> split_ifs <;> rfl

def realifyVector {n : Type*} (v : n → ℂ) : n ⊕ n → ℝ :=
  Sum.elim (fun i => (v i).re) (fun i => (v i).im)

end KS.W08

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_RealificationSPD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08

open Matrix
open scoped ComplexOrder BigOperators

def complexifyVector {n : Type*} (x : n ⊕ n → ℝ) : n → ℂ :=
  fun i => ⟨x (Sum.inl i), x (Sum.inr i)⟩

@[simp] theorem realifyVector_complexify {n : Type*} (x : n ⊕ n → ℝ) :
    realifyVector (complexifyVector x) = x := by
  funext i
  cases i <;> rfl

@[simp] theorem realifyVector_zero {n : Type*} : realifyVector (0 : n → ℂ) = 0 := by
  funext i
  cases i <;> rfl

end KS.W08

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Affine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix
open scoped BigOperators

variable {n m p : ℕ}

lemma vector_eq_sum_single {R : Type*} [Semiring R] (x : Fin n → R) :
    x=∑ i : Fin n,x i • (Pi.single i 1 : Fin n → R) := by
  classical
  ext j
  simp [Pi.single_apply]

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_FinRealify
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix CurrentKS.HermitianCoordinates KS.W08
open scoped BigOperators ComplexOrder

variable {n m p d N : ℕ}

noncomputable def finRealify (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (d+d)) (Fin (d+d)) ℝ :=
  (realify A).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

noncomputable def complexSum (coords : Fin N → Fin d × Fin d → ℝ) (x : Fin N → ℝ) :
    Matrix (Fin d) (Fin d) ℂ := ∑ i,x i • decode (coords i)
noncomputable def complexEta (coords : Fin N → Fin d × Fin d → ℝ) (θ : Fin N → ℝ)
    (Z : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ i,(384*θ i) • (decode (coords i)*Z*decode (coords i))

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_ComplexValueProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix CurrentKS.HermitianCoordinates
open scoped BigOperators ComplexOrder

variable {d N : ℕ}

def complexValueProgram (ε : ℝ) (S : Matrix (Fin d) (Fin d) ℂ)
    (η : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (t : ℝ) (X Y : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (Matrix.fromBlocks (t • (1 : Matrix (Fin d) (Fin d) ℂ)-S-η Y) 1 1 X).PosSemidef ∧
  (Matrix.fromBlocks (t • (1 : Matrix (Fin d) (Fin d) ℂ)+S-η X) 1 1 Y).PosSemidef ∧
  (X-(1/400:ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef ∧
  ((200/ε) • (1 : Matrix (Fin d) (Fin d) ℂ)-X).PosSemidef ∧
  (Y-(1/400:ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef ∧
  ((200/ε) • (1 : Matrix (Fin d) (Fin d) ℂ)-Y).PosSemidef ∧ 0 ≤ t ∧ t ≤ 100

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_SchurBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

def schurBlock (T X : H d) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ :=
  Matrix.fromBlocks (T : Mat d) 1 1 (X : Mat d)

def valueBlock₁ (S : H d) (η : H d →L[ℝ] H d) (z : Point d) :=
  schurBlock (z.1 • (Hermitian.one : H d)-S-η z.2.2) z.2.1

def valueBlock₂ (S : H d) (η : H d →L[ℝ] H d) (z : Point d) :=
  schurBlock (z.1 • (Hermitian.one : H d)+S-η z.2.1) z.2.2

def oracleBox (ε : ℝ) (z : Point d) : Prop :=
  z.1 ∈ Icc 0 100 ∧
  ((1/400 : ℝ) • (Hermitian.one : H d) ≤ z.2.1 ∧ z.2.1 ≤ (200/ε) • Hermitian.one) ∧
  ((1/400 : ℝ) • (Hermitian.one : H d) ≤ z.2.2 ∧ z.2.2 ≤ (200/ε) • Hermitian.one)

def valueSpectrahedron (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d) : Set (Point d) :=
  {z | oracleBox ε z ∧ (valueBlock₁ S η z).PosSemidef ∧ (valueBlock₂ S η z).PosSemidef}

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_OperatorNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian

section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {d : ℕ}

def operatorNorm (A : H d) : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A : Mat d)‖

end

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ParameterCube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

def ParameterCube (θ : Coordinates N) : Prop := ∀ i, 0 ≤ θ i ∧ θ i ≤ 1

def etaTheta (c : ℝ) (A : Fin N → H d) (θ : Coordinates N) : H d →L[ℝ] H d :=
  ∑ i, (c*θ i) • sandwichCLM (A i)

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_RationalAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.RationalSDP
open CurrentKS.Hermitian CurrentKS.HermitianCoordinates CurrentKS.Variational CurrentKS.State
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

def rationalAtoms (coords : Fin N → Fin d × Fin d → ℚ) (i : Fin N) : H d :=
  assemble (WithLp.toLp 2 fun j => (coords i j:ℝ))

end CurrentKS.RationalSDP

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Transition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
open CurrentKS.RationalSDP CurrentKS.Difference

variable {d N : ℕ}

def StripCube (σ : ℚ) (x : Fin N → ℚ) : Prop :=
  (∀ i,|x i| ≤ 1) ∧ ∀ i,|x i|<1 → |x i| ≤ 1-σ

noncomputable section
open CurrentKS.Hermitian CurrentKS.State CurrentKS.Variational CurrentKS.Scalar
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

def fullPotential (coords : Fin N → Fin d × Fin d → ℚ) (ν lam : ℚ) (x : Fin N → ℚ) : ℝ :=
  potential 384 ((ν/(d:ℚ):ℚ):ℝ) (lam:ℝ) (rationalAtoms coords) (pointCast x)

end
end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_VarianceH
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

def varianceH (A : Fin N → H d) : H d := ∑ i,sandwich (A i) (Hermitian.one : H d)

def jointObjective (ε lam : ℝ) (w : Coordinates N × Point d) : ℝ :=
  objective ε w.2+lam*(∑ i,psi (w.1 i))

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_GlobalCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.RationalSDP
variable {n d : ℕ}

def queryDimensionBound (B : ℕ) : ℕ := 1+2*B^2
def queryOuterBound (B : ℕ) : ℕ := (queryDimensionBound B+1)*(100+400*B*(B+1))
def queryLipschitzBound (B : ℕ) : ℕ := (queryDimensionBound B+1)*(1+2*B)
def queryInnerInvBound (B : ℕ) : ℕ := 4000*(B^2+1)
def queryNearInvBound (B : ℕ) : ℕ :=
  queryLipschitzBound B*(2*queryOuterBound B+1)*B*queryInnerInvBound B
def querySearchBound (B : ℕ) : ℕ :=
  4*(queryOuterBound B)^2*(queryNearInvBound B*(queryDimensionBound B+1))^2+1

def queryScanBound (B : ℕ) : ℕ := (200*B+4)*querySearchBound B

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialMatrixFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization

def QParts (H : ℕ) (q : ℚ) : Prop := q.num.natAbs≤2^H ∧ q.den≤2^H

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_RationalGridBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.RationalGridSize

def Grid (D : ℕ) (q : ℚ) : Prop := q.den ∣ D

open scoped BigOperators

def bitSize (q : ℚ) : ℕ := q.num.natAbs.size+q.den.size

end CurrentKS.RationalGridSize

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_StoredBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.ScheduleBits
open CurrentKS.RationalBits

abbrev Args := Fin 4 → ℚ
def eps (x:Args) := x 2/x 0
def strip (x:Args) := (x 3)^2/x 2
def movement (x:Args) : ℚ :=
  let s₀ := eps x/40000
  let J := 1+(3*x 1)^2/s₀
  let E₀ := 2*J^2*(1+3*x 1)^2
  max 1 (max (48*E₀/23) (4*(1+9*(x 1)^2)))
def coarse (x:Args) : ℚ :=
  200+(x 0+1)+|eps x|+(200/eps x)*(x 0+1)+200*(x 0+1)+
    ((x 0+1)+x 1)+384*x 1*(1+800/(strip x)^3)
def jacobian (x:Args) : ℚ := 10^18*(x 0+1)*(1+(eps x)⁻¹)^4
def derivative (x:Args) : ℚ := 300*(coarse x)^5
def second (x:Args) : ℚ :=
  (1+|eps x| *(2*(x 0+1)))*(jacobian x*derivative x*(1+jacobian x*derivative x)^2)
def third (x:Args) : ℚ :=
  (1+|eps x| *(2*(x 0+1)))*(jacobian x*derivative x*
    ((1+jacobian x*derivative x)^3+3*(1+jacobian x*derivative x)*
      (jacobian x*derivative x*(1+jacobian x*derivative x)^2)))
def curvature (x:Args) : ℚ :=
  1+second x+third x+|x 3| *x 1*(1+800/(strip x)^3)
def threshold (x:Args) : ℚ := x 3/(512*(movement x)^2)
def step (x:Args) : ℚ := min (strip x/4) (min (threshold x/(4*curvature x)) (1/4))
def mesh (x:Args) : ℚ := step x*threshold x/(4096*curvature x*x 1)

def args (d n : ℕ) (ν lam:ℚ) : Args := ![d,n,ν,lam]
end CurrentKS.ScheduleBits

namespace CurrentKS.RationalFace
open CurrentKS.RationalBits CurrentKS.RationalRoot CurrentKS.RationalSDP
open scoped BigOperators

variable {d N : ℕ}

def baseBits (d N : ℕ) : ℕ := d.size+N.size+2*(1000*N*d^2).size+1+(200*N).size

end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_FlattenLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization

lemma getD_flatten_ofFn {α : Type*} {n m : ℕ} (rows : Fin n → List α)
    (hl : ∀ i,(rows i).length=m) (i : Fin n) (j : ℕ) (hj : j < m) (d : α) :
    (List.ofFn rows).flatten.getD (i.val*m+j) d=(rows i).getD j d := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [List.ofFn_succ,List.flatten_cons]
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [Fin.val_zero,Nat.zero_mul,Nat.zero_add]
      exact List.getD_append _ _ _ _ (by simpa only [hl] using hj)
    · rw [List.getD_append_right _ _ _ _ (by rw [hl];simp only [Fin.val_succ,Nat.add_mul,Nat.one_mul];omega)]
      simp only [hl,Fin.val_succ]
      have he : (k.val+1)*m+j-m=k.val*m+j := by simp only [Nat.add_mul,Nat.one_mul];omega
      rw [he]
      exact ih (fun i => rows i.succ) (fun i => hl i.succ) k

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_MatrixStructureRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open Matrix
open scoped BigOperators

variable {α : Type*}

lemma ofFn_sum {n m : ℕ} (f : Fin (n+m) → α) :
    List.ofFn f=List.ofFn (fun i : Fin n => f (finSumFinEquiv (.inl i)))++
      List.ofFn (fun j : Fin m => f (finSumFinEquiv (.inr j))) := by
  exact List.ofFn_add (f := f)

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FaceArrayRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization

def activeData (xs : List ℚ) : List ℕ :=
  (List.range xs.length).filter (fun j => decide (|xs.getD j 0| < 1))

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ValueDataRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open Matrix
open scoped BigOperators

def coordinateIndex (second : Bool) (p : (ℕ×ℕ)×ℕ) : ℕ :=
  1+(if second then p.1.1*p.1.1 else 0)+(p.2+p.1.1*p.1.2)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ValueEvalRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open Matrix
open scoped BigOperators

def eyeData (n : ℕ) := (List.range n).map (fun i => (List.range n).map (fun j => if i=j then (1:ℚ) else 0))

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ValueQueryRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization

structure ValueQueryParams where
  d : ℕ
  N : ℕ
  coords : Fin N → Fin d×Fin d → ℚ
  x : Fin N → ℚ
  theta : Fin N → ℚ
  nu : ℚ
  delta : ℚ

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_PotentialRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open scoped BigOperators

structure PotentialParams where
  d : ℕ
  N : ℕ
  coords : Fin N → Fin d×Fin d → ℚ
  x : Fin N → ℚ
  nu : ℚ
  lam : ℚ
  error : ℚ

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FaceQueryRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization

def gatherData (p : List ℚ×List ℕ) : List ℚ := p.2.map (fun i => p.1.getD i 0)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_StencilRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization

variable {α : Type*}

lemma vectorNeg_ofFn {n : ℕ} (v : Fin n → ℚ) :
    (List.ofFn v).map (fun q => -q)=List.ofFn (-v) := by simp; rfl
lemma vectorScale_ofFn {n : ℕ} (t : ℚ) (v : Fin n → ℚ) :
    (List.ofFn v).map (fun q => t*q)=List.ofFn (t • v) := by simp;rfl

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_CurvatureRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open scoped BigOperators

def squareSumData (v : List ℚ) : ℚ := (v.map (fun q => q^2)).sum

def initialScaleData (v : List ℚ) := v.map (fun x => x/(1+squareSumData v))

structure CurvatureParams where
  n : ℕ
  H : Matrix (Fin n) (Fin n) ℚ
  a : ℚ
  M : ℚ
  s : ℚ
  rho : ℚ

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Coarea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uE uV2 uE2 uV3 uE3 uI uI2 uI3

section
open scoped Classical
open Matrix

namespace StrongThinTree.Geometry
noncomputable section
open Finset MeasureTheory Set

def clamp (a b x : ℝ) : ℝ := min b (max a x)

end
end StrongThinTree.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_SpectralPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uι uι2 uV uι3 uV2 uV3 uV4 uV5 uV6 uι4 uη

section
open scoped Classical
open Matrix

namespace StrongThinTree.Spectral
noncomputable section
open Finset LinearMap
open scoped InnerProductSpace
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def frobSq (T : E →ₗ[ℝ] E) : ℝ := LinearMap.trace ℝ E (T.adjoint ∘ₗ T)

end
end StrongThinTree.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Hierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset
variable {n m : ℕ} (G : MultiGraph n m)

def inducedEdges (A : Finset (Fin n)) : Finset (Fin m) :=
  univ.filter (fun e => G.left e ∈ A ∧ G.right e ∈ A)

def EdgeConnectedReal (A : Finset (Fin n)) (q : ℝ) : Prop :=
  ∀S : Finset (Fin n), S.Nonempty → S ⊂ A → q ≤ (G.cut (G.inducedEdges A) S).card

lemma mem_inducedEdges (A : Finset (Fin n)) (e : Fin m) :
    e ∈ G.inducedEdges A ↔ G.left e ∈ A ∧ G.right e ∈ A := by simp [inducedEdges]

def VertexPartition (A : Finset (Fin n)) (P : Finset (Finset (Fin n))) : Prop :=
  (∀B ∈ P, B.Nonempty ∧ B ⊆ A) ∧
  (P : Set (Finset (Fin n))).Pairwise Disjoint ∧ P.biUnion id = A

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset
variable {n m : ℕ} (G : MultiGraph n m)

def endpointMass (A : Finset (Fin n)) (e : Fin m) : ℝ :=
  (if G.left e ∈ A then 1 else 0)+(if G.right e ∈ A then 1 else 0)

def volume (R A : Finset (Fin n)) : ℝ := ∑e ∈ G.inducedEdges R, G.endpointMass A e

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset

structure Hierarchy (n : ℕ) where
  nodes : Finset (Finset (Fin n))
  nonempty : ∀A ∈ nodes, A.Nonempty
  root_mem : univ ∈ nodes
  singletons : ∀v, {v} ∈ nodes
  laminar : ∀A ∈ nodes, ∀B ∈ nodes, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B
  parent : Finset (Fin n) → Finset (Fin n)
  parent_mem : ∀A ∈ nodes, A ≠ univ → parent A ∈ nodes
  parent_strict : ∀A ∈ nodes, A ≠ univ → A ⊂ parent A
  parent_minimal : ∀A ∈ nodes, A ≠ univ → ∀B ∈ nodes, A ⊂ B → parent A ⊆ B

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Records
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n h : ℕ} (H : Hierarchy n)

def domain (A : Finset (Fin n)) (P : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  H.nodes.filter (fun B => B ⊆ A ∧ ∀S ∈ P, ¬B ⊆ S)

def leaves (_H : Hierarchy n) (A : Finset (Fin n)) (P : Finset (Finset (Fin n))) : Finset (Fin n) :=
  A\P.biUnion id

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

def parentBoundary (A : Finset (Fin n)) : Finset (Fin m) :=
  G.cut (G.inducedEdges (H.parent A)) A

def LocallyConnectedReal (q : ℝ) : Prop := ∀A ∈ H.nodes, G.EdgeConnectedReal A q

end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Selection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uU uI

section
open scoped Classical
open Matrix

namespace StrongThinTree.AssignedAccounting
noncomputable section

def base (avoiding : Bool) (R δ : ℝ) : ℝ :=
  max (R-3*δ) 0 / (if avoiding then 10 else 1)

def fresh (δ ε : ℝ) : ℝ := δ-3*ε

def theta : ℝ := 1/512

end
end StrongThinTree.AssignedAccounting

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Truncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2 uE3 uE4

section
open scoped Classical
open Matrix

namespace StrongThinTree.Truncation
noncomputable section
open Finset
open scoped Classical
variable {E : Type uE2} [DecidableEq E]

def dyadicIndex (L x : ℝ) : ℕ := ⌊Real.logb 2 (x/L)⌋₊

end
end StrongThinTree.Truncation

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
open scoped Classical
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}

def truncationBins (α : ℝ) : ℕ := 1+⌈Real.logb 2 (256/α^2)⌉₊
def truncationGain (α : ℝ) : ℝ := 1/(4*(truncationBins α:ℝ)^4)

end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Duality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uJ uV uI2 uI3 uV2 uW uJ2 uV3 uE2 uT uJ3 uH uI4

section

namespace StrongThinTree.Duality
noncomputable section
open Finset
open scoped Classical
variable {E : Type uE} {I : Type uI} [AddCommGroup E] [Module ℝ E] [Fintype I]

def strictUpperImage (S : Set E) (F : I → E → ℝ) : Set (I → ℝ) :=
  {v | ∃x ∈ S, ∀i, F i x < v i}

end
end StrongThinTree.Duality

namespace StrongThinTree.ShortcutDual
noncomputable section
open Matrix Finset Filter Topology
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {V : Type uV3} {E : Type uE2} {T : Type uT} {J : Type uJ3} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype T] [Fintype J]

def boundaryMatrix (b : E → V → ℝ) (O : T → Finset E) (t : T) : Matrix V V ℝ :=
  ((O t).card : ℝ)⁻¹ • ∑e ∈ O t, vecMulVec (b e) (b e)

def boundaryAverage (b : E → V → ℝ) (O : T → Finset E) (t : T)
    (D : Matrix V V ℝ) : ℝ :=
  ((O t).card : ℝ)⁻¹ * ∑e ∈ O t, b e ⬝ᵥ (D⁻¹ *ᵥ b e)

def objectiveMatrix (b : E → V → ℝ) (O : T → Finset E) (lam : T → ℝ) : Matrix V V ℝ :=
  ∑t, lam t • boundaryMatrix b O t

def edgeWeight (O : T → Finset E) (lam : T → ℝ) (e : E) : ℝ :=
  Real.sqrt (∑t, if e ∈ O t then lam t / ((O t).card : ℝ) else 0)

end
end StrongThinTree.ShortcutDual

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_ShortcutDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Matrix Finset StrongThinTree.Geometry
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {n m h : ℕ} (G : MultiGraph n m)

def cutIndicator (S : Finset (Fin n)) (v : Fin n) : ℝ := if v ∈ S then 1 else 0

namespace Hierarchy
variable {G : MultiGraph n m} {H : Hierarchy n}

def shortcutCoefficient (q L R : ℕ) (α ε : ℝ) : ℝ :=
  2*α+2*(R:ℝ)*(L:ℝ)/(((q:ℝ)/8192)*((α*truncationGain α/32)^ε/(6912*(1024/ε^2)))*truncationGain α)

end Hierarchy
end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

section
open Matrix
namespace StrongThinTree
section Resistance
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma quadratic_cauchy_schwarz {X : Matrix ι ι ℝ} (hX : X.PosSemidef)
    (x y : ι → ℝ) :
    (x ⬝ᵥ (X *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (X *ᵥ x)) * (y ⬝ᵥ (X *ᵥ y)) := by
  let := X.toSeminormedAddCommGroup hX
  let := X.toInnerProductSpace hX
  have h := real_inner_mul_inner_self_le x y
  change ((X *ᵥ y) ⬝ᵥ star x) * ((X *ᵥ y) ⬝ᵥ star x) ≤
    ((X *ᵥ x) ⬝ᵥ star x) * ((X *ᵥ y) ⬝ᵥ star y) at h
  simpa only [star_trivial, dotProduct_comm, pow_two] using h

end Resistance
end StrongThinTree

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_GraphMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree
variable {V : Type uV} [Fintype V] [DecidableEq V]
def qform (X : Matrix V V ℝ) (v : V → ℝ) : ℝ := v ⬝ᵥ (X *ᵥ v)
omit [DecidableEq V] in
lemma qform_nonneg {X : Matrix V V ℝ} (hX : X.PosSemidef) (v : V → ℝ) : 0 ≤ qform X v := by
  simpa only [qform,star_trivial] using hX.dotProduct_mulVec_nonneg v
omit [DecidableEq V] in
lemma qform_continuous (v : V → ℝ) : Continuous (fun X : Matrix V V ℝ => qform X v) := by
  unfold qform mulVec dotProduct
  fun_prop
lemma qform_single (X : Matrix V V ℝ) (i : V) : qform X (Pi.single i 1)=X i i := by
  simp [qform]
end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_MatrixDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder Matrix.Norms.Elementwise
namespace StrongThinTree
variable {V : Type uV} [Fintype V] [DecidableEq V]
omit [DecidableEq V] in
lemma isClosed_psd : IsClosed {X : Matrix V V ℝ | X.PosSemidef} := by
  have heq : {X : Matrix V V ℝ | X.PosSemidef}=
      {X | X.IsHermitian} ∩ ⋂v : V → ℝ, {X | 0 ≤ qform X v} := by
    ext X
    simp only [Set.mem_ofPred,Set.mem_inter_iff,Set.mem_iInter]
    exact ⟨fun h => ⟨h.isHermitian,qform_nonneg h⟩,fun h =>
      Matrix.PosSemidef.of_dotProduct_mulVec_nonneg h.1 (by simpa only [star_trivial,qform] using h.2)⟩
  rw [heq]
  apply IsClosed.inter
  · exact isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  · exact isClosed_iInter (fun v => isClosed_le continuous_const (qform_continuous v))
lemma psd_entry_bound {X : Matrix V V ℝ} (hX : X.PosSemidef) {C : ℝ} (hC : 0 ≤ C)
    (hdiag : ∀i, X i i ≤ C) (i j : V) : |X i j| ≤ C := by
  have hi : 0 ≤ X i i := by simpa only [qform_single] using qform_nonneg hX (Pi.single i 1)
  have hj : 0 ≤ X j j := by simpa only [qform_single] using qform_nonneg hX (Pi.single j 1)
  have hh := quadratic_cauchy_schwarz hX (Pi.single i 1) (Pi.single j 1)
  simp only [mulVec_single_one,single_one_dotProduct] at hh
  change (X i j)^2 ≤ X i i*X j j at hh
  have hm := mul_le_mul (hdiag i) (hdiag j) hj hC
  nlinarith [sq_abs (X i j),abs_nonneg (X i j)]

end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_HierarchyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Finset Filter
open scoped Topology
namespace StrongThinTree.ShortcutNumeric
open MultiGraph.Hierarchy

def alpha (x : ℝ) : ℝ := x^(-4/5:ℝ)
def gamma (x : ℝ) : ℝ := truncationGain (alpha x)
def scale (x : ℝ) : ℝ := alpha x*gamma x/32
def rho (x : ℝ) : ℝ := 1/(2*x^2)
def count (x : ℝ) : ℕ := ⌈x^(1/100:ℝ)⌉₊

def coefficient (x : ℝ) : ℝ :=
  2*alpha x+2*(count x:ℝ)*(count x:ℝ)/
    ((x/8192)*((scale x)^(1/10:ℝ)/(6912*(1024/(1/10:ℝ)^2)))*gamma x)

def largeConstant : ℝ := 8*8192*6912*102400

structure GoodParameters (x : ℝ) : Prop where
  large : 2 ≤ x
  small : (scale x)^(1/10:ℝ) ≤ 1/(1728*(1024/(1/10:ℝ)^2))
  assignment : 6144/x ≤ (scale x)^(1+2*(1/10:ℝ))
  rho_small : rho x ≤ 1/1536
  log_left : Real.logb 2 (16/(alpha x*gamma x))+1 < (count x:ℝ)
  log_right : Real.logb 2 (24/(rho x*(scale x)^2)) < (count x:ℝ)
  coefficient_small : coefficient x ≤ x^(-31/40:ℝ)/2

end StrongThinTree.ShortcutNumeric

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_BasePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uV uI2

section

noncomputable section
open Finset Submodule
namespace StrongThinTree.Packing

variable {E : Type uE} {I : Type uI} {V : Type uV} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

abbrev span (v : E → V) (s : Finset E) : Submodule ℝ V :=
  Submodule.span ℝ (v '' (s : Set E))

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma mem_span_self (v : E → V) {s : Finset E} {e : E} (he : e ∈ s) :
    v e ∈ span v s := Submodule.subset_span ⟨e, he, rfl⟩

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma span_le_iff (v : E → V) {s : Finset E} {W : Submodule ℝ V} :
    span v s ≤ W ↔ ∀ e ∈ s, v e ∈ W := by
  rw [Submodule.span_le]
  constructor
  · intro h e he; exact h ⟨e, he, rfl⟩
  · rintro h x ⟨e, he, rfl⟩; exact h e he

def Valid (v : E → V) (F : I → Finset E) : Prop :=
  (∀ i, LinearIndepOn ℝ v (F i : Set E)) ∧ Pairwise (fun i j => Disjoint (F i) (F j))

abbrev State (v : E → V) (I : Type uI2) [Fintype I] := {F : I → Finset E // Valid v F}

def cost {v : E → V} (F : State v I) : ℕ := ∑ i, (F.1 i).card

def unused {v : E → V} (F : State v I) (e : E) : Prop := ∀ i, e ∉ F.1 i

def Move {v : E → V} (F F' : State v I) : Prop :=
  ∃ i e f, unused F e ∧ f ∈ F.1 i ∧
    F'.1 = Function.update F.1 i (insert e ((F.1 i).erase f))

def recycled {v : E → V} (F : State v I) : Finset E := by
  classical
  exact Finset.univ.filter fun e => ∃ F', Relation.ReflTransGen Move F F' ∧ unused F' e

end StrongThinTree.Packing

namespace StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)

def crossing (T : Finset (Fin m)) (p : Fin n → Fin n) : Finset (Fin m) :=
  T.filter fun e => p (G.left e) ≠ p (G.right e)

def partitionSize (p : Fin n → Fin n) : ℕ := (Finset.univ.image p).card

def TreePackable (T : Finset (Fin m)) (r : ℕ) : Prop :=
  ∃ F : Fin r → Finset (Fin m),
    (∀ i, F i ⊆ T ∧ G.SpanningTree (F i)) ∧ Pairwise (fun i j => Disjoint (F i) (F j))

end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_ScalarRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar realization. -/

section

namespace CurrentKS.Realization

abbrev SquareScan := ℕ×(ℚ×List ℚ)

def squareScanStep (p : SquareScan) : SquareScan :=
  (p.1/4,(2*p.2.1,p.2.2++List.replicate (p.1%4) p.2.1))

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_PartitionRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uV uE2 uV2

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset Submodule
variable {n m : ℕ} (G : MultiGraph n m)

def internal (F : Finset (Fin m)) (A : Finset (Fin n)) : Finset (Fin m) :=
  F.filter (fun e => G.left e ∈ A ∧ G.right e ∈ A)

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_HierarchyBuilder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset
variable {n : ℕ}

structure PartitionChain (n : ℕ) where
  parts : ℕ → Finset (Finset (Fin n))
  partition : ∀i, VertexPartition univ (parts i)
  coarsens : ∀i j, i ≤ j → ∀A ∈ parts i, ∃B ∈ parts j, A ⊆ B

namespace PartitionChain
variable (P : PartitionChain n)

lemma part_exists (i : ℕ) (v : Fin n) : ∃A ∈ P.parts i, v ∈ A := by
  have hv : v ∈ (P.parts i).biUnion id := (P.partition i).2.2.symm ▸ mem_univ v
  exact mem_biUnion.mp hv

def nodes (I : Finset ℕ) : Finset (Finset (Fin n)) :=
  I.biUnion P.parts ∪ univ.image (fun v : Fin n => {v})

end PartitionChain
end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_ChainEdges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.MultiGraph.PartitionChain
noncomputable section
open Finset
variable {n m : ℕ} (P : PartitionChain n) (G : MultiGraph n m)

def block (i : ℕ) (v : Fin n) : Finset (Fin n) := (P.part_exists i v).choose

def crossing (i : ℕ) : Finset (Fin m) := univ.filter (fun e => P.block i (G.left e) ≠ P.block i (G.right e))

end
end StrongThinTree.MultiGraph.PartitionChain

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_Profiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric profiles. -/

section

noncomputable section

namespace AlgorithmicThinTrees.MetricProfiles

open Finset Set

section Profiles

variable {V : Type*} [Fintype V] [PseudoMetricSpace V]

def profile (x : V) : V → ℝ := fun z => dist x z

def polytope : Set (V → ℝ) := convexHull ℝ (Set.range (profile (V := V)))

end Profiles

section Double

variable (V : Type*) [Fintype V] [PseudoMetricSpace V]

def commonRadius : ℝ := 1 + 2 * ∑ x : V, ∑ y : V, dist x y

lemma commonRadius_pos : 0 < commonRadius V := by
  have h : 0 ≤ ∑ x : V, ∑ y : V, dist x y :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => dist_nonneg
  unfold commonRadius
  linarith

lemma twice_dist_lt_commonRadius (x y : V) : 2 * dist x y < commonRadius V := by
  have h₁ : dist x y ≤ ∑ z : V, dist x z :=
    single_le_sum (fun z _ => (dist_nonneg : (0 : ℝ) ≤ dist x z)) (mem_univ y)
  have h₂ : (∑ z : V, dist x z) ≤ ∑ u : V, ∑ z : V, dist u z :=
    single_le_sum (fun u _ => sum_nonneg fun z _ =>
      (dist_nonneg : (0 : ℝ) ≤ dist u z)) (mem_univ x)
  unfold commonRadius
  linarith

@[ext]
structure Doubled where
  sign : Bool
  point : V
  deriving Fintype

variable {V}

def doubledDist (a b : Doubled V) : ℝ :=
  if a.sign = b.sign then dist a.point b.point
  else commonRadius V - dist a.point b.point

lemma doubledDist_self (a : Doubled V) : doubledDist a a = 0 := by
  simp [doubledDist]

lemma doubledDist_comm (a b : Doubled V) : doubledDist a b = doubledDist b a := by
  simp only [doubledDist, eq_comm, dist_comm]

lemma doubledDist_triangle (a b c : Doubled V) :
    doubledDist a c ≤ doubledDist a b + doubledDist b c := by
  have hab := twice_dist_lt_commonRadius V a.point b.point
  have hbc := twice_dist_lt_commonRadius V b.point c.point
  have hac := twice_dist_lt_commonRadius V a.point c.point
  have hR := commonRadius_pos V
  have h₁ := dist_triangle a.point b.point c.point
  have h₂ := dist_triangle a.point c.point b.point
  have h₃ := dist_triangle b.point a.point c.point
  rw [dist_comm c.point b.point] at h₂
  rw [dist_comm b.point a.point] at h₃
  rcases a with ⟨a, x⟩
  rcases b with ⟨b, y⟩
  rcases c with ⟨c, z⟩
  cases a <;> cases b <;> cases c <;>
    simp_all only [doubledDist, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte] <;> linarith

instance instPseudoMetricSpaceDoubled : PseudoMetricSpace (Doubled V) where
  dist := doubledDist
  dist_self := doubledDist_self
  dist_comm := doubledDist_comm
  dist_triangle := doubledDist_triangle

def plus (x : V) : Doubled V := ⟨true, x⟩
def minus (x : V) : Doubled V := ⟨false, x⟩

end Double

section Segments

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def mix (q r : E) (t : ℝ) : E := (1 - t) • q + t • r

@[simp] lemma mix_zero (q r : E) : mix q r 0 = q := by simp [mix]
@[simp] lemma mix_one (q r : E) : mix q r 1 = r := by simp [mix]

end Segments

end AlgorithmicThinTrees.MetricProfiles

end 
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_ShellCharging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric shell charging. -/

section

noncomputable section

namespace AlgorithmicThinTrees.MetricProfiles

open Finset Set StrongThinTree.Geometry

variable {V I : Type*} [Fintype V] [PseudoMetricSpace V]

def relativeShell (c : V → ℝ) (a b : ℝ) : Set (V → ℝ) :=
  {q | q ∈ polytope ∧ a < ‖q - c‖ ∧ ‖q - c‖ < b}

end AlgorithmicThinTrees.MetricProfiles

end 
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_DyadicSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.Dyadic
noncomputable section
open Finset

def selected (M : ℕ → ℕ) (z : ℕ) : Finset ℕ :=
  ((range (z+1)).filter (fun i => 0 < M i)).filter
    (fun i => ∀j ≤ z, 0 < M j → Nat.log 2 (M j)=Nat.log 2 (M i) → i ≤ j)

end
end StrongThinTree.Dyadic

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_ResponseBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.MultiGraph.PartitionChain
noncomputable section
open Finset
variable {n m : ℕ} (P : PartitionChain n) (G : MultiGraph n m)

def nextIndex (I : Finset ℕ) (i z : ℕ) : ℕ :=
  if h : (I.filter (fun j => i < j)).Nonempty then (I.filter (fun j => i < j)).min' h else z

end
end StrongThinTree.MultiGraph.PartitionChain

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Representation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι uE uT uI uE2 uE3 uV uE4 uV2 uW

section

open Matrix Finset
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise
namespace StrongThinTree
noncomputable section

section Covariance
variable {T : Type uT} {I : Type uI} [Fintype T] [DecidableEq T] [Nonempty T]
  [Fintype I] [DecidableEq I]

def basisCov (b : Matrix I I ℝ) (a : I → ℝ) : Matrix I I ℝ :=
  b * diagonal (fun j => Real.exp (a j)) * bᵀ

def packingCov (b : T → Matrix I I ℝ) (a : EuclideanSpace ℝ (T × I)) :
    Matrix I I ℝ := ∑ t, basisCov (b t) (fun j => a (t, j))

def packingObjective (b : T → Matrix I I ℝ) (a : EuclideanSpace ℝ (T × I)) : ℝ :=
  Real.log (packingCov b a).det - (∑ e, a e) / Fintype.card T

end Covariance

end
end StrongThinTree

namespace StrongThinTree.MultiGraph
noncomputable section
open Matrix Finset
open scoped BigOperators
variable {n m : ℕ} (G : MultiGraph n m)

def zeroSumSpace (n : ℕ) : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.ker (∑ u : Fin n, LinearMap.proj u)

lemma mem_zeroSumSpace (x : Fin n → ℝ) : x ∈ zeroSumSpace n ↔ ∑ u, x u = 0 := by
  simp [zeroSumSpace, LinearMap.mem_ker, LinearMap.sum_apply]

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Normalization_Descent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization descent. -/

section

namespace AlgorithmicThinTrees.Normalization
open Matrix Finset StrongThinTree
open scoped MatrixOrder

section Covariance
variable {E I : Type*} [normalizationFintypeE : Fintype E]
  [normalizationDecidableEqE : DecidableEq E] [normalizationFintypeI : Fintype I]
  [normalizationDecidableEqI : DecidableEq I]

def shrink {K : Type*} [Field K] (δ : K) (a : E → K) (e : E) : E → K :=
  Function.update a e ((1-δ)*a e)

end Covariance

section Bases
variable {E : Type*} [Fintype E] [basisPackingDecidableEqE : DecidableEq E] {q d : ℕ}

structure BasisPacking (v : E → Fin d → ℝ) (q : ℕ) where
  positive : 0 < q
  edges : (Fin q × Fin d) ≃ E
  invertible : ∀t, IsUnit (Matrix.of (fun i j => v (edges (t,j)) i))
  determinant : ∀t, 1 ≤ (Matrix.det (fun i j => v (edges (t,j)) i))^2

namespace BasisPacking
variable {v : E → Fin d → ℝ} (B : BasisPacking v q)
noncomputable def matrices (t : Fin q) : Matrix (Fin d) (Fin d) ℝ := fun i j => v (B.edges (t,j)) i
noncomputable def logWeights (a : E → ℝ) : EuclideanSpace ℝ (Fin q × Fin d) :=
  WithLp.toLp 2 (fun e => Real.log (a (B.edges e)))

end BasisPacking
end Bases
end AlgorithmicThinTrees.Normalization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Normalization_Packing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization packing. -/

section

namespace AlgorithmicThinTrees.Normalization
open Matrix Finset StrongThinTree
open scoped MatrixOrder

structure ContainedPacking {E : Type*} {d : ℕ} (v : E → Fin d → ℝ) (q : ℕ) where
  positive : 0 < q
  edges : (Fin q × Fin d) ↪ E
  invertible : ∀t, IsUnit (Matrix.of (fun i j => v (edges (t,j)) i))
  determinant : ∀t, 1 ≤ (Matrix.det (fun i j => v (edges (t,j)) i))^2

namespace ContainedPacking
variable {E : Type*} [Fintype E] [DecidableEq E] {q d : ℕ}
variable {v : E → Fin d → ℝ} (B : ContainedPacking v q)

noncomputable def full : BasisPacking (v ∘ B.edges) q :=
  ⟨B.positive,Equiv.refl _,B.invertible,B.determinant⟩

end ContainedPacking
end AlgorithmicThinTrees.Normalization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Normalization_Algorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization algorithm. -/

section

namespace AlgorithmicThinTrees.Normalization
open Matrix Finset StrongThinTree
open scoped MatrixOrder
variable {m d : ℕ}

def realColumns (v : Fin m → Fin d → ℚ) : Fin m → Fin d → ℝ := fun e i => (v e i : ℝ)
noncomputable def realWeights (s : Fin m → ℚ) : Fin m → ℝ := fun e => (s e : ℝ)^2

end AlgorithmicThinTrees.Normalization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_CompactCharging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric compact charging. -/

section

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry
noncomputable section
open Finset

section RadialLaws
variable {J : Type*} [Fintype J] [PseudoMetricSpace J]

def normDistance (q r : J → ℝ) : ℝ := ‖q-r‖

def inPolytope (q : J → ℝ) : Prop := q ∈ polytope

def isProfile (q : J → ℝ) : Prop := ∃ j : J, q = profile j

omit [PseudoMetricSpace J] in
lemma normDistance_comm (q r : J → ℝ) : normDistance q r = normDistance r q :=
  norm_sub_rev _ _

end RadialLaws

structure RadialShell (V : Type*) where
  center : V
  inner : ℝ
  outer : ℝ
  ordinary : Bool
  deriving DecidableEq

namespace RadialShell
variable {V : Type*} {J : Type*} [Fintype J] [PseudoMetricSpace J]

def ball (v : V) (r : ℝ) : RadialShell V := ⟨v,0,r,true⟩
def hollow (v : V) (a b : ℝ) : RadialShell V := ⟨v,a,b,false⟩
def width (H : RadialShell V) : ℝ := H.outer-H.inner

def support (X : V → J → ℝ) (H : RadialShell V) : Set (J → ℝ) :=
  {w | inPolytope w ∧ normDistance w (X H.center)<H.outer ∧
    (H.ordinary = true ∨ H.inner<normDistance w (X H.center))}

def Valid (X : V → J → ℝ) (H : RadialShell V) : Prop :=
  0 ≤ H.inner ∧ H.inner < H.outer ∧ (H.ordinary = true → H.inner = 0) ∧
  (∃u, normDistance (X u) (X H.center) ≤ H.inner) ∧
  (∃v, H.outer ≤ normDistance (X v) (X H.center))

end RadialShell
end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
noncomputable section
open Finset
variable {V : Type*} [DecidableEq V] {J : Type*} [Fintype J] [PseudoMetricSpace J] {X : V → J → ℝ}

def Arrangement (X : V → J → ℝ) (O : Finset (RadialShell V)) : Prop :=
  (∀H ∈ O, H.Valid X) ∧ (O : Set (RadialShell V)).Pairwise (fun H K => Disjoint (H.support X) (K.support X))

def capacity (Δ : ℝ) (H : RadialShell V) : ℝ := max (H.width-6*Δ) 0

def potential (Δ : ℝ) (O : Finset (RadialShell V)) : ℝ := ∑H ∈ O, capacity Δ H

end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
noncomputable section
open Finset
variable {V : Type*} [DecidableEq V] {J : Type*} [Fintype J] [PseudoMetricSpace J] {X : V → J → ℝ}

structure CompactFamily (X : V → J → ℝ) (δ Δ : ℝ) where
  bags : Finset (Finset V)
  nonempty : bags.Nonempty
  radius_pos : 0 < δ
  bags_disjoint : (bags : Set (Finset V)).Pairwise Disjoint
  balls_disjoint : (bags.biUnion id : Set V).Pairwise
    (fun u v => Disjoint ((ball u δ).support X) ((ball v δ).support X))
  cardinal : ∀D ∈ bags, 2 ≤ D.card
  diameter : ∀D ∈ bags, ∀u ∈ D, ∀v ∈ D, normDistance (X u) (X v) ≤ Δ
  compact : ∀D ∈ bags, 36*Δ ≤ (D.card : ℝ)*δ

end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_PartitionLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partition lattice. -/

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset
open scoped Classical

variable {V E : Type*} [Fintype V]

instance partitionsFinite : Finite (Setoid V) :=
  Finite.of_injective (fun p : Setoid V => p.r) (fun p q h => by
    apply Setoid.ext
    intro a b
    exact iff_of_eq (congrFun (congrFun h a) b))

instance partitionsFintype : Fintype (Setoid V) := Fintype.ofFinite _

def partCount (p : Setoid V) : ℕ := Fintype.card (Quotient p)

def constants (p : Setoid V) : Submodule ℝ (V → ℝ) where
  carrier := {x | p ≤ Setoid.ker x}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := by
    intro x y hx hy a b hab
    change x a+y a=x b+y b
    rw [hx hab,hy hab]
  smul_mem' := by
    intro c x hx a b hab
    change c*x a=c*x b
    rw [hx hab]

def quotientConstants (p : Setoid V) : (Quotient p → ℝ) ≃ₗ[ℝ] constants p where
  toFun f := ⟨fun a => f (Quotient.mk p a),fun _ _ hab => congrArg f (Quotient.sound hab)⟩
  invFun x := Quotient.lift x (fun _ _ hab => x.property hab)
  left_inv f := by
    funext a
    exact Quotient.inductionOn a (fun _ => rfl)
  right_inv x := by
    apply Subtype.ext
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def potential (p : Setoid V) : ℝ := (partCount p : ℝ)^2

def crossingIndicator (p : Setoid V) (a b : V) : ℝ := if p a b then 0 else 1

variable [Fintype E]

def capacity (left right : E → V) (w : E → ℝ) (p : Setoid V) : ℝ :=
  ∑e, w e*crossingIndicator p (left e) (right e)

def slack (left right : E → V) (w : E → ℝ) (r : ℝ) (p : Setoid V) : ℝ :=
  capacity left right w p-r*((partCount p:ℝ)-1)

end
end AlgorithmicThinTrees.Partitions
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_PartitionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partition geometry. -/

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical

variable {V : Type*} [Fintype V]

def block (p : Setoid V) (v : V) : Finset V := univ.filter (p v ·)

@[simp] lemma mem_block (p : Setoid V) (v w : V) : w ∈ block p v ↔ p v w := by
  simp [block]

lemma self_mem_block (p : Setoid V) (v : V) : v ∈ block p v :=
  (mem_block p v v).mpr (p.refl v)

lemma block_eq_iff (p : Setoid V) (v w : V) : block p v=block p w ↔ p v w := by
  constructor
  · intro he
    exact (mem_block p v w).mp (he ▸ self_mem_block p w)
  · intro h
    ext a
    simp only [mem_block]
    exact ⟨fun hv => p.trans (p.symm h) hv, fun hw => p.trans h hw⟩

lemma block_mono {p q : Setoid V} (hpq : p ≤ q) (v : V) : block p v ⊆ block q v := by
  intro w hw
  exact (mem_block _ _ _).mpr (hpq ((mem_block _ _ _).mp hw))

def parts (p : Setoid V) : Finset (Finset V) := univ.image (block p)

lemma block_mem_parts (p : Setoid V) (v : V) : block p v ∈ parts p :=
  mem_image.mpr ⟨v,mem_univ v,rfl⟩

lemma mem_parts (p : Setoid V) (A : Finset V) : A ∈ parts p ↔ ∃v, block p v=A := by
  simp [parts]

lemma parts_disjoint (p : Setoid V) {A B : Finset V} (hA : A ∈ parts p)
    (hB : B ∈ parts p) (hAB : A ≠ B) : Disjoint A B := by
  obtain ⟨a,rfl⟩ := (mem_parts p A).mp hA
  obtain ⟨b,rfl⟩ := (mem_parts p B).mp hB
  apply disjoint_left.mpr
  intro v hva hvb
  apply hAB
  exact (block_eq_iff p a b).mpr
    (p.trans ((mem_block _ _ _).mp hva) (p.symm ((mem_block _ _ _).mp hvb)))

variable {n m : ℕ}

lemma parts_partition (p : Setoid (Fin n)) : VertexPartition univ (parts p) := by
  refine ⟨?_,?_,?_⟩
  · intro A hA
    obtain ⟨v,rfl⟩ := (mem_parts p A).mp hA
    exact ⟨⟨v,self_mem_block p v⟩,subset_univ _⟩
  · intro A hA B hB hAB
    exact parts_disjoint p hA hB hAB
  · apply eq_univ_of_forall
    intro v
    exact mem_biUnion.mpr ⟨block p v,block_mem_parts p v,self_mem_block p v⟩

def toChain (f : ℕ → Setoid (Fin n)) (hf : Monotone f) : PartitionChain n where
  parts i := parts (f i)
  partition i := parts_partition (f i)
  coarsens i j hij A hA := by
    obtain ⟨v,rfl⟩ := (mem_parts (f i) A).mp hA
    exact ⟨block (f j) v,block_mem_parts _ _,block_mono (hf hij) v⟩

end
end AlgorithmicThinTrees.Partitions
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_AssignedCharging
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric assigned charging. -/

section

open scoped Classical

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)

structure Record (n : ℕ) where
  shell : RadialShell (Fin n)
  owner : Finset (Fin n)
  predecessors : Finset (Finset (Fin n))
  avoided : Option (Finset (Fin n))
  deriving DecidableEq

namespace Record
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Doubled Coord → ℝ)

def excluded (B : Record n) : Finset (Finset (Fin n)) :=
  B.predecessors ∪ B.avoided.toFinset

def conflict (B : Record n) := H.domain B.owner B.excluded
def leafSet (B : Record n) := H.leaves B.owner B.excluded
def routing (B : Record n) : Finset (Fin n) := B.owner\B.avoided.getD ∅

def Shape (B : Record n) : Prop :=
  B.owner ∈ H.nodes ∧ (∀S ∈ B.excluded, S ∈ H.nodes ∧ S ⊂ B.owner)

def Protected (B : Record n) : Prop :=
  ∀S ∈ B.predecessors, ∀e ∈ G.cut univ S,
    B.shell.outer ≤ normDistance (X (G.left e)) (X B.shell.center) ∧
    B.shell.outer ≤ normDistance (X (G.right e)) (X B.shell.center)

def RoutingCertificate (q : ℝ) (B : Record n) : Prop :=
  ∃R : Finset (Fin n), R ⊆ B.routing ∧ G.EdgeConnectedReal R q ∧
    (∃u ∈ R, u ∈ B.leafSet H ∧ normDistance (X u) (X B.shell.center) ≤ B.shell.inner) ∧
    (∃v ∈ R, B.shell.outer ≤ normDistance (X v) (X B.shell.center))

def Valid (q : ℝ) (B : Record n) : Prop :=
  B.Shape H ∧ B.Protected G X ∧ B.shell.Valid X ∧ B.RoutingCertificate H G X q

end Record
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Doubled Coord → ℝ)

def LabeledArrangement (q : ℝ) (Z : Finset (Record n)) : Prop :=
  (∀B ∈ Z, B.Valid H G X q) ∧
  (Z : Set (Record n)).Pairwise (fun B D =>
    ¬Disjoint (B.shell.support X) (D.shell.support X) →
      Disjoint (B.conflict H) (D.conflict H))

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Doubled Coord → ℝ)

def parentBoundary (A : Finset (Fin n)) : Finset (Fin m) :=
  G.cut (G.inducedEdges (H.parent A)) A

def LocallyConnectedReal (q : ℝ) : Prop := ∀A ∈ H.nodes, G.EdgeConnectedReal A q

structure AssignedBag (δ η : ℝ) where
  owner : Finset (Fin n)
  owner_mem : owner ∈ H.nodes
  nonroot : owner ≠ univ
  centers : Finset (Fin n)
  nonempty : centers.Nonempty
  radius_pos : 0 < δ
  disjoint : (centers : Set (Fin n)).Pairwise (fun u v =>
    Disjoint ((RadialShell.ball u δ).support X) ((RadialShell.ball v δ).support X))
  assignment : η*(parentBoundary H G owner).card ≤ (centers.card : ℝ)
  endpoint : ∀u ∈ centers, u ∈ owner ∧ ∃e ∈ parentBoundary H G owner,
    (G.left e = u ∨ G.right e = u) ∧ normDistance (X (G.left e)) (X (G.right e)) < δ

namespace AssignedBag
variable {H G X} {δ η : ℝ} (A : AssignedBag H G X δ η)

def input (P : Finset (Finset (Fin n))) (u : Fin n) : Record n :=
  ⟨RadialShell.ball u δ,A.owner,P,none⟩

end AssignedBag
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] (H : Hierarchy n)

namespace Record
variable (G : MultiGraph n m) (X : Fin n → Doubled Coord → ℝ)

def innerRecord (B : Record n) (t : Finset (Fin n)) (a b : ℝ) : Record n :=
  ⟨RadialShell.hollow B.shell.center a b,t,B.predecessors.filter (fun S => S ⊂ t),none⟩
def outsideRecord (B : Record n) (t : Finset (Fin n)) (a b : ℝ) : Record n :=
  ⟨RadialShell.hollow B.shell.center a b,B.owner,B.predecessors,some t⟩

end Record
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Doubled Coord → ℝ)

namespace Record

def Compatible (B D : Record n) : Prop :=
  Disjoint (B.shell.support X) (D.shell.support X) ∨ Disjoint (B.conflict H) (D.conflict H)

def Interior (C δ : ℝ) (A B : Record n) : Prop :=
  (A.conflict H ∩ B.conflict H).Nonempty ∧
    B.shell.inner+C*δ < normDistance (X A.shell.center) (X B.shell.center) ∧
    normDistance (X A.shell.center) (X B.shell.center) < B.shell.outer-C*δ

end Record

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Doubled Coord → ℝ)

namespace Record

def restriction (B : Record n) (a b : ℝ) : Record n :=
  {B with shell := RadialShell.hollow B.shell.center a b}

def Refines (D B : Record n) : Prop :=
  D.shell.support X ⊆ B.shell.support X ∧ D.conflict H ⊆ B.conflict H

end Record

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Doubled Coord → ℝ)

namespace Record

def phaseToken (F : Finset (Record n)) (δ ε : ℝ) (B : Record n) : ℝ :=
  if B ∈ F then AssignedAccounting.fresh δ ε else
    AssignedAccounting.base B.avoided.isSome B.shell.width δ

end Record

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Doubled Coord → ℝ)

namespace Record

def restrictionSet (B : Record n) (a b : ℝ) : Finset (Record n) :=
  if a < b then {B.restriction a b} else ∅

end Record

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ} {δ η : ℝ}

namespace AssignedBag

lemma neighbor_exists (A : AssignedBag H G X δ η) {u : Fin n} (hu : u ∈ A.centers) :
    ∃v ∈ H.parent A.owner\A.owner, normDistance (X u) (X v) < δ ∧
      ∃e : Fin m, (G.left e = u ∧ G.right e = v) ∨
        (G.left e = v ∧ G.right e = u) := by
  obtain ⟨huT,e,he,heu,hlen⟩ := A.endpoint u hu
  obtain ⟨heP,heT⟩ := mem_filter.mp he
  obtain ⟨hlP,hrP⟩ := (G.mem_inducedEdges _ _).mp heP
  rcases heu with heu | heu
  · have hrT : G.right e ∉ A.owner := by
      rcases heT with hh | hh
      · exact hh.2
      · exact (hh.2 (heu.symm ▸ huT)).elim
    refine ⟨G.right e,mem_sdiff.mpr ⟨hrP,hrT⟩,?_,e,Or.inl ⟨heu,rfl⟩⟩
    simpa only [heu] using hlen
  · have hlT : G.left e ∉ A.owner := by
      rcases heT with hh | hh
      · exact (hh.2 (heu.symm ▸ huT)).elim
      · exact hh.2
    refine ⟨G.left e,mem_sdiff.mpr ⟨hlP,hlT⟩,?_,e,Or.inr ⟨rfl,heu⟩⟩
    simpa only [heu,normDistance_comm] using hlen

def neighbor (A : AssignedBag H G X δ η) (u : Fin n) : Fin n :=
  if hu : u ∈ A.centers then (A.neighbor_exists hu).choose else u

end AssignedBag

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ}

namespace Record

def RadialRefines (D B : Record n) : Prop :=
  D.shell.center = B.shell.center ∧ B.shell.inner ≤ D.shell.inner ∧
    D.shell.outer ≤ B.shell.outer ∧ D.conflict H ⊆ B.conflict H

def InteriorTo (δ : ℝ) (Z : Finset (Record n)) (A : Record n) : Prop :=
  ∃B ∈ Z, A.Interior H X 256 δ B

end Record

def Evolution (F Z Z' : Finset (Record n)) : Prop :=
  ∀D ∈ Z', D ∈ F ∨ ∃B ∈ Z, D.RadialRefines (H := H) B

def OwnerEvolution (t : Finset (Fin n)) (Z Z' : Finset (Record n)) : Prop :=
  ∀D ∈ Z', D.owner = t ∨ ∃B ∈ Z, D.owner = B.owner

namespace AssignedBag
variable {δ η : ℝ} (A : AssignedBag H G X δ η)

def SameOwnerSeparated (P : Finset (Finset (Fin n))) (U : Finset (Fin n))
    (Z : Finset (Record n)) : Prop :=
  ∀u ∈ U, (A.input P u).InteriorTo (H := H) (X := X) δ Z →
    ∀B ∈ Z, B.owner = A.owner →
      Disjoint ((RadialShell.ball u δ).support X) (B.shell.support X)

end AssignedBag
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ} {δ η : ℝ}
namespace AssignedBag

structure InteriorMove (A : AssignedBag H G X δ η)
    (q ε : ℝ) (P : Finset (Finset (Fin n)))
    (F Z : Finset (Record n)) (U : Finset (Fin n)) where
  treated : Finset (Fin n)
  next : Finset (Record n)
  nonempty : treated.Nonempty
  treated_interior : ∀u ∈ treated, u ∈ U ∧
    (A.input P u).InteriorTo (H := H) (X := X) δ Z
  valid : LabeledArrangement H G X (q/4) next
  credit : (∑D ∈ Z, Record.phaseToken F δ ε D)+
      AssignedAccounting.theta*(treated.card : ℝ)*δ ≤
      ∑D ∈ next, Record.phaseToken F δ ε D
  evolution : Evolution (H := H) F Z next
  owners : OwnerEvolution A.owner Z next
  fresh : ∀D ∈ next, D ∈ F → D ∈ Z ∨ ∃u ∈ treated, D = A.input P u
  separation : A.SameOwnerSeparated P (U\treated) next

end AssignedBag
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ}
namespace Record

def baseToken (r : ℝ) (B : Record n) : ℝ :=
  AssignedAccounting.base B.avoided.isSome B.shell.width r

def shrinkRecord (F : Finset (Record n)) (δ : ℝ) (B : Record n) : Record n :=
  if B ∈ F then B else B.restriction (B.shell.inner+257*δ) (B.shell.outer-257*δ)

def shrinkValue (F : Finset (Record n)) (δ ε : ℝ) (B : Record n) : ℝ :=
  if B ∈ F then AssignedAccounting.fresh δ ε else
    AssignedAccounting.base B.avoided.isSome (B.shell.width-514*δ) ε

end Record

def shrinkFamily (F Z : Finset (Record n)) (δ : ℝ) : Finset (Record n) :=
  (Z.filter (fun B => 0 < (B.shrinkRecord F δ).shell.width)).image (Record.shrinkRecord F δ)

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ} {η : ℝ}

structure AssignedFamily (H : Hierarchy n) (G : MultiGraph n m)
    (X : Fin n → Doubled Coord → ℝ) (η : ℝ) where
  radius : ℝ
  positive : 0 < radius
  count : ℕ
  bag : Fin count → AssignedBag H G X radius η
  owner_injective : Function.Injective (fun i => (bag i).owner)
  separated : ∀i, ∀u ∈ (bag i).centers, ∀j, ∀v ∈ (bag j).centers,
    (i ≠ j ∨ u ≠ v) → Disjoint ((RadialShell.ball u radius).support X)
      ((RadialShell.ball v radius).support X)

namespace AssignedFamily
variable (F : AssignedFamily H G X η)

def owners : Finset (Finset (Fin n)) := univ.image (fun i => (F.bag i).owner)
def mass : ℝ := (∑i, ((F.bag i).centers.card : ℝ))*F.radius
def predecessors (E : Finset (Finset (Fin n))) (i : Fin F.count) : Finset (Finset (Fin n)) :=
  E.filter (fun S => S ⊂ (F.bag i).owner)

def ProtectedFrom (E : Finset (Finset (Fin n))) : Prop :=
  ∀i, ∀u ∈ (F.bag i).centers, ((F.bag i).input (F.predecessors E i) u).Protected G X

end AssignedFamily

namespace AssignedSequence
abbrev Family := AssignedFamily H G X η

def initialRadius : List (Family (H := H) (G := G) (X := X) (η := η)) → ℝ
  | [] => 0
  | F::_ => F.radius

def mass : List (Family (H := H) (G := G) (X := X) (η := η)) → ℝ
  | [] => 0
  | F::L => F.mass+mass L

def Geometric : List (Family (H := H) (G := G) (X := X) (η := η)) → Prop
  | [] => True
  | F::L => initialRadius L ≤ F.radius/1536 ∧ Geometric L

def Ready (E : Finset (Finset (Fin n))) : List (Family (H := H) (G := G) (X := X) (η := η)) → Prop
  | [] => True
  | F::L => Disjoint E F.owners ∧ F.ProtectedFrom E ∧ Ready (E∪F.owners) L

end AssignedSequence
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ} {η : ℝ}

namespace AssignedFamily
variable (F : AssignedFamily H G X η)

def goodCenters (E : Finset (Finset (Fin n))) (i : Fin F.count) : Finset (Fin n) :=
  (F.bag i).centers.filter (fun u => ((F.bag i).input (F.predecessors E i) u).Protected G X)

def badCenters (E : Finset (Finset (Fin n))) (i : Fin F.count) : Finset (Fin n) :=
  (F.bag i).centers\F.goodCenters E i

def badCount (E : Finset (Finset (Fin n))) : ℕ := ∑i, (F.badCenters E i).card

def boundaryCount (G : MultiGraph n m) (E : Finset (Finset (Fin n))) : ℕ :=
  ∑S ∈ E, (G.cut univ S).card

end AssignedFamily
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ}

namespace AssignedFamily
variable {q : ℝ} (F : AssignedFamily H G X (6144/q))

def BoundaryRatio (ρ : ℝ) : Prop := ∀i,
  (q*ρ)*((G.cut univ (F.bag i).owner).card : ℝ) ≤ (parentBoundary H G (F.bag i).owner).card

end AssignedFamily

namespace AssignedSequence
open AssignedFamily
variable {q : ℝ}

def Fresh (E : Finset (Finset (Fin n))) : List (AssignedFamily H G X (6144/q)) → Prop
  | [] => True
  | F::L => Disjoint E F.owners ∧ Fresh (E∪F.owners) L

def Ratios (ρ : ℝ) : List (AssignedFamily H G X (6144/q)) → Prop
  | [] => True
  | F::L => F.BoundaryRatio ρ ∧ Ratios ρ L

def GeometricAt {η : ℝ} (ρ : ℝ) : List (AssignedFamily H G X η) → Prop
  | [] => True
  | F::L => initialRadius L ≤ ρ*F.radius ∧ GeometricAt ρ L

end AssignedSequence
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_ScaleCharging
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric scale charging. -/

section

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
open scoped Classical

structure CompactPackage {n : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] (X : Fin n → Doubled Coord → ℝ) where
  radius : ℝ
  diameter : ℝ
  family : CompactFamily X radius diameter

namespace CompactPackage
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {G : MultiGraph n m} {X : Fin n → Doubled Coord → ℝ}
def mass (F : CompactPackage X) : ℝ := F.radius*(∑D ∈ F.family.bags, (D.card : ℝ))

end CompactPackage

variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m} {X : Fin n → Doubled Coord → ℝ}

namespace AssignedBag
variable {δ η η' : ℝ}
def weaken (A : AssignedBag H G X δ η) (hη : η' ≤ η) : AssignedBag H G X δ η' :=
  { A with assignment := (mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg _)).trans A.assignment }
end AssignedBag

namespace AssignedFamily
variable {η η' : ℝ}
def weaken (F : AssignedFamily H G X η) (hη : η' ≤ η) : AssignedFamily H G X η' where
  radius := F.radius
  positive := F.positive
  count := F.count
  bag := fun i => (F.bag i).weaken hη
  owner_injective := F.owner_injective
  separated := F.separated
end AssignedFamily

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
open scoped Classical
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m} {X : Fin n → Doubled Coord → ℝ}

abbrev CapturedFamily (H : Hierarchy n) (G : MultiGraph n m) (X : Fin n → Doubled Coord → ℝ) (η : ℝ) :=
  Sum (CompactPackage X) (AssignedFamily H G X η)

namespace CapturedFamily
variable {η : ℝ}
def radius : CapturedFamily H G X η → ℝ
  | .inl F => F.radius
  | .inr F => F.radius
def upper : CapturedFamily H G X η → ℝ
  | .inl F => F.diameter
  | .inr F => F.radius
def mass : CapturedFamily H G X η → ℝ
  | .inl F => F.mass
  | .inr F => F.mass
def owners : CapturedFamily H G X η → Finset (Finset (Fin n))
  | .inl _ => ∅
  | .inr F => F.owners

def Ratio {q : ℝ} (F : CapturedFamily H G X (6144/q)) (ρ : ℝ) : Prop :=
  match F with
  | .inl _ => True
  | .inr F => F.BoundaryRatio ρ

end CapturedFamily
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_SpectralMetricBridge
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral metric bridge. -/

section

namespace AlgorithmicThinTrees.MetricProfiles
noncomputable section
open Finset

variable {V E F : Type*} [Fintype V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def SquaredTriangle (p : V → E) : Prop :=
  ∀ u v w, ‖p u-p w‖^2 ≤ ‖p u-p v‖^2+‖p v-p w‖^2

@[instance_reducible] def squaredPseudoMetric (p : V → E) (ht : SquaredTriangle p) : PseudoMetricSpace V where
  dist u v := ‖p u-p v‖^2
  dist_self u := by simp
  dist_comm u v := by rw [norm_sub_rev]
  dist_triangle := ht

open AssignedGeometry AssignedGeometry.AssignedSequence

end
end AlgorithmicThinTrees.MetricProfiles
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_MatrixBound
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric matrix bound. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m d : ℕ}

def columnPoints (X : Matrix (Fin d) (Fin n) ℝ) : Fin n → EuclideanSpace ℝ (Fin d) :=
  fun v => WithLp.toLp 2 (fun i => X i v)

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_ConicDuality
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric conic duality. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree
open scoped Classical MatrixOrder Topology
open Filter

section GeneralFinite
variable {V E T J : Type*} [Fintype V] [DecidableEq V] [Fintype T] [Fintype J]

omit [DecidableEq V] in
lemma trace_pairing_continuous (Z : Matrix V V ℝ) :
    Continuous (fun D : Matrix V V ℝ => (D*Z).trace) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  fun_prop

end GeneralFinite

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_CompactDuality
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric compact duality. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n : ℕ} {E T : Type*}

def pdBox (B : Matrix (Fin n) (Fin n) ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {D | (1/4:ℝ) • B ≤ D ∧ D.trace ≤ B.trace}

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Ramp
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation ramp. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

def lowerCapacity (κ t u y : ℝ) : ℝ :=
  if 0 < u then κ+min 1 (u+t*(5*y-4)) else κ

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Domain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation domain. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

abbrev ResponseSpace (n m : ℕ) := Matrix (Fin n) (Fin n) ℝ × (Fin m → ℝ)

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Restriction
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Finset
namespace StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)

def edgeEmbedding (F : Finset (Fin m)) : Fin F.card ↪ Fin m :=
  F.equivFin.symm.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩
def restrict (F : Finset (Fin m)) : MultiGraph n F.card where
  left e := G.left (edgeEmbedding F e)
  right e := G.right (edgeEmbedding F e)
  loopless e := G.loopless (edgeEmbedding F e)
def liftEdges (F : Finset (Fin m)) (T : Finset (Fin F.card)) : Finset (Fin m) :=
  T.map (edgeEmbedding F)
end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_PartitionLocalConnectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partition local connectivity. -/

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical

variable {V : Type*} [Fintype V]

def split (p : Setoid V) (S : Finset V) : Setoid V := p ⊓ Setoid.ker (fun v => v ∈ S)

variable {n m : ℕ}

def active (u : Fin m → ℝ) : Finset (Fin m) := univ.filter (fun e => 0 < u e)

@[simp] lemma mem_active (u : Fin m → ℝ) (e : Fin m) : e ∈ active u ↔ 0 < u e := by
  simp [active]

end
end AlgorithmicThinTrees.Partitions
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Gains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation gains. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Finset
open scoped Classical

variable {m : ℕ}

def booleanResponse (good : Fin m → Prop) : Fin m → ℝ :=
  fun e => if good e then 1 else 0

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_PartitionUncrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partition uncrossing. -/

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset
open scoped Classical

variable {V X : Type*} [Fintype V]

def Certificates (C : Set X) (f : Setoid V → X → ℝ) (b : ℝ) : Set (Setoid V → ℝ) :=
  {w | (∀p, 0 ≤ w p) ∧ (∑p, w p)=1 ∧ ∀x ∈ C, (∑p, w p*f p x) ≤ b}

def uncrossWeight (w : Setoid V → ℝ) (p q : Setoid V) (δ : ℝ) : Setoid V → ℝ :=
  fun i => w i+(if i=p ⊓ q then δ else 0)+(if i=p ⊔ q then δ else 0)-
    (if i=p then δ else 0)-(if i=q then δ else 0)

end
end AlgorithmicThinTrees.Partitions
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_ConeRepresentation
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric cone representation. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder Matrix.Norms.Elementwise Topology
open Filter

section Representation
variable {n : ℕ} {J : Type*} [Fintype J]

def coneImage (W : J → Matrix (Fin n) (Fin n) ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | ∃P : Matrix (Fin n) (Fin n) ℝ, ∃lam : J → ℝ,
    P.PosSemidef ∧ (∀j, 0 ≤ lam j) ∧ A=P+∑j, lam j • W j}

lemma continuous_trace : Continuous (fun P : Matrix (Fin n) (Fin n) ℝ => P.trace) := by
  simpa only [mul_one] using trace_pairing_continuous (1 : Matrix (Fin n) (Fin n) ℝ)

lemma psd_trace_compact {c : ℝ} (hc : 0 ≤ c) :
    IsCompact {P : Matrix (Fin n) (Fin n) ℝ | P.PosSemidef ∧ P.trace ≤ c} := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨isClosed_psd.inter (isClosed_le continuous_trace continuous_const),?_⟩
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨c,fun P hP => ?_⟩
  have hd : ∀i, P i i ≤ c := fun i =>
    (single_le_sum (fun j _ => hP.1.diag_nonneg (i:=j)) (mem_univ i)).trans hP.2
  apply (pi_norm_le_iff_of_nonneg hc).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hc).mpr
  intro j
  simpa only [Real.norm_eq_abs] using psd_entry_bound hP.1 hc hd i j

lemma coneImage_trace_bound (W : J → Matrix (Fin n) (Fin n) ℝ)
    (hW : ∀j, (W j).trace=2) (P : Matrix (Fin n) (Fin n) ℝ) (lam : J → ℝ)
    (hP : P.PosSemidef) (hlam : ∀j, 0 ≤ lam j) {c : ℝ}
    (ht : (P+∑j, lam j • W j).trace ≤ c) :
    P.trace ≤ c ∧ ∀j, lam j ≤ c := by
  simp only [trace_add,trace_sum,trace_smul,smul_eq_mul,hW,←sum_mul] at ht
  have hsum : 0 ≤ ∑j, lam j := sum_nonneg (fun j _ => hlam j)
  refine ⟨by linarith only [hsum,ht],?_⟩
  intro j
  have hj := single_le_sum (fun i _ => hlam i) (mem_univ j)
  have hp := hP.trace_nonneg
  linarith only [ht,hp,hlam j,hj]

lemma coneImage_closed (W : J → Matrix (Fin n) (Fin n) ℝ)
    (hW : ∀j, (W j).trace=2) : IsClosed (coneImage W) := by
  let : FirstCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℝ))
  apply IsSeqClosed.isClosed
  intro A L hA hlim
  choose P lam hP hlam he using hA
  have htr : Tendsto (fun k => (A k).trace) atTop (𝓝 L.trace) := continuous_trace.tendsto L |>.comp hlim
  obtain ⟨c,hc⟩ := (htr.cauchySeq.isBounded_range).exists_norm_le
  let d := max c 0
  have hd : 0 ≤ d := le_max_right _ _
  let K := {P : Matrix (Fin n) (Fin n) ℝ | P.PosSemidef ∧ P.trace ≤ d} ×ˢ
    Set.Icc (0 : J → ℝ) (fun _ => d)
  have hK : IsCompact K := (psd_trace_compact hd).prod isCompact_Icc
  have hw : ∀k, (P k,lam k) ∈ K := by
    intro k
    have hle : (P k+∑j, lam k j • W j).trace ≤ d := by
      rw [←he k]
      exact (le_abs_self _).trans ((hc _ (Set.mem_range_self k)).trans (le_max_left _ _))
    have hb := coneImage_trace_bound W hW (P k) (lam k) (hP k) (hlam k) hle
    exact ⟨⟨hP k,hb.1⟩,hlam k,hb.2⟩
  obtain ⟨p,hp,φ,hφ,hseq⟩ := hK.tendsto_subseq hw
  have hcont : Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × (J → ℝ) =>
    p.1+∑j, p.2 j • W j) := by fun_prop
  have hi := (hcont.tendsto p).comp hseq
  have hi' : Tendsto (fun k => P (φ k)+∑j, lam (φ k) j • W j) atTop (𝓝 L) := by
    simpa only [Function.comp_def,←he] using hlim.comp hφ.tendsto_atTop
  exact ⟨p.1,p.2,hp.1.1,hp.2.1,(tendsto_nhds_unique hi' hi)⟩

lemma coneImage_zero (W : J → Matrix (Fin n) (Fin n) ℝ) : 0 ∈ coneImage W := by
  exact ⟨0,fun _ => 0,PosSemidef.zero,fun _ => le_refl _,by simp⟩

lemma coneImage_add (W : J → Matrix (Fin n) (Fin n) ℝ)
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ coneImage W) (hB : B ∈ coneImage W) :
    A+B ∈ coneImage W := by
  obtain ⟨P,lam,hP,hlam,rfl⟩ := hA
  obtain ⟨Q,γ,hQ,hγ,rfl⟩ := hB
  refine ⟨P+Q,lam+γ,hP.add hQ,fun j => add_nonneg (hlam j) (hγ j),?_⟩
  simp only [Pi.add_apply,add_smul,sum_add_distrib]
  abel

lemma coneImage_smul (W : J → Matrix (Fin n) (Fin n) ℝ)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ coneImage W) {a : ℝ} (ha : 0 ≤ a) :
    a • A ∈ coneImage W := by
  obtain ⟨P,lam,hP,hlam,rfl⟩ := hA
  refine ⟨a • P,fun j => a*lam j,hP.smul ha,fun j => mul_nonneg ha (hlam j),?_⟩
  simp only [smul_add,smul_sum,smul_smul]

def representedCone (W : J → Matrix (Fin n) (Fin n) ℝ) (hW : ∀j, (W j).trace=2) :
    ProperCone ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := coneImage W
  zero_mem' := coneImage_zero W
  add_mem' := coneImage_add W
  smul_mem' := fun a _ hA => coneImage_smul W hA a.property
  isClosed' := coneImage_closed W hW

end Representation
section TraceDual
variable {n : ℕ}

def linearTraceMatrix (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => f (Matrix.single j i 1)

def symmetricTraceMatrix (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ) :
    Matrix (Fin n) (Fin n) ℝ := (1/2 : ℝ) • (linearTraceMatrix f+(linearTraceMatrix f)ᵀ)

end TraceDual

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Flow_ParallelCopies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Parallel copies. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical
variable {n m : ℕ}

abbrev Copy (a : Fin m → ℕ) := Σe, Fin (a e)

def copyEquiv (a : Fin m → ℕ) : Copy a ≃ Fin (Fintype.card (Copy a)) := Fintype.equivFin _

def copyProjection (a : Fin m → ℕ) (f : Fin (Fintype.card (Copy a))) : Fin m :=
  ((copyEquiv a).symm f).1

end
end AlgorithmicThinTrees.Orientations
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_RealMatrixBridge
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real matrix bridge. -/

section

namespace AlgorithmicThinTrees.RealMatrixBridge
noncomputable section
open Matrix CurrentKS
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {n m d : ℕ}

def complexMatrix (A : Matrix (Fin n) (Fin m) ℝ) : Matrix (Fin n) (Fin m) ℂ :=
  A.map Complex.ofReal

end
end AlgorithmicThinTrees.RealMatrixBridge
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_RationalSigning
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational signing. -/

section

namespace AlgorithmicThinTrees.RationalSigning
open Matrix Finset CurrentKS
open RealMatrixBridge
open scoped MatrixOrder ComplexOrder
variable {d m : ℕ}

def realVec (v : Fin m → Fin d → ℚ) : Fin m → Fin d → ℝ := fun e i => (v e i:ℝ)

noncomputable def outer (v : Fin m → Fin d → ℚ) (e : Fin m) :=
  vecMulVec (realVec v e) (realVec v e)

end AlgorithmicThinTrees.RationalSigning
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_StackedSigning
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stacked signing. -/

section

namespace AlgorithmicThinTrees.StackedSigning
open Matrix Finset
open scoped MatrixOrder
variable {a b m : ℕ}

def gram {d : ℕ} (v : Fin m → Fin d → ℝ) (A : Finset (Fin m)) : Matrix (Fin d) (Fin d) ℝ :=
  ∑e∈A, vecMulVec (v e) (v e)

end AlgorithmicThinTrees.StackedSigning
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_GraphicNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Graphic normalization. -/

section

namespace AlgorithmicThinTrees.Normalization
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
variable {d m q : ℕ}

def dropRoot (d : ℕ) : zeroSumSpace (d+1) ≃ₗ[ℝ] (Fin d → ℝ) where
  toFun x i := x.val i.succ
  invFun y := ⟨Fin.cases (-(∑i, y i)) y,by
    rw [mem_zeroSumSpace,Fin.sum_univ_succ]
    simp only [Fin.cases_zero,Fin.cases_succ,neg_add_cancel]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => rfl) i
    have hh := (mem_zeroSumSpace x.val).mp x.property
    rw [Fin.sum_univ_succ] at hh
    change -(∑i : Fin d, x.val i.succ)=x.val 0
    linarith only [hh]
  right_inv y := rfl
  map_add' x y := rfl
  map_smul' c x := rfl

end AlgorithmicThinTrees.Normalization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_HalfNumeric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Half numeric. -/

section

namespace AlgorithmicThinTrees.GraphicHalf
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open MetricTests Normalization RationalSigning Filter Topology
open scoped MatrixOrder

def countError (r : ℕ) : ℚ := 1/(Nat.nthRoot 16 r:ℚ)

def nextCount (r : ℕ) : ℕ := ⌊(1-16*countError r)*(r:ℚ)/2⌋₊

end AlgorithmicThinTrees.GraphicHalf
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_InputArrays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Input arrays. -/

section

namespace AlgorithmicThinTrees.InputStack
open StrongThinTree Finset CurrentKS CurrentKS.Realization

abbrev E := {x : ExplicitInput // 2 ≤ x.n ∧ 1 ≤ x.k ∧ x.graph.EdgeConnected x.k}
abbrev B := {x : BinaryInput // 2 ≤ x.n ∧ 1 ≤ x.k ∧ x.graph.EdgeConnected x.k}
def bFields (x : BinaryInput) : List ℕ :=
  [x.n,x.p,x.k] ++ (List.ofFn fun i => [(x.left i).val,(x.right i).val,x.multiplicity i]).flatten

lemma records_lookup {n w : ℕ} (a b c : ℕ) (rows : Fin n → List ℕ)
    (hl : ∀i,(rows i).length=w) (i : Fin n) (j : ℕ) (hj : j<w) :
    ([a,b,c] ++ (List.ofFn rows).flatten).getD (3+i.val*w+j) 0 = (rows i).getD j 0 := by
  rw [List.getD_append_right _ _ _ _ (by simp only [List.length_cons,List.length_nil];omega)]
  have he : 3+i.val*w+j-[a,b,c].length=i.val*w+j := by simp;omega
  rw [he]
  exact getD_flatten_ofFn rows hl i j hj 0

end AlgorithmicThinTrees.InputStack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_OrderedGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered graph. -/

section

namespace AlgorithmicThinTrees.OrderedGraph
open Finset StrongThinTree StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)

def edgeEmbedding (F : Finset (Fin m)) : Fin F.card ↪ Fin m :=
  (F.orderEmbOfFin rfl).toEmbedding
def liftEdges (F : Finset (Fin m)) (T : Finset (Fin F.card)) : Finset (Fin m) :=
  T.map (edgeEmbedding F)
noncomputable def lowerEdges (F T : Finset (Fin m)) : Finset (Fin F.card) :=
  T.preimage (edgeEmbedding F) (edgeEmbedding F).injective.injOn

lemma embedding_mem (F : Finset (Fin m)) (e : Fin F.card) : edgeEmbedding F e ∈ F :=
  F.orderEmbOfFin_mem rfl e
lemma embedding_surj (F : Finset (Fin m)) {e : Fin m} (he : e ∈ F) :
    ∃i : Fin F.card, edgeEmbedding F i=e := by
  refine ⟨(F.orderIsoOfFin rfl).symm ⟨e,he⟩,?_⟩
  change ((F.orderIsoOfFin rfl) ((F.orderIsoOfFin rfl).symm ⟨e,he⟩)).val=e
  simp
end AlgorithmicThinTrees.OrderedGraph
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_SelectionRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selection realization. -/

section

namespace CurrentKS.Realization
open Finset
open AlgorithmicThinTrees.OrderedGraph

variable {α : Type*}

lemma sorted_selected {m : ℕ} (A : Finset (Fin m)) :
    (List.finRange m).filter (fun e => decide (e ∈ A))=List.ofFn (edgeEmbedding A) := by
  have hh : (List.ofFn (edgeEmbedding A))=A.sort (· ≤ ·) := by
    rw [List.ofFn_eq_map]
    exact A.listMap_orderEmbOfFin_finRange rfl
  rw [hh]
  apply ((List.sortedLT_finRange m).pairwise.filter _).sortedLT.eq_of_mem_iff A.sortedLT_sort
  intro e
  simp

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_IterationPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iteration potential. -/

section

noncomputable section
namespace AlgorithmicThinTrees.Iteration
open StrongThinTree

def lossB : ℝ := 80 / ((2:ℝ)^(1/16:ℝ)-1)

end AlgorithmicThinTrees.Iteration
end

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_RationalIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational iteration. -/

section

namespace AlgorithmicThinTrees.Iteration
open Finset StrongThinTree StrongThinTree.MultiGraph GraphicHalf
open MetricTests

def initialCount (k : ℕ) : ℕ := max 1 (k/2)

end AlgorithmicThinTrees.Iteration
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_IterationRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iteration realization. -/

section

namespace AlgorithmicThinTrees.OrderedGraph
open StrongThinTree Finset
lemma sorted_lift {m : ℕ} (A : Finset (Fin m)) (B : Finset (Fin A.card)) :
    List.ofFn (edgeEmbedding (liftEdges A B)) =
      List.ofFn (fun i => edgeEmbedding A (edgeEmbedding B i)) := by
  have ha := List.sortedLT_ofFn_iff.mpr ((liftEdges A B).orderEmbOfFin rfl).strictMono
  have hb := List.sortedLT_ofFn_iff.mpr
    ((A.orderEmbOfFin rfl).strictMono.comp (B.orderEmbOfFin rfl).strictMono)
  apply ha.eq_of_mem_iff hb
  · intro e
    simp only [List.mem_ofFn]
    constructor
    · rintro ⟨i,rfl⟩
      obtain ⟨j,hj,hji⟩ := mem_map.mp (embedding_mem (liftEdges A B) i)
      obtain ⟨l,rfl⟩ := embedding_surj B hj
      exact ⟨l,hji⟩
    · rintro ⟨i,rfl⟩
      exact embedding_surj (liftEdges A B) (mem_map.mpr ⟨_,embedding_mem B i,rfl⟩)

lemma mapped_sorted_lift {m : ℕ} (A : Finset (Fin m)) (B : Finset (Fin A.card)) (f : Fin m → ℕ) :
    List.ofFn (fun i => f (edgeEmbedding (liftEdges A B) i)) =
      List.ofFn (fun i => f (edgeEmbedding A (edgeEmbedding B i))) := by
  have h := congrArg (List.map f) (sorted_lift A B)
  simpa only [List.map_ofFn,Function.comp_def] using h
end AlgorithmicThinTrees.OrderedGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_InputDispatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Input dispatch. -/

section

namespace AlgorithmicThinTrees.InputStack
open StrongThinTree Finset CurrentKS CurrentKS.Realization

abbrev Good := {x : AlgorithmicThinTrees.Input // Valid x}
abbrev Large := {x : AlgorithmicThinTrees.Input // Valid x ∧ 2 ≤ x.n}

end AlgorithmicThinTrees.InputStack
end

end OAI
end


