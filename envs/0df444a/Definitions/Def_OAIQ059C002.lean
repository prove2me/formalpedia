-- Prove2me | Definitions.Def_OAIQ059C002
-- name    : OAIQ059C002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T21:30:19.584207+00:00
-- url     : https://prove2.me/theorems/f96612c6-21a4-4194-8bd6-1b05b9e8ddd7
-- title:
--   Definitions bundle OAIQ059C002 of the split of OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 157 declarations of OpenAI's Lean: 75 definitions, 5 instances and 77 theorems. The definitions and types are `OAI.ScalarConductivity.clippedValue`, `OAI.ScalarConductivity.commonScalar`, `OAI.ScalarConductivity.compactFiberMarginal`, `OAI.ScalarConductivity.cylinderFourierCompleteMeasureSpace`, `OAI.ScalarConductivity.cylinderPointEnergyMeasureSpace`, `OAI.ScalarConductivity.divSymbolTwo`, `OAI.ScalarConductivity.endPointEnergyMeasureSpaceUnitAddCircle`, `OAI.ScalarConductivity.endingJoinCutoff`, `OAI.ScalarConductivity.endingMatrixMeasurableSpace`, `OAI.ScalarConductivity.endpointGraph`, `OAI.ScalarConductivity.expCosLinear`, `OAI.ScalarConductivity.fiberPrimitive`, `OAI.ScalarConductivity.flatPulse`, `OAI.ScalarConductivity.fourierMatchingCutoff`, `OAI.ScalarConductivity.fourierResidualCutoff`, `OAI.ScalarConductivity.instMeasurableSpaceMatrixFinOfNatNatReal_solutions_1`, `OAI.ScalarConductivity.instMeasureSpaceUnitAddCircle_solutions_10`, `OAI.ScalarConductivity.instMeasureSpaceUnitAddCircle_solutions_11`, `OAI.ScalarConductivity.instMeasureSpaceUnitAddCircle_solutions_13`, `OAI.ScalarConductivity.instMeasureSpaceUnitAddCircle_solutions_14`, `OAI.ScalarConductivity.instMeasureSpaceUnitAddCircle_solutions_4`, `OAI.ScalarConductivity.instMeasureSpaceUnitAddCircle_solutions_8`, `OAI.ScalarConductivity.inverseBump`, `OAI.ScalarConductivity.inverseChartPiolaOperator`, `OAI.ScalarConductivity.inverseClip`, `OAI.ScalarConductivity.inverseCorrection`, `OAI.ScalarConductivity.iteratedAveragesMeasureSpace`, `OAI.ScalarConductivity.laminateLower`, `OAI.ScalarConductivity.lineShift`, `OAI.ScalarConductivity.lineShiftGradientOperator`, `OAI.ScalarConductivity.localPullback`, `OAI.ScalarConductivity.localVariance`, `OAI.ScalarConductivity.normalizedSlope`, `OAI.ScalarConductivity.openDisjointify`, `OAI.ScalarConductivity.originalPiGradient`, `OAI.ScalarConductivity.originalVoltageValue`, `OAI.ScalarConductivity.periodicPulse`, `OAI.ScalarConductivity.physicalEndSmoothEnergyMeasureSpace`, `OAI.ScalarConductivity.physicalRealTraceMeasureSpaceUnitAddCircle`, `OAI.ScalarConductivity.physicalRootMeasureSpaceUnitAddCircle` and 35 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Conductivity_Branching_Ending`, `Conductivity_Branching_JoinHull`, `Conductivity_Branching_OpenDisjointify`, `Conductivity_Branching_PhysicalTraceTransport`, `Conductivity_Branching_TorusEndingCorrection`, `Conductivity_Flux_CompactBoxDivergence`, `Conductivity_Flux_CylinderSlopeGreen`, `Conductivity_Flux_FiberDivergenceBounds`, `Conductivity_Flux_PhysicalBlockTensor`, `Conductivity_Flux_PhysicalTensorPatch`, `Conductivity_Flux_TorusCylinderGreenComplex`, `Conductivity_Flux_TorusCylinderGreenReal`, `Conductivity_Fourier_AnalyticNull`, `Conductivity_Fourier_CylinderFourierComplete`, `Conductivity_Fourier_FourierMatchingInterpolation`, `Conductivity_Fourier_PoissonTraceRate`, `Conductivity_Fourier_SpectralTerminalIntegral`, `Conductivity_Fourier_SpectralTerminalL2`, `Conductivity_Fourier_TorusDirectionalFourier`, `Conductivity_Fourier_TorusPeriodicDescent`, `Conductivity_Fourier_TorusPoissonContinuous`, `Conductivity_Fourier_TorusSmoothModeJet`, `Conductivity_Geometry_CylinderPointEnergy`, `Conductivity_Geometry_CylinderPolynomial`, `Conductivity_Geometry_FlatTorusPDE`, `Conductivity_Geometry_InverseChartPiolaOperator`, `Conductivity_Geometry_TorusDirectionalDerivative`, `Conductivity_Scalarization_ScalarRelationStrongClosed`, `Conductivity_Sobolev_L2SpectralMultiplier`, `Conductivity_Sobolev_LocalPullback`, `Conductivity_Sobolev_SobolevMaximum`, `Conductivity_Sobolev_SobolevSmoothOperations`, `Conductivity_Sobolev_SobolevSmoothTests`, `Conductivity_Sobolev_VoltageOriginalH10`, `Conductivity_Sobolev_WallParticular`, `Conductivity_Sobolev_WallPrimitive`, `Conductivity_Sources_EndPointEnergy`, `Conductivity_Sources_FaceIntegral`, `Conductivity_Sources_FaceMeasure`, `Conductivity_Sources_FluxCylinder`, `Conductivity_Sources_IteratedAverages`, `Conductivity_Sources_PhysicalMaximum`, `Conductivity_Sources_PhysicalRoot`, `Conductivity_Sources_PhysicalTrace`, `Conductivity_Sources_WordTrace`, `Conductivity_Variational_AdaptedSpatialBasis`, `Conductivity_Variational_AirySymbol`, `Conductivity_Variational_CentralSmoothTrace`, `Conductivity_Variational_CompactFiberDecomposition`, `Conductivity_Variational_CompactFiberPrimitive`, `Conductivity_Variational_CompactParametricIntegral`, `Conductivity_Variational_CrossingProfiles`, `Conductivity_Variational_DerivativeEquiv`, `Conductivity_Variational_DivSymbolTwo`, `Conductivity_Variational_FullWeakEndEnergy`, `Conductivity_Variational_MatrixCompact`, `Conductivity_Variational_OriginalVoltageRestriction`, `Conductivity_Variational_OverlapPoincare`, `Conductivity_Variational_ParametricDiffeomorph`, `Conductivity_Variational_ParametricLocalRegularCorrection`, `Conductivity_Variational_PhysicalEndSmoothEnergy`, `Conductivity_Variational_PhysicalRealTrace`, `Conductivity_Variational_PhysicalTraceMean`, `Conductivity_Variational_RankProjectionFirst`, `Conductivity_Variational_SmoothCompactParameter`, `Conductivity_Variational_SmoothSupportedAdd`, `Conductivity_Variational_SymmetricCorrection`, `Conductivity_Variational_Symmetrize`, `Conductivity_Variational_TransitionMajorant`, `Conductivity_Variational_UniformNormBound`, `Conductivity_Variational_UnitSquarePoincare`, `Conductivity_Variational_VariationalDN`, `Conductivity_Variational_VoltageBoundaryTrace`, `Conductivity_Walls_EndingJoinCutoff`, `Conductivity_Walls_HadamardWall`, `Conductivity_Walls_ParametricWallOperators`, `Conductivity_Walls_WallHalfspaceIntegral`, `Conductivity_Walls_WallHomogeneous`.
--
--   **Imports.** It imports the published bundle `Def_Conductivity`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ059C004` and `OAIQ059C005`.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Conductivity

section
-- module Solutions.OAIQ059_CD.Compat
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CrossingProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma smoothTransition_flat_left {x : ℝ} (hx : x < 0) :
    deriv smoothTransition x = 0 ∧ deriv (deriv smoothTransition) x = 0 := by
  have he : smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    exact smoothTransition.zero_of_nonpos hy.le
  exact ⟨by simpa using he.deriv_eq, by simpa using he.deriv.deriv_eq⟩

lemma smoothTransition_flat_right {x : ℝ} (hx : 1 < x) :
    deriv smoothTransition x = 0 ∧ deriv (deriv smoothTransition) x = 0 := by
  have he : smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact smoothTransition.one_of_one_le hy.le
  exact ⟨by simpa using he.deriv_eq, by simpa using he.deriv.deriv_eq⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_InverseChartPiolaOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Set Filter Topology MeasureTheory

def inverseChartPiolaOperator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : OpenPartialHomeomorph E E) (y : E) : E →L[ℝ] E :=
  |(fderiv ℝ X.symm (X y)).det|⁻¹ • fderiv ℝ X.symm (X y)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_DivSymbolTwo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity
open Matrix

def divSymbolTwo (ξ : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 5) ℝ :=
  !![ξ 0, ξ 1, 0, ξ 2, 0; 0, ξ 0, ξ 1, 0, ξ 2]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_AirySymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity
open Matrix

def transverseSymbol (ξ : Fin 3 → ℝ) (p q r : ℝ) : Fin 5 → ℝ :=
  ![ξ 2 * p, ξ 2 * q, ξ 2 * r,
    -(ξ 0 * p) - ξ 1 * q, -(ξ 0 * q) - ξ 1 * r]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SmoothSupportedAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

def lineShift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : E) (f : E → ℝ) (x : E) : E := x + f x • d

def rankOneEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : E) (L : E →L[ℝ] ℝ) (h : 1 + L d ≠ 0) : E ≃L[ℝ] E := by
  let T := ContinuousLinearMap.id ℝ E + L.smulRight d
  let S := ContinuousLinearMap.id ℝ E - (1 + L d)⁻¹ • L.smulRight d
  have hTS (x : E) : T (S x) = x := by
    change x - (1 + L d)⁻¹ • (L x • d) +
      L (x - (1 + L d)⁻¹ • (L x • d)) • d = x
    simp only [smul_smul, map_sub, map_smul]
    have hscalar : -((1 + L d)⁻¹ * L x) +
        (L x - (1 + L d)⁻¹ * L x * L d) = 0 := by field_simp [h]; ring
    calc
      _ = x + (-((1 + L d)⁻¹ * L x) +
        (L x - (1 + L d)⁻¹ * L x * L d)) • d := by module
      _ = x := by rw [hscalar, zero_smul, add_zero]
  have hST (x : E) : S (T x) = x := by
    change x + L x • d - (1 + L d)⁻¹ • (L (x + L x • d) • d) = x
    simp only [smul_smul, map_add, map_smul]
    have hscalar : L x - (1 + L d)⁻¹ * (L x + L x * L d) = 0 := by
      field_simp [h]; ring
    calc
      _ = x + (L x - (1 + L d)⁻¹ * (L x + L x * L d)) • d := by module
      _ = x := by rw [hscalar, zero_smul, add_zero]
  exact {
    toLinearEquiv := {
      T.toLinearMap with
      invFun := S
      left_inv := hST
      right_inv := hTS }
    continuous_toFun := T.continuous
    continuous_invFun := S.continuous }

@[simp] theorem rankOneEquiv_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (d : E) (L : E →L[ℝ] ℝ) (h : 1 + L d ≠ 0) (x : E) :
    rankOneEquiv d L h x = x + L x • d := rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_AdaptedSpatialBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity

section

open Filter Topology

def rawTwoSpatial {E : Type*} [AddCommGroup E] [Module ℝ E]
    (v : Fin 3 → E) (r : Fin 5 → ℝ) : Fin 2 → E :=
  ![r 0 • v 0 + r 1 • v 1 + r 3 • v 2,
    r 1 • v 0 + r 2 • v 1 + r 4 • v 2]

end

open MeasureTheory Filter Topology

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_LocalPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Set Filter Topology

def localPullback {E V : Type*} [TopologicalSpace E] [Zero V]
    (X : OpenPartialHomeomorph E E) (f : E → V) (x : E) : V := by
  classical
  exact if x ∈ X.source then f (X x) else 0

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_VariationalDN
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

def laminateLower (c C : ℝ) : ℝ :=
  (2 * C) * (1 - Real.sqrt (1 - c / (2 * C))) ^ 3 / 2

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SymmetricCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

section
open Matrix

def symmetricCorrection {m n : Type*} [Fintype m] [Fintype n]
    (E R : Matrix m n ℝ) (L : Matrix n m ℝ) : Matrix m m ℝ :=
  R * L + Lᵀ * Rᵀ - Lᵀ * (Eᵀ * R) * L

end

open Filter Topology Set TopologicalSpace

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_Symmetrize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

def symmetrize {n : Type*} [Fintype n] (M : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (M + Mᵀ)

lemma symmetrize_isSymm {n : Type*} [Fintype n] (M : Matrix n n ℝ) :
    (symmetrize M).IsSymm := by
  unfold Matrix.IsSymm symmetrize
  simp only [transpose_smul, transpose_add, transpose_transpose, add_comm]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_DerivativeEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
section

def smoothEquivHomeomorph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : E ≃ E) (hX : Differentiable ℝ X) (hXi : Differentiable ℝ X.symm) : E ≃ₜ E :=
  { X with continuous_toFun := hX.continuous, continuous_invFun := hXi.continuous }

end

open Set MeasureTheory Filter Topology
open scoped BigOperators

def flatPulse (θ δ t : ℝ) : ℝ :=
  Real.smoothTransition (t / δ) - Real.smoothTransition ((t - θ) / δ)

def periodicPulse (θ δ t : ℝ) : ℝ := ∑ᶠ n : ℤ, flatPulse θ δ (t - n)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_UniformNormBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity

open Set Filter Topology

def lineShiftGradientOperator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : E) (c : ℝ) : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E) :=
  c • (ContinuousLinearMap.smulRightL ℝ E E).flip d

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_Ending
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Real Set Filter Topology MeasureTheory Matrix

local instance endingMatrixMeasurableSpace : MeasurableSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))

end

open Real Set Filter Topology MeasureTheory Matrix

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_JoinHull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Set Filter Topology

def endpointGraph {P X : Type*} (a b : P) (G U V : Set X) : Set (P × X) :=
  {p | p.2 ∈ G ∧ (p.1 ≠ a ∨ p.2 ∈ U) ∧ (p.1 ≠ b ∨ p.2 ∈ V)}

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_OpenDisjointify
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Set MeasureTheory Metric
open scoped ENNReal Topology

def openDisjointify {E : Type*} [TopologicalSpace E] {n : ℕ}
    (U : Fin n → Set E) (i : Fin n) : Set E :=
  U i \ ⋃ j ∈ Finset.Iio i, closure (U j)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_L2SpectralMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open MeasureTheory Filter Topology
open scoped ENNReal

variable {ι : Type*}

def sequenceMultiplier (m : ι → ℂ) (C : ℝ) (hC : 0≤C) (hm : ∀ i, ‖m i‖≤C) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun i => m i*f i,
        ((lp.memℓp f).norm.const_smul C).mono (fun i => by
          simpa only [Pi.smul_apply,smul_eq_mul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hC,
            abs_of_nonneg (norm_nonneg _),norm_mul] using mul_le_mul_of_nonneg_right (hm i) (norm_nonneg (f i)))⟩
      map_add' := fun f g => by ext i; change m i*(f i+g i)=_; exact mul_add _ _ _
      map_smul' := fun r f => by ext i; change m i*(r*f i)=r*(m i*f i); ring }
    C (fun f => by
      have hh := lp.norm_mono (p:=(2:ℝ≥0∞)) (show (2:ℝ≥0∞)≠0 by norm_num)
        (x:=⟨fun i => m i*f i, by
          exact ((lp.memℓp f).norm.const_smul C).mono (fun i => by
            simpa only [Pi.smul_apply,smul_eq_mul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hC,
              abs_of_nonneg (norm_nonneg _),norm_mul] using mul_le_mul_of_nonneg_right (hm i) (norm_nonneg (f i)))⟩)
        (y:=C • f) (fun i => by
          change ‖m i*f i‖≤‖C • f i‖
          rw [norm_mul,norm_smul,Real.norm_eq_abs,abs_of_nonneg hC]
          exact mul_le_mul_of_nonneg_right (hm i) (norm_nonneg _))
      change ‖(⟨fun i => m i*f i, _⟩ : lp (fun _ : ι => ℂ) 2)‖≤_
      simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hC] using hh)

@[simp] lemma sequenceMultiplier_apply (m : ι → ℂ) (C : ℝ) (hC : 0≤C)
    (hm : ∀ i, ‖m i‖≤C) (f : lp (fun _ : ι => ℂ) 2) (i : ι) :
    sequenceMultiplier m C hC hm f i=m i*f i := rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactParametricIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Metric

variable {E P G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [SecondCountableTopology P]
  [MeasurableSpace P] [BorelSpace P] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [CompleteSpace G] {μ : Measure P} [IsLocallyFiniteMeasure μ]

omit [NormedSpace ℝ P] [CompleteSpace G] in
lemma hasFDerivAt_compact_integral {F : E × P → G} {D : E × P → E →L[ℝ] G}
    (hF : Continuous F) (hD : Continuous D)
    (hderiv : ∀ x p, HasFDerivAt (fun y => F (y,p)) (D (x,p)) x)
    {K : Set P} (hK : IsCompact K) (x : E) :
    HasFDerivAt (fun y => ∫ p in K, F (y,p) ∂μ) (∫ p in K, D (x,p) ∂μ) x := by
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod hK).exists_bound_of_continuousOn
    hD.continuousOn
  have hFd (y : E) : Continuous (fun p => F (y,p)) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hDd (y : E) : Continuous (fun p => D (y,p)) :=
    hD.comp (continuous_const.prodMk continuous_id)
  have hi : Integrable (fun _ : P => C) (μ.restrict K) :=
    ContinuousOn.integrableOn_compact hK continuous_const.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := μ.restrict K) (s := closedBall x 1) (bound := fun _ => C)
    (closedBall_mem_nhds x (by norm_num))
    (Filter.Eventually.of_forall fun y => (hFd y).aestronglyMeasurable)
    (ContinuousOn.integrableOn_compact hK (hFd x).continuousOn)
    (hDd x).aestronglyMeasurable _ hi
  · exact Filter.Eventually.of_forall (fun p y _ => hderiv y p)
  · filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    intro y hy
    exact hC (y,p) ⟨hy,hp⟩

lemma contDiff_compact_integral_nat (n : ℕ) {F : E × P → G}
    (hF : ContDiff ℝ n F) {K : Set P} (hK : IsCompact K) :
    ContDiff ℝ n (fun x => ∫ p in K, F (x,p) ∂μ) := by
  induction n generalizing G with
  | zero =>
    exact contDiff_zero.mpr (continuous_parametric_integral_of_continuous (f := fun x p => F (x,p)) hF.continuous hK)
  | succ n ih =>
    let D : E × P → E →L[ℝ] G := fun z =>
      (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ E P)
    have hD : ContDiff ℝ n D := by
      exact (hF.fderiv_right (by norm_cast)).clm_comp contDiff_const
    have hderiv : ∀ x p, HasFDerivAt (fun y => F (y,p)) (D (x,p)) x := by
      intro x p
      have hf := (hF.differentiable (by norm_cast)).differentiableAt.hasFDerivAt
        (x := (x,p))
      exact hf.comp x ((hasFDerivAt_id x).prodMk (hasFDerivAt_const p x))
    rw [Nat.cast_add, Nat.cast_one]
    apply contDiff_succ_iff_hasFDerivAt.mpr
    exact ⟨fun x => ∫ p in K, D (x,p) ∂μ, ih hD,
      hasFDerivAt_compact_integral hF.continuous hD.continuous hderiv hK⟩

lemma contDiff_compact_integral {F : E × P → G}
    (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F) {K : Set P} (hK : IsCompact K) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => ∫ p in K, F (x,p) ∂μ) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_compact_integral_nat n (contDiff_infty.mp hF n) hK

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_UnitSquarePoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

def squarePartial (f : ℝ×ℝ → ℝ) (v : ℝ×ℝ) (z : ℝ×ℝ) : ℝ := fderiv ℝ f z v

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_OverlapPoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def localVariance (Q : Set X) (f : X → ℝ) (m : ℝ) : ℝ := ∫ x in Q, (f x-m)^2 ∂μ

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralSmoothTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open Set MeasureTheory UnitAddTorus
open scoped ENNReal

local instance instMeasureSpaceUnitAddCircle_solutions_4 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_HadamardWall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

def wallDerivative (f : E × ℝ → ℝ) (p : E × ℝ) : ℝ :=
  fderiv ℝ f p (0,1)

def wallQuotient (f : E × ℝ → ℝ) (p : E × ℝ) : ℝ :=
  ∫ t in Icc (0:ℝ) 1, wallDerivative f (p.1,t*p.2)

omit [ProperSpace E] in
lemma wallDerivative_smooth {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallDerivative f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma wallQuotient_smooth {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallQuotient f) := by
  change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun p : E × ℝ =>
    ∫ t in Icc (0:ℝ) 1, wallDerivative f (p.1,t*p.2))
  apply contDiff_compact_integral (μ := volume)
    (F := fun p : (E × ℝ) × ℝ => wallDerivative f (p.1.1,p.2*p.1.2))
    (K := Icc (0:ℝ) 1) _ isCompact_Icc
  exact (wallDerivative_smooth hf).comp
    (contDiff_fst.fst.prodMk (contDiff_snd.mul contDiff_fst.snd))

omit [ProperSpace E] in
lemma wallQuotient_identity {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (x : E) (z : ℝ) :
    f (x,z)-f (x,0)=z*wallQuotient f (x,z) := by
  have hd (t : ℝ) : HasDerivAt (fun q : ℝ => f (x,q*z))
      (z*wallDerivative f (x,t*z)) t := by
    have h := (hf.differentiable (by simp) (x,t*z)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t x).prodMk ((hasDerivAt_id t).mul_const z))
    have he : (0,z) = z • ((0:E),1) := by simp
    simpa only [Function.comp_def,id_eq,one_mul,wallDerivative,he,map_smul,smul_eq_mul] using h
  have hc : Continuous (fun t : ℝ => z*wallDerivative f (x,t*z)) :=
    continuous_const.mul ((wallDerivative_smooth hf).continuous.comp
      (continuous_const.prodMk (continuous_id.mul continuous_const)))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun t _ => hd t) (hc.intervalIntegrable _ _)
  simp only [one_mul,zero_mul] at h
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    ←integral_Icc_eq_integral_Ioc,integral_const_mul] at h
  exact h.symm

lemma smooth_wall_division {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hzero : ∀ x, f (x,0)=0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallQuotient f) ∧
      ∀ p : E × ℝ, f p=p.2*wallQuotient f p := by
  refine ⟨wallQuotient_smooth hf,?_⟩
  rintro ⟨x,z⟩
  simpa only [hzero,sub_zero] using wallQuotient_identity hf x z

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_WallPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

def wallPrimitive (f : E × ℝ → ℝ) (p : E × ℝ) : ℝ :=
  p.2 * ∫ t in Icc (0:ℝ) 1, f (p.1,t*p.2)

lemma wallPrimitive_smooth {f : E × ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallPrimitive f) := by
  apply contDiff_snd.mul
  apply contDiff_compact_integral (μ := volume)
    (F := fun p : (E × ℝ) × ℝ => f (p.1.1,p.2*p.1.2))
    (K := Icc (0:ℝ) 1) _ isCompact_Icc
  exact hf.comp (contDiff_fst.fst.prodMk (contDiff_snd.mul contDiff_fst.snd))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] in
lemma wallPrimitive_eq_intervalIntegral (f : E × ℝ → ℝ) (x : E) (z : ℝ) :
    wallPrimitive f (x,z)=∫ t in (0:ℝ)..z, f (x,t) := by
  have he := intervalIntegral.smul_integral_comp_mul_right
    (fun t : ℝ => f (x,t)) z (a := 0) (b := 1)
  simpa only [smul_eq_mul,zero_mul,one_mul,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    ←integral_Icc_eq_integral_Ioc,wallPrimitive] using he

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] in
lemma wallPrimitive_zero (f : E × ℝ → ℝ) (x : E) : wallPrimitive f (x,0)=0 := by
  simp [wallPrimitive]

omit [NormedSpace ℝ E] [ProperSpace E] in
lemma wallPrimitive_hasDerivAt {f : E × ℝ → ℝ} (hf : Continuous f) (x : E) (z : ℝ) :
    HasDerivAt (fun t : ℝ => wallPrimitive f (x,t)) (f (x,z)) z := by
  simp_rw [wallPrimitive_eq_intervalIntegral]
  have hc : Continuous (fun t : ℝ => f (x,t)) :=
    hf.comp (continuous_const.prodMk continuous_id)
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

lemma wallDerivative_primitive {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (p : E × ℝ) :
    wallDerivative (wallPrimitive f) p=f p := by
  have h := ((wallPrimitive_smooth hf).differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  exact h.unique (wallPrimitive_hasDerivAt hf.continuous p.1 p.2)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactFiberPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

def fiberPrimitive (a : ℝ) (f : E × ℝ → ℝ) (p : E × ℝ) : ℝ :=
  wallPrimitive f p-wallPrimitive f (p.1,a)

lemma fiberPrimitive_smooth (a : ℝ) {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fiberPrimitive a f) :=
  (wallPrimitive_smooth hf).sub ((wallPrimitive_smooth hf).comp (contDiff_fst.prodMk contDiff_const))

omit [NormedSpace ℝ E] [ProperSpace E] in
lemma fiberPrimitive_eq_integral (a : ℝ) {f : E × ℝ → ℝ} (hf : Continuous f) (p : E × ℝ) :
    fiberPrimitive a f p=∫ t in a..p.2, f (p.1,t) := by
  have hc : Continuous (fun t : ℝ => f (p.1,t)) := hf.comp (continuous_const.prodMk continuous_id)
  change wallPrimitive f (p.1,p.2)-wallPrimitive f (p.1,a)=_
  simp only [wallPrimitive_eq_intervalIntegral]
  exact intervalIntegral.integral_interval_sub_left (μ := volume) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)

lemma fiberPrimitive_derivative (a : ℝ) {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (p : E × ℝ) :
    wallDerivative (fiberPrimitive a f) p=f p := by
  have h := ((fiberPrimitive_smooth a hf).differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  have hd : HasDerivAt (fun t : ℝ => fiberPrimitive a f (p.1,t)) (f p) p.2 := by
    exact (wallPrimitive_hasDerivAt hf.continuous p.1 p.2).sub_const (wallPrimitive f (p.1,a))
  exact h.unique hd

omit [NormedSpace ℝ E] [ProperSpace E]

lemma fiberPrimitive_of_zero_fiber (a : ℝ) {f : E × ℝ → ℝ} (hf : Continuous f)
    (x : E) (hx : ∀ t, f (x,t)=0) (z : ℝ) : fiberPrimitive a f (x,z)=0 := by
  rw [fiberPrimitive_eq_integral a hf]
  simp only [hx,intervalIntegral.integral_zero]

lemma fiberPrimitive_below {a b : ℝ} {f : E × ℝ → ℝ} (hf : Continuous f)
    (hv : ∀ p, f p≠0 → p.2∈Ioo a b) (p : E × ℝ) (hp : p.2≤a) :
    fiberPrimitive a f p=0 := by
  rw [fiberPrimitive_eq_integral a hf]
  calc
    _ = ∫ t in a..p.2, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_ge hp] at ht
      by_contra hn
      exact (not_lt_of_ge ht.2) (hv (p.1,t) hn).1
    _ = 0 := by simp

lemma fiberPrimitive_above {a b : ℝ} {f : E × ℝ → ℝ} (hf : Continuous f)
    (hv : ∀ p, f p≠0 → p.2∈Ioo a b)
    (hz : ∀ x, (∫ t in a..b, f (x,t))=0) (p : E × ℝ) (hp : b≤p.2) :
    fiberPrimitive a f p=0 := by
  have hc : Continuous (fun t : ℝ => f (p.1,t)) := hf.comp (continuous_const.prodMk continuous_id)
  rw [fiberPrimitive_eq_integral a hf,←intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable a b) (hc.intervalIntegrable b p.2),hz,zero_add]
  calc
    _ = ∫ t in b..p.2, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hp] at ht
      by_contra hn
      exact (not_lt_of_ge ht.1) (hv (p.1,t) hn).2
    _ = 0 := by simp

theorem fiberPrimitive_compact {a b : ℝ} {f : E × ℝ → ℝ} (hf : Continuous f)
    (hs : HasCompactSupport f) (hv : ∀ p, f p≠0 → p.2∈Ioo a b)
    (hz : ∀ x, (∫ t in a..b, f (x,t))=0) :
    HasCompactSupport (fiberPrimitive a f) ∧
      tsupport (fiberPrimitive a f) ⊆ (Prod.fst '' tsupport f) ×ˢ Icc a b := by
  have hK : IsCompact ((Prod.fst '' tsupport f) ×ˢ Icc a b) :=
    (hs.image continuous_fst).prod isCompact_Icc
  have hsub : Function.support (fiberPrimitive a f) ⊆ (Prod.fst '' tsupport f) ×ˢ Icc a b := by
    intro p hp
    refine ⟨?_,?_,?_⟩
    · by_contra hx
      have hz' : ∀ t, f (p.1,t)=0 := by
        intro t
        by_contra hn
        exact hx ⟨(p.1,t),subset_tsupport f hn,rfl⟩
      exact hp (fiberPrimitive_of_zero_fiber a hf p.1 hz' p.2)
    · by_contra h
      exact hp (fiberPrimitive_below hf hv p (le_of_lt (lt_of_not_ge h)))
    · by_contra h
      exact hp (fiberPrimitive_above hf hv hz p (le_of_lt (lt_of_not_ge h)))
  refine ⟨HasCompactSupport.of_support_subset_isCompact hK hsub,?_⟩
  exact closure_minimal hsub hK.isClosed

end

open Set MeasureTheory Matrix

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactFiberDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

def compactFiberMarginal (a b : ℝ) (f : E × ℝ → ℝ) (x : E) : ℝ :=
  ∫ t in a..b, f (x,t)

lemma compactFiberMarginal_smooth {a b : ℝ} (hab : a≤b) {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (compactFiberMarginal a b f) := by
  have he : compactFiberMarginal a b f=fun x => ∫ t in Icc a b, f (x,t) := by
    funext x
    rw [compactFiberMarginal,intervalIntegral.integral_of_le hab,integral_Icc_eq_integral_Ioc]
  rw [he]
  exact contDiff_compact_integral hf isCompact_Icc

omit [NormedSpace ℝ E] [ProperSpace E] in
lemma compactFiberMarginal_support {a b : ℝ} {f : E × ℝ → ℝ}
    (hs : HasCompactSupport f) :
    HasCompactSupport (compactFiberMarginal a b f) ∧
      tsupport (compactFiberMarginal a b f) ⊆ Prod.fst '' tsupport f := by
  have hc := hs.image continuous_fst
  have hsub : Function.support (compactFiberMarginal a b f) ⊆ Prod.fst '' tsupport f := by
    intro x hx
    by_contra hn
    have hz : ∀ t, f (x,t)=0 := by
      intro t
      by_contra hf
      exact hn ⟨(x,t),subset_tsupport f hf,rfl⟩
    exact hx (by simp [compactFiberMarginal,hz])
  exact ⟨HasCompactSupport.of_support_subset_isCompact hc hsub,closure_minimal hsub hc.isClosed⟩

end

open Set MeasureTheory

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CompactBoxDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma interval_integral_eq_integral_of_support {a b : ℝ} (hab : a≤b)
    {f : ℝ → ℝ} (hv : ∀ t, f t≠0 → t∈Ioo a b) :
    (∫ t in a..b, f t)=∫ t, f t := by
  rw [intervalIntegral.integral_of_le hab]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  by_contra hn
  exact hx ⟨(hv x hn).1,(hv x hn).2.le⟩

lemma compactFiberMarginal_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [SFinite (volume : Measure E)]
    {a b : ℝ} (hab : a≤b) {f : E×ℝ → ℝ} (hf : Integrable f)
    (hv : ∀ p, f p≠0 → p.2∈Ioo a b) :
    (∫ x, compactFiberMarginal a b f x)=∫ p, f p := by
  have he (x : E) : compactFiberMarginal a b f x=∫ t, f (x,t) :=
    interval_integral_eq_integral_of_support hab (fun t ht => hv (x,t) ht)
  simp_rw [he]
  exact (integral_prod f hf).symm

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_FiberDivergenceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] in
lemma compactFiberMarginal_abs_bound {a b : ℝ} (hab : a≤b)
    {f : E×ℝ → ℝ} {M : ℝ} (h : ∀ p,|f p|≤M) (x : E) :
    |compactFiberMarginal a b f x|≤(b-a)*M := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := fun t => f (x,t)) (C := M)
    (fun t _ => by simpa only [Real.norm_eq_abs] using h (x,t))
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab),mul_comm,
    compactFiberMarginal] using hh

omit [NormedSpace ℝ E] [ProperSpace E] in
lemma fiberPrimitive_abs_bound {a b : ℝ} (hab : a≤b)
    {f : E×ℝ → ℝ} (hf : Continuous f)
    (hv : ∀ p,f p≠0 → p.2∈Ioo a b)
    (hz : ∀ x,(∫ t in a..b,f (x,t))=0)
    {M : ℝ} (hM : 0≤M) (h : ∀ p,|f p|≤M) (p : E×ℝ) :
    |fiberPrimitive a f p|≤(b-a)*M := by
  by_cases ha : p.2≤a
  · rw [fiberPrimitive_below hf hv p ha,abs_zero]
    positivity
  by_cases hb : b≤p.2
  · rw [fiberPrimitive_above hf hv hz p hb,abs_zero]
    positivity
  rw [fiberPrimitive_eq_integral a hf]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := p.2) (f := fun t => f (p.1,t)) (C := M)
    (fun t _ => by simpa only [Real.norm_eq_abs] using h (p.1,t))
  rw [Real.norm_eq_abs,abs_of_pos (sub_pos.mpr (lt_of_not_ge ha))] at hh
  exact hh.trans (by nlinarith [lt_of_not_ge hb])

theorem compact_fiber_decomposition_bounded {a b : ℝ} (hab : a<b)
    {f : E×ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hs : HasCompactSupport f) (hv : ∀ p,f p≠0 → p.2∈Ioo a b)
    {η : ℝ → ℝ} (hη : ContDiff ℝ (↑(⊤ : ℕ∞)) η) (hsη : HasCompactSupport η)
    (hvη : tsupport η⊆Ioo a b) (hiη : (∫ t in a..b,η t)=1)
    {M K : ℝ} (hM : 0≤M) (hK : 0≤K)
    (hbound : ∀ p,|f p|≤M) (hηbound : ∀ t,|η t|≤K) :
    ∃ F : E×ℝ → ℝ,ContDiff ℝ (↑(⊤ : ℕ∞)) F ∧ HasCompactSupport F ∧
      (∀ p,wallDerivative F p+η p.2*compactFiberMarginal a b f p.1=f p) ∧
      tsupport F⊆(Prod.fst '' tsupport f) ×ˢ Icc a b ∧
      (∀ p,|F p|≤(b-a)*(1+K*(b-a))*M) ∧
      (∀ p,|wallDerivative F p|≤(1+K*(b-a))*M) ∧
      F=fiberPrimitive a (fun p => f p-η p.2*compactFiberMarginal a b f p.1) := by
  let R := compactFiberMarginal a b f
  have hR := compactFiberMarginal_smooth hab.le hf
  have hsR : HasCompactSupport R := (compactFiberMarginal_support (a := a) (b := b) hs).1
  let g := fun p : E×ℝ => f p-η p.2*R p.1
  have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g := hf.sub ((hη.comp contDiff_snd).mul (hR.comp contDiff_fst))
  have hsg : HasCompactSupport g := by
    apply hs.sub
    apply HasCompactSupport.of_support_subset_isCompact (hsR.prod hsη)
    intro p hp
    exact ⟨subset_tsupport R (mul_ne_zero_iff.mp hp).2,subset_tsupport η (mul_ne_zero_iff.mp hp).1⟩
  have hvg : ∀ p,g p≠0 → p.2∈Ioo a b := by
    intro p hp
    by_contra hn
    have hz : f p=0 := by by_contra hh; exact hn (hv p hh)
    have hzη : η p.2=0 := image_eq_zero_of_notMem_tsupport (fun hh => hn (hvη hh))
    exact hp (by simp [g,hz,hzη])
  have hzg : ∀ x,(∫ t in a..b,g (x,t))=0 := by
    intro x
    rw [show (fun t => g (x,t))=(fun t => f (x,t)-η t*R x) from rfl,
      intervalIntegral.integral_sub (f := fun t => f (x,t)) (g := fun t => η t*R x)
        ((hf.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b)
        ((hη.continuous.mul continuous_const).intervalIntegrable a b)]
    rw [intervalIntegral.integral_mul_const,hiη,one_mul]
    exact sub_self _
  have hgb (p : E×ℝ) : |g p|≤(1+K*(b-a))*M := by
    calc
      |g p| ≤ |f p|+|η p.2| * |R p.1| := by simpa only [g,abs_mul] using abs_sub (f p) (η p.2*R p.1)
      _ ≤ M+K*((b-a)*M) := add_le_add (hbound p)
        (mul_le_mul (hηbound p.2) (compactFiberMarginal_abs_bound hab.le hbound p.1) (abs_nonneg _) hK)
      _ = _ := by ring
  have hc := fiberPrimitive_compact hg.continuous hsg hvg hzg
  refine ⟨fiberPrimitive a g,fiberPrimitive_smooth a hg,hc.1,?_,?_,?_,?_,rfl⟩
  · intro p
    rw [fiberPrimitive_derivative a hg]
    exact sub_add_cancel _ _
  · apply hc.2.trans
    intro p hp
    refine ⟨?_,hp.2⟩
    obtain ⟨q,hq,hqp⟩ := hp.1
    by_contra hn
    have hfg : Function.support g⊆(Prod.fst '' tsupport f) ×ˢ univ := by
      intro y hy
      refine ⟨?_,mem_univ _⟩
      by_contra hyf
      have hz : f y=0 := by
        by_contra h
        exact hyf ⟨y,subset_tsupport f h,rfl⟩
      have hzR : R y.1=0 := image_eq_zero_of_notMem_tsupport
        (fun h => hyf ((compactFiberMarginal_support hs).2 h))
      exact hy (by simp [g,hz,hzR])
    have hts := closure_minimal hfg ((hs.image continuous_fst).isClosed.prod isClosed_univ)
    exact hn (hqp ▸ (hts hq).1)
  · intro p
    simpa only [mul_assoc] using fiberPrimitive_abs_bound hab.le hg.continuous hvg hzg
      (by positivity : 0≤(1+K*(b-a))*M) hgb p
  · intro p
    rw [fiberPrimitive_derivative a hg]
    exact hgb p

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_WallParticular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma wallDerivative_add [ProperSpace E] {f g : E × ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (p : E × ℝ) :
    wallDerivative (fun q => f q+g q) p=wallDerivative f p+wallDerivative g p := by
  simp only [wallDerivative,fderiv_fun_add (hf p) (hg p),add_apply]

lemma wallDerivative_sub [ProperSpace E] {f g : E × ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (p : E × ℝ) :
    wallDerivative (fun q => f q-g q) p=wallDerivative f p-wallDerivative g p := by
  simp only [wallDerivative,fderiv_fun_sub (hf p) (hg p),sub_apply]

lemma wallDerivative_mul [ProperSpace E] {f g : E × ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (p : E × ℝ) :
    wallDerivative (fun q => f q*g q) p=wallDerivative f p*g p+f p*wallDerivative g p := by
  simp only [wallDerivative,fderiv_fun_mul (hf p) (hg p),add_apply,
    smul_apply,smul_eq_mul]
  ring

lemma wall_ratio_multiply [ProperSpace E] {f g : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (hf0 : ∀ x, f (x,0)=0) (hg0 : ∀ x, g (x,0)=0)
    (p : E × ℝ) (hq : wallQuotient g p≠0) :
    (wallQuotient f p/wallQuotient g p)*g p=f p := by
  rw [(smooth_wall_division hg hg0).2 p,(smooth_wall_division hf hf0).2 p]
  field_simp

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_WallHomogeneous
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

omit [ProperSpace E] in
lemma wallDerivative_pullback {a : E → ℝ} (ha : Differentiable ℝ a) (p : E × ℝ) :
    wallDerivative (fun q => a q.1) p=0 := by
  change (fderiv ℝ (a ∘ Prod.fst) p) (0,1)=0
  rw [fderiv_comp p (ha p.1) differentiableAt_fst,fderiv_fst]
  change (fderiv ℝ a p.1) 0=0
  exact map_zero _

end

open Set MeasureTheory Filter Topology

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusPoissonContinuous
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

local instance torusPoissonContinuousMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance torusPoissonContinuousProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

end

open MeasureTheory Filter Topology UnitAddTorus Real Set
open scoped ENNReal

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_PoissonTraceRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma poissonMultiplier_sub_one_bound {m t : ℝ} (hm : 0≤ m) (ht : 0≤t) :
    ‖(Real.exp (-m*t):ℂ)-1‖≤ m*t := by
  rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr (by nlinarith : -m*t≤0)))]
  linarith [Real.add_one_le_exp (-m*t)]

end

open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

local instance instMeasureSpaceUnitAddCircle_solutions_8 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_8 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma complexL2_norm_sq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : Lp ℂ 2 μ) : ‖f‖^2=∫ x,‖f x‖^2 ∂μ := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

lemma continuousMap_L2_sq (f : C(UnitAddTorus (Fin 2),ℂ)) :
    (∫ θ,‖f θ‖^2)=‖f.toLp 2 volume ℂ‖^2 := by
  rw [complexL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (μ:=volume) (p:=2) (𝕜:=ℂ) f] with θ hθ
  rw [hθ]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevSmoothOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology Real

def valueBump (M : ℝ) : ContDiffBump (0:ℝ) :=
  ⟨|M|+1,|M|+2,by positivity,by linarith⟩

def clippedValue (M r : ℝ) : ℝ := valueBump M r*r

lemma clippedValue_smooth (M : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (clippedValue M) :=
  (valueBump M).contDiff.mul contDiff_id

lemma clippedValue_compact (M : ℝ) : HasCompactSupport (clippedValue M) :=
  (valueBump M).hasCompactSupport.mul_right

lemma clippedValue_zero (M : ℝ) : clippedValue M 0=0 := by simp [clippedValue]

def squaredValue (M r : ℝ) : ℝ := valueBump M r * r^2

lemma squaredValue_smooth (M : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (squaredValue M) :=
  (valueBump M).contDiff.mul (contDiff_id.pow 2)

lemma squaredValue_compact (M : ℝ) : HasCompactSupport (squaredValue M) :=
  (valueBump M).hasCompactSupport.mul_right

lemma squaredValue_zero (M : ℝ) : squaredValue M 0=0 := by simp [squaredValue]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevSmoothTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open Set MeasureTheory Filter Topology

open Set MeasureTheory Filter Topology Real

def inverseBump : ContDiffBump (0:ℝ) := ⟨3/5,3/4,by norm_num,by norm_num⟩
def inverseClip (r : ℝ) : ℝ := inverseBump r*r

def inverseCorrection (r : ℝ) : ℝ := (1+inverseClip r)⁻¹-1

lemma inverseClip_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) inverseClip :=
  inverseBump.contDiff.mul contDiff_id

lemma inverseClip_bound (r : ℝ) : |inverseClip r|≤3/4 := by
  by_cases hr : |r|<3/4
  · calc
      |inverseClip r|=inverseBump r*|r| := by
        rw [inverseClip,abs_mul,abs_of_nonneg inverseBump.nonneg]
      _ ≤ 1*|r| := mul_le_mul_of_nonneg_right inverseBump.le_one (abs_nonneg _)
      _ ≤ 3/4 := by simpa only [one_mul] using hr.le
  · have hb : inverseBump r=0 := inverseBump.zero_of_le_dist (by
      change (3/4:ℝ)≤dist r 0; simpa only [dist_zero_right,Real.norm_eq_abs] using le_of_not_gt hr)
    norm_num [inverseClip,hb]

lemma inverseClip_denominator_pos (r : ℝ) : 0<1+inverseClip r := by
  have h := (abs_le.mp (inverseClip_bound r)).1
  linarith

lemma inverseCorrection_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) inverseCorrection :=
  ((contDiff_const.add inverseClip_smooth).inv (fun r => (inverseClip_denominator_pos r).ne')).sub contDiff_const

lemma inverseCorrection_compact : HasCompactSupport inverseCorrection := by
  apply inverseBump.hasCompactSupport.mono
  intro r hr
  contrapose! hr
  simp only [Function.mem_support,not_not] at hr ⊢
  simp [inverseCorrection,inverseClip,hr]

lemma inverseCorrection_zero : inverseCorrection 0=0 := by
  simp [inverseCorrection,inverseClip]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Real

def upperTransitionFun (M r : ℝ) : ℝ := smoothTransition (r-M)

lemma upperTransitionFun_smooth (M : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (upperTransitionFun M) :=
  smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

lemma upperTransitionFun_deriv (M r : ℝ) :
    deriv (upperTransitionFun M) r=deriv smoothTransition (r-M) := by
  change deriv (fun s => smoothTransition (s-M)) r=_
  have hs : ContDiff ℝ (1:ℕ) smoothTransition := smoothTransition.contDiff
  simpa only [mul_one,upperTransitionFun,Function.comp_def,id_eq] using (((hs.differentiable (by simp) (r-M)).hasDerivAt).comp r
    ((hasDerivAt_id r).sub_const M)).deriv

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_CylinderPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def smoothComplexAxis : Submodule ℂ (ℝ → ℂ) where
  carrier := {q | ContDiff ℝ (↑(⊤ : ℕ∞)) q}
  zero_mem' := by
    change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun _ : ℝ => (0:ℂ))
    exact contDiff_const
  add_mem' := by
    intro q r hq hr
    exact (show ContDiff ℝ (↑(⊤ : ℕ∞)) q from hq).add
      (show ContDiff ℝ (↑(⊤ : ℕ∞)) r from hr)
  smul_mem' := by
    intro c q hq
    exact (show ContDiff ℝ (↑(⊤ : ℕ∞)) q from hq).const_smul c

instance instCoeFunSubtypeForallRealComplexMemSubmoduleSmoothComplexAxis : CoeFun smoothComplexAxis (fun _ => ℝ → ℂ) := ⟨fun q => q.val⟩

lemma smoothComplexAxis_smooth (q : smoothComplexAxis) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) q := q.property

open Set MeasureTheory Filter Topology
open scoped ENNReal

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CylinderSlopeGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma complex_linear_axis_smooth (r : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun t : ℝ => (r:ℂ)*(t:ℂ)) :=
  contDiff_const.mul Complex.ofRealCLM.contDiff

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalTensorPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise
local instance physicalTensorPatchMeasurableSpace :
    MeasurableSpace (Matrix (Fin 3) (Fin 3) ℝ) := borel _

end ScalarConductivity

end


end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FullWeakEndEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

def originalPiGradient (u : H1) (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun k => weakGradient u (WithLp.toLp 2 y) k

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalBlockTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise ENNReal
local instance instMeasurableSpaceMatrixFinOfNatNatReal_solutions_1 : MeasurableSpace (Matrix (Fin 3) (Fin 3) ℝ) := borel _

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_CylinderFourierComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

local instance cylinderFourierCompleteMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance cylinderFourierCompleteProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusDirectionalFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal
local instance torusDirectionalFourierMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_TorusDirectionalDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal
local instance torusDirectionalDerivativeMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SmoothCompactParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Metric

section CompactParameter
variable {E Q P G : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [TopologicalSpace P] [SecondCountableTopology P] [CompactSpace P]
  [MeasurableSpace P] [BorelSpace P]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {μ : Measure P} [IsFiniteMeasure μ]

omit [CompleteSpace G] in
lemma hasFDerivAt_compact_parameter {F : E × P → G} {D : E × P → E →L[ℝ] G}
    (hF : Continuous F) (hD : Continuous D)
    (hd : ∀ x p, HasFDerivAt (fun y => F (y,p)) (D (x,p)) x) (x : E) :
    HasFDerivAt (fun y => ∫ p, F (y,p) ∂μ) (∫ p, D (x,p) ∂μ) x := by
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod (isCompact_univ : IsCompact (univ : Set P))).exists_bound_of_continuousOn
    hD.continuousOn
  have hFs (y : E) : Continuous (fun p => F (y,p)) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hDs (y : E) : Continuous (fun p => D (y,p)) :=
    hD.comp (continuous_const.prodMk continuous_id)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := μ) (s := closedBall x 1) (bound := fun _ => C)
    (closedBall_mem_nhds x (by norm_num))
    (Eventually.of_forall fun y => (hFs y).aestronglyMeasurable)
    ((hFs x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hDs x).aestronglyMeasurable _ (integrable_const _)
  · exact Eventually.of_forall (fun p y _ => hd y p)
  · exact Eventually.of_forall (fun p y hy => hC (y,p) ⟨hy,mem_univ p⟩)

lemma contDiff_compact_parameter_nat (n : ℕ) {F : E × Q → G}
    (hF : ContDiff ℝ n F) {r : P → Q} (hr : Continuous r) :
    ContDiff ℝ n (fun x => ∫ p, F (x,r p) ∂μ) := by
  induction n generalizing G with
  | zero =>
    apply contDiff_zero.mpr
    have hFC : Continuous (fun z : E × P => F (z.1,r z.2)) :=
      hF.continuous.comp (continuous_fst.prodMk (hr.comp continuous_snd))
    simpa only [Measure.restrict_univ] using
      continuous_parametric_integral_of_continuous (μ:=μ)
        (f:=fun x p => F (x,r p)) hFC (isCompact_univ : IsCompact (univ : Set P))
  | succ n ih =>
    let D : E × Q → E →L[ℝ] G := fun z =>
      (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ E Q)
    have hD : ContDiff ℝ n D :=
      (hF.fderiv_right (by norm_cast)).clm_comp contDiff_const
    have hd : ∀ x p, HasFDerivAt (fun y => F (y,r p)) (D (x,r p)) x := by
      intro x p
      exact ((hF.differentiable (by norm_cast)).differentiableAt.hasFDerivAt
        (x:=(x,r p))).comp x ((hasFDerivAt_id x).prodMk (hasFDerivAt_const (r p) x))
    rw [Nat.cast_add,Nat.cast_one]
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun x => ∫ p, D (x,r p) ∂μ,ih hD,?_⟩
    intro x
    apply hasFDerivAt_compact_parameter (F:=fun z : E × P => F (z.1,r z.2))
      (D:=fun z : E × P => D (z.1,r z.2))
    · exact hF.continuous.comp (continuous_fst.prodMk (hr.comp continuous_snd))
    · exact hD.continuous.comp (continuous_fst.prodMk (hr.comp continuous_snd))
    · exact hd

lemma contDiff_compact_parameter {F : E × Q → G}
    (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F) {r : P → Q} (hr : Continuous r) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => ∫ p, F (x,r p) ∂μ) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_compact_parameter_nat n (contDiff_infty.mp hF n) hr

end CompactParameter
end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_CylinderPointEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal
local instance cylinderPointEnergyMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_EndPointEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal
local instance endPointEnergyMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_FaceMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal
local instance sourceFaceMeasureCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_FaceIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal
local instance sourceFaceIntegralCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalEndSmoothEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal
local instance physicalEndSmoothEnergyMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_TransitionMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
namespace ScalarConductivity

def transitionMajorant (θ δ t : ℝ) : ℝ :=
  periodicPulse (2 * δ) δ (t + δ) + periodicPulse (2 * δ) δ (t - θ + δ)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_MatrixCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set

lemma matrix_tsupport_subset_union {E : Type*} [TopologicalSpace E]
    {ι κ : Type*} [Finite ι] [Finite κ] (B : E → Matrix ι κ ℝ) :
    tsupport B⊆⋃ i,⋃ j,tsupport (fun x => B x i j) := by
  apply closure_minimal _ (isClosed_iUnion_of_finite (fun i =>
    isClosed_iUnion_of_finite (fun j => isClosed_closure)))
  intro x hx
  by_contra h
  apply hx
  ext i j
  apply image_eq_zero_of_notMem_tsupport (f := fun y => B y i j)
  intro hij
  exact h (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,hij⟩⟩)

lemma matrix_hasCompactSupport {E : Type*} [TopologicalSpace E]
    {ι κ : Type*} [Finite ι] [Finite κ] (B : E → Matrix ι κ ℝ)
    (hB : ∀ i j,HasCompactSupport (fun x => B x i j)) : HasCompactSupport B :=
  (isCompact_iUnion (fun i => isCompact_iUnion (fun j => hB i j))).of_isClosed_subset
    isClosed_closure (matrix_tsupport_subset_union B)

lemma matrix_tsupport_subset {E : Type*} [TopologicalSpace E]
    {ι κ : Type*} [Finite ι] [Finite κ] (B : E → Matrix ι κ ℝ) {U : Set E}
    (hB : ∀ i j,tsupport (fun x => B x i j)⊆U) : tsupport B⊆U :=
  (matrix_tsupport_subset_union B).trans (iUnion_subset (fun i => iUnion_subset (hB i)))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_ParametricDiffeomorph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_parametric_diffeomorph
    {φ : P×E → E} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (p : P) (x : E)
    (L : E ≃L[ℝ] E)
    (hL : fderiv ℝ (fun y => φ (p,y)) x=(L : E →L[ℝ] E))
    {U : Set (P×E)} (hU : IsOpen U) (hpx : (p,x)∈U) :
    ∃ Y : OpenPartialHomeomorph (P×E) (P×E),
      (p,x)∈Y.source ∧ Y.source⊆U ∧
      (∀ q y,Y (q,y)=(q,φ (q,y))) ∧
      ContDiff ℝ (↑(⊤:ℕ∞)) Y ∧ ContDiffOn ℝ (↑(⊤:ℕ∞)) Y.symm Y.target := by
  let D := fderiv ℝ φ (p,x)
  let F : P×E → P×E := fun q => (q.1,φ q)
  have hF : ContDiff ℝ (↑(⊤:ℕ∞)) F := contDiff_fst.prodMk hφ
  have hD : D.comp (ContinuousLinearMap.inr ℝ P E)=(L : E →L[ℝ] E) := by
    have hd := (hφ.differentiable (by simp) (p,x)).hasFDerivAt.comp x
      ((hasFDerivAt_const p x).prodMk (hasFDerivAt_id x))
    have he := hd.fderiv
    change fderiv ℝ (fun y => φ (p,y)) x=D.comp (ContinuousLinearMap.inr ℝ P E) at he
    exact he.symm.trans hL
  let D₀ : P×E →L[ℝ] P×E := (ContinuousLinearMap.fst ℝ P E).prod D
  have hdF : HasFDerivAt F D₀ (p,x) := hasFDerivAt_fst.prodMk
    ((hφ.differentiable (by simp) (p,x)).hasFDerivAt)
  have hsurj : Function.Surjective D₀ := by
    rintro ⟨a,b⟩
    refine ⟨(a,L.symm (b-D (a,0))),?_⟩
    change (a,D (a,L.symm (b-D (a,0))))=(a,b)
    apply Prod.ext
    · rfl
    change D (a,L.symm (b-D (a,0)))=b
    have he : (a,L.symm (b-D (a,0)))=(a,0)+(0,L.symm (b-D (a,0))) := by simp
    rw [he,map_add]
    have hh := congrArg (fun (A : E →L[ℝ] E) => A (L.symm (b-D (a,0)))) hD
    change D (0,L.symm (b-D (a,0)))=L (L.symm (b-D (a,0))) at hh
    rw [hh,L.apply_symm_apply]
    abel
  let e : (P×E) ≃L[ℝ] (P×E) := (LinearEquiv.ofBijective D₀.toLinearMap
    ⟨LinearMap.injective_iff_surjective.mpr hsurj,hsurj⟩).toContinuousLinearEquiv
  have he : (e : P×E →L[ℝ] P×E)=D₀ := rfl
  have hde : HasFDerivAt F (e : P×E →L[ℝ] P×E) (p,x) := he.symm ▸ hdF
  let Y₀ := hF.contDiffAt.toOpenPartialHomeomorph F hde (by simp)
  let V := U∩{q | IsUnit (fderiv ℝ F q)}
  have hV : IsOpen V := hU.inter (Units.isOpen.preimage (hF.continuous_fderiv (by simp)))
  have hpV : (p,x)∈V := by
    refine ⟨hpx,?_⟩
    change IsUnit (fderiv ℝ F (p,x))
    rw [hde.fderiv]
    exact ⟨e.toUnit,rfl⟩
  let Y := Y₀.restr V
  have heq : (Y : P×E → P×E)=F := rfl
  have hs : Y.source=Y₀.source∩V := by
    simp only [Y,OpenPartialHomeomorph.restr_source,hV.interior_eq]
  refine ⟨Y,?_,?_,fun _ _ => rfl,heq ▸ hF,?_⟩
  · rw [hs]
    exact ⟨hF.contDiffAt.mem_toOpenPartialHomeomorph_source hde (by simp),hpV⟩
  · rw [hs]; exact fun _ hx => hx.2.1
  · intro y hy
    have hx := (hs ▸ Y.map_target hy).2.2
    obtain ⟨v,hv⟩ := hx
    let A : (P×E) ≃L[ℝ] (P×E) := ContinuousLinearEquiv.ofUnit v
    have hA : (A : P×E →L[ℝ] P×E)=fderiv ℝ Y (Y.symm y) := by
      change (v : P×E →L[ℝ] P×E)=_
      simpa only [heq] using hv
    have hd : HasFDerivAt Y (A : P×E →L[ℝ] P×E) (Y.symm y) := by
      rw [hA,heq]
      exact (hF.differentiable (by simp) _).hasFDerivAt
    exact (Y.contDiffAt_symm hy hd (heq ▸ hF.contDiffAt)).contDiffWithinAt

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_WallHalfspaceIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma hasCompactSupport_prodMkLeft {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [T1Space E] {f : E×F → ℝ} (hf : HasCompactSupport f) (x : E) :
    HasCompactSupport (fun y => f (x,y)) := by
  apply hf.comp_isClosedEmbedding
  refine ⟨isEmbedding_prodMkRight x, ?_⟩
  convert (isClosed_singleton (x := x)).prod (isClosed_univ : IsClosed (Set.univ : Set F)) using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  rcases p with ⟨p₁,p₂⟩
  simp [Prod.ext_iff,eq_comm]

lemma hasCompactSupport_prodMkRight {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [T1Space F] {f : E×F → ℝ} (hf : HasCompactSupport f) (y : F) :
    HasCompactSupport (fun x => f (x,y)) := by
  apply hf.comp_isClosedEmbedding
  refine ⟨isEmbedding_prodMkLeft y, ?_⟩
  convert (isClosed_univ : IsClosed (Set.univ : Set E)).prod (isClosed_singleton (x := y)) using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  rcases p with ⟨p₁,p₂⟩
  simp [Prod.ext_iff,eq_comm]

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AnalyticNull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set Filter MeasureTheory Topology

def splitFinCLE (n : ℕ) : (Fin (n+1) → ℝ) ≃L[ℝ] ℝ × (Fin n → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toEquiv := (Fin.insertNthEquiv (fun _ : Fin (n+1) => ℝ) 0).symm
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_ParametricWallOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

lemma wallPrimitive_parametric_smooth {f : P×(E×ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×(E×ℝ) => wallPrimitive (fun x => f (q.1,x)) q.2) := by
  apply contDiff_snd.snd.mul
  apply contDiff_compact_integral (μ:=volume) (K:=Icc (0:ℝ) 1)
    (F:=fun z : (P×(E×ℝ))×ℝ => f (z.1.1,(z.1.2.1,z.2*z.1.2.2))) _ isCompact_Icc
  exact hf.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.fst.prodMk
    (contDiff_snd.mul contDiff_fst.snd.snd)))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_FlatTorusPDE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def expCosLinear (L K : E →L[ℝ] ℝ) (p : ℝ) (x : E) : ℝ := exp (L x)*cos (K x+p)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_ParametricLocalRegularCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

lemma exists_open_product_inside {P E : Type*} [TopologicalSpace P] [TopologicalSpace E]
    {O : Set (P×E)} (hO : IsOpen O) {p : P} {x : E} (hx : (p,x)∈O) :
    ∃ V W,IsOpen V ∧ IsOpen W ∧ p∈V ∧ x∈W ∧ V×ˢW⊆O := by
  obtain ⟨V,W,hV,hW,hp,hx',hs⟩ := generalized_tube_lemma
    (isCompact_singleton (x := p)) (isCompact_singleton (x := x)) hO
    (show ({p} : Set P)×ˢ{ x }⊆O from by
      rintro ⟨q,y⟩ ⟨hq,hy⟩
      rcases hq with rfl
      rcases hy with rfl
      exact hx)
  exact ⟨V,W,hV,hW,hp (mem_singleton p),hx' (mem_singleton x),hs⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusSmoothModeJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal
local instance torusSmoothModeJetMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_EndingJoinCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

def endingJoinCutoff (t : ℝ) : ℝ := smoothTransition (t-6)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_FourierMatchingInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

def fourierMatchingCutoff (t : ℝ) : ℝ := 1-smoothTransition ((t-2)/2)

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def fourierResidualCutoff (t : ℝ) : ℝ := smoothTransition (t-1)*smoothTransition (5-t)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_ScalarRelationStrongClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ScalarConductivity
open Filter Topology

def commonScalar {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a : ℝ) (E F : V) : ℝ := by
  classical
  exact if E = 0 then a else inner ℝ E F / ‖E‖ ^ 2

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_RankProjectionFirst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def scaleSecondEquiv (L : ℝ) (hL : L≠0) : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearEquiv.piCongrRight (fun i : Fin 2 =>
    (LinearEquiv.smulOfNeZero ℝ ℝ (if i=0 then 1 else L)
      (by split_ifs; norm_num; exact hL)).toContinuousLinearEquiv)

@[simp] lemma scaleSecondEquiv_apply (L : ℝ) (hL : L≠0) (v : Fin 2 → ℝ) (i : Fin 2) :
    scaleSecondEquiv L hL v i=(if i=0 then 1 else L)*v i := rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_TorusEndingCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

def normalizedSlope (j : Fin 2) : ℝ := if j=0 then 1 else 0

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusPeriodicDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal
local instance torusPeriodicDescentMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_TorusCylinderGreenReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal
local instance torusCylinderGreenRealMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal
local instance torusCylinderGreenRealFluxMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance torusCylinderGreenRealFluxIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_SpectralTerminalL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sqrt_rate_exp_bound {r R : ℝ} (hr : 0 ≤ r) (hR : 0<R) :
    |Real.sqrt r*Real.exp (-r*R)|≤1+R⁻¹ := by
  rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)]
  have hs : Real.sqrt r≤1+r := by
    have := Real.sq_sqrt hr
    nlinarith [Real.sqrt_nonneg r,sq_nonneg r]
  have he : Real.exp (-r*R)≤1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hm : r*R≤Real.exp (r*R) := le_trans (by linarith) (Real.add_one_le_exp (r*R))
  have hexp : Real.exp (r*R)*Real.exp (-r*R)=1 := by rw [←Real.exp_add]; simp
  have hmul := mul_le_mul_of_nonneg_right hm (Real.exp_pos (-r*R)).le
  rw [hexp] at hmul
  have hi : R*R⁻¹=1 := mul_inv_cancel₀ hR.ne'
  have hb : r*Real.exp (-r*R)≤R⁻¹ := by nlinarith
  have ht := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-r*R)).le
  nlinarith

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_TorusCylinderGreenComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal
local instance torusCylinderGreenComplexMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_FluxCylinder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus Matrix
open scoped ENNReal
local instance sourceFluxCylinderMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_SpectralTerminalIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped ENNReal
local instance spectralTerminalIntegralMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_VoltageOriginalH10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal Classical

def voltageValueComponentJet (j : Fin 2) : (Fin 2 → ℝ) →L[ℝ] JetFiber :=
  ({ toFun := fun v => WithLp.toLp 2 (Fin.cases (v j) (fun _ => 0))
     map_add' := by intro v w; ext i; refine Fin.cases ?_ (fun k => ?_) i <;> simp
     map_smul' := by intro c v; ext i; refine Fin.cases ?_ (fun k => ?_) i <;> simp } :
    (Fin 2 → ℝ) →ₗ[ℝ] JetFiber).toContinuousLinearMap

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_OriginalVoltageRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal Classical

def originalVoltageValue (j : Fin 2) : JetFiber →L[ℝ] (Fin 2 → ℝ) :=
  ({ toFun := fun w k => if k=j then w 0 else 0
     map_add' := by intro w v; ext k; by_cases h : k=j <;> simp [h]
     map_smul' := by intro c w; ext k; by_cases h : k=j <;> simp [h] } :
    JetFiber →ₗ[ℝ] (Fin 2 → ℝ)).toContinuousLinearMap

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_VoltageBoundaryTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped Convolution ENNReal NNReal
local instance instMeasureSpaceUnitAddCircle_solutions_10 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_10 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalRealTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal
local instance physicalRealTraceMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalTraceMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal
local instance physicalTraceMeanMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalTraceTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
local instance physicalTraceTransportMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_PhysicalTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal
local instance sourcePhysicalTraceMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_PhysicalRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
attribute [local instance] Classical.propDecidable
local instance physicalRootMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_PhysicalMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
local instance instMeasureSpaceUnitAddCircle_solutions_11 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_WordTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
local instance instMeasureSpaceUnitAddCircle_solutions_13 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
local instance instMeasureSpaceUnitAddCircle_solutions_14 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_IteratedAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
local instance iteratedAveragesMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
end ScalarConductivity

end
end

end OAI
end


