-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
-- name    : LIDT_MIPStarRE_LDT_Test_StrategyCore
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:33:45.24403+00:00
-- url     : https://prove2.me/theorems/8a1ff2c2-f6cf-482b-8d17-fcbe6206290c
-- title:
--   LIDT definitions: LDT / Test / StrategyCore
-- statement:
--   This bundle defines the core symmetric strategy interfaces for the low-individual-degree test. It packages permutation-invariant states, outcome-level and transport-level rebasing invariance for axis-parallel and diagonal measurements, and the covariant measurement structures used by the test.
--
--   Principal definitions:
--   - `PermInvState`: permutation invariance of a bipartite state.
--   - `AxisParallelMeasurementReparamInvariant`: outcome-level covariance for axis-parallel measurements.
--   - `DiagonalMeasurementReparamInvariant`: outcome-level covariance for diagonal measurements.
--   - `DiagonalEvaluationReparamInvariant`: evaluation invariance under diagonal-line rebasing.
--   - `AxisParallelEvaluationReparamInvariant`: evaluation invariance under axis-line rebasing.
--   - `AxisParallelMeasurementTransportInvariant`: transport-level covariance for axis-parallel measurements.
--   - `DiagonalMeasurementTransportInvariant`: transport-level covariance for diagonal measurements.
--   - `AxisParallelCovariantMeasurement`: the bundled axis-parallel covariance structure.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/StrategyCore.lean#L17-L812

-- Generated from MIPStarRE/LDT/Test/StrategyCore.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

/-!
# Section 3 — Strategy core

Base state-invariance and strategy structures for the low individual degree test.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

instance : Fintype Role where
  elems := {Role.A, Role.B}
  complete r := by
    cases r <;> simp

/-- The SWAP reindexing on `ι × ι`: permutes the two tensor factors.
`swapDensity M (i₁,i₂) (j₁,j₂) = M (i₂,i₁) (j₂,j₁)`. -/
def swapDensity {ι : Type*} (M : MIPStarRE.Quantum.Op (ι × ι)) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  Matrix.of fun (ij : ι × ι) (kl : ι × ι) => M (ij.2, ij.1) (kl.2, kl.1)

/-- `swapDensity` is equal to reindexing by the product-commutation equivalence. -/
lemma swapDensity_eq_reindex {ι : Type*}
    (X : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity X = Matrix.reindex (Equiv.prodComm ι ι) (Equiv.prodComm ι ι) X := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  rfl

@[simp] lemma swapDensity_swapDensity {ι : Type*}
    (X : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity (swapDensity X) = X := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  rfl

@[simp] lemma swapDensity_add {ι : Type*}
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity (X + Y) = swapDensity X + swapDensity Y := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  rfl

@[simp] lemma swapDensity_smul {ι : Type*} (c : ℂ)
    (X : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity (c • X) = c • swapDensity X := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  rfl

/-- `swapDensity` preserves matrix multiplication. -/
lemma swapDensity_mul {ι : Type*} [Fintype ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity (X * Y) = swapDensity X * swapDensity Y := by
  classical
  simpa [swapDensity_eq_reindex] using
    (map_mul (Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodComm ι ι)) X Y)

lemma swapDensity_opTensor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op ι) :
    swapDensity (opTensor X Y) = opTensor Y X := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  simp [swapDensity, opTensor, mul_comm]

lemma normalizedTrace_swapDensity {ι : Type*} [Fintype ι]
    (X : MIPStarRE.Quantum.Op (ι × ι)) :
    MIPStarRE.Quantum.normalizedTrace (swapDensity X) = MIPStarRE.Quantum.normalizedTrace X := by
  simpa [swapDensity_eq_reindex] using
    MIPStarRE.Quantum.normalizedTrace_reindex (Equiv.prodComm ι ι) X

theorem ev_swapDensity_of_density_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev ψ (swapDensity Z) = ev ψ Z := by
  unfold ev
  apply congrArg Complex.re
  calc
    MIPStarRE.Quantum.normalizedTrace (ψ.density * swapDensity Z)
      = MIPStarRE.Quantum.normalizedTrace (swapDensity (ψ.density * Z)) := by
          rw [swapDensity_mul]
          simp [hfix]
    _ = MIPStarRE.Quantum.normalizedTrace (ψ.density * Z) :=
          normalizedTrace_swapDensity _

theorem ev_opTensor_swap_of_density_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    (X Y : MIPStarRE.Quantum.Op ι) :
    ev ψ (opTensor X Y) = ev ψ (opTensor Y X) := by
  rw [show opTensor Y X = swapDensity (opTensor X Y) by
    rw [swapDensity_opTensor]]
  exact (ev_swapDensity_of_density_fixed ψ hfix (opTensor X Y)).symm

theorem qBipartiteMatchMass_symm_of_density_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    {Outcome : Type*} [Fintype Outcome]
    (A B : SubMeas Outcome ι) :
    qBipartiteMatchMass ψ A B = qBipartiteMatchMass ψ B A := by
  unfold qBipartiteMatchMass
  refine Finset.sum_congr rfl ?_
  intro a _
  exact ev_opTensor_swap_of_density_fixed ψ hfix (A.outcome a) (B.outcome a)

theorem qBipartiteConsDefect_symm_of_density_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    {Outcome : Type*} [Fintype Outcome]
    (A B : SubMeas Outcome ι) :
    qBipartiteConsDefect ψ A B = qBipartiteConsDefect ψ B A := by
  simp [qBipartiteConsDefect,
    qBipartiteMatchMass_symm_of_density_fixed ψ hfix,
    ev_opTensor_swap_of_density_fixed ψ hfix]

theorem consRel_symm_of_density_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι)
    (δ : Error) :
    ConsRel ψ 𝒟 A B δ → ConsRel ψ 𝒟 B A δ := by
  intro ⟨h⟩
  constructor
  unfold bipartiteConsError at *
  calc
    avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (B q) (A q))
      = avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (A q) (B q)) := by
          apply avgOver_congr
          intro q
          symm
          exact qBipartiteConsDefect_symm_of_density_fixed ψ hfix (A q) (B q)
    _ ≤ δ := h

/-- Permutation-invariance for a bipartite state on `ι × ι`.

The primary datum is that the density operator is fixed by the SWAP reindexing,
`swapDensity ψ.density = ψ.density`.  We also cache the frequently used
one-sided expectation consequence
`ev ψ (leftTensor M) = ev ψ (rightTensor M)`.
This matches the symmetric-strategy construction used in the paper
(Section 3) and exposes enough symmetry to swap fully bipartite
consistency expressions. -/
structure PermInvState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) : Prop where
  /-- The density operator is fixed by the SWAP reindexing. -/
  density_swap : swapDensity ψ.density = ψ.density
  /-- Swapping tensor factors preserves one-sided expectation values. -/
  swap_ev : ∀ (M : MIPStarRE.Quantum.Op ι),
    ev ψ (leftTensor (ι₂ := ι) M) =
      ev ψ (rightTensor (ι₁ := ι) M)

/-- Direct outcome-level covariance for axis-parallel-line measurements.

Rebasing a line question by `t` and reparametrizing an outcome polynomial by
the same translation leaves the corresponding projector unchanged. -/
def AxisParallelMeasurementReparamInvariant (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι) : Prop :=
  ∀ (ℓ : AxisParallelLine params) (t : Fq params) (f : AxisLinePolynomial params),
    (M (ℓ.rebaseAt t)).outcome (AxisLinePolynomial.reparamAt f t) =
      (M ℓ).outcome f

/-- Direct outcome-level covariance for diagonal-line measurements.

Rebasing a line question by `t` and reparametrizing an outcome polynomial by
the same translation leaves the corresponding projector unchanged. -/
def DiagonalMeasurementReparamInvariant (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι) : Prop :=
  ∀ (ℓ : DiagonalLine params) (t : Fq params) (f : DiagonalLinePolynomial params),
    (M (ℓ.rebaseAt t)).outcome (DiagonalLinePolynomial.reparamAt f t) =
      (M ℓ).outcome f

/-- Reparametrization invariance for diagonal-line measurements: evaluating a
rebased line at `zeroCoord` agrees outcome-wise with evaluating the original
line at the rebasing parameter.

At the answer level, the geometric identity is
`DiagonalLinePolynomial.reparamAt_apply_zero`. This predicate is stronger: it
asserts that the *measurement family itself* is covariant under rebasing the
question index. -/
def DiagonalEvaluationReparamInvariant (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι) : Prop :=
  ∀ (ℓ : DiagonalLine params) (t a : Fq params),
    (postprocess ((M (DiagonalLine.rebaseAt ℓ t)).toSubMeas) (· zeroCoord)).outcome a =
      (postprocess ((M ℓ).toSubMeas) (fun f => f t)).outcome a

/-- Reparametrization invariance for axis-parallel-line measurements: evaluating a
rebased line at `zeroCoord` agrees outcome-wise with evaluating the original
line at the rebasing parameter. -/
def AxisParallelEvaluationReparamInvariant (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι) : Prop :=
  ∀ (ℓ : AxisParallelLine params) (t a : Fq params),
    (postprocess ((M (AxisParallelLine.rebaseAt ℓ t)).toSubMeas) (· zeroCoord)).outcome a =
      (postprocess ((M ℓ).toSubMeas) (fun f => f t)).outcome a

namespace AxisParallelLine

/-- Transport an axis-parallel-line measurement along rebasing of the line
question by translating its polynomial outcomes. -/
noncomputable def transportMeasurement {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ProjMeas (AxisLinePolynomial params) ι) (t : Fq params) :
    ProjMeas (AxisLinePolynomial params) ι :=
  ProjMeas.transport (AxisLinePolynomial.reparamAtEquiv (params := params) t) M

/-- Evaluating a transported axis-line measurement at `zeroCoord` agrees with
reading the original measurement at the rebasing parameter. -/
theorem transportMeasurement_postprocess_zero
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ProjMeas (AxisLinePolynomial params) ι) (t a : Fq params) :
    (postprocess (transportMeasurement (params := params) M t).toSubMeas
        (· zeroCoord)).outcome a =
      (postprocess M.toSubMeas (fun f => f t)).outcome a := by
  have h :=
    SubMeas.postprocess_transport
      (e := AxisLinePolynomial.reparamAtEquiv (params := params) t)
      (A := M.toSubMeas)
      (f := fun g : AxisLinePolynomial params => g zeroCoord)
  simpa [transportMeasurement, AxisLinePolynomial.reparamAtEquiv,
    AxisLinePolynomial.reparamAt_apply_zero, addCoord, zeroCoord] using
    congrArg (fun A => A.outcome a) h

end AxisParallelLine

namespace DiagonalLine

/-- Transport a diagonal-line measurement along rebasing of the line question by
translating its polynomial outcomes. -/
noncomputable def transportMeasurement {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ProjMeas (DiagonalLinePolynomial params) ι) (t : Fq params) :
    ProjMeas (DiagonalLinePolynomial params) ι :=
  ProjMeas.transport (DiagonalLinePolynomial.reparamAtEquiv (params := params) t) M



end DiagonalLine

/-- Stronger rebasing compatibility for axis-parallel-line measurements: the
measurement indexed by the rebased line is equal to the transport of the
original measurement along the answer reparametrization equivalence. -/
def AxisParallelMeasurementTransportInvariant (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι) : Prop :=
  ∀ (ℓ : AxisParallelLine params) (t : Fq params),
    M (AxisParallelLine.rebaseAt ℓ t) =
      AxisParallelLine.transportMeasurement (params := params) (M ℓ) t

/-- Stronger rebasing compatibility for diagonal-line measurements: the
measurement indexed by the rebased line is equal to the transport of the
original measurement along the answer reparametrization equivalence. -/
def DiagonalMeasurementTransportInvariant (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι) : Prop :=
  ∀ (ℓ : DiagonalLine params) (t : Fq params),
    M (DiagonalLine.rebaseAt ℓ t) =
      DiagonalLine.transportMeasurement (params := params) (M ℓ) t





/-- Direct axis-parallel outcome covariance implies transport-level covariance. -/
theorem AxisParallelMeasurementReparamInvariant.toTransportInvariant
    {params : Parameters} [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι}
    (hM : AxisParallelMeasurementReparamInvariant params M) :
    AxisParallelMeasurementTransportInvariant params M := by
  intro ℓ t
  ext a : 1
  obtain ⟨f, rfl⟩ :=
    (AxisLinePolynomial.reparamAtEquiv (params := params) t).surjective a
  change (M (ℓ.rebaseAt t)).outcome (AxisLinePolynomial.reparamAt f t) = _
  rw [hM ℓ t f]
  simp [AxisParallelLine.transportMeasurement, ProjMeas.transport,
    Measurement.transport, SubMeas.transport]

/-- Direct diagonal outcome covariance implies transport-level covariance. -/
theorem DiagonalMeasurementReparamInvariant.toTransportInvariant
    {params : Parameters} [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι}
    (hM : DiagonalMeasurementReparamInvariant params M) :
    DiagonalMeasurementTransportInvariant params M := by
  intro ℓ t
  ext a : 1
  obtain ⟨f, rfl⟩ :=
    (DiagonalLinePolynomial.reparamAtEquiv (params := params) t).surjective a
  change (M (ℓ.rebaseAt t)).outcome (DiagonalLinePolynomial.reparamAt f t) = _
  rw [hM ℓ t f]
  simp [DiagonalLine.transportMeasurement, ProjMeas.transport,
    Measurement.transport, SubMeas.transport]





/-- The stronger transport-level axis-parallel compatibility implies the older
outcome-level reparametrization invariant predicate. -/
theorem AxisParallelMeasurementTransportInvariant.toEvaluationReparamInvariant
    {params : Parameters} [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι}
    (hM : AxisParallelMeasurementTransportInvariant params M) :
    AxisParallelEvaluationReparamInvariant params M := by
  intro ℓ t a
  rw [hM ℓ t]
  exact AxisParallelLine.transportMeasurement_postprocess_zero
    (params := params) (M := M ℓ) t a



/-- Axis-parallel line measurements bundled with the stronger transport-level
rebasing covariance. -/
structure AxisParallelCovariantMeasurement (params : Parameters)
    [FieldModel params.q] (ι : Type*) [Fintype ι] [DecidableEq ι] where
  toIdxProjMeas :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι
  transportInvariant :
    AxisParallelMeasurementTransportInvariant params toIdxProjMeas

instance {params : Parameters} [FieldModel params.q] {ι : Type*}
    [Fintype ι] [DecidableEq ι] :
    CoeFun (AxisParallelCovariantMeasurement params ι)
      (fun _ => AxisParallelLine params → ProjMeas (AxisLinePolynomial params) ι) where
  coe M := M.toIdxProjMeas

namespace AxisParallelCovariantMeasurement

/-- A covariant wrapper automatically satisfies the older evaluation-level
rebasing invariant. -/
theorem reparamInvariant {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : AxisParallelCovariantMeasurement params ι) :
    AxisParallelEvaluationReparamInvariant params M.toIdxProjMeas :=
  M.transportInvariant.toEvaluationReparamInvariant

end AxisParallelCovariantMeasurement

/-- Diagonal line measurements bundled with the stronger transport-level
rebasing covariance. -/
structure DiagonalCovariantMeasurement (params : Parameters)
    [FieldModel params.q] (ι : Type*) [Fintype ι] [DecidableEq ι] where
  toIdxProjMeas :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι
  transportInvariant :
    DiagonalMeasurementTransportInvariant params toIdxProjMeas

instance {params : Parameters} [FieldModel params.q] {ι : Type*}
    [Fintype ι] [DecidableEq ι] :
    CoeFun (DiagonalCovariantMeasurement params ι)
      (fun _ => DiagonalLine params → ProjMeas (DiagonalLinePolynomial params) ι) where
  coe M := M.toIdxProjMeas

namespace DiagonalCovariantMeasurement



end DiagonalCovariantMeasurement

/-- Transport covariance for diagonal-line measurements whose answers are the
paper-level line functions. -/
def DiagonalAnswerMeasurementTransportInvariant (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (DiagonalLine params) (DiagonalLineAnswer params) ι) : Prop :=
  ∀ (ℓ : DiagonalLine params) (t : Fq params),
    M (DiagonalLine.rebaseAt ℓ t) =
      ProjMeas.transport (DiagonalLineAnswer.reparamAtEquiv t) (M ℓ)

/-- Diagonal-line measurements with paper-level function answers, bundled with
transport-level rebasing covariance.

This parallel API is intended for the paper-faithful restriction redesign: unlike
`DiagonalLinePolynomial`, the function-answer alphabet admits a total slice
append/restrict equivalence. -/
structure DiagonalAnswerCovariantMeasurement (params : Parameters)
    [FieldModel params.q] (ι : Type*) [Fintype ι] [DecidableEq ι] where
  toIdxProjMeas :
    IdxProjMeas (DiagonalLine params) (DiagonalLineAnswer params) ι
  transportInvariant :
    DiagonalAnswerMeasurementTransportInvariant params toIdxProjMeas

instance {params : Parameters} [FieldModel params.q] {ι : Type*}
    [Fintype ι] [DecidableEq ι] :
    CoeFun (DiagonalAnswerCovariantMeasurement params ι)
      (fun _ => DiagonalLine params → ProjMeas (DiagonalLineAnswer params) ι) where
  coe M := M.toIdxProjMeas

/-- Paper-level symmetric strategy data whose diagonal-line answers are functions.

This parallel structure is the target shape for the restriction redesign in
Section 6: restricting an ambient diagonal line to a slice is total for function
answers, unlike the current degree-bounded `DiagonalLinePolynomial` alphabet. -/
structure AnswerSymStrat (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  state : QuantumState (ι × ι)
  permInvState : PermInvState state
  densityFixed : swapDensity state.density = state.density
  isNormalized : state.IsNormalized
  pointMeasurement : IdxProjMeas (Point params) (Fq params) ι
  axisParallelMeasurement : AxisParallelCovariantMeasurement params ι
  diagonalMeasurement : DiagonalAnswerCovariantMeasurement params ι

/-- Paper-local symmetric strategy data.

The line-measurement fields are bundled as transport-covariant wrappers:
rebasing the question index is required to agree with transporting the
projective measurement along the corresponding answer reparametrization
equivalence. This is stronger than the older evaluation-level formulas
at `zeroCoord`, but those formulas remain available as derived lemmas via
`AxisParallelCovariantMeasurement.reparamInvariant` and
`DiagonalCovariantMeasurement.reparamInvariant`.

The `isNormalized` field records that the bipartite state's density
operator has normalized trace `1`. For pure states, this coincides
with the usual unit-vector condition (`⟨ψ|ψ⟩ = 1`) used in the paper.
Bundling normalization with the strategy avoids threading a
`state.IsNormalized` hypothesis through every downstream consumer
(pasting cascade, `triangleSub` users, self-improvement helpers). -/
structure SymStrat (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  state : QuantumState (ι × ι)  -- bipartite state on ℋ ⊗ ℋ
  permInvState : PermInvState state
  densityFixed : swapDensity state.density = state.density
  isNormalized : state.IsNormalized
  pointMeasurement : IdxProjMeas (Point params) (Fq params) ι
  axisParallelMeasurement : AxisParallelCovariantMeasurement params ι
  diagonalMeasurement : DiagonalCovariantMeasurement params ι

-- NOTE: no global `Inhabited` instance for `SymStrat`; constructing default
-- projective measurement families is non-canonical and requires additional
-- assumptions on outcome types.

/-- Encoded samples `(u, i)` for the axis-parallel lines test.
The paper samples a random point `u ∈ F_q^m` and a coordinate
`i ∈ {1, …, m}`. In Lean, `Fin params.m` represents the 0-indexed
coordinates `{0, …, m - 1}`, corresponding to the paper's 1-indexed
choice. The sample forms the axis-parallel line through `u` in that
coordinate direction. -/
abbrev AxisParallelTestSample (params : Parameters) :=
  Point params × Fin params.m

/-- Extend restricted direction coordinates to a full direction vector.
For restriction index `j` (0-indexed), the first `j + 1` coordinates
are the given free coordinates and the remaining are zero.
This matches the paper's convention that `v` has its last `m − i`
coordinates zero, where `i = j + 1`. -/
def extendRestrictedDirection {params : Parameters}
    [FieldModel params.q] (j : Fin params.m)
    (freeCoords : Fin (j.val + 1) → Fq params) :
    Point params :=
  fun k =>
    if h : k.val ≤ j.val then
      freeCoords ⟨k.val, Nat.lt_succ_of_le h⟩
    else zeroCoord

/-- Encoded samples `(u, freeCoords)` for the `j`-restricted diagonal
lines test. The base point `u ∈ F_q^m` and the free coordinates of
the restricted direction (first `j + 1` coordinates; rest are zero).
The full diagonal test averages over `j ∈ {0, …, m − 1}`. -/
abbrev RestrictedDiagonalSample (params : Parameters)
    (j : Fin params.m) :=
  Point params × (Fin (j.val + 1) → Fq params)

/-- The restricted diagonal sample space is nonempty. -/
instance restrictedDiagonalSampleNonempty (params : Parameters) (j : Fin params.m) :
    Nonempty (RestrictedDiagonalSample params j) :=
  inferInstance

/-- Sampled point answers in the axis-parallel lines test, obtained from a
point measurement. -/
noncomputable abbrev axisParallelPointAnswerFamilyOf
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (pointMeasurement : IdxProjMeas (Point params) (Fq params) ι) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ι :=
  fun s => (pointMeasurement s.1).toSubMeas

/-- Sampled line answers in the axis-parallel lines test, obtained from an
axis-parallel measurement and evaluated at the base point. -/
noncomputable abbrev axisParallelLineAnswerFamilyOf
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (axisParallelMeasurement :
      AxisParallelLine params → ProjMeas (AxisLinePolynomial params) ι) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ι :=
  fun s =>
    let ℓ : AxisParallelLine params :=
      { base := s.1, direction := s.2 }
    postprocess
      ((axisParallelMeasurement ℓ).toSubMeas)
      (· zeroCoord)

/-- Sampled point answers in the restricted diagonal test, obtained from a
point measurement. -/
noncomputable abbrev diagonalPointAnswerFamilyOf
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (pointMeasurement : IdxProjMeas (Point params) (Fq params) ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
  fun s => (pointMeasurement s.1).toSubMeas

/-- Sampled diagonal-line answers in the restricted diagonal test, obtained from
a diagonal-line measurement and evaluated at the base point. -/
noncomputable abbrev diagonalLineAnswerFamilyOf
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Answer : Type*} [Fintype Answer]
    (diagonalMeasurement : DiagonalLine params → ProjMeas Answer ι)
    (evalAtBase : Answer → Fq params)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    let ℓ : DiagonalLine params :=
      { base := s.1, direction := v }
    postprocess
      ((diagonalMeasurement ℓ).toSubMeas)
      evalAtBase

/-- Sampled point answers in the axis-parallel lines test.
The point player receives `u` (the base point) and answers with
their measurement at `u`. -/
noncomputable def axisParallelPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params)
      (Fq params) ι :=
  axisParallelPointAnswerFamilyOf strategy.pointMeasurement

/-- Sampled line answers in the axis-parallel lines test,
evaluated at the base point `u`.
The line player receives `ℓ` and returns a polynomial `f`.
The verifier checks `f(u) = a`; since `u = ℓ.pointAt zeroCoord`,
we evaluate `f` at `zeroCoord`. -/
noncomputable def axisParallelLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params)
      (Fq params) ι :=
  axisParallelLineAnswerFamilyOf strategy.axisParallelMeasurement

-- Paper: `not:conditioned-on-last-direction` abbreviates the axis-parallel
-- line in the last coordinate direction of `F_q^(m+1)` by its base point `u`.


-- Paper: `not:conditioned-on-last-direction` writes `B^u` for the axis-parallel
-- line measurement conditioned on the last direction choice.


/-- Sampled point answers in the `j`-restricted diagonal test.
The point player receives `u` and answers at `u`. -/
noncomputable def diagonalPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j)
      (Fq params) ι :=
  diagonalPointAnswerFamilyOf strategy.pointMeasurement j

/-- Sampled diagonal-line answers in the `j`-restricted diagonal
test, evaluated at the base point `u`.
Since `u = ℓ.pointAt zeroCoord`, we evaluate `f` at
`zeroCoord`. -/
noncomputable def diagonalLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j)
      (Fq params) ι :=
  diagonalLineAnswerFamilyOf strategy.diagonalMeasurement (· zeroCoord) j

namespace AnswerSymStrat

/-- Sampled point answers in the axis-parallel lines test for an answer-valued
symmetric strategy. -/
noncomputable def axisParallelPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ι :=
  axisParallelPointAnswerFamilyOf strategy.pointMeasurement

/-- Sampled line answers in the axis-parallel lines test for an answer-valued
symmetric strategy, evaluated at the base point. -/
noncomputable def axisParallelLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ι :=
  axisParallelLineAnswerFamilyOf strategy.axisParallelMeasurement

/-- Sampled point answers in the restricted diagonal test for an answer-valued
symmetric strategy. -/
noncomputable def diagonalPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
  diagonalPointAnswerFamilyOf strategy.pointMeasurement j

/-- Sampled diagonal-line answers in the restricted diagonal test for an
answer-valued symmetric strategy, evaluated at the base point. -/
noncomputable def diagonalLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
  diagonalLineAnswerFamilyOf strategy.diagonalMeasurement (· zeroCoord) j

/-- Axis-parallel failure surrogate for an answer-valued symmetric strategy. -/
noncomputable def axisParallelFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamily strategy)
    (axisParallelLineAnswerFamily strategy)

/-- Self-consistency failure surrogate for an answer-valued symmetric strategy. -/
noncomputable def selfConsistencyFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι) : Error :=
  bipartiteSSCError strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)

/-- Diagonal-line failure surrogate for an answer-valued symmetric strategy. -/
noncomputable def diagonalFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      bipartiteConsError strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (diagonalPointAnswerFamily strategy j)
        (diagonalLineAnswerFamily strategy j)

/-- Goodness data for an answer-valued symmetric strategy. -/
structure IsGood {params : Parameters}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error) : Prop where
  /-- The axis-parallel test fails with probability at most `eps`. -/
  axisParallelTest : strategy.axisParallelFailureProbability ≤ eps
  /-- The self-consistency test fails with probability at most `delta`. -/
  selfConsistencyTest : strategy.selfConsistencyFailureProbability ≤ delta
  /-- The diagonal-line test fails with probability at most `gamma`. -/
  diagonalLineTest : strategy.diagonalFailureProbability ≤ gamma

end AnswerSymStrat

/-- Paper-faithful two-space projective strategy data.

This matches the paper's `def:general-projective-strategy`
(`test_definition.tex`, lines 98--115): Alice's and Bob's measurements act on
separate local carriers `ιA` and `ιB`, and the bipartite state lives on
`ιA × ιB` without a built-in swap symmetry.

The `isNormalized` field records that the bipartite state's density operator
has normalized trace `1`.

The four covariance conditions express that the line-indexed projectors
descend from chosen affine parametrizations to geometric lines; transport and
zero-coordinate evaluation are equivalent consequences. -/
structure ProjStrat (params : Parameters) [FieldModel params.q]
    (ιA : Type*) [Fintype ιA] [DecidableEq ιA]
    (ιB : Type*) [Fintype ιB] [DecidableEq ιB] where
  /-- Bipartite state on the tensor product of Alice's and Bob's local carriers. -/
  state : QuantumState (ιA × ιB)
  /-- The bipartite state's density operator is trace-normalized. -/
  isNormalized : state.IsNormalized
  /-- Alice's point-measurement family, acting on `ιA`. -/
  pointMeasurementA : IdxProjMeas (Point params) (Fq params) ιA
  /-- Alice's axis-parallel-line measurement family, acting on `ιA`. -/
  axisParallelMeasurementA :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ιA
  /-- Alice's axis-parallel measurement is covariant under line rebasing. -/
  axisParallelReparamInvariantA :
    AxisParallelMeasurementReparamInvariant params axisParallelMeasurementA
  /-- Alice's diagonal-line measurement family, acting on `ιA`. -/
  diagonalMeasurementA :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ιA
  /-- Alice's diagonal measurement is covariant under line rebasing. -/
  diagonalReparamInvariantA :
    DiagonalMeasurementReparamInvariant params diagonalMeasurementA
  /-- Bob's point-measurement family, acting on `ιB`. -/
  pointMeasurementB : IdxProjMeas (Point params) (Fq params) ιB
  /-- Bob's axis-parallel-line measurement family, acting on `ιB`. -/
  axisParallelMeasurementB :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ιB
  /-- Bob's axis-parallel measurement is covariant under line rebasing. -/
  axisParallelReparamInvariantB :
    AxisParallelMeasurementReparamInvariant params axisParallelMeasurementB
  /-- Bob's diagonal-line measurement family, acting on `ιB`. -/
  diagonalMeasurementB :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ιB
  /-- Bob's diagonal measurement is covariant under line rebasing. -/
  diagonalReparamInvariantB :
    DiagonalMeasurementReparamInvariant params diagonalMeasurementB

end MIPStarRE.LDT

end

end LIDT


