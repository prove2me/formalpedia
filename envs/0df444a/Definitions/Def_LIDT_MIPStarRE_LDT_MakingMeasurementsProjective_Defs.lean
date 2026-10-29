-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
-- name    : LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:51:36.650414+00:00
-- url     : https://prove2.me/theorems/ffc23e02-6b59-4006-8225-c8b683103efc
-- title:
--   LIDT definitions: LDT / MakingMeasurementsProjective / Defs
-- statement:
--   This bundle defines the concrete finite-matrix objects used by the projectivization construction. It connects matrix-level submeasurements and measurements with the paper-local structures and packages the one-measurement and questionwise Naimark data.
--
--   Principal definitions:
--   - `FiniteHilbertSpace`: a finite index type used as a finite-dimensional Hilbert-space carrier.
--   - `MatrixOperator`: a square complex matrix operator on a finite carrier.
--   - `PositiveMatrixState`: a positive matrix used as a possibly unnormalized state witness.
--   - `MatrixSubmeasurement`: a matrix-valued submeasurement with positive effects summing below the identity.
--   - `MatrixMeasurement`: a matrix-valued measurement with effects summing to the identity.
--   - `toSubMeas`: conversion from a concrete matrix submeasurement to the paper-local submeasurement structure.
--   - `OneMeasNaimarkData`: Naimark dilation data for one measurement.
--   - `NaimarkData`: question-indexed Naimark data for the full assembly.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MakingMeasurementsProjective/Defs.lean#L53-L305

-- Generated from MIPStarRE/LDT/MakingMeasurementsProjective/Defs.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib

namespace LIDT

/-!
# Section 5 — Making measurements projective: definitions

Definitions for Naimark dilation and orthonormalization, matching
Section 5 of `references/ldt-paper/orthonormalization.tex` and
Chapter 4 of the blueprint (`blueprint/src/chapter/ch04_projective.tex`).

## Naimark dilation structure

The key mathematical content is the **Naimark dilation theorem**: given
submeasurements on a bipartite space, there exist auxiliary registers and
projective measurements on the enlarged space that preserve all correlations
exactly.

### One-measurement Naimark (Lemma 5.2)

The building block is the one-measurement Naimark lemma. Given a
submeasurement `{M_a}_{a ∈ α}` on `Op d`, it produces a projective
submeasurement on the enlarged space `Op (d × Option α)`. The auxiliary
register has dimension `|α| + 1`, with the extra dimension absorbing the
"missing mass" `I − ∑ M_a`. The construction uses the isometry
`V|ψ⟩ = ∑_a √M_a |ψ⟩ ⊗ |a⟩ + √(I−M)|ψ⟩ ⊗ |⊥⟩` and defines
`P̂_a = V† (I ⊗ |a⟩⟨a|) V`.

### Questionwise Naimark data

For a prospective full bipartite assembly, one-measurement Naimark is applied
independently to each question on each side.  The current formal interface
records these questionwise local data and their marginal preservation
identities, not the full tensor-product correlation theorem.

## Matrix-level witnesses

Concrete `Matrix d d ℂ` witnesses are provided alongside the abstract
operator-algebra formulation, giving honest probability and overlap formulas.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-! ### Finite Hilbert space infrastructure -/

/-- A finite-dimensional Hilbert space represented by a finite index type. -/
structure FiniteHilbertSpace where
  carrier : Type*
  instFintype : Fintype carrier
  instDecidableEq : DecidableEq carrier
  instNonempty : Nonempty carrier

attribute [instance] FiniteHilbertSpace.instFintype
attribute [instance] FiniteHilbertSpace.instDecidableEq
attribute [instance] FiniteHilbertSpace.instNonempty

/-- Concrete operators on a finite Hilbert space. -/
abbrev MatrixOperator (H : FiniteHilbertSpace) :=
  MIPStarRE.Quantum.Op H.carrier

namespace MatrixOperator

/-! The SDP separation argument uses the elementwise finite-matrix norm.  These
instances record that choice once for the project's concrete operator type,
rather than reintroducing it in each analytic argument. -/

noncomputable instance seminormedAddCommGroup
    (H : FiniteHilbertSpace) :
    SeminormedAddCommGroup (MatrixOperator H) :=
  Matrix.seminormedAddCommGroup

noncomputable instance normedAddCommGroup
    (H : FiniteHilbertSpace) :
    NormedAddCommGroup (MatrixOperator H) :=
  Matrix.normedAddCommGroup

noncomputable instance normedSpace
    (H : FiniteHilbertSpace) :
    NormedSpace ℝ (MatrixOperator H) :=
  Matrix.normedSpace

instance firstCountableTopology
    (H : FiniteHilbertSpace) :
    FirstCountableTopology (MatrixOperator H) :=
  inferInstanceAs (FirstCountableTopology (H.carrier → H.carrier → ℂ))

noncomputable instance locallyConvexSpace
    (H : FiniteHilbertSpace) :
    LocallyConvexSpace ℝ (MatrixOperator H) :=
  NormedSpace.toLocallyConvexSpace

end MatrixOperator

/-- A positive operator used as a possibly unnormalized state witness. -/
structure PositiveMatrixState (H : FiniteHilbertSpace) where
  matrix : MatrixOperator H
  positive : 0 ≤ matrix

/-- Concrete submeasurements on a finite Hilbert space. -/
abbrev MatrixSubmeasurement (Outcome : Type*)
    [Fintype Outcome] [DecidableEq Outcome] (H : FiniteHilbertSpace) :=
  MIPStarRE.Quantum.Submeasurement Outcome H.carrier

/-- Concrete measurements on a finite Hilbert space. -/
abbrev MatrixMeasurement (Outcome : Type*)
    [Fintype Outcome] [DecidableEq Outcome] (H : FiniteHilbertSpace) :=
  MIPStarRE.Quantum.Measurement Outcome H.carrier

namespace MatrixSubmeasurement

/-- View a concrete matrix submeasurement as the paper-local submeasurement
structure. -/
noncomputable def toSubMeas {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (M : MatrixSubmeasurement Outcome H) : SubMeas Outcome H.carrier where
  outcome := M.effect
  total := MIPStarRE.Quantum.Submeasurement.total M
  outcome_pos := M.pos
  sum_eq_total := rfl
  total_le_one := M.sum_le_one

@[simp] theorem toSubMeas_outcome {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (M : MatrixSubmeasurement Outcome H) (a : Outcome) :
    (toSubMeas M).outcome a = M.effect a :=
  rfl

@[simp] theorem toSubMeas_total {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (M : MatrixSubmeasurement Outcome H) :
    (toSubMeas M).total = MIPStarRE.Quantum.Submeasurement.total M :=
  rfl

end MatrixSubmeasurement

namespace MatrixMeasurement

/-- View a concrete matrix measurement as the paper-local measurement
structure. -/
noncomputable def toMeasurement {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (M : MatrixMeasurement Outcome H) : MIPStarRE.LDT.Measurement Outcome H.carrier where
  toSubMeas := MatrixSubmeasurement.toSubMeas M.toSubmeasurement
  total_eq_one := M.sum_eq_one

@[simp] theorem toMeasurement_toSubMeas {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (M : MatrixMeasurement Outcome H) :
    (toMeasurement M).toSubMeas =
      MatrixSubmeasurement.toSubMeas M.toSubmeasurement :=
  rfl

@[simp] theorem toMeasurement_outcome {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (M : MatrixMeasurement Outcome H) (a : Outcome) :
    (toMeasurement M).outcome a = M.effect a :=
  rfl

end MatrixMeasurement

/-- The concrete expectation `τ(ρ X)` on the local matrix layer. -/
noncomputable def matrixExpectation {H : FiniteHilbertSpace}
    (ρ : PositiveMatrixState H) (X : MatrixOperator H) : ℂ :=
  MIPStarRE.Quantum.normalizedTrace (ρ.matrix * X)

/-! ### One-measurement Naimark dilation (Lemma 5.2)

The one-measurement Naimark dilation is the building block for the full
theorem. Given a submeasurement `M` on space `d`, it produces a projective
submeasurement on the enlarged space `d × Option α`, where `Option α`
models the auxiliary register with one extra dimension `none = ⊥` for the
missing mass `I − ∑ M_a`. -/

/-- The auxiliary pure-state projector `|⊥⟩⟨⊥|` on `Option α`, where `⊥ = none`.
This is the initial state of the auxiliary register before the Naimark
isometry is applied. -/
def naimarkAuxProjector (α : Type*) [Fintype α] [DecidableEq α] :
    MIPStarRE.Quantum.Op (Option α) :=
  Matrix.single none none 1

/-- The lifted density matrix for one-measurement Naimark dilation:
`ρ_lifted = |Option α| · (ρ ⊗ |⊥⟩⟨⊥|)`.
The scaling by `|Option α|` ensures the normalized trace is preserved:
`τ'(ρ_lifted) = τ(ρ)`, where `τ'` is the normalized trace on the enlarged space. -/
noncomputable def oneMeasLiftedDensity {d : Type*} [Fintype d] [DecidableEq d]
    (α : Type*) [Fintype α] [DecidableEq α]
    (ρ : MIPStarRE.Quantum.Op d) :
    MIPStarRE.Quantum.Op (d × Option α) :=
  (Fintype.card (Option α) : ℂ) • Matrix.kronecker ρ (naimarkAuxProjector α)

/-- One-measurement Naimark dilation data at the matrix level.

Given a submeasurement `M : Submeasurement α d`, this witnesses the existence
of a projective submeasurement on the enlarged space `d × Option α` that
preserves all expectation values. This is Lemma 5.2 of the paper.

The construction: let `V : H → H ⊗ ℂ^{|α|+1}` be the isometry
`V|ψ⟩ = ∑_a √M_a |ψ⟩ ⊗ |a⟩ + √(I−M)|ψ⟩ ⊗ |⊥⟩`.
Then `P̂_a = V† (I ⊗ |a⟩⟨a|) V` is a projection, and
`⟨ψ|M_a|ψ⟩ = ⟨ψ⊗⊥|P̂_a|ψ⊗⊥⟩`. -/
structure OneMeasNaimarkData (α : Type*) [Fintype α] [DecidableEq α]
    (d : Type*) [Fintype d] [DecidableEq d] where
  /-- The source submeasurement being dilated. -/
  source : MIPStarRE.Quantum.Submeasurement α d
  /-- The dilated projective effects on `d × Option α`.
  For outcome `some a`, this is the Naimark projector `P̂_a`.
  For outcome `none`, this is the projector for the "missing mass". -/
  liftedEffect : Option α → MIPStarRE.Quantum.Op (d × Option α)
  /-- Each lifted effect is a genuine orthogonal projection. Positivity follows
  from `IsStarProjection.nonneg`. -/
  lifted_isProj : ∀ a, MIPStarRE.Quantum.IsProj (liftedEffect a)
  /-- The lifted projections sum to at most identity (which together with
  `lifted_isProj` implies mutual orthogonality). -/
  lifted_sum_le_one : ∑ a, liftedEffect a ≤ 1
  /-- **Expectation preservation**: for any operator `ρ` on `Op d`,
  the expectation of outcome `a` under the original submeasurement equals
  the expectation under the dilated projective submeasurement with the
  Naimark-lifted state. The identity is linear, so it holds for all operators,
  not just density matrices. This is the core content of the dilation. -/
  expectation_preservation : ∀ (ρ : MIPStarRE.Quantum.Op d) (a : α),
    MIPStarRE.Quantum.normalizedTrace (ρ * source.effect a) =
      MIPStarRE.Quantum.normalizedTrace
        (oneMeasLiftedDensity α ρ * liftedEffect (some a))

/-- Positivity of a lifted Naimark effect, derived from its projectivity.

Lean-only consequence of the one-measurement Naimark data: the paper records
the lifted effects as projections, and positivity is supplied here by the
Mathlib star-projection order theorem through `IsStarProjection.nonneg`. -/
theorem OneMeasNaimarkData.lifted_pos {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (data : OneMeasNaimarkData α d) (a : Option α) :
    0 ≤ data.liftedEffect a :=
  (data.lifted_isProj a).nonneg

/-! ### Questionwise Naimark data

The current Lean data applies one-measurement Naimark independently to each
question on each side. -/

/-- Questionwise Naimark data for the prospective full assembly.

Given submeasurements on space `ι`, this carries the questionwise
one-measurement Naimark dilations used as the local building blocks for the
full tensor-product assembly. -/
structure NaimarkData (QuestionA OutcomeA QuestionB OutcomeB : Type*)
    (ι : Type*)
    [Fintype QuestionA] [DecidableEq QuestionA]
    [Fintype OutcomeA] [DecidableEq OutcomeA]
    [Fintype QuestionB] [DecidableEq QuestionB]
    [Fintype OutcomeB] [DecidableEq OutcomeB]
    [Fintype ι] [DecidableEq ι] where
  /-- Alice's questionwise one-measurement Naimark dilations. -/
  left : (x : QuestionA) → OneMeasNaimarkData OutcomeA ι
  /-- Bob's questionwise one-measurement Naimark dilations. -/
  right : (y : QuestionB) → OneMeasNaimarkData OutcomeB ι

-- NOTE: no global `Inhabited` instance for `NaimarkData`:
-- constructing defaults for projective measurements is mathematically non-canonical
-- and would require additional assumptions on outcome types.

/-! ### Error functions for orthonormalization -/

/-- The explicit error in `thm:orthonormalization`. -/
noncomputable def orthonormalizationError (ζ : Error) : Error :=
  100 * Real.rpow ζ (1 / (4 : Error))



/-- The explicit error in the measurement version of the lemma. -/
noncomputable def orthonormalizationMainLemmaError (ζ : Error) : Error :=
  84 * Real.rpow ζ (1 / (4 : Error))

/-- The almost-projective error extracted from a consistency hypothesis. -/
def consistencyToAlmostProjectiveError (ζ : Error) : Error :=
  2 * ζ

/-- The spectral-truncation error when rounding one almost-projective effect to a
    projection via eigenvalue truncation. Dominated by `√ζ`. -/
noncomputable def spectralTruncationError (ζ : Error) : Error :=
  Real.rpow ζ (1 / (2 : Error))

/-- The rounding error when converting an almost-projective POVM to a projective submeasurement. -/
noncomputable def roundingToProjectiveError (ζ : Error) : Error :=
  12 * Real.rpow ζ (1 / (2 : Error))

end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT


