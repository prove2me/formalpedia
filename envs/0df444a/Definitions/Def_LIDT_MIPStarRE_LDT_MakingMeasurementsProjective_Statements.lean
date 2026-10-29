-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
-- name    : LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:40:34.482536+00:00
-- url     : https://prove2.me/theorems/1f9554b5-6d5b-4d88-beb1-61ce91eabe00
-- title:
--   LIDT definitions: LDT / MakingMeasurementsProjective / Statements
-- statement:
--   This bundle defines the statement records for Naimark dilation and projective measurement repair. It packages one-measurement and tensor-product interfaces, register extensions, almost-projective hypotheses, spectral truncation, and rounded projective measurement conclusions.
--
--   Principal definitions:
--   - `OneMeasNaimarkLemma`: the one-measurement Naimark lemma statement.
--   - `NaimarkStatement`: the questionwise Naimark dilation interface.
--   - `naimarkProductExtensionDensity`: the density matrix of the extended tensor-product state.
--   - `naimarkProductExtensionEquiv`: the canonical register-order equivalence.
--   - `NaimarkTensorProductCorrelationData`: witness data for the tensor-product correlation theorem.
--   - `AlmostProjMeasStatement`: the almost-projective measurement hypothesis.
--   - `SpectralTruncationStatement`: the spectral truncation conclusion.
--   - `RoundedProjMeasStatement`: the rounded projective measurement conclusion.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MakingMeasurementsProjective/Statements.lean#L45-L372

-- Generated from MIPStarRE/LDT/MakingMeasurementsProjective/Statements.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

/-!
# Section 5 — Statements

Statements for Naimark dilation, one-measurement Naimark, the
orthogonalization lemma, rounding to projectors, rank reduction, and completing
to measurement.

## Naimark dilation statements

The **one-measurement Naimark lemma** (`OneMeasNaimarkLemma`) is the
building block: any submeasurement can be dilated to a projective
submeasurement on a space enlarged by one auxiliary register.

The questionwise **Naimark interface** (`NaimarkStatement`) records the
per-question one-measurement dilations and their single-outcome marginal
preservation identities.  It is not the full tensor-product statement of
`\label{thm:naimark}`.

The source theorem form is recorded separately as
`NaimarkTensorProductCorrelationStatement` and
`naimarkTensorProductCorrelation`.  This statement contains the full
bipartite auxiliary-state and correlation-preservation conclusion of
`\label{thm:naimark}` in the projective-submeasurement form supplied by the
paper's one-measurement helper.  The proof is the tensor-product assembly
implemented in `NaimarkFull.lean`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

universe u

/-! ### One-measurement Naimark statement -/

/-- Statement of the one-measurement Naimark lemma (Lemma 5.2).

For any submeasurement `M` on `Op d`, there exists a one-measurement
Naimark dilation on the enlarged space `Op (d × Option α)`. -/
def OneMeasNaimarkLemma (α : Type*) [Fintype α] [DecidableEq α]
    (d : Type*) [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) : Prop :=
  ∃ data : OneMeasNaimarkData α d, data.source = M

/-! ### Questionwise Naimark interface -/

/-- Paper origin: Lean-only questionwise interface below
`docs/paper-gaps/naimark-dilation.tex`.

The paper's full tensor-product Naimark dilation
(`references/ldt-paper/orthonormalization.tex:36-115`,
`\label{thm:naimark}`) is formalized separately by
`NaimarkTensorProductCorrelationStatement`.  This structure records the
per-question one-measurement dilations of
`\label{lem:naimark-helper}`
(`references/ldt-paper/orthonormalization.tex:121-159`) together with the
single-outcome marginal-preservation conclusions used by downstream
projectivization arguments.

This records the questionwise one-measurement Naimark dilations that appear in
the proof of the full theorem: each `A x` and `B y` is equipped with a local
projective dilation preserving all single-outcome expectations. The
tensor-product assembly of the paper theorem is the separate source-facing
theorem `naimarkTensorProductCorrelation`. -/
structure NaimarkStatement {QuestionA OutcomeA QuestionB OutcomeB : Type*}
    {ι : Type*}
    [Fintype QuestionA] [DecidableEq QuestionA]
    [Fintype OutcomeA] [DecidableEq OutcomeA]
    [Fintype QuestionB] [DecidableEq QuestionB]
    [Fintype OutcomeB] [DecidableEq OutcomeB]
    [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (A : IdxSubMeas QuestionA OutcomeA ι)
    (B : IdxSubMeas QuestionB OutcomeB ι)
    (data : NaimarkData QuestionA OutcomeA QuestionB OutcomeB ι) : Prop where
  /-- Alice's local dilations are attached to the correct source submeasurements. -/
  leftSource : ∀ x : QuestionA, (data.left x).source.effect = (A x).outcome
  /-- Bob's local dilations are attached to the correct source submeasurements. -/
  rightSource : ∀ y : QuestionB, (data.right y).source.effect = (B y).outcome
  /-- Alice's single-outcome expectations are preserved by each local dilation. -/
  leftMarginalPreservation :
    ∀ x : QuestionA, ∀ (ρ : MIPStarRE.Quantum.Op ι) (a : OutcomeA),
      MIPStarRE.Quantum.normalizedTrace (ρ * (A x).outcome a) =
        MIPStarRE.Quantum.normalizedTrace
          (oneMeasLiftedDensity OutcomeA ρ * (data.left x).liftedEffect (some a))
  /-- Bob's single-outcome expectations are preserved by each local dilation. -/
  rightMarginalPreservation :
    ∀ y : QuestionB, ∀ (ρ : MIPStarRE.Quantum.Op ι) (b : OutcomeB),
      MIPStarRE.Quantum.normalizedTrace (ρ * (B y).outcome b) =
        MIPStarRE.Quantum.normalizedTrace
          (oneMeasLiftedDensity OutcomeB ρ * (data.right y).liftedEffect (some b))

/-! ### Tensor-product Naimark source theorem -/

/-- The density matrix of `ψ ⊗ aux`, written in the register order used by the
paper's dilated measurements:
`(Alice × AliceAux) × (Bob × BobAux)`.

The source paper writes the dilated vector as
`\ket{\widehat{\psi}} = \ket{\psi} \otimes \ket{\mathsf{aux}}`.  Since the
local dilated measurements act on `Alice × AliceAux` and `Bob × BobAux`, the
matrix entries below are the corresponding tensor-product density after the
canonical reassociation and permutation of the four finite registers. -/
noncomputable def naimarkProductExtensionDensity
    (HA HB HauxA HauxB : FiniteHilbertSpace.{u})
    (ψ : QuantumState (HA.carrier × HB.carrier))
    (aux : QuantumState (HauxA.carrier × HauxB.carrier)) :
    MIPStarRE.Quantum.Op
      ((HA.carrier × HauxA.carrier) × (HB.carrier × HauxB.carrier)) :=
  fun r c =>
    ψ.density (r.1.1, r.2.1) (c.1.1, c.2.1) *
      aux.density (r.1.2, r.2.2) (c.1.2, c.2.2)

/-- The canonical register permutation from
`(Alice × Bob) × (AliceAux × BobAux)` to
`(Alice × AliceAux) × (Bob × BobAux)`. -/
def naimarkProductExtensionEquiv
    (HA HB HauxA HauxB : FiniteHilbertSpace.{u}) :
    ((HA.carrier × HB.carrier) × (HauxA.carrier × HauxB.carrier)) ≃
      ((HA.carrier × HauxA.carrier) × (HB.carrier × HauxB.carrier)) :=
  Equiv.prodProdProdComm HA.carrier HB.carrier HauxA.carrier HauxB.carrier

/-- The product-extension density is the ordinary tensor-product density after
the register permutation used by the dilated measurements. -/
theorem naimarkProductExtensionDensity_eq_reindex_opTensor
    (HA HB HauxA HauxB : FiniteHilbertSpace.{u})
    (ψ : QuantumState (HA.carrier × HB.carrier))
    (aux : QuantumState (HauxA.carrier × HauxB.carrier)) :
    naimarkProductExtensionDensity HA HB HauxA HauxB ψ aux =
      Matrix.reindex (naimarkProductExtensionEquiv HA HB HauxA HauxB)
        (naimarkProductExtensionEquiv HA HB HauxA HauxB)
        (opTensor ψ.density aux.density) := by
  ext r c
  rfl

/-- The product-extension density is positive semidefinite. -/
theorem naimarkProductExtensionDensity_nonneg
    (HA HB HauxA HauxB : FiniteHilbertSpace.{u})
    (ψ : QuantumState (HA.carrier × HB.carrier))
    (aux : QuantumState (HauxA.carrier × HauxB.carrier)) :
    0 ≤ naimarkProductExtensionDensity HA HB HauxA HauxB ψ aux := by
  rw [naimarkProductExtensionDensity_eq_reindex_opTensor]
  exact MIPStarRE.Quantum.reindex_nonneg (naimarkProductExtensionEquiv HA HB HauxA HauxB)
    (opTensor_nonneg ψ.density_psd aux.density_psd)

/-- The quantum state `ψ ⊗ aux` in the register order used by the full Naimark
correlation theorem. -/
noncomputable def naimarkProductExtensionState
    (HA HB HauxA HauxB : FiniteHilbertSpace.{u})
    (ψ : QuantumState (HA.carrier × HB.carrier))
    (aux : QuantumState (HauxA.carrier × HauxB.carrier)) :
    QuantumState ((HA.carrier × HauxA.carrier) × (HB.carrier × HauxB.carrier)) where
  density := naimarkProductExtensionDensity HA HB HauxA HauxB ψ aux
  density_psd := naimarkProductExtensionDensity_nonneg HA HB HauxA HauxB ψ aux

@[simp] theorem naimarkProductExtensionState_density
    (HA HB HauxA HauxB : FiniteHilbertSpace.{u})
    (ψ : QuantumState (HA.carrier × HB.carrier))
    (aux : QuantumState (HauxA.carrier × HauxB.carrier)) :
    (naimarkProductExtensionState HA HB HauxA HauxB ψ aux).density =
      naimarkProductExtensionDensity HA HB HauxA HauxB ψ aux := rfl



/-- Witness data for the full tensor-product Naimark correlation theorem.

Paper origin: `references/ldt-paper/orthonormalization.tex:36-80`
(`\label{thm:naimark}`), with the tensor-product assembly proof at
`references/ldt-paper/orthonormalization.tex:161-187`.

The data records the auxiliary Hilbert spaces, an auxiliary product state, the
dilated state `ψ ⊗ aux`, and projective submeasurements on the enlarged Alice
and Bob spaces.  This is the form produced by
`references/ldt-paper/orthonormalization.tex:121-187`: the fresh `⊥` outcome
carries the residual mass, so the original outcome family is projective but not
complete in general.  The final field is the source theorem's correlation
identity for all questions and original outcomes. -/
structure NaimarkTensorProductCorrelationData
    {QuestionA OutcomeA QuestionB OutcomeB : Type*}
    [Fintype QuestionA] [DecidableEq QuestionA]
    [Fintype OutcomeA] [DecidableEq OutcomeA]
    [Fintype QuestionB] [DecidableEq QuestionB]
    [Fintype OutcomeB] [DecidableEq OutcomeB]
    (HA HB HauxA HauxB : FiniteHilbertSpace.{u})
    (ψ : QuantumState (HA.carrier × HB.carrier))
    (A : IdxSubMeas QuestionA OutcomeA HA.carrier)
    (B : IdxSubMeas QuestionB OutcomeB HB.carrier) where
  /-- The auxiliary state on the tensor product of the two auxiliary spaces. -/
  auxState : QuantumState (HauxA.carrier × HauxB.carrier)
  /-- The auxiliary state is normalized. -/
  auxState_normalized : auxState.IsNormalized
  /-- Alice's factor in the auxiliary product state. -/
  auxLeft : QuantumState HauxA.carrier
  /-- Bob's factor in the auxiliary product state. -/
  auxRight : QuantumState HauxB.carrier
  /-- Alice's auxiliary factor is normalized. -/
  auxLeft_normalized : auxLeft.IsNormalized
  /-- Bob's auxiliary factor is normalized. -/
  auxRight_normalized : auxRight.IsNormalized
  /-- The auxiliary state is the product of its Alice and Bob factors. -/
  auxState_product :
    auxState.density = opTensor auxLeft.density auxRight.density
  /-- The dilated bipartite state in the register order of the dilated measurements. -/
  dilatedState :
    QuantumState ((HA.carrier × HauxA.carrier) × (HB.carrier × HauxB.carrier))
  /-- The dilated state is `ψ ⊗ aux`, with the four registers reassociated. -/
  dilatedState_density :
    dilatedState.density =
      naimarkProductExtensionDensity HA HB HauxA HauxB ψ auxState
  /-- The dilated state is normalized. -/
  dilatedState_normalized : dilatedState.IsNormalized
  /-- Alice's projective submeasurements on the enlarged Alice space. -/
  left : IdxProjSubMeas QuestionA OutcomeA (HA.carrier × HauxA.carrier)
  /-- Bob's projective submeasurements on the enlarged Bob space. -/
  right : IdxProjSubMeas QuestionB OutcomeB (HB.carrier × HauxB.carrier)
  /-- Preservation of the bipartite correlations for every question and outcome. -/
  correlation_preservation :
    ∀ (x : QuestionA) (y : QuestionB) (a : OutcomeA) (b : OutcomeB),
      ev ψ (opTensor ((A x).outcome a) ((B y).outcome b)) =
        ev dilatedState (opTensor ((left x).outcome a) ((right y).outcome b))



/-! ### Orthonormalization statements -/

/-- Paper origin: `references/ldt-paper/preliminaries.tex:348-376`
(`\label{def:approx_delta}`) and `references/ldt-paper/orthonormalization.tex`
§4 prose around `\label{lem:projective-non-measurement}` (lines 414-538).

Conclusion of the intermediate almost-projective step: a measurement which is
ζ-strongly self-consistent and ζ-self-close in the state-dependent distance,
and whose effects satisfy `Σₐ (Aₐ − Aₐ²) ≤ ζ`. -/
structure AlmostProjMeasStatement {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) : Prop where
  strongSelfConsistency :
    SSCRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) ζ
  selfDistance :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily A.toSubMeas)
      (2 * ζ)
  sourceAlmostProjective :
    ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ ζ

/-- Paper origin: `references/ldt-paper/orthonormalization.tex:414-538`
(`\label{lem:projective-non-measurement}`); the truncation-function `trunc_δ`
itself is introduced inside the proof at lines 434-444, with the supporting
inequality `\label{lem:trunc-inequality}` at line 447.

Conclusion of the truncation-function step in the proof of rounding to
projectors. -/
structure SpectralTruncationStatement {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) where
  /-- The operator family obtained by applying the truncation function to each effect. -/
  roundedFamily : OpFamily Outcome ι
  /-- Each truncated effect is a projection. -/
  projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (roundedFamily.outcome a)
  /-- The truncated family stays close to the input measurement in
  state-dependent operator distance, with the paper's `2√ζ` bound
  (`references/ldt-paper/orthonormalization.tex:417`). -/
  closeness :
    SDDOpRel ψ (uniformDistribution Unit)
      (fun _ => (A.toSubMeas : OpFamily Outcome ι))
      (fun _ => roundedFamily)
      (2 * spectralTruncationError ζ)
  /-- The stored total operator is the sum of the rounded family. -/
  sum_eq_total : ∑ a, roundedFamily.outcome a = roundedFamily.total
  /-- The total operator of the rounded family is almost bounded by `I`. -/
  total_le :
    roundedFamily.total ≤ (((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
      (1 : MIPStarRE.Quantum.Op ι)

/-- Paper origin: `references/ldt-paper/orthonormalization.tex:414-538`
(`\label{lem:projective-non-measurement}`).

Conclusion of the rounding-to-projective step: a genuine projective
sub-measurement `P` which is `ζ`-close to the input measurement `A` in the
state-dependent operator distance. -/
structure RoundedProjMeasStatement {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι)
    (P : ProjSubMeas Outcome ι) (ζ : Error) : Prop where
  closeness :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily P.toSubMeas)
      ζ

/-- Complete a submeasurement by adjoining the residual `I - ∑ₐ Aₐ` at the
fresh `none` outcome.

This is the completion used in the paper's proof of
`thm:orthonormalization`: the original outcomes are kept as `some a`, and the
missing mass is recorded separately at `none`. -/
noncomputable def optionCompletion {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (A : SubMeas Outcome ι) : Measurement (Option Outcome) ι where
  toSubMeas :=
    { outcome := fun
        | none => 1 - A.total
        | some a => A.outcome a
      total := 1
      outcome_pos := fun
        | none => sub_nonneg.mpr A.total_le_one
        | some a => A.outcome_pos a
      sum_eq_total := (Fintype.sum_option _).trans <|
        (congrArg (1 - A.total + ·) A.sum_eq_total).trans (sub_add_cancel 1 A.total)
      total_le_one := le_rfl }
  total_eq_one := rfl

@[simp] lemma optionCompletion_outcome_none {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (A : SubMeas Outcome ι) :
    (optionCompletion A).outcome none = 1 - A.total := rfl

@[simp] lemma optionCompletion_outcome_some {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (A : SubMeas Outcome ι) (a : Outcome) :
    (optionCompletion A).outcome (some a) = A.outcome a := rfl

end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT


