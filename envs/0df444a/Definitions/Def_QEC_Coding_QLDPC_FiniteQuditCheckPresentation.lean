-- Prove2me | Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
-- name    : QEC_Coding_QLDPC_FiniteQuditCheckPresentation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:51:19.082336+00:00
-- url     : https://prove2.me/theorems/2fcc72d5-6e16-4fa1-b86b-79524f445218
-- title:
--   Finite Qudit Check Presentation
-- statement:
--   Definitions and structural lemmas for Finite Qudit Check Presentation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
set_option autoImplicit false
noncomputable section
namespace QEC
namespace QLDPC
universe u v
abbrev uniformQuditDimensions {ι : Type u} (alphabetSize : Nat) : ι → Nat :=
  fun _ => alphabetSize
def SupportsNondetectableLocalOperator
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (code : Semantics.QuantumCode (Semantics.Qudit.QuditRegister q))
    (region : Semantics.QuditSubsystem q) : Prop :=
  ∃ localOperator : Semantics.Operator region.selectedSystem,
    ¬ Semantics.DetectableOn code
      (region.extendLocalToRegister localOperator)
def semanticQuditDistance
    {ι : Type u} [Fintype ι] [DecidableEq ι] (q : ι → Nat)
    (code : Semantics.QuantumCode (Semantics.Qudit.QuditRegister q)) : Nat :=
  sInf {weight : Nat | ∃ region : Semantics.QuditSubsystem q,
    Fintype.card region.SelectedCoordinates = weight ∧
      SupportsNondetectableLocalOperator code region}
structure FiniteQuditCheck (ι : Type u) [Fintype ι] [DecidableEq ι]
    (alphabetSize : Nat) where
  region : Semantics.QuditSubsystem (uniformQuditDimensions (ι := ι) alphabetSize)
  localOperator : Semantics.Operator region.selectedSystem
namespace FiniteQuditCheck
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {alphabetSize : Nat}
noncomputable def globalOperator (check : FiniteQuditCheck ι alphabetSize) :
    Semantics.Operator
      (Semantics.Qudit.QuditRegister (uniformQuditDimensions (ι := ι) alphabetSize)) :=
  check.region.extendLocalToRegister check.localOperator
end FiniteQuditCheck
structure FiniteQuditCheckPresentation
    (ι : Type u) (κ : Type v) [Fintype ι] [DecidableEq ι] [Fintype κ] where
  alphabetSize : Nat
  alphabetSize_ge_two : 2 ≤ alphabetSize
  code : Semantics.QuantumCode
    (Semantics.Qudit.QuditRegister
      (uniformQuditDimensions (ι := ι) alphabetSize))
  checks : κ → FiniteQuditCheck ι alphabetSize
  carrier_iff_fixed : ∀ ψ, ψ ∈ code.carrier ↔
    ∀ checkIndex, (checks checkIndex).globalOperator ψ = ψ
  encodedQudits : Nat
  dimension_eq : code.dimension = alphabetSize ^ encodedQudits
namespace FiniteQuditCheckPresentation
variable {ι : Type u} {κ : Type v}
variable [Fintype ι] [DecidableEq ι] [Fintype κ]
def blockLength (_P : FiniteQuditCheckPresentation ι κ) : Nat :=
  Fintype.card ι
def incidence (P : FiniteQuditCheckPresentation ι κ) :
    CheckIncidence κ ι where
  incident checkIndex coordinate :=
    coordinate ∈ (P.checks checkIndex).region.selected
noncomputable def localityProfile (P : FiniteQuditCheckPresentation ι κ) :
    Coding.LocalityProfile :=
  P.incidence.localityProfile
def distance (P : FiniteQuditCheckPresentation ι κ) : Nat :=
  semanticQuditDistance
    (uniformQuditDimensions (ι := ι) P.alphabetSize) P.code
end FiniteQuditCheckPresentation
end QLDPC
end QEC


