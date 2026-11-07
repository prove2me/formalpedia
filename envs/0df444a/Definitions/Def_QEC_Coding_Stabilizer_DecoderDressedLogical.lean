-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
-- name    : QEC_Coding_Stabilizer_DecoderDressedLogical
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:11:39.930702+00:00
-- url     : https://prove2.me/theorems/a50caa63-1799-4d85-837f-22928a14c5ae
-- title:
--   Decoder Dressed Logical
-- statement:
--   Definitions and structural lemmas for Decoder Dressed Logical, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generators_commute

set_option autoImplicit false
noncomputable section
namespace QEC
namespace Coding
namespace StabilizerCode
open PauliSymplectic
open Semantics
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
abbrev DecoderSyndrome (κ : Type v) := JointSyndrome κ
namespace LocalStabilizerHamiltonian
def syndromeProjector
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (syndrome : DecoderSyndrome κ) :
    Operator (Qubit.QubitRegister ι) :=
  jointStabilizerProjector H.generators H.generators_commute syndrome
noncomputable def transportSyndrome
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (error : Binary ι) (syndrome : DecoderSyndrome κ) :
    DecoderSyndrome κ := by
  classical
  exact fun check =>
    if Commutes error (H.generators check) then
      syndrome check
    else
      (syndrome check).opposite
theorem syndromeFactor_pairwise
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (syndrome : DecoderSyndrome κ) (selected : Finset κ) :
    (selected : Set κ).Pairwise
      (Function.onFun Commute (jointStabilizerFactor H.generators syndrome)) := by
  intro left _ right _ _
  exact jointStabilizerFactor_commute H.generators H.generators_commute
    left right syndrome syndrome
end LocalStabilizerHamiltonian
structure DecoderDressedLogical
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) where
  correction : DecoderSyndrome κ → Binary ι
  logicalX : Binary ι
  logicalZ : Binary ι
  logicalX_normalizer : H.code.1.InBinaryNormalizer logicalX
  logicalZ_normalizer : H.code.1.InBinaryNormalizer logicalZ
  logicalX_not_commutes_logicalZ : ¬ Commutes logicalX logicalZ
namespace DecoderDressedLogical
variable {H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)}
noncomputable def phase (D : DecoderDressedLogical H)
    (logical : Binary ι) (syndrome : DecoderSyndrome κ) : Complex :=
  by
    classical
    exact if Commutes (D.correction syndrome) logical then 1 else -1
def phaseOperator (D : DecoderDressedLogical H) (logical : Binary ι) :
    Operator (Qubit.QubitRegister ι) :=
  ∑ syndrome : DecoderSyndrome κ,
    D.phase logical syndrome • H.syndromeProjector syndrome
def errorCorrectedObservable (D : DecoderDressedLogical H)
    (observable : Operator (Qubit.QubitRegister ι)) :
    Operator (Qubit.QubitRegister ι) :=
  ∑ syndrome : DecoderSyndrome κ,
    H.syndromeProjector syndrome *
      LinearMap.adjoint (toHermitianQubitOperator (D.correction syndrome)) *
      observable *
      toHermitianQubitOperator (D.correction syndrome) *
      H.syndromeProjector syndrome
def dressedLogical (D : DecoderDressedLogical H) (logical : Binary ι) :
    Operator (Qubit.QubitRegister ι) :=
  toHermitianQubitOperator logical * D.phaseOperator logical
def dressedX (D : DecoderDressedLogical H) :
    Operator (Qubit.QubitRegister ι) :=
  D.dressedLogical D.logicalX
def dressedZ (D : DecoderDressedLogical H) :
    Operator (Qubit.QubitRegister ι) :=
  D.dressedLogical D.logicalZ
end DecoderDressedLogical
end StabilizerCode
end Coding
end QEC


