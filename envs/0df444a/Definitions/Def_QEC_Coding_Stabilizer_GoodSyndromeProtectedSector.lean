-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
-- name    : QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:13:11.234184+00:00
-- url     : https://prove2.me/theorems/476eaa0c-d626-484c-827a-2e0c04a481e0
-- title:
--   Good Syndrome Protected Sector
-- statement:
--   Definitions and structural lemmas for Good Syndrome Protected Sector, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean

import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
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
namespace DecoderDressedLogical
variable {H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)}
def commutationPhase (left right : Binary ι) : Complex :=
  binaryPhaseScalar (symplecticForm left.vector right.vector)
def goodSyndrome (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary ι))
    (syndrome : DecoderSyndrome κ) : Prop :=
  ∀ error ∈ elementaryErrors,
    binaryMul (D.correction (H.transportSyndrome error syndrome))
        (binaryMul error (D.correction syndrome)) ∈ H.code.1.generatedGroup
def goodSyndromes (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary ι)) : Finset (DecoderSyndrome κ) := by
  classical
  exact Finset.univ.filter (D.goodSyndrome elementaryErrors)
def badSyndromes (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary ι)) : Finset (DecoderSyndrome κ) := by
  classical
  exact Finset.univ.filter (fun syndrome =>
    ¬ D.goodSyndrome elementaryErrors syndrome)
def goodSyndromeProjector (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary ι)) :
    Operator (Qubit.QubitRegister ι) :=
  ∑ syndrome ∈ D.goodSyndromes elementaryErrors,
    H.syndromeProjector syndrome
def badSyndromeProjector (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary ι)) :
    Operator (Qubit.QubitRegister ι) :=
  ∑ syndrome ∈ D.badSyndromes elementaryErrors,
    H.syndromeProjector syndrome
def badSyndromeGibbsWeight
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι))
    (rhoBeta : DensityOperator (Qubit.QubitRegister ι)) : Complex :=
  ∑ syndrome ∈ D.badSyndromes elementaryErrors,
    LinearMap.trace Complex (Qubit.QubitRegister ι)
      (H.syndromeProjector syndrome * rhoBeta.toOperator)
def GoodSyndromeProtectedObservable
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι)) : Prop :=
  IsStarProjection (D.goodSyndromeProjector elementaryErrors) ∧
    Commute (D.goodSyndromeProjector elementaryErrors) D.dressedX ∧
    Commute (D.goodSyndromeProjector elementaryErrors) D.dressedZ ∧
    Commute (D.goodSyndromeProjector elementaryErrors) H.operator ∧
    D.goodSyndromeProjector elementaryErrors * D.dressedX *
        D.goodSyndromeProjector elementaryErrors =
      D.dressedX * D.goodSyndromeProjector elementaryErrors ∧
    D.goodSyndromeProjector elementaryErrors * D.dressedZ *
        D.goodSyndromeProjector elementaryErrors =
      D.dressedZ * D.goodSyndromeProjector elementaryErrors ∧
    (∀ error ∈ elementaryErrors,
      (toHermitianQubitOperator error * D.dressedX -
          D.dressedX * toHermitianQubitOperator error) *
        D.goodSyndromeProjector elementaryErrors = 0 ∧
      (toHermitianQubitOperator error * D.dressedZ -
          D.dressedZ * toHermitianQubitOperator error) *
        D.goodSyndromeProjector elementaryErrors = 0) ∧
    ∀ rhoBeta : DensityOperator (Qubit.QubitRegister ι),
      LinearMap.trace Complex (Qubit.QubitRegister ι)
          ((1 - D.goodSyndromeProjector elementaryErrors) * rhoBeta.toOperator) =
        D.badSyndromeGibbsWeight elementaryErrors rhoBeta
end DecoderDressedLogical
end StabilizerCode
end Coding
end QEC


