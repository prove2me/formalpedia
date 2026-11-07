-- Prove2me | Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
-- name    : QEC_Coding_QLDPC_QuantumCodeFamily
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:41:48.755654+00:00
-- url     : https://prove2.me/theorems/744010db-8e2c-4257-8741-82b846449fa0
-- title:
--   Quantum Code Family
-- statement:
--   Definitions and structural lemmas for Quantum Code Family, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/QuantumCodeFamily.lean

import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
set_option autoImplicit false
noncomputable section
namespace QEC.QLDPC
universe u v w
structure QuantumCodeFamily
    (A : Type u) (ι : A → Type v) (κ : A → Type w)
    [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)] where
  presentation : ∀ a, FiniteQuditCheckPresentation (ι a) (κ a)
  cofinal_blockLength : ∀ N : Nat, ∃ a : A, N ≤ (presentation a).blockLength
namespace QuantumCodeFamily
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]
def blockLength (F : QuantumCodeFamily A ι κ) (a : A) : Nat :=
  (F.presentation a).blockLength
def encodedDimension (F : QuantumCodeFamily A ι κ) (a : A) : Nat :=
  (F.presentation a).encodedQudits
def distance (F : QuantumCodeFamily A ι κ) (a : A) : Nat :=
  (F.presentation a).distance
def localityProfile (F : QuantumCodeFamily A ι κ) (a : A) : Coding.LocalityProfile :=
  (F.presentation a).localityProfile
def maxCheckWeight (F : QuantumCodeFamily A ι κ) (a : A) : Nat :=
  (F.localityProfile a).maxCheckWeight
def maxVariableDegree (F : QuantumCodeFamily A ι κ) (a : A) : Nat :=
  (F.localityProfile a).maxVariableDegree
end QuantumCodeFamily
end QEC.QLDPC


