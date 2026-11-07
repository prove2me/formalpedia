-- Prove2me | Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily
-- name    : QEC_Coding_QLDPC_AsymptoticallyGoodFamily
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:43:05.492651+00:00
-- url     : https://prove2.me/theorems/6fe8ea87-6b2e-4147-a100-a2b7447494c8
-- title:
--   Asymptotically Good Family
-- statement:
--   Definitions and structural lemmas for Asymptotically Good Family, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/AsymptoticallyGoodFamily.lean

import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
set_option autoImplicit false
noncomputable section
namespace QEC.QLDPC
universe u v w
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]
def HasUniformLDPC (F : QuantumCodeFamily A ι κ) : Prop :=
  ∃ B : Nat, ∀ a, Coding.BoundedLocality (F.localityProfile a) B
def HasEventualRateAtLeast (F : QuantumCodeFamily A ι κ) (rate : ℝ) : Prop :=
  ∃ N : Nat, ∀ a, N ≤ F.blockLength a →
    rate * (F.blockLength a : ℝ) ≤ (F.encodedDimension a : ℝ)
def HasEventualRelativeDistanceAtLeast
    (F : QuantumCodeFamily A ι κ) (relativeDistance : ℝ) : Prop :=
  ∃ N : Nat, ∀ a, N ≤ F.blockLength a →
    relativeDistance * (F.blockLength a : ℝ) ≤ (F.distance a : ℝ)
def IsAsymptoticallyGoodQLDPCFamily (F : QuantumCodeFamily A ι κ) : Prop :=
  HasUniformLDPC F ∧
    (∃ rate : ℝ, 0 < rate ∧ HasEventualRateAtLeast F rate) ∧
    (∃ relativeDistance : ℝ, 0 < relativeDistance ∧
      HasEventualRelativeDistanceAtLeast F relativeDistance)
end QEC.QLDPC


