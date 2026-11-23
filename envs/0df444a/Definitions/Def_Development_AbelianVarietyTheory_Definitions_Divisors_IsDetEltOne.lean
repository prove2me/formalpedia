-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsDetEltOne
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_IsDetEltOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:41:57.350947+00:00
-- url     : https://prove2.me/theorems/6d8ce762-d1e7-47e3-a519-b0a3c9f24536
-- title:
--   Is Det Elt One
-- statement:
--   Definitions and structural lemmas for Is Det Elt One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsDetEltOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IotaScalarOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal Matrix GlobalTheory.Sandwich TensorProduct
namespace GlobalTheory.DetInv
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]
def IsDetElt (ε : PreTilt O p) (ψ : RL p O Λ →+* RL p O Λ) (N : ℕ) (Δ : RL p O Λ) : Prop :=
  Δ ∣ (inA (mu ε) : RL p O Λ) ^ N ∧ ∃ g, Δ = g * ψ Δ ∧ g ∣ (inA (xi ε) : RL p O Λ) ^ N
def HasOrders (C : Type) [Field C] [Algebra O C] (ε : PreTilt O p) (N : ℕ) (Δ : RL p O Λ)
    (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C) : Prop :=
  ∀ σ f, IsTheta σ f →
    a σ ≤ N ∧ c σ ≠ 0 ∧ Lead ((algebraMap O C).comp f) (inA (xi ε)) Δ (a σ) (c σ)
def IsIsom (C : Type) [Field C] [Algebra O C] (v : Valuation C NNReal) (γ : O ≃+* O) : Prop :=
  ∃ γC : C ≃+* C, (∀ x, γC (algebraMap O C x) = algebraMap O C (γ x)) ∧ ∀ z, v (γC z) = v z
end GlobalTheory.DetInv


