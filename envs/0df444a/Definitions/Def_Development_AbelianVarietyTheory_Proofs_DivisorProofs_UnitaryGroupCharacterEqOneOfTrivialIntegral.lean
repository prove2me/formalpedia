-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupCharacterEqOneOfTrivialIntegral
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupCharacterEqOneOfTrivialIntegral
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T15:47:23.58926+00:00
-- url     : https://prove2.me/theorems/2b9baccb-614b-4f96-b56e-8ca67872334a
-- title:
--   Unitary Group Character Eq One Of Trivial Integral
-- statement:
--   Definitions and structural lemmas for Unitary Group Character Eq One Of Trivial Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupCharacterEqOneOfTrivialIntegral.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


set_option autoImplicit false
open Formalism.UG Matrix GlobalTheory.UnitarySwap
noncomputable section
namespace GlobalTheory.UnitaryCharacter
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
section Abstract
variable {V : Type} [AddCommGroup V] [Module L V] {σ : L →+* L} {B : V →ₛₗ[σ] V →ₗ[L] L}
def ReflIn (B : V →ₛₗ[σ] V →ₗ[L] L) (N : Submonoid (Module.End L V)) (Λ : Set V) : Prop :=
  ∀ w ∈ Λ, ∀ μ : L, μ ≠ 0 → μ⁻¹ ∈ intL L → B w w = μ + σ μ → refl B w μ ∈ N
end Abstract
variable {n : ℕ} {σ : L →+* L}
def kerEnd {J : Matrix (Fin n) (Fin n) L} (ν : UJ σ J →* Circle) : Submonoid (Module.End L (Fin n → L)) where
  carrier := {s | ∃ g : UJ σ J, ν g = 1 ∧ ∀ v, s v = ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ v}
  one_mem' := ⟨1, map_one ν, fun v => by simp⟩
  mul_mem' := by
    rintro s t ⟨g, hg, es⟩ ⟨h, hh, et⟩
    refine ⟨g * h, by rw [map_mul, hg, hh, mul_one], fun v => ?_⟩
    rw [Module.End.mul_apply, es, et, Matrix.mulVec_mulVec]
    rfl
end GlobalTheory.UnitaryCharacter


