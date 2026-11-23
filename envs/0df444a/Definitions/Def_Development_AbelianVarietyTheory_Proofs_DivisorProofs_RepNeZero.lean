-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:16.622039+00:00
-- url     : https://prove2.me/theorems/e7ff977b-8e31-4c12-83f6-54627ed468c1
-- title:
--   Rep Ne Zero
-- statement:
--   Definitions and structural lemmas for Rep Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RepNeZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
namespace GlobalTheory.SlopeTestRemainingChoices.EisFibre
variable {F : Type} [Field F] [NumberField F]
def NzElt (𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) : Type :=
  {b : F // b ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ∧ b ≠ 0}
def unitRel (𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) : Setoid (NzElt 𝔟) where
  r p q := ∃ ε : (𝓞 F)ˣ, q.1 = ((ε : 𝓞 F) : F) * p.1
  iseqv :=
    { refl := fun _ => ⟨1, by simp⟩
      symm := fun {p q} ⟨ε, h⟩ => ⟨ε⁻¹, by rw [h, ← mul_assoc, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.unit_inv_mul, one_mul]⟩
      trans := fun {p q r} ⟨ε, h⟩ ⟨ε', h'⟩ => ⟨ε' * ε, by rw [h', h, ← mul_assoc]; simp⟩ }
def NzCls (𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) : Type := Quotient (unitRel 𝔟)
def rep {𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} (β : NzCls 𝔟) : F := (Quotient.out β : NzElt 𝔟).1
def posCone (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (b : F) : Type :=
  {ν : F // ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ τ : F →+* ℝ, 0 < τ (ν * b)}
example : NzCls (1 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) :=
  Quotient.mk _ ⟨1, by simp [FractionalIdeal.one_mem_one], one_ne_zero⟩
end GlobalTheory.SlopeTestRemainingChoices.EisFibre


