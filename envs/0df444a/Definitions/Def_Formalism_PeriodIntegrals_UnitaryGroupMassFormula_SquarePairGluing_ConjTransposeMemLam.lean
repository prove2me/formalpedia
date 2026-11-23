-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_ConjTransposeMemLam
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_ConjTransposeMemLam
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:54:16.916016+00:00
-- url     : https://prove2.me/theorems/e633cf44-5ce2-4616-a57d-d3b54c9e62a2
-- title:
--   Conj Transpose Mem Lam
-- statement:
--   Definitions and structural lemmas for Conj Transpose Mem Lam, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairGluing/ConjTransposeMemLam.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_SplitPairEquations_SplitPairGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
namespace PI.SqPairW
open Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
def lam (L' L'' : Submodule (𝓞 E) (Fin N → E)) : Subring (Matrix (Fin N) (Fin N) E) where
  carrier := {e | (∀ y ∈ L', e *ᵥ y ∈ L') ∧ (∀ y ∈ L'', e *ᵥ y ∈ L'')}
  mul_mem' {a b} ha hb := ⟨fun y hy => by rw [← mulVec_mulVec]; exact ha.1 _ (hb.1 y hy),
    fun y hy => by rw [← mulVec_mulVec]; exact ha.2 _ (hb.2 y hy)⟩
  one_mem' := ⟨fun y hy => by simpa using hy, fun y hy => by simpa using hy⟩
  add_mem' {a b} ha hb := ⟨fun y hy => by rw [add_mulVec]; exact L'.add_mem (ha.1 y hy) (hb.1 y hy),
    fun y hy => by rw [add_mulVec]; exact L''.add_mem (ha.2 y hy) (hb.2 y hy)⟩
  zero_mem' := ⟨fun y _ => by simp, fun y _ => by simp⟩
  neg_mem' {a} ha := ⟨fun y hy => by rw [neg_mulVec]; exact L'.neg_mem (ha.1 y hy),
    fun y hy => by rw [neg_mulVec]; exact L''.neg_mem (ha.2 y hy)⟩
def mset (e : Matrix (Fin N) (Fin N) E) : Set (Matrix (Fin N) (Fin N) E) :=
  {e * e - e, eᴴ * e, (1 - e)ᴴ * (1 - e)}
def yg (L' L'' : Submodule (𝓞 E) (Fin N → E)) (n : 𝓞 E) : AddSubgroup (Fin N → E) where
  carrier := {x | ∃ m, m ∈ L' ∧ m ∈ L'' ∧ x = (n : E) • m}
  add_mem' := by
    rintro _ _ ⟨m1, h1, h1', rfl⟩ ⟨m2, h2, h2', rfl⟩
    exact ⟨m1 + m2, L'.add_mem h1 h2, L''.add_mem h1' h2', (smul_add _ _ _).symm⟩
  zero_mem' := ⟨0, L'.zero_mem, L''.zero_mem, (smul_zero _).symm⟩
  neg_mem' := by
    rintro _ ⟨m, h, h', rfl⟩
    exact ⟨-m, L'.neg_mem h, L''.neg_mem h', (smul_neg _ _).symm⟩
end PI.SqPairW


