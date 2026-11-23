-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsComplementWithoutCommonIrreducibleTypes
-- name    : Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsComplementWithoutCommonIrreducibleTypes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:22.575729+00:00
-- url     : https://prove2.me/theorems/dfdf8578-5a51-4265-9d96-42a423a56253
-- title:
--   Exists Complement Without Common Irreducible Types
-- statement:
--   Definitions and structural lemmas for Exists Complement Without Common Irreducible Types, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsComplementWithoutCommonIrreducibleTypes.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
namespace TypeComplement
variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}
def supRep (P : Subrepresentation ρ → Prop) : Subrepresentation ρ where
  toSubmodule := ⨆ (S : Subrepresentation ρ) (_ : P S), S.toSubmodule
  apply_mem_toSubmodule k := by
    have h : (⨆ (S : Subrepresentation ρ) (_ : P S), S.toSubmodule) ≤
        (⨆ (S : Subrepresentation ρ) (_ : P S), S.toSubmodule).comap (ρ k) := by
      refine iSup₂_le fun S hS x hx => ?_
      exact (le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : P S) => S.toSubmodule) S hS)
        (S.apply_mem_toSubmodule k hx)
    exact fun v hv => h hv
def imRep (f : V →ₗ[ℂ] V) (hf : ∀ k v, f (ρ k v) = ρ k (f v)) (S : Subrepresentation ρ) :
    Subrepresentation ρ where
  toSubmodule := S.toSubmodule.map f
  apply_mem_toSubmodule k := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨ρ k s, S.apply_mem_toSubmodule k hs, hf k s⟩
def preRep (f : V →ₗ[ℂ] V) (hf : ∀ k v, f (ρ k v) = ρ k (f v)) (S C : Subrepresentation ρ) :
    Subrepresentation ρ where
  toSubmodule := S.toSubmodule ⊓ C.toSubmodule.comap f
  apply_mem_toSubmodule k := by
    rintro v ⟨hv1, hv2⟩
    refine ⟨S.apply_mem_toSubmodule k hv1, ?_⟩
    show f (ρ k v) ∈ C.toSubmodule
    rw [hf k v]
    exact C.apply_mem_toSubmodule k hv2
end TypeComplement
end GlobalTheory
namespace GlobalTheory
namespace TypeComplement
variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}
end TypeComplement
end GlobalTheory
namespace GlobalTheory
namespace TypeComplement
end TypeComplement
end GlobalTheory


