-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
-- name    : Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:29.13626+00:00
-- url     : https://prove2.me/theorems/02547fa7-982d-4cd9-a332-32e201df1bab
-- title:
--   Ab By POf Comm
-- statement:
--   Definitions and structural lemmas for Ab By POf Comm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/CommutativeAlgebra/AbByPOfComm.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BI
def IsChar (K L : Type) [Field K] [Field L] [Algebra K L] {G : Type} [Group G] (χ : G → L) : Prop :=
  ∃ (n : ℕ) (ρ : Representation K G (Fin n → K)), ∀ g, χ g = algebraMap K L (ρ.character g)
def IsIrrChar (K L : Type) [Field K] [Field L] [Algebra K L] {G : Type} [Group G] (χ : G → L) : Prop :=
  ∃ (n : ℕ) (ρ : Representation K G (Fin n → K)), ρ.IsIrreducible ∧ ∀ g, χ g = algebraMap K L (ρ.character g)
def Virt (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] : AddSubgroup (G → L) :=
  AddSubgroup.closure {χ | IsChar K L χ}
open Classical in

def ext0 {L G : Type} [Field L] [Group G] (H : Subgroup G) (ψ : H → L) (g : G) : L :=
  if h : g ∈ H then ψ ⟨g, h⟩ else 0
def ind {L G : Type} [Field L] [Group G] (H : Subgroup G) (ψ : H → L) (g : G) : L :=
  (Nat.card H : L)⁻¹ * ∑ᶠ x : G, ext0 H ψ (x⁻¹ * g * x)
def pair {L G : Type} [Field L] [Group G] (a b : G → L) : L :=
  (Nat.card G : L)⁻¹ * ∑ᶠ g : G, a g * b g⁻¹
def AbByP (G : Type) [Group G] : Prop :=
  ∃ p : ℕ, p.Prime ∧ ∃ A : Subgroup G, A.Normal ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ ∀ g : G, ∃ k : ℕ, g ^ p ^ k ∈ A
end GlobalTheory.BI


