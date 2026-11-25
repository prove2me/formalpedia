-- Prove2me | Definitions.Def_SCCThm8_PowerRigidity
-- name    : SCCThm8_PowerRigidity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:48:32.324103+00:00
-- url     : https://prove2.me/theorems/cbbebd50-bada-5c44-b5b8-d910e9125de6
-- title:
--   Power Rigidity
-- statement:
--   Definitions and structural lemmas for Power Rigidity, from Eyali1001 (Eyali1001/scc-group-barrier; see pinned Apache-2.0 LICENSE and README.md)'s pinned Group constructions cannot refute the Set Cover Conjecture, including tensor powers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerRigidity.lean

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace SCCThm8
open Finset
namespace PRig
open Rig Function
section Swaps
variable {G : Type*} [Group G] {k m : ℕ} {f₁ f₂ f₃ : (Fin m → Finset (Fin (3 * k))) → G}
def Good (k : ℕ) (f₁ f₂ f₃ : (Fin m → Finset (Fin (3 * k))) → G) : Prop :=
  ∀ A B C : Fin m → Finset (Fin (3 * k)),
    (∀ j, (A j).card = k) → (∀ j, (B j).card = k) → (∀ j, (C j).card = k) →
    (∀ j, Disjoint (A j) (B j) ∧ Disjoint (A j) (C j) ∧ Disjoint (B j) (C j)) →
    f₁ A * f₂ B * f₃ C = 1
noncomputable def D (k : ℕ) (f₁ : (Fin m → Finset (Fin (3 * k))) → G) (j : Fin m)
    (s t : Fin (3 * k)) : G :=
  if h : ∃ A : Fin m → Finset (Fin (3 * k)), (∀ j', (A j').card = k) ∧ s ∈ A j ∧ t ∉ A j then
    f₁ (update h.choose j (sw (h.choose j) s t)) * (f₁ h.choose)⁻¹ else 1
end Swaps
end PRig
end SCCThm8


