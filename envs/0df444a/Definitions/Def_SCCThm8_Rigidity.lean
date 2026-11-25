-- Prove2me | Definitions.Def_SCCThm8_Rigidity
-- name    : SCCThm8_Rigidity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:46:43.261256+00:00
-- url     : https://prove2.me/theorems/07f90a7e-0832-43b7-ada0-37253713d173
-- title:
--   Rigidity
-- statement:
--   Definitions and structural lemmas for Rigidity, from Eyali1001 (Eyali1001/scc-group-barrier; see pinned Apache-2.0 LICENSE and README.md)'s pinned Group constructions cannot refute the Set Cover Conjecture, including tensor powers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean

module
public import Definitions.Def_SCCThm8_Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace SCCThm8
open Finset
namespace Rig
variable {n : ℕ}
def sw (A : Finset (Fin n)) (i j : Fin n) : Finset (Fin n) := insert j (A.erase i)
section Swaps
variable {G : Type*} [Group G] {k : ℕ} {f₁ f₂ f₃ : Finset (Fin (3 * k)) → G}
noncomputable def dl (k : ℕ) (f₁ : Finset (Fin (3 * k)) → G) (i j : Fin (3 * k)) : G :=
  if h : ∃ A : Finset (Fin (3 * k)), A.card = k ∧ i ∈ A ∧ j ∉ A then
    f₁ (sw h.choose i j) * (f₁ h.choose)⁻¹ else 1
end Swaps
section Delta
variable {G : Type*} [Group G] {k : ℕ} {F : Finset (Fin (3 * k)) → G}
  {d : Fin (3 * k) → Fin (3 * k) → G}
variable (hk : 2 ≤ k)
  (hs : ∀ A : Finset (Fin (3 * k)), A.card = k → ∀ i j, i ∈ A → j ∉ A → F (sw A i j) = d i j * F A)
include hk hs
end Delta
section Gen
variable {G : Type*} [Group G] {k : ℕ}
def gg (d : Fin (3 * k) → Fin (3 * k) → G) (o i : Fin (3 * k)) : G := if i = o then 1 else d o i
variable {F : Finset (Fin (3 * k)) → G} {d : Fin (3 * k) → Fin (3 * k) → G} (hk : 2 ≤ k)
  (hs : ∀ A : Finset (Fin (3 * k)), A.card = k → ∀ i j, i ∈ A → j ∉ A → F (sw A i j) = d i j * F A)
include hk hs
end Gen
end Rig
end SCCThm8


