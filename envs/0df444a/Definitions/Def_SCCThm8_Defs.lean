-- Prove2me | Definitions.Def_SCCThm8_Defs
-- name    : SCCThm8_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:40:49.257827+00:00
-- url     : https://prove2.me/theorems/b0e7afa0-351f-56f9-9963-1ddeb068238b
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Eyali1001 (Eyali1001/scc-group-barrier; see pinned Apache-2.0 LICENSE and README.md)'s pinned Group constructions cannot refute the Set Cover Conjecture, including tensor powers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Defs.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace SCCThm8
open Finset
def mult {n : ℕ} (A B C : Finset (Fin n)) (i : Fin n) : ℤ :=
  (if i ∈ A then 1 else 0) + (if i ∈ B then 1 else 0) + (if i ∈ C then 1 else 0)
def psi {G : Type*} [Group G] {n : ℕ} (g : Fin n → G) (e : Fin n → ℤ) : G :=
  ((List.finRange n).map fun i => g i ^ e i).prod
def multP {m n : ℕ} (A B C : Fin m → Finset (Fin n)) (j : Fin m) (i : Fin n) : ℤ :=
  mult (A j) (B j) (C j) i
def psiP {G : Type*} [Group G] {m n : ℕ} (g : Fin m → Fin n → G) (e : Fin m → Fin n → ℤ) : G :=
  ((List.finRange m).map fun j => psi (g j) (e j)).prod
end SCCThm8


