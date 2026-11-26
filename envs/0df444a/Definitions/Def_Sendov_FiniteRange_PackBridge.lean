-- Prove2me | Definitions.Def_Sendov_FiniteRange_PackBridge
-- name    : Sendov_FiniteRange_PackBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T18:01:08.856791+00:00
-- url     : https://prove2.me/theorems/c88b7949-e914-5c2a-a1b3-ba0a4d3f9422
-- title:
--   Pack Bridge
-- statement:
--   Definitions and structural lemmas for Pack Bridge, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
set_option autoImplicit false
namespace Sendov
def rowZ (r : List (List ℤ)) (β : ℤ) : List ℤ := r.map (fun p => pevZ p β)
def wsum (L : ℤ) : ℕ → List (List ℤ) → List ℤ
  | _, [] => []
  | i, p :: r => padd (p.map (fun c => (L / ((i : ℤ) + 4)) * c)) (wsum L (i + 1) r)
def l1 : List ℤ → ℤ
  | [] => 0
  | a :: p => |a| + l1 p
def l1row : List (List ℤ) → ℤ
  | [] => 0
  | p :: r => l1 p + l1row r
def wsumZ (L : ℤ) : ℕ → List ℤ → ℤ
  | _, [] => 0
  | i, a :: s => (L / ((i : ℤ) + 4)) * a + wsumZ L (i + 1) s
end Sendov


