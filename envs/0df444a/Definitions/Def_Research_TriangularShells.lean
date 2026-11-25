-- Prove2me | Definitions.Def_Research_TriangularShells
-- name    : Research_TriangularShells
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T17:38:29.120708+00:00
-- url     : https://prove2.me/theorems/510b588d-46de-45f8-a529-7dd5006a4e95
-- title:
--   Triangular Shells
-- statement:
--   Definitions and structural lemmas for Triangular Shells, from Colin Snyder / Star Fleet Math; AItoBit (AItoBit/erdos-662-proof; see pinned Apache-2.0 LICENSE and NOTICE)'s pinned Erdos 662: corrected global threshold conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/TriangularShells.lean

module
public import Definitions.Def_Research_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Research
def triNormSq (p : ℤ × ℤ) : ℤ :=
  p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2
def intWindow3 : Finset ℤ := {(-3 : ℤ), -2, -1, 0, 1, 2, 3}
def triCoordsWithin (s : ℤ) : Finset (ℤ × ℤ) :=
  ((intWindow3.product intWindow3).filter
    (fun p => triNormSq p ≤ s)).erase (0, 0)
noncomputable def triCoordsWithinReal (s : ℝ) : Finset (ℤ × ℤ) :=
  ((intWindow3.product intWindow3).filter
    (fun p => (triNormSq p : ℝ) ≤ s)).erase (0, 0)
noncomputable def triPoint (p : ℤ × ℤ) : ℝ × ℝ :=
  ((p.1 : ℝ) + (p.2 : ℝ) / 2, Real.sqrt 3 * (p.2 : ℝ) / 2)
end Research


