-- Prove2me | Definitions.Def_QuadraticFloor_Corollaries
-- name    : QuadraticFloor_Corollaries
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:45:51.047261+00:00
-- url     : https://prove2.me/theorems/64947b12-04d5-46cb-be3e-35c385011cb5
-- title:
--   Corollaries
-- statement:
--   Definitions and structural lemmas for Corollaries, from J. S. Farland (jkfarland-bot/QuadraticFloor; see pinned Apache-2.0 LICENSE and README.md)'s pinned QuadraticFloor: quadratic floor sums and the trace of a quartic Bernoulli number development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Corollaries.lean

module
public import Definitions.Def_QuadraticFloor_SquareClass
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
noncomputable def chi3 : DirichletCharacter ℂ 3 :=
  (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)
end QuadraticFloor


