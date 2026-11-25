-- Prove2me | Definitions.Def_JacPoisson_Main
-- name    : JacPoisson_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T14:40:59.728532+00:00
-- url     : https://prove2.me/theorems/106448a8-cea5-4715-a447-aa58213dfd85
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Zayn Blore (zblore/fc-jacobian-poisson; definitions and statement reused under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and source headers)'s pinned The Jacobian conjecture in dimension 2n implies the Poisson conjecture in dimension n development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/fc-jacobian-poisson/blob/e395ab52d16b1c26b354daecf0c62b361f01c7a8/JacPoisson/Main.lean

module
public import Definitions.Def_JacPoisson_Defs
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace JacPoisson
open MvPolynomial Matrix JacobianConjecture
section Bracket
variable {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
end Bracket
section Congr
variable {k : Type*} [CommRing k] {σ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]
  [DecidableEq τ]
end Congr
section Inverse
variable {k : Type*} [CommRing k] {σ : Type*}
end Inverse
open Arxiv.«math.0608009»
end JacPoisson


