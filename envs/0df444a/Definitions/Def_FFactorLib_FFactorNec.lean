-- Prove2me | Definitions.Def_FFactorLib_FFactorNec
-- name    : FFactorLib_FFactorNec
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:52:21.251848+00:00
-- url     : https://prove2.me/theorems/275375ed-2a1f-4aba-8404-dfbbc7ec1f32
-- title:
--   FFactor Nec
-- statement:
--   Definitions and structural lemmas for FFactor Nec, from Juan Pablo Traverso Gianini (jtraverso/tutte-f-factor; see pinned Apache-2.0 LICENSE and source headers)'s pinned Tutte f-factor theorem for finite simple graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorNec.lean

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset SimpleGraph
namespace FFactor
variable {V : Type*} [Fintype V] [DecidableEq V]
end FFactor


