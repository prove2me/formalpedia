-- Prove2me | Definitions.Def_FFactorLib_FFactorCount
-- name    : FFactorLib_FFactorCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:55:47.425823+00:00
-- url     : https://prove2.me/theorems/546c24b2-3fe5-4da7-9669-9bd77b8d4d10
-- title:
--   FFactor Count
-- statement:
--   Definitions and structural lemmas for FFactor Count, from Juan Pablo Traverso Gianini (jtraverso/tutte-f-factor; see pinned Apache-2.0 LICENSE and source headers)'s pinned Tutte f-factor theorem for finite simple graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorSuff
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset SimpleGraph Classical
namespace FFactor
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {f : V → ℕ}
  {U : Set (GV G f)}
end FFactor


