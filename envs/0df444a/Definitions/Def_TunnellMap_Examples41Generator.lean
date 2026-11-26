-- Prove2me | Definitions.Def_TunnellMap_Examples41Generator
-- name    : TunnellMap_Examples41Generator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T15:24:15.425985+00:00
-- url     : https://prove2.me/theorems/7a8d9faa-c31e-5de1-8fee-fe2673282941
-- title:
--   Examples41 Generator
-- statement:
--   Definitions and structural lemmas for Examples41 Generator, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Generator.lean

import Definitions.Def_TunnellMap_Examples41Residual
set_option autoImplicit true
namespace TunnellMap
namespace Examples41
open OrderedGenerator
set_option maxRecDepth 10000
def frame41 : OrthogonalFrame (tau (residualSourceLift s2)) where
  e₁ := ⟨1, 0, 0⟩
  e₂ := ⟨0, -4, 5⟩
  z := ⟨0, -1, 1⟩
  cross_eq := by
    norm_num [s2, midpointSource, residualSourceLift, bLift, tau, cross]
  bezout := by
    norm_num [s2, midpointSource, residualSourceLift, bLift, tau, dot]
def latticeIndex : GeneratorIndex := ⟨20, 1, -4, 2⟩
def rowIndex1 : GeneratorIndex := ⟨5, 1, -1, 2⟩
def rowIndex2 : GeneratorIndex := ⟨5, -1, 1, 2⟩
def rowIndex3 : GeneratorIndex := latticeIndex
def rowIndex4 : GeneratorIndex := ⟨20, -1, 4, 2⟩
end Examples41
end TunnellMap


