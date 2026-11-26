-- Prove2me | Definitions.Def_TunnellMap_GeneratorSoundness
-- name    : TunnellMap_GeneratorSoundness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:48:07.888322+00:00
-- url     : https://prove2.me/theorems/d417ce26-6f16-406d-81a0-f7f5d7912df1
-- title:
--   Generator Soundness
-- statement:
--   Definitions and structural lemmas for Generator Soundness, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/GeneratorSoundness.lean

import Definitions.Def_TunnellMap_GeneratorRecovery
set_option autoImplicit true
namespace TunnellMap
def reconstructedTarget (E : Triple) (q : ℤ) (d : Triple) : Triple :=
  vadd (negTriple E) (vsmul (2 * q) d)
end TunnellMap


