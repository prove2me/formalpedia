-- Prove2me | Definitions.Def_TunnellMap_RecordSign
-- name    : TunnellMap_RecordSign
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T15:29:10.74461+00:00
-- url     : https://prove2.me/theorems/4e62152f-7bc5-55d6-b78f-d7d4f4acc8ea
-- title:
--   Record Sign
-- statement:
--   Definitions and structural lemmas for Record Sign, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordSign.lean

import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
namespace TunnellMap
namespace BlockGen
open OrderedGenerator
variable {n : ℤ} {s : BResidual n}
end BlockGen
end TunnellMap


