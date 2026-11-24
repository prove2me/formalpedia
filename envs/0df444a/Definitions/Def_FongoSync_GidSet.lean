-- Prove2me | Definitions.Def_FongoSync_GidSet
-- name    : FongoSync_GidSet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:57:08.587622+00:00
-- url     : https://prove2.me/theorems/07866f1f-328d-4956-b4fe-8fd1b0c42719
-- title:
--   Gid Set
-- statement:
--   Definitions and structural lemmas for Gid Set, from bongofongo (bongofongo/fongo-sync; see pinned Apache-2.0 LICENSE-APACHE)'s pinned FongoSync local-first CRDT replication convergence laws development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/GidSet.lean

import Definitions.Def_FongoSync_Clock
set_option autoImplicit false
namespace FongoSync
def insertGid (g : Gid) : List Gid → List Gid
  | [] => [g]
  | h :: t => if g < h then g :: h :: t else if g = h then h :: t else h :: insertGid g t
def gidSet (l : List Gid) : List Gid := l.foldr insertGid []
end FongoSync


