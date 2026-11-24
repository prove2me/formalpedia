-- Prove2me | Definitions.Def_FongoSync_Laws
-- name    : FongoSync_Laws
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:58:53.468395+00:00
-- url     : https://prove2.me/theorems/d4177006-6119-4b67-9d81-20a6bff6fdef
-- title:
--   Laws
-- statement:
--   Definitions and structural lemmas for Laws, from bongofongo (bongofongo/fongo-sync; see pinned Apache-2.0 LICENSE-APACHE)'s pinned FongoSync local-first CRDT replication convergence laws development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
set_option autoImplicit false
namespace FongoSync.Laws
open FongoSync
section Register
variable {V : Type} [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]
end Register
end FongoSync.Laws


