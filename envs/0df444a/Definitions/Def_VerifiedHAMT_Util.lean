-- Prove2me | Definitions.Def_VerifiedHAMT_Util
-- name    : VerifiedHAMT_Util
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:25:11.617559+00:00
-- url     : https://prove2.me/theorems/5a0d9a8f-2e50-4f05-8036-6729469c6d82
-- title:
--   Util
-- statement:
--   Definitions and structural lemmas for Util, from verse-lab/VerifiedHAMT contributors (see pinned LICENSE and source headers)'s pinned Verified hash array mapped tries development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Util.lean

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Init.Data.Array.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace VerifiedHAMT
open Lean.PersistentHashMap (shift maxDepth)
end VerifiedHAMT


