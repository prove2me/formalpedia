-- Prove2me | Definitions.Def_MillerRabin_Miscellaneous
-- name    : MillerRabin_Miscellaneous
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T08:10:32.514555+00:00
-- url     : https://prove2.me/theorems/1859ed83-e2a8-4fe7-9688-65dc6c1e04d9
-- title:
--   Miscellaneous
-- statement:
--   Definitions and structural lemmas for Miscellaneous, from hanwenzhu/miller-rabin contributors (see pinned LICENSE and source headers)'s pinned Miller–Rabin primality test error bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Miscellaneous.lean

import Definitions.Def_MillerRabin_StrongProbable
set_option autoImplicit false
open Nat Subgroup
instance {α} {a : α} [i0 : Zero α] [inst : Decidable (a ≠ 0)] : Decidable (NeZero a) :=
  propext (@neZero_iff α i0 a) ▸ inst
namespace SPP
end SPP


