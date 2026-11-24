-- Prove2me | Definitions.Def_LexPat_Encoding_Proofs
-- name    : LexPat_Encoding_Proofs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:34:27.432795+00:00
-- url     : https://prove2.me/theorems/707e76b1-4cd2-43ab-beea-7a46b7b8dfea
-- title:
--   Proofs
-- statement:
--   Definitions and structural lemmas for Proofs, from scidonia/lexpat contributors (see pinned LICENSE and source headers)'s pinned UTF-8 decoder properties for LexPat development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scidonia/lexpat/blob/15eee92b433940e5481f09c7f77e6f833e5f684d/LexPat/Encoding/Proofs.lean

import Definitions.Def_LexPat_Encoding
set_option autoImplicit true
namespace LexPat
open LexPat
def encodeAscii (s : Scalar) : ByteArray :=
  ByteArray.mk #[UInt8.ofNat s.n]
end LexPat


