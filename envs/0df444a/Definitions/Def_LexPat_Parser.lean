-- Prove2me | Definitions.Def_LexPat_Parser
-- name    : LexPat_Parser
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:16:42.239041+00:00
-- url     : https://prove2.me/theorems/fe855394-dcdc-4b10-ab5d-7ee83b81bd2b
-- title:
--   Parser
-- statement:
--   Definitions and structural lemmas for Parser, from scidonia/lexpat contributors (see pinned LICENSE and source headers)'s pinned UTF-8 decoder properties for LexPat development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scidonia/lexpat/blob/15eee92b433940e5481f09c7f77e6f833e5f684d/LexPat/Parser.lean

import Definitions.Def_LexPat_Grammar
import Definitions.Def_LexPat_Stream
set_option autoImplicit true
namespace LexPat
def parseDocument (bytes : ByteArray) (limits : Limits := {}) :
    Except ParseError (Array Event) :=
  let s := Stream.new limits
  let (s1, events1) := Stream.feed s bytes
  let (s2, events2) := Stream.finish s1
  match Stream.result s2 with
  | some (.ok ()) => .ok (events1 ++ events2)
  | some (.error e) => .error e
  | none => .error ⟨.syntaxErr, "incompleteStream", 0⟩
end LexPat


