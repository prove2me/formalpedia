-- Prove2me | Definitions.Def_LexPat_Grammar
-- name    : LexPat_Grammar
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:34:29.075318+00:00
-- url     : https://prove2.me/theorems/2b1ad112-f1af-4fec-a1b1-234e5c1abcc9
-- title:
--   Grammar
-- statement:
--   Definitions and structural lemmas for Grammar, from scidonia/lexpat contributors (see pinned LICENSE and source headers)'s pinned UTF-8 decoder properties for LexPat development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scidonia/lexpat/blob/15eee92b433940e5481f09c7f77e6f833e5f684d/LexPat/Grammar.lean

import Definitions.Def_LexPat_Types
import Definitions.Def_LexPat_Lexer
import Definitions.Def_LexPat_Encoding
set_option autoImplicit true
namespace LexPat
inductive Phase where
  | prolog
  | content
  | epilog
deriving Repr, DecidableEq
def decDigitValue (n : Nat) : Option Nat :=
  if between n 0x30 0x39 then some (n - 0x30) else none
def hexDigitValue (n : Nat) : Option Nat :=
  if between n 0x30 0x39 then some (n - 0x30)
  else if between n 0x41 0x46 then some (n - 0x41 + 10)
  else if between n 0x61 0x66 then some (n - 0x61 + 10)
  else none
def validEncName (label : String) : Bool :=
  match label.toList with
  | [] => false
  | c :: rest =>
    isAsciiLetter c.toNat && rest.all (fun d => isAsciiNameChar d.toNat)
def checkEncodingLabel (detected : Encoding) (label : String) (offset : Nat) :
    Except ParseError Unit :=
  match classifyLabel label with
  | .unknown => .error ⟨.unknownEncoding, "unknownEncoding", offset⟩
  | .utf8 =>
    if detected = .utf8 then .ok ()
    else .error ⟨.incorrectEncoding, "encodingMismatch", offset⟩
  | .ascii =>
    if detected = .ascii then .ok ()
    else .error ⟨.incorrectEncoding, "encodingMismatch", offset⟩
  | .latin1 =>
    if detected = .latin1 then .ok ()
    else .error ⟨.incorrectEncoding, "encodingMismatch", offset⟩
  | .utf16 =>
    if detected = .utf16le ∨ detected = .utf16be then .ok ()
    else .error ⟨.incorrectEncoding, "encodingMismatch", offset⟩
  | .utf16le =>
    if detected = .utf16le then .ok ()
    else .error ⟨.incorrectEncoding, "encodingMismatch", offset⟩
  | .utf16be =>
    if detected = .utf16be then .ok ()
    else .error ⟨.incorrectEncoding, "encodingMismatch", offset⟩
end LexPat


