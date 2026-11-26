-- Prove2me | Definitions.Def_FramedDescriptorBitWidth
-- name    : FramedDescriptorBitWidth
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-26T21:59:54.940226+00:00
-- url     : https://prove2.me/theorems/bf6173a2-08c5-4baf-8b9d-f91bf27dc5af
-- title:
--   Key and action fields in a framed transition table
-- statement:
--   After a marker and two framed header fields, decode the remaining bits as a list of transition rows. From each row extract the input symbol in its key and the output symbol in its action, using the framed unary-option decoder. The parser is defined for all bit lists.
-- source:
--   Framed universal-machine transition encoding in the Prove2Me Complexitylib definition library.

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Decoder

namespace FramedDescriptor

open Turing.MultiTapeTM

/-- The descriptor payload begins immediately after its first true bit. -/
def afterMarker : List Bool → List Bool
  | [] => []
  | false :: w => afterMarker w
  | true :: w => w

/-- Skip two framed header fields and recover the rows of the transition table. -/
def rows (w : List Bool) : List (List Bool) :=
  frames (dropFrame (dropFrame (afterMarker w)))

/-- The input symbol is the second field of the key. -/
def inputSymbol (row : List Bool) : Option ℕ :=
  (Decoder.unary.option).decode (unframe (dropFrame (unframe row)))

/-- The output symbol is the third field of the action, after the key. -/
def outputSymbol (row : List Bool) : Option ℕ :=
  (Decoder.unary.option).decode (unframe (dropFrame (dropFrame (dropFrame row))))

end FramedDescriptor


