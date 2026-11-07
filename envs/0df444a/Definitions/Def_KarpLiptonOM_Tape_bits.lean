-- Prove2me | Definitions.Def_KarpLiptonOM_Tape_bits
-- name    : KarpLiptonOM_Tape_bits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:38:27.053296+00:00
-- url     : https://prove2.me/theorems/0c3a0fed-63d2-4814-a67c-4831edf50d7c
-- title:
--   Binary string read from a tape
-- statement:
--   The **string written on a tape** is the binary string read from the scanned square rightwards, up to (not including) the first square that holds neither the symbol for $0$ nor the symbol for $1$. An oracle machine's query is the string on its query tape and its output is the string on its work tape, read this way.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.1, p.20 (oracle machines, transducers)

import Mathlib
import Definitions.Def_KarpLiptonOM_Tape

namespace KarpLiptonOM

/-- The binary string written on a tape from the scanned square rightwards: the maximal run of
squares holding `ι(0)` or `ι(1)`, read as bits (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.1, p.20).

**Formalization Note** This is how an oracle machine's query string (on the query tape) and its
output string (on the work tape) are read: the run stops at the first blank or non-bit symbol. -/
def Tape.bits {Γ : Type} [DecidableEq Γ] (ι : Option Bool ↪ Γ) (t : Tape Γ) : List Bool :=
  ((t.head :: t.right).takeWhile
      (fun s => decide (s = some (ι (some true)) ∨ s = some (ι (some false))))).map
    (fun s => decide (s = some (ι (some true))))

end KarpLiptonOM


