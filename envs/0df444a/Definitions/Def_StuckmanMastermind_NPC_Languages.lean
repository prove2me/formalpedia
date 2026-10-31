-- Prove2me | Definitions.Def_StuckmanMastermind_NPC_Languages
-- name    : StuckmanMastermind_NPC_Languages
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-31T00:52:34.684132+00:00
-- url     : https://prove2.me/theorems/d76a363b-ffbc-44e4-8563-8abcd167e800
-- title:
--   Binary encodings and uniform and fixed-color MSP languages
-- statement:
--   Encode each natural number by its canonical little-endian binary digits, with zero represented by one false digit, preceded by one true bit per digit and a false terminator. Encode an instance by its color count, length and row count, followed by all rows in order. Each row contains its length-many color entries, black score and white score. The uniform language consists exactly of these complete encodings of canonical satisfiable instances with more than one color. The fixed-κ language adds equality of the encoded color count with κ. Strings not encoding such an instance are rejected: truncation, trailing data, noncanonical digits, invalid color entries, and unsorted or duplicate guesses never encode a canonical instance. Complete encoded bit length is the computational input size. Impossible nonnegative feedback is a NO instance. Empty lists and zero length are allowed.
-- source:
--   Stuckman and Zhang, arXiv:cs/0512049v1, §2.1, PDF p. 4; explicit finite-string convention for MSP; https://arxiv.org/abs/cs/0512049v1

import Definitions.Def_StuckmanMastermind_NPC_Instance

namespace StuckmanMastermind.NPC

/-- Length-prefixed little-endian binary; zero has the single digit false. -/
def encodeNat (n : ℕ) : List Bool :=
  let digits := if n = 0 then [false] else n.bits
  List.replicate digits.length true ++ [false] ++ digits

def encodeRow {κ ℓ : ℕ} (r : Row κ ℓ) : List Bool :=
  (guessEntries r.guess).flatMap encodeNat ++
    encodeNat r.feedback.1 ++ encodeNat r.feedback.2

def encodeInstance (I : Instance) : List Bool :=
  encodeNat I.colors ++ encodeNat I.length ++ encodeNat I.rows.length ++
    I.rows.flatMap encodeRow

def uniformLanguage : Set (List Bool) :=
  { w | ∃ I : Instance, 1 < I.colors ∧ I.Canonical ∧
      w = encodeInstance I ∧ I.Satisfiable }

def fixedLanguage (κ : ℕ) : Set (List Bool) :=
  { w | ∃ I : Instance, I.colors = κ ∧ 1 < I.colors ∧ I.Canonical ∧
      w = encodeInstance I ∧ I.Satisfiable }

end StuckmanMastermind.NPC


