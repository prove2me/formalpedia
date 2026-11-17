-- Prove2me | Definitions.Def_AvoidPlast_Supplement_cnfRecords
-- name    : AvoidPlast_Supplement_cnfRecords
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:51:45.326823+00:00
-- url     : https://prove2.me/theorems/ba1c8426-508e-4806-a214-cf2085bd6c62
-- title:
--   Literal records of the fixed CNF encoding
-- statement:
--   SAT gates read their input under one fixed encoding of CNF formulas. A string $1^w0\,b$ is read as a list of records of $w+2$ bits: a variable index written in $w$ bits (least significant first), the sign of the literal, and an end-of-clause flag. An incomplete last record is dropped, so every string encodes a CNF.
--
--   **Formalization Note** The encoding has fixed-width fields and is computable both ways in polynomial time, so SAT under it is $\mathsf{NP}$-complete.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.9, p.25 ($\mathrm{SIZE}^{\mathrm{SAT}}$)

import Mathlib
import Definitions.Def_UniqueOptScores_decodeNat

namespace AvoidPlast.Supplement

/-- The literal records of a string under the fixed CNF encoding used by SAT gates (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728),
Theorem 5.9, p.25, `SIZE^SAT`). A string `1^w 0 b` lists records of `w + 2` bits each: a
variable index (`w` bits, least significant first), a sign bit, and an end-of-clause flag; an
incomplete last record is dropped. -/
def cnfRecords (c : List Bool) : List (ℕ × Bool × Bool) :=
  let w := (c.takeWhile (· = true)).length
  let body := c.drop (w + 1)
  ((body.toChunks (w + 2)).filter (fun ch => ch.length = w + 2)).map fun ch =>
    (UniqueOptScores.decodeNat (ch.take w), ch.getD w false, ch.getD (w + 1) false)

end AvoidPlast.Supplement


