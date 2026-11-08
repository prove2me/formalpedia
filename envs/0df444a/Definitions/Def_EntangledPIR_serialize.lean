-- Prove2me | Definitions.Def_EntangledPIR_serialize
-- name    : EntangledPIR_serialize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:05.602681+00:00
-- url     : https://prove2.me/theorems/27b70d93-a719-47dd-ab85-7a059ba89d38
-- title:
--   Message formats and sizes
-- statement:
--   The bit formats of the messages of Protocol 1: a table of $4k$ strings of $d$ bits, lexicographic in $(i,j)$; the positions $t\in[4]^k$ at two bits each; the test outcomes on the traps; and $K$. This module also gives the length of the client's random string, $n\lambda w+2k+4kd$, and `msgBound`, an upper bound on the length of every message that exceeds all prescribed lengths.
--
--   **Formalization Note** The formats are the ones the counts of App. C.2 require: $4kd$, $2k$, $3kd$ and $kd$ bits.
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Protocol 1, p.26; App. A.1, p.53; App. C.2, p.57

import Definitions.Def_EntangledPIR_Field

/-!
Mantri, *Private Information Retrieval from Two Entangled Servers*, manuscript (Nov. 2026), Protocol 1,
p.26, A.1, p.53: the formats of the messages, as bit lists.
-/

namespace EntangledPIR

/-- The copies `(i, j) ∈ [k] × [4]` of Protocol 1, p.26. -/
abbrev CopyIdx (k : ℕ) : Type := Fin k × Fin 4

/-- Bits `l[off], …, l[off + d − 1]` as a string, with `false` past the end. -/
def chunk (l : List Bool) (off d : ℕ) : Bits d := fun b => l.getD (off + b) false

/-- Format of a table `(a_{i,j})` of `4k` strings of `d` bits: lexicographic in `(i, j)`, `4kd` bits. -/
def serMat {k d : ℕ} (a : CopyIdx k → Bits d) : List Bool :=
  (List.finRange k).flatMap fun i => (List.finRange 4).flatMap fun j => List.ofFn (a (i, j))

/-- Reading a table in that format. -/
def parseMat (k d : ℕ) (l : List Bool) : CopyIdx k → Bits d :=
  fun c => chunk l ((c.1.val * 4 + c.2.val) * d) d

/-- Format of a position `j ∈ [4]`: two bits, high bit first. -/
def serPosOne (j : Fin 4) : List Bool := [decide (2 ≤ j.val), decide (j.val % 2 = 1)]

/-- Format of `t = (t_1, …, t_k)`: `2k` bits. -/
def serPos {k : ℕ} (t : Fin k → Fin 4) : List Bool :=
  (List.finRange k).flatMap fun i => serPosOne (t i)

/-- Reading `t` from that format. -/
def parsePos (k : ℕ) (l : List Bool) : Fin k → Fin 4 :=
  fun i =>
    ⟨(if l.getD (2 * i.val) false then 2 else 0) + (if l.getD (2 * i.val + 1) false then 1 else 0), by
      split_ifs <;> omega⟩

/-- Format of the test outcomes `(f_{i,j})_{j≠t_i}`: lexicographic over the traps, `3kd` bits. -/
def serTraps {k d : ℕ} (t : Fin k → Fin 4) (f : CopyIdx k → Bits d) : List Bool :=
  (List.finRange k).flatMap fun i => (List.finRange 4).flatMap fun j =>
    if j ≠ t i then List.ofFn (f (i, j)) else []

/-- Format of `K = (K_1, …, K_k)`: `kd` bits. -/
def serVec {k d : ℕ} (K : Fin k → Bits d) : List Bool :=
  (List.finRange k).flatMap fun i => List.ofFn (K i)

/-- Reading `K` from bit `off` on. -/
def parseVec (k d : ℕ) (l : List Bool) (off : ℕ) : Fin k → Bits d :=
  fun i => chunk l (off + i.val * d) d

/-- The number of random bits of the client, App. C.2, p.57: `nλw` for `r_1, …, r_λ`, `2k` for `t`,
`4kd` for the masks. -/
def tapeLen (n lam : ℕ) : ℕ :=
  lam * queryLen n lam + 2 * shareCount n lam + 4 * shareCount n lam * queryLen n lam

/-- The largest prescribed message length plus two; the alphabet of messages is `BitStr` of this
length, so it also represents every over-long message (see `BitStr`). -/
def msgBound (n m lam : ℕ) : ℕ :=
  4 * shareCount n lam * queryLen n lam + 2 * shareCount n lam + m + 2

end EntangledPIR


