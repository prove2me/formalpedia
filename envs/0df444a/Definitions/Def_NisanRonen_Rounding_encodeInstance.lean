-- Prove2me | Definitions.Def_NisanRonen_Rounding_encodeInstance
-- name    : NisanRonen_Rounding_encodeInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:22:29.941364+00:00
-- url     : https://prove2.me/theorems/1f02be2b-d191-4382-8187-29c2a12668ba
-- title:
--   Binary encoding of a rounded instance
-- statement:
--   A rounded instance in $\delta$-units, a list of task columns $c = (c_1, \dots, c_n) \in \mathbb N^n$, is written over the finite alphabet $\{0, 1, (, ), ,\}$ as follows: each column becomes an opening bracket, then for each agent $i = 1, \dots, n$ the binary digits of $c_i$ followed by a comma, then a closing bracket; the columns are concatenated.
--
--   This is the input encoding in which "polynomial time" is measured for the allocation algorithm. Numbers are written in binary, so the input length grows with the number of tasks and the bit lengths of the entries.
--
--   **Formalization Note** The alphabet is Mathlib's `Computability.Γ'` and the digits are `Computability.encodeNat` (least significant bit first; $0$ is the empty string).
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, Theorem 5.9, p. 193 (PDF p. 28): "a polynomial time mechanism"; p. 172 (PDF p. 7): "a mechanism is poly-time computable if the output and payment functions are computable in polynomial time"

import Mathlib

namespace NisanRonen.Rounding

/-- **Binary encoding of a δ-unit instance** (cost model for "polynomial time", Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001),
Theorem 5.9, p. 193, and p. 172: "a mechanism is poly-time computable if the output and payment
functions are computable in polynomial time"). Each column `c : Fin n → ℕ` (one task) is written
as `bra`, then for each agent `i` in increasing order the binary digits of `c i`
(`Computability.encodeNat`) followed by `comma`, then `ket`; the columns are concatenated.

**Formalization Note** Numbers are written in binary, so the input length is polynomial in
`k` and in the bit-lengths of the entries (a unary encoding would make "polynomial"
pseudo-polynomial). The alphabet is Mathlib's finite `Computability.Γ'`. -/
def encodeInstance {n : ℕ} (cols : List (Fin n → ℕ)) : List Computability.Γ' :=
  cols.flatMap fun c =>
    [Computability.Γ'.bra] ++
      (List.finRange n).flatMap
        (fun i => (Computability.encodeNat (c i)).map Computability.Γ'.bit ++
          [Computability.Γ'.comma]) ++
      [Computability.Γ'.ket]

end NisanRonen.Rounding


