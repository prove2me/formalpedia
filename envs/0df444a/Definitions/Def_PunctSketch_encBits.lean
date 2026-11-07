-- Prove2me | Definitions.Def_PunctSketch_encBits
-- name    : PunctSketch_encBits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:30.613105+00:00
-- url     : https://prove2.me/theorems/37e91333-7d83-4a5f-8d05-f52380730110
-- title:
--   Machine alphabet: unary numbers, bit strings, lists
-- statement:
--   The machines of the mission work over a four-letter alphabet: the symbols $0,1$ are bits, $2$ ends a list entry and $3$ separates input fields. This item fixes the encoding of a bit string, of a number in unary, of a list of binary numbers and of a list of bit strings.
--
--   The order $n$ of the graph is always written in unary. Result 1 bounds the coordinator's time by $\mathrm{poly}(n,k)$, and with $n$ in binary an input could have length $O(\log n)$, too short for a running time polynomial in $n$.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §2, p.4 (PDF p.5); Result 1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_bit
import Definitions.Def_OnlineCRS_Combine_encNat
open OnlineCRS.Combine

namespace PunctSketch

/-- **Machine alphabet: unary numbers, bit strings and lists.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §2, p.4 (conventions).
Auxiliary encoding for the polynomial-time clauses of Result 1, p.2.

Symbols of `Sym = Fin 4`: `0`, `1` are bits, `2` ends a list entry, `3` separates input fields.
`encUnary n` is `n` written in unary, `encBits` a bit string, `encNatList` a list of binary
naturals, `encBitsList` a list of bit strings.

**Formalization Note.** Every machine input writes the order `n` in unary, because the bound of
Result 1 is `poly(n, k)` while the input could otherwise be as short as `O(log n)` bits. -/
def encBits (l : List Bool) : List Sym := l.map bit

/-- `n` in unary: `n` copies of the symbol `1`. -/
def encUnary (n : ℕ) : List Sym := List.replicate n 1

/-- A list of naturals, each in binary and ended by the symbol `2`. -/
def encNatList (l : List ℕ) : List Sym := l.flatMap (fun x => encNat x ++ [2])

/-- A list of bit strings, each ended by the symbol `2`. -/
def encBitsList (l : List (List Bool)) : List Sym := l.flatMap (fun m => encBits m ++ [2])

end PunctSketch


