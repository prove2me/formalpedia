-- Prove2me | Definitions.Def_PPSLattice_decPMove
-- name    : PPSLattice_decPMove
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:34:31.123125+00:00
-- url     : https://prove2.me/theorems/0aa8fe4b-377f-4647-9f9d-de85e055901e
-- title:
--   Moves of a PPS adversary and their parser
-- statement:
--   After receiving $(\mathrm{crs},\mathrm{ct}_{i^*})$ an adversary makes moves of three kinds: an oracle query $(i,\mu_i)$, the set $S$, or the guess $b'$. The parser reads `tup [00, i, µ]` as a query ($i$ in binary), `tup [01, S]` as a set, and every other string as the guess given by the first bit of its second field; every string is a move.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.1, p.18

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_PPSLattice_decBin
import Definitions.Def_PPSLattice_decSet
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- A move of an adversary in the PPS games of Definition 4.1 after it has received
`(crs, ct_{i*})`: an oracle query `(i, µ_i)`, the set `S`, or the guess `b′`. -/
inductive PMove
  | query (i : ℕ) (mu : Str)
  | setS (S : Finset ℕ)
  | guess (b : Bool)

/-- The **parser of PPS moves**: `tup [00, i, µ]` is the oracle query `(i, µ)` (`i` in binary),
`tup [01, S]` names the set `S` (`decSet`), and every other string is the guess given by the first bit
of its second field (`0` if absent).
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.1, Mode Indistinguishability and Payload Hiding, p.18 ("S ← A^{O(·,·)}(crs,
ct_{i*,b})", "the oracle O takes as input (i, µ_i) ∈ [N] × M_λ", "b ← A(sk_S)").

**Formalization Note.** Every string parses, so every adversary output is a move. -/
def decPMove (o : Str) : PMove :=
  let fs := BeyondDS.untup o
  match fs.getD 0 [] with
  | [false, false] => .query (decBin (fs.getD 1 [])) (fs.getD 2 [])
  | [false, true] => .setS (decSet (fs.getD 1 []))
  | _ => .guess ((fs.getD 1 []).headD false)

end PPSLattice


