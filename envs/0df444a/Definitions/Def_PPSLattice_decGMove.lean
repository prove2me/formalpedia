-- Prove2me | Definitions.Def_PPSLattice_decGMove
-- name    : PPSLattice_decGMove
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:20.358195+00:00
-- url     : https://prove2.me/theorems/0489438c-14ac-4c1d-89fd-07926c772895
-- title:
--   Moves of a garbling adversary and their parser
-- statement:
--   An adversary in the garbling experiment makes oracle queries $\mathrm{CircGarb}(\mathrm{gk},C)$, names the challenge input $x$ and the challenge circuit $C$, and guesses. The parser reads `tup [00, d]`, `tup [01, x]`, `tup [10, d]` and everything else as the guess.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.4, Security, p.20

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_RestrictedDec_Circuit
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- A move of an adversary in the garbling security game: an oracle query `CircGarb(gk, C)`, the
challenge input `x`, the challenge circuit `C`, or the guess `b′` (`none` = not a circuit code). -/
inductive GMove
  | query (C : Option RestrictedDec.Circuit)
  | input (x : Str)
  | circ (C : Option RestrictedDec.Circuit)
  | guess (b : Bool)

/-- The **parser of garbling-game moves**: `tup [00, d]` is an oracle query on the circuit with code
`d`, `tup [01, x]` the challenge input, `tup [10, d]` the challenge circuit, and every other string the
guess given by the first bit of its second field.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.4, Security, p.20 ("x ← A^{CircGarb(gk,·)}(1^λ)", "C ← A^{CircGarb(gk,·)}(x̃)",
"b ← A^{CircGarb(gk,·)}(C̃)"). -/
def decGMove (o : Str) : GMove :=
  let fs := BeyondDS.untup o
  match fs.getD 0 [] with
  | [false, false] => .query (RestrictedDec.decCircuit (fs.getD 1 []))
  | [false, true] => .input (fs.getD 1 [])
  | [true, false] => .circ (RestrictedDec.decCircuit (fs.getD 1 []))
  | _ => .guess ((fs.getD 1 []).headD false)

end PPSLattice


