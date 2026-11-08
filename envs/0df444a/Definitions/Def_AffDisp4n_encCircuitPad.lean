-- Prove2me | Definitions.Def_AffDisp4n_encCircuitPad
-- name    : AffDisp4n_encCircuitPad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:59:23.331871+00:00
-- url     : https://prove2.me/theorems/c2def2d0-1265-46b0-8ef8-e42cd08a8119
-- title:
--   Encoding of the input of the algorithm of Theorem 4.1
-- statement:
--   The input of the algorithm of Theorem 4.1 is written as the number $n$, the circuit $C_0$, and the number $2^d$ in unary.
--
--   **Formalization Note** Mathlib's polynomial time is polynomial in the input length. The word $2^d$ makes the input length polynomial in $n$, $|C_0|$ and $2^d$, and at least each of them. For $|C_0| < 4n - 10d$, time polynomial in the input length is therefore time $\mathrm{poly}(n, 2^d)$.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), Theorem 4.1, p.21

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_Circuit
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_AffDisp4n_vecWord
import Definitions.Def_AffDisp4n_Acyclic_tokens

namespace AffDisp4n

/-- **Encoding of the input of the algorithm of Theorem 4.1** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), Theorem 4.1, p.21: "given a B₂-circuit C₀ on n inputs … in time poly(n, 2ᵈ)"): the number `n`, the
circuit, and the number `2ᵈ` in unary.

**Formalization Note** Mathlib's polynomial time is polynomial in the input length. The word `2ᵈ` makes the
input length polynomial in `n`, `|C₀|` and `2ᵈ`, and at least each of them, so for `|C₀| < 4n − 10d` "time
polynomial in the input length" is "time poly(n, 2ᵈ)". -/
def encCircuitPad (x : (Σ n, Circuit n) × ℕ) : List (Fin 3) :=
  LowErrExt.encWords ([natWord x.1.1] ++ x.1.2.tokens (fun i => natWord i.val) ++ [natWord (2 ^ x.2)])

end AffDisp4n


