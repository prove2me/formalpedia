-- Prove2me | Definitions.Def_CompNonlocal_ICirc_qubitEffect
-- name    : CompNonlocal_ICirc_qubitEffect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:42:42.787675+00:00
-- url     : https://prove2.me/theorems/ef6a4bf6-0cfa-4a6e-bf53-afd967b9c1b0
-- title:
--   A player's effect on its qubit
-- statement:
--   For a circuit reading a classical question $x$ and one qubit, the effect $A^x_a$ on that qubit of the event "the answer lies in $P$". These are the POVMs $\{A^x_a\}_a$ "implemented by $A$".
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §5.1, p.24

import Mathlib
import Definitions.Def_CompNonlocal_ICirc_effectOn
import Definitions.Def_CompNonlocal_toQubit

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The effect, on a single input qubit, of a classical-output event of a circuit with classical
input `x`. This is `effectOn` for a one-qubit input register, read on the qubit basis `Bool`. It is
the effect `A^x_a` of a player's answer `a` on its share of the state in Głuch, Morimae, *From
Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027
submission, sha256 e245edd7…), §5.1, p.24 ("{A^x_a}_a denotes the POVM implemented by A"). -/
noncomputable def ICirc.qubitEffect (C : ICirc) (x : Str) (P : Str → Bool) : Matrix Bool Bool ℂ :=
  toQubit (C.effectOn 1 x P)

end CompNonlocal


