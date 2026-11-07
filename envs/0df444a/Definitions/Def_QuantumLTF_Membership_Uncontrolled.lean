-- Prove2me | Definitions.Def_QuantumLTF_Membership_Uncontrolled
-- name    : QuantumLTF_Membership_Uncontrolled
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:32:40.602683+00:00
-- url     : https://prove2.me/theorems/857d2bb8-75c7-47c8-a59a-79f493978a1b
-- title:
--   An oracle circuit with no controlled oracle call
-- statement:
--   An oracle circuit is uncontrolled if every oracle call in it is a plain call or an inverse call, and none has a control wire. The paper's algorithms use only such calls.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, p. 24 (PDF p. 25); pp. 28–29 (PDF pp. 29–30)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit

namespace QuantumLTF.Membership

open QAlgorithms

/-- **An oracle circuit with no controlled oracle call.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, p. 24 (PDF p. 25) and pp. 28–29
(PDF pp. 29–30): the paper's algorithms apply the oracle only as a plain call, or its inverse,
never with a control wire.

**Formalization Note.** Inverse calls remain allowed; they are counted by `queryCount`. -/
def Uncontrolled {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ} (c : OracleCircuit S a m) : Prop :=
  ∀ st ∈ c, match st with
    | .gate _ => True
    | .query _ _ control _ _ => control = none

end QuantumLTF.Membership


