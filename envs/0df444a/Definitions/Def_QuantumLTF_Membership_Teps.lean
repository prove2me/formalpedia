-- Prove2me | Definitions.Def_QuantumLTF_Membership_Teps
-- name    : QuantumLTF_Membership_Teps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:33:01.316393+00:00
-- url     : https://prove2.me/theorems/faae12e1-7171-4bfa-9bee-5300dfdb993d
-- title:
--   $T_\epsilon=\sqrt{2\log(1/\epsilon)}$
-- statement:
--   $T_\epsilon:=\sqrt{2\log(1/\epsilon)}$, for $0<\epsilon\le1/2$ the scale of the thresholds at which the problem is not almost constant.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 3.1, p. 21 (PDF p. 22)

import Mathlib

namespace QuantumLTF.Membership

/-- **`T_ϵ`.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 3.1, p. 21 (PDF p. 22): `T_ϵ := √(2 log(1/ϵ))`.

**Formalization Note.** Every use has `0 < ϵ ≤ 1/2`, so `log(1/ϵ) > 0` and the root is of a positive
number. -/
noncomputable def Teps (ε : ℝ) : ℝ :=
  Real.sqrt (2 * Real.log (1 / ε))

end QuantumLTF.Membership


