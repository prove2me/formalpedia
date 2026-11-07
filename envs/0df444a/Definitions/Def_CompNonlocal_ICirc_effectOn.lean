-- Prove2me | Definitions.Def_CompNonlocal_ICirc_effectOn
-- name    : CompNonlocal_ICirc_effectOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:41:23.431823+00:00
-- url     : https://prove2.me/theorems/2d9bef8b-d98b-49d1-a88a-663f4b6b5506
-- title:
--   The POVM element of a classical-output event
-- statement:
--   For a circuit $C$ with classical input $x$ run on an $m$-qubit register and a set $P$ of output strings, the effect of "the classical output lies in $P$" is the sum of the record effects $E_z$ over the full outcomes $z$ whose measured wires read a string in $P$. Its acceptance probability on $\rho$ is $\operatorname{Re}\operatorname{Tr}(E\rho)$; "every quantum circuit taking an $n$-qubit input and producing a classical bit induces an effect".
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §4.1, p.19 and Remark 2, p.36

import Mathlib
import Definitions.Def_CompNonlocal_ICirc_recordEffectOn

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The POVM element of a classical-output event. For a circuit `C` with classical input `x` run
on an `m`-qubit input register, `C.effectOn m x P` is the effect of the event "the classical output
string satisfies `P`": the sum of the record effects over all outcomes `z` of the wires whose
classical output `C.clOut z` satisfies `P`. The probability of the event on an input state `ρ` is
`Re Tr(E ρ)`. This is the effect "describ[ing] a binary quantum test" of Głuch, Morimae, *From
Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027
submission, sha256 e245edd7…), §4.1, p.19 and Remark 2, p.36 ("Every quantum circuit taking an
n-qubit input and producing a classical bit induces an effect"). -/
noncomputable def ICirc.effectOn (C : ICirc) (m : ℕ) (x : Str) (P : Str → Bool) :
    Matrix (Bits m) (Bits m) ℂ :=
  ∑ z : Bits C.width, if P (C.clOut z) then C.recordEffectOn m x z else 0

end CompNonlocal


