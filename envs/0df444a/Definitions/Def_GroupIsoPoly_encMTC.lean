-- Prove2me | Definitions.Def_GroupIsoPoly_encMTC
-- name    : GroupIsoPoly_encMTC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:53:27.960676+00:00
-- url     : https://prove2.me/theorems/a8483849-fe9b-4cf8-b5e6-2f5f3dec14e0
-- title:
--   Binary input of matrix tuple congruence
-- statement:
--   An instance of matrix tuple congruence over a presented field $\mathbb F_q$ consists of $n$, $m$ and two $m$-tuples $A,B$ of $n\times n$ matrices. Its **code** is the self-delimiting code of $n$, then of $m$, then the field, then the entries of $A_1,\dots,A_m$ and of $B_1,\dots,B_m$ (row by row, each entry by its field coordinates).
--
--   The dimensions come first, so the length is $O(mn^2e+e+\log(nm))$ for $q=p^e$ with $p$ fixed.
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 4.1, p.27 (PDF p.31)

import Mathlib
import Definitions.Def_GroupIsoPoly_encField

set_option autoImplicit false

namespace GroupIsoPoly

open ExponomialAssortment.FPTAS (encodeNat)
open AvgCaseTI (FieldPres)

/-- **The binary input of matrix tuple congruence** over a presented field.

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 4.1, p.27 (PDF p.31): "Let A = (A1, . . . , Am),
B = (B1, . . . , Bm) ∈ M(n, 2^f)^m be two tuples of matrices."

The code is `n`, `m`, the field (`encField`), then the entries of `A₁, …, A_m` and of
`B₁, …, B_m`, each matrix row by row and each entry by its power-basis coordinates.

**Formalization Note.** The dimensions come first, so a zero dimension is read in `O(1)` bits; the
input length is `O(m n² deg f + deg f + log(nm))`. -/
noncomputable def encMTC (P : FieldPres) (n m : ℕ) (A B : Fin m → Matrix (Fin n) (Fin n) P.F) :
    List Bool :=
  encodeNat n ++ encodeNat m ++ encField P ++
    ((List.ofFn fun i : Fin m => matNats P (A i)).flatten.map encodeNat).flatten ++
    ((List.ofFn fun i : Fin m => matNats P (B i)).flatten.map encodeNat).flatten

end GroupIsoPoly


