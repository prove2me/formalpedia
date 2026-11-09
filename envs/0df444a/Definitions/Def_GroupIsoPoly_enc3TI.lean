-- Prove2me | Definitions.Def_GroupIsoPoly_enc3TI
-- name    : GroupIsoPoly_enc3TI
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:53:30.469018+00:00
-- url     : https://prove2.me/theorems/eb5e013b-a1c8-499e-a732-3c29e9c324da
-- title:
--   Binary input of 3-tensor isomorphism
-- statement:
--   An instance of 3-tensor isomorphism over a presented field $\mathbb F_q$ consists of $\ell,m,n$ and two $\ell\times m\times n$ arrays $A,B$. Its **code** is the self-delimiting code of $\ell$, $m$, $n$, the field, then the entries of $A$ and of $B$ in lexicographic order of $(i,j,k)$, each by its field coordinates. Its length is $O(\ell mn\log q+e\log p+\log(\ell mn))$.
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 1.2, p.2 (PDF p.6)

import Mathlib
import Definitions.Def_GroupIsoPoly_encField
import Definitions.Def_GroupIsoPoly_TensorIso

set_option autoImplicit false

namespace GroupIsoPoly

open ExponomialAssortment.FPTAS (encodeNat)
open AvgCaseTI (FieldPres)

/-- The coordinates of the entries of a 3-way array, in lexicographic order of `(i, j, k)`. -/
noncomputable def arrayNats (P : FieldPres) {l m n : ℕ} (A : Array3 P.F l m n) : List ℕ :=
  (List.ofFn fun i : Fin l => (List.ofFn fun j : Fin m =>
    (List.ofFn fun k : Fin n => elemNats P (A i j k)).flatten).flatten).flatten

/-- **The binary input of 3-tensor isomorphism** over a presented field.

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 1.2, p.2 (PDF p.6): "Let A, B be two ℓ × m × n
3-way arrays over Fq."

The code is `ℓ`, `m`, `n`, the field (`encField`), then the entries of `A` and of `B` in
lexicographic order, each by its power-basis coordinates.

**Formalization Note.** The dimensions come first; the input length is
`O(ℓ m n · log q + deg f · log p + log(ℓ m n))`. -/
noncomputable def enc3TI (P : FieldPres) (l m n : ℕ) (A B : Array3 P.F l m n) : List Bool :=
  encodeNat l ++ encodeNat m ++ encodeNat n ++ encField P ++
    ((arrayNats P A).map encodeNat).flatten ++ ((arrayNats P B).map encodeNat).flatten

end GroupIsoPoly


