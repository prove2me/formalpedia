-- Prove2me | Definitions.Def_GroupIsoPoly_encQFTI
-- name    : GroupIsoPoly_encQFTI
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:55:12.845565+00:00
-- url     : https://prove2.me/theorems/428feefb-50bc-4d07-a7b1-5d984507bef4
-- title:
--   Binary input of quadratic form tuple isometry
-- statement:
--   A quadratic form in $n$ variables is determined by its $n(n+1)/2$ coefficients of $x_ix_j$, $i\le j$. An instance of quadratic form tuple isometry over a presented field consists of $n$, $m$ and two $m$-tuples of quadratic forms; its **code** is the self-delimiting code of $n$, of $m$, the field, then the coefficients of $f_1,\dots,f_m$ and of $g_1,\dots,g_m$ in lexicographic order of $(i,j)$, each by its field coordinates.
--
--   On homogeneous quadratic polynomials the code is injective.
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Corollary 4.2, p.27 (PDF p.31)

import Mathlib
import Definitions.Def_GroupIsoPoly_encField

set_option autoImplicit false

namespace GroupIsoPoly

open ExponomialAssortment.FPTAS (encodeNat)
open AvgCaseTI (FieldPres)

/-- The coefficient of `x_i x_j` in a polynomial in `n` variables. -/
noncomputable def quadCoeff {K : Type*} [CommRing K] {n : ℕ} (g : MvPolynomial (Fin n) K)
    (i j : Fin n) : K :=
  MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single j 1) g

/-- The `n(n+1)/2` coefficients of a quadratic form, `x_i x_j` for `i ≤ j`, in lexicographic order. -/
noncomputable def formNats (P : FieldPres) {n : ℕ} (g : MvPolynomial (Fin n) P.F) : List ℕ :=
  (List.ofFn fun i : Fin n => (List.ofFn fun j : Fin n =>
    if i ≤ j then elemNats P (quadCoeff g i j) else []).flatten).flatten

/-- **The binary input of quadratic form tuple isometry** over a presented field.

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Corollary 4.2, p.27 (PDF p.31): "Let (f1, . . . , fm),
(g1, . . . , gm) ∈ F_{2^f}[x1, . . . , xn]^m be two tuples of quadratic forms."

The code is `n`, `m`, the field (`encField`), then the forms `f₁, …, f_m, g₁, …, g_m`, each by its
`n(n+1)/2` coefficients of `x_i x_j` (`i ≤ j`), each coefficient by its power-basis coordinates.

**Formalization Note.** A homogeneous quadratic polynomial has no other monomials, so on quadratic
forms the code is injective. -/
noncomputable def encQFTI (P : FieldPres) (n m : ℕ) (f g : Fin m → MvPolynomial (Fin n) P.F) :
    List Bool :=
  encodeNat n ++ encodeNat m ++ encField P ++
    ((List.ofFn fun i : Fin m => formNats P (f i)).flatten.map encodeNat).flatten ++
    ((List.ofFn fun i : Fin m => formNats P (g i)).flatten.map encodeNat).flatten

end GroupIsoPoly


