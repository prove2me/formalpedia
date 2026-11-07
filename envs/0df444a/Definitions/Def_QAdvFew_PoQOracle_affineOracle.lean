-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_affineOracle
-- name    : QAdvFew_PoQOracle_affineOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:51:30.698694+00:00
-- url     : https://prove2.me/theorems/020afb11-1305-46e2-bce8-e9a7da9c25c6
-- title:
--   Affine oracle
-- statement:
--   The **affine oracle** $\tilde f=\{\mathrm{ML}_{2^d}[f_n]\}_{d,n}$ of a family $f_n:\{0,1\}^n\to\{0,1\}$ is the collection of multilinear extensions of the $f_n$ over all $\mathbb F_{2^d}$, with field elements represented by bit strings. It is also the component $A$ of §4.1, with $A_t(d,x)=\mathrm{ML}_{2^d}[\mathrm{RO}_t](x)$.
--
--   **Formalization Note** A field-valued answer is given bit by bit. The query $1^n0\,1^d0\,1^j0\,x$, with $d\ge1$ and $x$ the $nd$ bits of $n$ field elements, is answered by bit $j$ of the value; every other query by $0$.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Theorem 4.4, p. 23 (PDF p. 25); §4.1, p. 21 (PDF p. 23)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_ML
import Definitions.Def_QAdvFew_PoQOracle_join

open Polynomial QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

open Classical in
/-- Level `t` of an affine oracle: the query `1^d 0 1^j 0 x`, with `d ≥ 1` and `x` the `t · d` bits
of `t` field elements of `F_{2^d}` (`d` bits each), is answered by bit `j` of
`ML_{2^d}[g](x)`; every other query by `0`. -/
noncomputable def affLevel (t : ℕ) (g : (Fin t → Bool) → Bool) : Oracle := fun q =>
  match splitTag q with
  | some (d, r) =>
    match splitTag r with
    | some (j, xs) =>
      if 1 ≤ d ∧ xs.length = t * d then
        decide ((mlValue d t g (fun i => fieldElt d (xs.drop ((i : ℕ) * d)))).coeff j = 1)
      else false
    | none => false
  | none => false

/-- The **affine oracle** `f̃ = {ML_{2^d}[f_n]}_{d,n∈ℕ}` of a family `f_n : {0,1}^n → {0,1}` (Goldin,
Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1,
Theorem 4.4, p. 23 (PDF p. 25): "the collection of multilinear extensions of `f_n` over `F_{2^d}`,
with field elements represented by bit strings"), and the component `A` of §4.1, p. 21 (PDF p. 23):
`A_t(d, x) = ML_{2^d}[RO_t](x)`. Level `n` (tag `1^n 0`) is `affLevel n (f n)`.

**Formalization Note** A field-valued answer is given bit by bit (the bit index is part of the
query); field elements use the representation of `qPoly`. -/
noncomputable def affineOracle (f : (n : ℕ) → (Fin n → Bool) → Bool) : Oracle :=
  join (fun n => affLevel n (f n))

end QAdvFew.PoQOracle


