-- Prove2me | Definitions.Def_AvgCaseTI_encodeInstance
-- name    : AvgCaseTI_encodeInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:20.953582+00:00
-- url     : https://prove2.me/theorems/2c213aec-b03c-4e63-ba72-431c52046ec6
-- title:
--   Instances of algebra isomorphism and their binary code
-- statement:
--   An **instance of algebra isomorphism** is a presented finite field $\mathbb F_q=\mathbb F_p[x]/(f)$, a dimension $n$, and two structure tensors $A,B\in T(n\times n\times n,q)$.
--
--   Its **binary code** is the concatenation of self-delimiting binary codes of
--   1. $p$ and $d=\deg f$;
--   2. the $d$ coefficients of $f$ below its leading coefficient;
--   3. $n$;
--   4. the entries of $A$, then those of $B$, in lexicographic order of $(i,j,k)$, each entry written as its $d$ coordinates in the basis $1,x,\dots,x^{d-1}$.
--
--   The **input length** $L$ is the length of this code. A number $m$ costs $2\lceil\log_2(m+1)\rceil+1$ bits, so $n^3d\le L=O(n^3\log q+\log n)$ and $\mathrm{poly}(L)=\mathrm{poly}(n,\log q)$.
--
--   **Formalization Note** Numbers are written with the published `ExponomialAssortment.FPTAS.encodeNat` (bit length in unary, a separator, then the bits). `inputLength x` is $L$.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.1, p.5 (PDF p.7); §3.1, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_AvgCaseTI_FieldPres
import Definitions.Def_AvgCaseTI_Tensor3

set_option autoImplicit false

namespace AvgCaseTI

open ExponomialAssortment.FPTAS (encodeNat)

/-- **An instance of algebra isomorphism**: a presented finite field `F_q`, a dimension `n`, and two
structure tensors `A, B ∈ T(n × n × n, q)`.

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.1, p.5
(PDF p.7): "given A, B ∈ U ⊗ U ⊗ U∗, decide whether they are isomorphic". -/
structure AlgIsoInstance where
  P : FieldPres
  n : ℕ
  A : Tensor3 P.F n
  B : Tensor3 P.F n

/-- Binary code of a field element: the self-delimiting codes of its `deg f` power-basis coordinates
(each a residue mod `p`, written as a natural number below `p`). -/
noncomputable def encodeElem (P : FieldPres) (a : P.F) : List Bool :=
  (List.ofFn fun i : Fin P.f.natDegree => encodeNat (P.coords a i).val).flatten

/-- Binary code of a 3-way array: the codes of its entries in lexicographic `(i, j, k)` order. -/
noncomputable def encodeTensor (P : FieldPres) {n : ℕ} (A : Tensor3 P.F n) : List Bool :=
  (List.ofFn fun i : Fin n => (List.ofFn fun j : Fin n =>
    (List.ofFn fun k : Fin n => encodeElem P (A i j k)).flatten).flatten).flatten

/-- **The binary input of an algebra-isomorphism instance.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.1, p.5
(PDF p.7) and §3.1, p.16 (PDF p.18): the algorithm is given the field and the structure constants of
`A` and `B`.

The code is the concatenation of the self-delimiting binary codes of `p`, `d = deg f`, the `d`
coefficients of `f` below the leading one, `n`, then the entries of `A` and of `B`.

**Formalization Note.** `encodeNat` is the published `ExponomialAssortment.FPTAS.encodeNat` (bit
length in unary, a separator, then the bits), so every number `m` costs `2·size(m) + 1` bits and the
code length `L` satisfies `n³·d ≤ L = O(n³ log q + log n)`; `poly(L) = poly(n, log q)`. -/
noncomputable def encodeInstance (x : AlgIsoInstance) : List Bool :=
  encodeNat x.P.p ++ encodeNat x.P.f.natDegree ++
    (List.ofFn fun i : Fin x.P.f.natDegree => encodeNat (x.P.f.coeff i).val).flatten ++
    encodeNat x.n ++ encodeTensor x.P x.A ++ encodeTensor x.P x.B

/-- The input length `L` of an instance: the length of `encodeInstance`. -/
noncomputable def inputLength (x : AlgIsoInstance) : ℕ := (encodeInstance x).length

end AvgCaseTI


