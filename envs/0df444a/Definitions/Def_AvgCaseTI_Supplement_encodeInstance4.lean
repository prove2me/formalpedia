-- Prove2me | Definitions.Def_AvgCaseTI_Supplement_encodeInstance4
-- name    : AvgCaseTI_Supplement_encodeInstance4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:28:28.050198+00:00
-- url     : https://prove2.me/theorems/31852137-9c7a-4d30-b9b5-6c0fc89a3097
-- title:
--   Binary input of a 4-tensor isomorphism instance
-- statement:
--   An **instance** of 4-tensor isomorphism is a presented finite field $\mathbb F_q=\mathbb F_p[x]/(f)$, a dimension $n$, and two 4-way arrays $A,B$ over $\mathbb F_q$.
--
--   Its **binary code** is the concatenation of the self-delimiting codes of $p$, of $d=\deg f$, of the $d$ lower coefficients of $f$, of $n$, and then of the entries of $A$ and of $B$ in lexicographic order, each entry written by its $d$ power-basis coordinates. This is the code of the published Theorem 1.1 instances with 4-way arrays in place of 3-way ones. The **input length** $L$ is the length of this code; it satisfies $n^4\le L=O(n^4\log q+\log n)$.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.3, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_AvgCaseTI_encodeInstance
import Definitions.Def_AvgCaseTI_Supplement_Tensor4

set_option autoImplicit false

namespace AvgCaseTI.Supplement

open AvgCaseTI
open ExponomialAssortment.FPTAS (encodeNat)

/-- **An instance of 4-tensor isomorphism**: a presented finite field `F_q`, a dimension `n`, and two
4-way arrays `A, B ∈ F_q^n ⊗ F_q^n ⊗ F_q^n ⊗ F_q^n` (Theorem 1.3, p.6, PDF p.8). -/
structure Instance4 where
  P : FieldPres
  n : ℕ
  A : Tensor4 P.F n
  B : Tensor4 P.F n

/-- Binary code of a 4-way array: the codes `encodeElem` of its entries in lexicographic
`(i, j, k, ℓ)` order. -/
noncomputable def encodeTensor4 (P : FieldPres) {n : ℕ} (A : Tensor4 P.F n) : List Bool :=
  (List.ofFn fun i : Fin n => (List.ofFn fun j : Fin n => (List.ofFn fun k : Fin n =>
    (List.ofFn fun l : Fin n => encodeElem P (A i j k l)).flatten).flatten).flatten).flatten

/-- **The binary input of a 4-tensor isomorphism instance.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.3, p.6 (PDF p.8).

The code is the concatenation of the self-delimiting binary codes of `p`, `d = deg f`, the `d`
coefficients of `f` below the leading one, `n`, then the entries of `A` and of `B`: the layout of
the published `encodeInstance` with 4-way arrays in place of 3-way ones.

**Formalization Note.** The code length `L` satisfies `n⁴ ≤ L = O(n⁴ log q + log n)`. -/
noncomputable def encodeInstance4 (x : Instance4) : List Bool :=
  encodeNat x.P.p ++ encodeNat x.P.f.natDegree ++
    (List.ofFn fun i : Fin x.P.f.natDegree => encodeNat (x.P.f.coeff i).val).flatten ++
    encodeNat x.n ++ encodeTensor4 x.P x.A ++ encodeTensor4 x.P x.B

/-- The input length `L` of a 4-tensor instance. -/
noncomputable def inputLength4 (x : Instance4) : ℕ := (encodeInstance4 x).length

end AvgCaseTI.Supplement


