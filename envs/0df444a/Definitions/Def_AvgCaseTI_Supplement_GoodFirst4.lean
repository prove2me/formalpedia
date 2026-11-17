-- Prove2me | Definitions.Def_AvgCaseTI_Supplement_GoodFirst4
-- name    : AvgCaseTI_Supplement_GoodFirst4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:29:58.164904+00:00
-- url     : https://prove2.me/theorems/c9abaaa6-76a4-41ce-812e-6aa296ab47c8
-- title:
--   First 4-tensors on which a randomized machine decides 4-tensor isomorphism
-- statement:
--   Fix a Turing machine $M$, a degree $k$, a presented finite field $\mathbb F_q$ and $n$. A first 4-way array $A$ is **good** for $M$ if for **every** second 4-way array $B$, at least two thirds of the coin strings $r\in\{0,1\}^{(L+q+2)^k}$ make $M$, started on the code of $(\mathbb F_q,n,A,B)$ followed by $r$, output within $(L+q+2)^k$ steps the bit $1$ if $A$ and $B$ are isomorphic under $\mathrm{GL}(n,q)^4$ and $0$ otherwise.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.3, p.6 (PDF p.8); §4.2, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_AvgCaseTI_Supplement_Halts4

set_option autoImplicit false

namespace AvgCaseTI.Supplement

open AvgCaseTI

open Classical in
/-- **First 4-tensors on which a randomized machine decides 4-tensor isomorphism.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.3, p.6 (PDF p.8): "the algorithm is correct for a 1/poly(q)-fraction of
A ∈ U ⊗ V ⊗ W ⊗ X", and §4.2, p.28 (PDF p.30): "On every such A, both kernel-matching procedures
finish for every B unless a randomized subroutine fails".

`GoodFirst4 M k P n A`: for **every** second 4-way array `B`, at least two thirds of the coin strings
`r ∈ {0,1}^{(L+q+2)^k}` make `M` output within `(L+q+2)^k` steps `[true]` if `A` and `B` are
isomorphic (`TensorIso4 A B`) and `[false]` otherwise.

**Formalization Note.** Success `2/3` over the coins is the standard bounded-error convention, as in
the published `GoodFirst`. -/
def GoodFirst4 (M : Turing.TM2ComputableAux Bool Bool) (k : ℕ) (P : FieldPres) (n : ℕ)
    (A : Tensor4 P.F n) : Prop :=
  ∀ B : Tensor4 P.F n,
    2 * 2 ^ timeBound4 k ⟨P, n, A, B⟩ ≤
      3 * Nat.card {r : Fin (timeBound4 k ⟨P, n, A, B⟩) → Bool //
        HMBinPacking.OutputsWithin M (encodeInstance4 ⟨P, n, A, B⟩ ++ List.ofFn r)
          [decide (TensorIso4 A B)] (timeBound4 k ⟨P, n, A, B⟩)}

end AvgCaseTI.Supplement


