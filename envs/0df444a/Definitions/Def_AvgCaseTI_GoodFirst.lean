-- Prove2me | Definitions.Def_AvgCaseTI_GoodFirst
-- name    : AvgCaseTI_GoodFirst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:44:16.648211+00:00
-- url     : https://prove2.me/theorems/1148c611-bc60-42e2-bcbb-c373a4cabb64
-- title:
--   First tensors on which a randomized machine is correct against every second tensor
-- statement:
--   Let $M$ be a machine, $k$ a degree, $\mathbb F_q$ a presented field and $A\in T(n\times n\times n,q)$. The tensor $A$ is **good** for $(M,k)$ when, for **every** second tensor $B\in T(n\times n\times n,q)$, at least two thirds of the coin strings $r\in\{0,1\}^{(L+2)^k}$ make $M$, started on the code of the instance $(\mathbb F_q,n,A,B)$ followed by $r$, output within $(L+2)^k$ steps the single bit
--   $$
--   [\,A\text{ and }B\text{ are isomorphic algebras}\,].
--   $$
--   Here $L$ is the input length of $(\mathbb F_q,n,A,B)$. Theorem 1.1 asserts that some machine has a $1/\Theta(q)$ fraction of good first tensors.
--
--   **Formalization Note** The success probability $2/3$ is the standard bounded-error convention: any constant in $(1/2,1)$ gives the same class by repetition and majority vote (the paper, p.21: "Bounded repetition reduces randomized polynomial-factorization failures to any fixed constant"). The count is `Nat.card` of the set of good coin strings.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.1, p.5 (PDF p.7); §3.1, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_AvgCaseTI_AlgIso
import Definitions.Def_AvgCaseTI_Halts

set_option autoImplicit false

namespace AvgCaseTI

open Classical in
/-- **First tensors on which a randomized machine decides algebra isomorphism.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.1, p.5
(PDF p.7): "The algorithm is correct for 1/Θ(q)-fraction of A ∈ U ⊗ U ⊗ U∗", and §3.1, p.21
(PDF p.23): "The correctness argument therefore applies for every second tensor B."

`GoodFirst M k P n A` says: for **every** second tensor `B`, at least two thirds of the coin strings
`r ∈ {0,1}^{(L+2)^k}` make `M`, started on the code of `(P, n, A, B)` followed by `r`, output within
`(L+2)^k` steps the one-bit answer `[true]` if `A` and `B` are isomorphic algebras and `[false]`
otherwise.

**Formalization Note.** Success probability `2/3` over the coins is the standard bounded-error
convention; any constant in `(1/2, 1)` gives the same class by majority vote (p.21: "Bounded
repetition reduces randomized polynomial-factorization failures to any fixed constant"). `L` is the
length of the code of the instance `(P, n, A, B)`. -/
def GoodFirst (M : Turing.TM2ComputableAux Bool Bool) (k : ℕ) (P : FieldPres) (n : ℕ)
    (A : Tensor3 P.F n) : Prop :=
  ∀ B : Tensor3 P.F n,
    2 * 2 ^ timeBound k ⟨P, n, A, B⟩ ≤
      3 * Nat.card {r : Fin (timeBound k ⟨P, n, A, B⟩) → Bool //
        HMBinPacking.OutputsWithin M (encodeInstance ⟨P, n, A, B⟩ ++ List.ofFn r)
          [decide (AlgIso A B)] (timeBound k ⟨P, n, A, B⟩)}

end AvgCaseTI


