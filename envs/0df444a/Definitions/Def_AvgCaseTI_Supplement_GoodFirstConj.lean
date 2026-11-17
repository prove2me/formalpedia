-- Prove2me | Definitions.Def_AvgCaseTI_Supplement_GoodFirstConj
-- name    : AvgCaseTI_Supplement_GoodFirstConj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:27:36.826617+00:00
-- url     : https://prove2.me/theorems/7c955de3-5271-4ca5-a20c-d90b9121f11c
-- title:
--   First arrays on which a randomized machine decides matrix code conjugacy
-- statement:
--   Fix a Turing machine $M$ (a Mathlib multi-stack machine with Boolean alphabets), a degree $k$, a presented finite field $\mathbb F_q$ and $n$. A first array $A$ is **good** for $M$ if for **every** second array $B$, at least two thirds of the coin strings $r\in\{0,1\}^{(L+2)^k}$ make $M$, started on the binary code of the instance $(\mathbb F_q,n,A,B)$ followed by $r$, output within $(L+2)^k$ steps the bit $1$ if $A$ and $B$ are conjugate matrix codes and the bit $0$ otherwise. Here $L$ is the length of the code of the instance.
--
--   This is the success notion of Theorem 1.2: the algorithm must be correct, with bounded error, against every second input.
--
--   **Formalization Note** The instance data, its code and the budget $(L+2)^k$ are the published ones of Theorem 1.1 (`AlgIsoInstance`, `encodeInstance`, `timeBound`); only the decided relation changes.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.2, p.5 (PDF p.7); §3.2, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_AvgCaseTI_Halts
import Definitions.Def_AvgCaseTI_Supplement_CodeConj

set_option autoImplicit false

namespace AvgCaseTI.Supplement

open AvgCaseTI

open Classical in
/-- **First tensors on which a randomized machine decides matrix code conjugacy.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.2, p.5 (PDF p.7): "The algorithm is correct for 1/Θ(q) fraction of
A ∈ U ⊗ U∗ ⊗ V", and §3.2, p.24 (PDF p.26): "the algorithm succeeds for every second code on these
first codes".

`GoodFirstConj M k P n A` says: for **every** second array `B`, at least two thirds of the coin strings
`r ∈ {0,1}^{(L+2)^k}` make `M`, started on the code of `(P, n, A, B)` followed by `r`, output within
`(L+2)^k` steps the one-bit answer `[true]` if `A` and `B` are conjugate matrix codes
(`CodeConj A B`) and `[false]` otherwise.

**Formalization Note.** The instance data (presented field, `n`, two `n × n × n` arrays), its code
`encodeInstance` and the budget `timeBound k = (L+2)^k` are the published ones of Theorem 1.1
(`AlgIsoInstance` names the data, not the relation). Success `2/3` over the coins is the standard
bounded-error convention, as in `GoodFirst`. -/
def GoodFirstConj (M : Turing.TM2ComputableAux Bool Bool) (k : ℕ) (P : FieldPres) (n : ℕ)
    (A : Tensor3 P.F n) : Prop :=
  ∀ B : Tensor3 P.F n,
    2 * 2 ^ timeBound k ⟨P, n, A, B⟩ ≤
      3 * Nat.card {r : Fin (timeBound k ⟨P, n, A, B⟩) → Bool //
        HMBinPacking.OutputsWithin M (encodeInstance ⟨P, n, A, B⟩ ++ List.ofFn r)
          [decide (CodeConj A B)] (timeBound k ⟨P, n, A, B⟩)}

end AvgCaseTI.Supplement


