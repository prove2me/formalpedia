-- Prove2me | Definitions.Def_AvgCaseTI_Supplement_Halts4
-- name    : AvgCaseTI_Supplement_Halts4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:29:07.849206+00:00
-- url     : https://prove2.me/theorems/c15ae388-6088-40bb-a2ea-f4f3ab107f6f
-- title:
--   Running time $(L+q+2)^k$ on every coin string for 4-tensor instances
-- statement:
--   For a 4-tensor instance $x$ of input length $L$ over a field of order $q$, the **budget** is $(L+q+2)^k$. A machine $M$ **runs within the budget** on $x$ if for **every** coin string $r\in\{0,1\}^{(L+q+2)^k}$, $M$ started on the code of $x$ followed by $r$ halts with some output within $(L+q+2)^k$ steps.
--
--   Since $n\le L=O(n^4\log q+\log n)$, the bounds $(L+q+2)^k$ are exactly the bounds polynomial in $n$ and $q$: this is the running time "$\mathrm{poly}(n,q)$" of Theorem 1.3, held on every input and every run.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.3, p.6 (PDF p.8); §4.1, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_AvgCaseTI_Supplement_encodeInstance4

set_option autoImplicit false

namespace AvgCaseTI.Supplement

open AvgCaseTI

/-- The `poly(n, q)` budget `(L + q + 2)^k` of a 4-tensor instance, `L` its input length and `q` the
order of its field: it bounds both the number of steps and the number of random bits. -/
noncomputable def timeBound4 (k : ℕ) (x : Instance4) : ℕ := (inputLength4 x + x.P.q + 2) ^ k

/-- **A randomized machine runs in time `(L + q + 2)^k` on a 4-tensor instance.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.3, p.6 (PDF p.8): "There is a randomized poly(n, q)-time algorithm", and §4.1,
p.27 (PDF p.29): "while retaining the poly(n, q) running-time bound on every input and every run".

`Halts4 M k x`: for **every** coin string `r ∈ {0,1}^{(L+q+2)^k}`, `M` started on the code of `x`
followed by `r` halts with some output within `(L + q + 2)^k` steps.

**Formalization Note.** Since `n ≤ L = O(n⁴ log q + log n)`, the class of bounds `(L + q + 2)^k` is
exactly `poly(n, q)`; the extra `q` is needed because the algorithm enumerates `q^{O(1)}` candidates.
Machine model as in the published `Halts` (Mathlib TM2 via `HMBinPacking.OutputsWithin`). -/
def Halts4 (M : Turing.TM2ComputableAux Bool Bool) (k : ℕ) (x : Instance4) : Prop :=
  ∀ r : Fin (timeBound4 k x) → Bool, ∃ out : List Bool,
    HMBinPacking.OutputsWithin M (encodeInstance4 x ++ List.ofFn r) out (timeBound4 k x)

end AvgCaseTI.Supplement


