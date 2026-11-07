-- Prove2me | Definitions.Def_AvgCaseTI_Halts
-- name    : AvgCaseTI_Halts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:16.544075+00:00
-- url     : https://prove2.me/theorems/5a38d2a3-29d0-4bdc-ba45-badb3da40f72
-- title:
--   A randomized machine runs in time $(L+2)^k$
-- statement:
--   Fix a multi-stack Turing machine $M$ with Boolean input and output alphabets and a degree $k$. For an instance $x$ of input length $L$, put $T=(L+2)^k$. $M$ **runs in time $(L+2)^k$ on $x$** when for **every** coin string $r\in\{0,1\}^{T}$, the machine started on the code of $x$ followed by $r$ halts with some output within $T$ steps.
--
--   So the random bits are an extra input, and the time bound holds for every outcome of the coins (worst-case running time of a Monte Carlo algorithm). This is the notion of "randomized $\mathrm{poly}(n,\log q)$-time algorithm" in Theorem 1.1.
--
--   **Formalization Note** The machine is Mathlib's `Turing.TM2ComputableAux Bool Bool`, run through the published `HMBinPacking.OutputsWithin` (halts with the given output within the given number of steps). `timeBound k x` is $(L+2)^k$; it bounds both the steps and the number of random bits. A Turing machine and a bit-operation algorithm simulate each other with polynomial overhead.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.1, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_AvgCaseTI_encodeInstance

set_option autoImplicit false

namespace AvgCaseTI

/-- The polynomial budget `(L + 2)^k` of an instance, `L` its input length: it bounds both the
number of steps and the number of random bits. -/
noncomputable def timeBound (k : ℕ) (x : AlgIsoInstance) : ℕ := (inputLength x + 2) ^ k

/-- **A randomized machine runs in time `(L + 2)^k` on an instance.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.1, p.5
(PDF p.7): "There is a randomized poly(n, log q)-time algorithm".

`Halts M k x` says: for **every** coin string `r ∈ {0,1}^{(L+2)^k}`, the machine `M` started on the
code of `x` followed by `r` halts with some output within `(L + 2)^k` steps.

**Formalization Note.** `M` is a Mathlib multi-stack Turing machine with Boolean alphabets, run
through the published `HMBinPacking.OutputsWithin` (halts with the given output within the given
number of steps). Randomness is a coin string appended to the input; the time bound is worst case
over coin strings (Monte Carlo). A Turing machine and a bit-operation algorithm simulate each other
with polynomial overhead, so the class `poly(L)` does not depend on the model. -/
def Halts (M : Turing.TM2ComputableAux Bool Bool) (k : ℕ) (x : AlgIsoInstance) : Prop :=
  ∀ r : Fin (timeBound k x) → Bool, ∃ out : List Bool,
    HMBinPacking.OutputsWithin M (encodeInstance x ++ List.ofFn r) out (timeBound k x)

end AvgCaseTI


