-- Prove2me | Definitions.Def_DoublyEffIP_Protocol
-- name    : DoublyEffIP_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:59.205018+00:00
-- url     : https://prove2.me/theorems/5cb7fbd7-054b-4dd3-afa7-70e012141f29
-- title:
--   A public-coin protocol $(P(x),V(y))[\mathrm{pp}]$
-- statement:
--   A **public-coin protocol** over the alphabet $\{0,1\}$ consists of three machines and two functions:
--
--   1. a **parameter machine** that computes, from the public parameters $\mathrm{pp}$, the number of rounds $\ell$ and the per-round message length $a$;
--   2. a deterministic **prover** machine $P$ computing the next-message function $a_j=P(x,j,(q_1,\dots,q_j))$;
--   3. a **verifier** machine $V$ that, given $\mathrm{pp}$, the input, its random queries $q_1,\dots,q_\ell\in\{0,1\}^a$ and the answers $a_1,\dots,a_\ell\in\{0,1\}^a$, accepts or rejects;
--   4. the functions $\ell(n,T,S,\sigma)$ and $a(n,T,S,\sigma)$, which must equal the parameter machine's output (see the definition of a sound IP).
--
--   In each round the verifier sends a uniformly random query and the prover answers. Since the coins are public and the verifier "never rejects in the middle of an execution", its whole behaviour is a decision on the full transcript.
--
--   **Formalization Note** The verifier's randomness is exactly its queries, given as an input to a deterministic machine. The functions $\ell$ and $a$ cannot carry advice because they are pinned to the output of a machine that sees only $\mathrm{pp}$.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.4, pp.10–11

import Mathlib
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

namespace DoublyEffIP

/-- **A public-coin protocol `(P(x), V(y))[pp]`** — Chen–Hong–Kalai–Xi, *Towards a Doubly
Efficient IP = PSPACE*, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.4,
pp.10–11: "a pair of interacting Turing machines (P(x), V(y))[pp] … both parties have explicit
access to the input parameters pp."

The data of a protocol over the alphabet `{0,1}`:
* `paramM` (output tape `paramOut`) computes the round count `ℓ` and the message length `a` from
  the public parameters; `rounds` and `msgLen` name the numbers it must output (see `IsSoundIP`);
* `proverM` (output tape `proverOut`) is the prover's next-message machine
  `a_j := P(x, j, (q_1, …, q_j))`;
* `verifierM` is the verifier's decision machine, run on the input, the public coins and the
  answers.

**Formalization Note.** Public coin: the verifier's random coins are exactly its queries
`q_1, …, q_ℓ`, uniform in `{0,1}^a`, so its randomness is an input to a deterministic machine.
"V never rejects in the middle of an execution" (p.11), so its decision is taken once on the whole
transcript. `rounds` and `msgLen` are functions of `(n, T, S, σ)` that `IsSoundIP` ties to the
output of `paramM`, so they carry no advice. -/
structure Protocol where
  /-- the machine computing `ℓ` and `a` from the public parameters -/
  paramM : PrimitiveMachine
  /-- its output tape -/
  paramOut : Fin paramM.tapeCount
  /-- the prover's next-message machine -/
  proverM : PrimitiveMachine
  /-- its output tape -/
  proverOut : Fin proverM.tapeCount
  /-- the verifier's decision machine -/
  verifierM : PrimitiveMachine
  /-- the round count `ℓ` as a function of `(n, T, S, σ)` -/
  rounds : ℕ → ℕ → ℕ → ℕ → ℕ
  /-- the per-round message length `a` as a function of `(n, T, S, σ)` -/
  msgLen : ℕ → ℕ → ℕ → ℕ → ℕ

end DoublyEffIP


