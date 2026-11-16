-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_OProtocol
-- name    : DoublyEffIP_Supplement_OProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:32:39.699664+00:00
-- url     : https://prove2.me/theorems/1af61ba2-3390-4520-99cd-d64ef3cae8f9
-- title:
--   Public-coin protocol whose verifier outputs a word
-- statement:
--   A **protocol** here consists of three deterministic machines and two functions of the public parameters $\mathrm{pp}$:
--
--   1. a parameter machine, which computes from $\mathrm{pp}$ the number of rounds $\ell$ and the message length $a$ (and, for an LDP-IP, the field);
--   2. a prover next-message machine, computing $a_j=P(x,j,(q_1,\dots,q_j))$;
--   3. a verifier machine, run on the public coins $q_1,\dots,q_\ell\in\{0,1\}^a$, the answers and $\mathrm{pp}$, which either rejects ($\bot$) or accepts with an output word on its output tape;
--
--   together with the functions $\mathrm{pp}\mapsto\ell$ and $\mathrm{pp}\mapsto a$ that the parameter machine must output.
--
--   This is the shape of the protocols of Definitions 8 and 9, whose verifier outputs a description instead of only accepting or rejecting.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.4, pp.10–11; Definition 8, p.11; Definition 9, p.12

import Mathlib
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

namespace DoublyEffIP.Supplement

/-- **A public-coin protocol whose verifier outputs a word** — the protocols of Section 3.4
(pp.10–11), Definition 8 (LDP-IP, p.11) and Definition 9 (IPP with row reduction, p.12) of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…),
where "the verifier either rejects (outputs ⊥) or outputs the description of a low-depth
predicate".

The data of a protocol over the alphabet `{0,1}`:
* `paramM` (output tape `paramOut`) computes the round count `ℓ`, the message length `a` (and, for
  an LDP-IP, the field) from the public parameters `pp`; `rounds` and `msgLen` name the numbers it
  must output;
* `proverM` (output tape `proverOut`) is the prover's next-message machine
  `a_j := P(x, j, (q_1, …, q_j))`;
* `verifierM` (output tape `verifierOut`) is the verifier, run on `pp`, the public coins and the
  answers; it halts rejecting (`⊥`) or accepting with its output word on `verifierOut`.

**Formalization Note.** Same shape as the published `DoublyEffIP.Protocol`, except that the
public parameters are an arbitrary word (each theorem fixes its own `pp`) and the verifier has an
output tape. Public coin: the verifier's coins are its queries. -/
structure OProtocol where
  /-- the machine computing the protocol's parameters from `pp` -/
  paramM : PrimitiveMachine
  /-- its output tape -/
  paramOut : Fin paramM.tapeCount
  /-- the prover's next-message machine -/
  proverM : PrimitiveMachine
  /-- its output tape -/
  proverOut : Fin proverM.tapeCount
  /-- the verifier -/
  verifierM : PrimitiveMachine
  /-- its output tape -/
  verifierOut : Fin verifierM.tapeCount
  /-- the round count `ℓ` as a function of `pp` -/
  rounds : List Bool → ℕ
  /-- the message length `a` as a function of `pp` -/
  msgLen : List Bool → ℕ

end DoublyEffIP.Supplement


