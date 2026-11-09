-- Prove2me | Definitions.Def_QMAvsQCIP_CTree
-- name    : QMAvsQCIP_CTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:44:39.443385+00:00
-- url     : https://prove2.me/theorems/61181795-a669-4a00-be9c-d42a96a6ca30
-- title:
--   Classical interactive query algorithm
-- statement:
--   A **classical interactive query algorithm** with oracle domain $Z$ and $\ell$-bit messages is a tree with three kinds of nodes: a query node asks the oracle at some $z\in Z$ and branches on the answer; a send node sends a message $m\in\{0,1\}^\ell$ to the prover and branches on the reply; a decide node stops with ACCEPT or REJECT.
--
--   These trees describe classical verifiers in the query complexity model, with unrestricted local computation: everything that happens may depend on all earlier answers and replies.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Definitions 3 and 5, pp.16–17

import Mathlib

set_option autoImplicit false

namespace QMAvsQCIP

/-- A **classical interactive query algorithm** (deterministic, given its random coins) with
oracle domain `Z` and `ℓ`-bit messages, as a tree: `query z k` asks the oracle at `z` and
continues with `k (O z)`; `send m k` sends the message `m` to the prover and continues with
`k b` on the prover's reply `b`; `decide b` stops with decision `b` (`true` = ACCEPT). Every
oracle answer and prover reply may influence everything that follows.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Definition 3, p.16 (PDF p.19): "A query algorithm is a family (A_λ)_{λ≥1}
of finite classical or quantum oracle circuits … local computation and workspace may be
arbitrarily large but finite"; Section 3.3, p.16: "Requiring the verifier in Definition 2 to be
classical and probabilistic polynomial-time, with classical oracle queries, gives IP^O";
Definition 5, p.17: "Restricting the verifier to classical queries and classical computation
with polynomially many random bits gives IP^bb."

**Formalization Note.** Local computation is unrestricted: the tree is arbitrary. Bounds on
rounds and queries along every path: `CTree.RoundsLE`, `CTree.QueriesLE`. -/
inductive CTree (Z : Type) (ℓ : ℕ) where
  | query (z : Z) (next : Bool → CTree Z ℓ)
  | send (m : Fin ℓ → Bool) (next : (Fin ℓ → Bool) → CTree Z ℓ)
  | decide (b : Bool)

end QMAvsQCIP


