-- Prove2me | Definitions.Def_QMAvsQCIP_CTree_QueriesLE
-- name    : QMAvsQCIP_CTree_QueriesLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:47:06.234172+00:00
-- url     : https://prove2.me/theorems/5b072a86-f5d5-4986-a7c1-6feda8b09ca7
-- title:
--   At most $n$ queries
-- statement:
--   A classical interactive query algorithm makes **at most $n$ queries** if every path of its tree has at most $n$ query nodes; equivalently, on every oracle and against every prover it makes at most $n$ classical queries.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Definition 4, p.16; Theorem 7, p.31

import Definitions.Def_QMAvsQCIP_CTree

set_option autoImplicit false

namespace QMAvsQCIP

/-- `CTree.QueriesLE n t`: along every path of `t` there are at most `n` oracle queries
(`query` nodes), i.e. on every oracle and against every prover the algorithm makes at most `n`
classical queries.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Definition 4, p.16 (PDF p.19): "making at most T(λ) queries on every
input oracle"; Theorem 7, p.31 (PDF p.34): "makes at most M = poly(r, N, t, ℓ, 1/ϵ) classical
queries". -/
inductive CTree.QueriesLE {Z : Type} {ℓ : ℕ} : ℕ → CTree Z ℓ → Prop
  | decide (n : ℕ) (b : Bool) : CTree.QueriesLE n (.decide b)
  | query (n : ℕ) (z : Z) (k : Bool → CTree Z ℓ) :
      (∀ b, CTree.QueriesLE n (k b)) → CTree.QueriesLE (n + 1) (.query z k)
  | send (n : ℕ) (m : Fin ℓ → Bool) (k : (Fin ℓ → Bool) → CTree Z ℓ) :
      (∀ r, CTree.QueriesLE n (k r)) → CTree.QueriesLE n (.send m k)

end QMAvsQCIP


