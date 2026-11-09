-- Prove2me | Definitions.Def_QMAvsQCIP_CTree_RoundsLE
-- name    : QMAvsQCIP_CTree_RoundsLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:46:40.445001+00:00
-- url     : https://prove2.me/theorems/d8780509-27b0-4318-a622-536d5072572e
-- title:
--   At most $n$ rounds
-- statement:
--   A classical interactive query algorithm has **at most $n$ rounds** if every path of its tree has at most $n$ send nodes (each round is one verifier message and one prover reply).
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Definition 5, p.17; Theorem 7, p.31

import Definitions.Def_QMAvsQCIP_CTree

set_option autoImplicit false

namespace QMAvsQCIP

/-- `CTree.RoundsLE n t`: along every path of `t` there are at most `n` message rounds
(`send` nodes; each round is one verifier message and one prover reply).

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Definition 5, p.17 (PDF p.20): "the parties exchange at most c(λ)
classical bits over at most r(λ) rounds"; Theorem 7, p.31 (PDF p.34): "V′ preserves the rounds
and message lengths". -/
inductive CTree.RoundsLE {Z : Type} {ℓ : ℕ} : ℕ → CTree Z ℓ → Prop
  | decide (n : ℕ) (b : Bool) : CTree.RoundsLE n (.decide b)
  | query (n : ℕ) (z : Z) (k : Bool → CTree Z ℓ) :
      (∀ b, CTree.RoundsLE n (k b)) → CTree.RoundsLE n (.query z k)
  | send (n : ℕ) (m : Fin ℓ → Bool) (k : (Fin ℓ → Bool) → CTree Z ℓ) :
      (∀ r, CTree.RoundsLE n (k r)) → CTree.RoundsLE (n + 1) (.send m k)

end QMAvsQCIP


