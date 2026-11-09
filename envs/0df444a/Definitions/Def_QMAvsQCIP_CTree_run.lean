-- Prove2me | Definitions.Def_QMAvsQCIP_CTree_run
-- name    : QMAvsQCIP_CTree_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:46:42.028623+00:00
-- url     : https://prove2.me/theorems/f89a2111-d6b2-42e7-84b1-9c39083b450a
-- title:
--   Decision of a classical interactive query algorithm
-- statement:
--   The decision of a classical interactive query algorithm run with oracle $O$ against a deterministic prover $P$: a query at $z$ is answered by $O(z)$, and a message $m$, sent after the messages $h$, is answered by $P(h\|m)$.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Section 3.1, p.14

import Definitions.Def_QMAvsQCIP_CTree
import Definitions.Def_QMAvsQCIP_BBProver

set_option autoImplicit false

namespace QMAvsQCIP

/-- The **decision** of a classical interactive query algorithm `t` run with oracle `O` against
the deterministic prover `P`, after the verifier messages `h` so far: an oracle query is answered
by `O`, a message `m` is answered by `P (h ++ [m])`.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Section 3.1, p.14 (PDF p.17): "We write ⟨P*, V⟩(x) for the verifier's
decision on common input x, with ACCEPT and REJECT encoded by one and zero." -/
def CTree.run {Z : Type} {ℓ : ℕ} (O : Z → Bool) (P : BBProver ℓ) :
    List (Fin ℓ → Bool) → CTree Z ℓ → Bool
  | _, .decide b => b
  | h, .query z k => CTree.run O P h (k (O z))
  | h, .send m k => CTree.run O P (h ++ [m]) (k (P (h ++ [m])))

end QMAvsQCIP


