-- Prove2me | Definitions.Def_QMAvsQCIP_cAccept
-- name    : QMAvsQCIP_cAccept
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:49:34.294046+00:00
-- url     : https://prove2.me/theorems/4666314d-9ad3-4388-92c5-88d6f149ad51
-- title:
--   Acceptance probability of a classical query verifier
-- statement:
--   The acceptance probability of a randomized classical query verifier with oracle $O$ against a deterministic prover $P$: the fraction of coin strings $c\in\{0,1\}^k$ on which the algorithm selected by $c$ accepts.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Section 3.1, p.14

import Definitions.Def_QMAvsQCIP_CVerifier
import Definitions.Def_QMAvsQCIP_CTree_run

set_option autoImplicit false

namespace QMAvsQCIP

/-- The **acceptance probability** of the randomized classical query verifier `V` with oracle
`O` against the deterministic prover `P`: the fraction of coin strings `c ∈ {0,1}^k` on which
`V.tree c` accepts.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Section 3.1, p.14 (PDF p.17): "acceptance probabilities are over the
parties' randomness and measurements, with the input and oracle fixed." -/
noncomputable def cAccept {Z : Type} {ℓ : ℕ} (V : CVerifier Z ℓ) (O : Z → Bool)
    (P : BBProver ℓ) : ℝ :=
  (∑ c : Fin V.k → Bool, if CTree.run O P [] (V.tree c) then (1 : ℝ) else 0) / (2 : ℝ) ^ V.k

end QMAvsQCIP


