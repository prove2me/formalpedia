-- Prove2me | Definitions.Def_DerivativeChainGini_PairDropPolynomialPower
-- name    : DerivativeChainGini_PairDropPolynomialPower
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:34:26.449228+00:00
-- url     : https://prove2.me/theorems/a3e14193-fe5c-453c-98f1-07246d308a9f
-- title:
--   Actual polynomial powers and their pair-distance drop
-- statement:
--   For complex polynomials $P,Q$ and $r\in\mathbb N$, define the powered source $P^r$ and the proposed child $P^{r-1}Q$. Define the literal unordered pair-distance drop
--
--   $$D(P,Q)=\tfrac12 S(P,P)-\tfrac12 S(Q,Q).$$
--
--   The power identities are subsequently proved under monicity, degree, and derivative hypotheses; the definitions alone do not assume those hypotheses.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/PairDropPolynomialPower.lean, lines 10-10, SHA-256 019e5330fe3efd56675481c9b0abfb31b88cdff5feccdc7f4c4353b1f40e54b4. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Section 6, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/PairDropPolynomialPower.lean, lines 8-8, SHA-256 019e5330fe3efd56675481c9b0abfb31b88cdff5feccdc7f4c4353b1f40e54b4. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Section 6, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/PairDropPolynomialPower.lean, lines 9-9, SHA-256 019e5330fe3efd56675481c9b0abfb31b88cdff5feccdc7f4c4353b1f40e54b4. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Section 6, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorAnchorFunctional
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainDivisorAnchor
end DerivativeChainDivisorAnchor
namespace DerivativeChainGini
end DerivativeChainGini
namespace DerivativeChainGiniCircle
end DerivativeChainGiniCircle
namespace DerivativeChainGiniFamily
end DerivativeChainGiniFamily
namespace DerivativeChainPrivate
end DerivativeChainPrivate

set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
namespace DerivativeChainDivisorAnchor
noncomputable section

def powerSource (P : ℂ[X]) (r : ℕ) : ℂ[X] := P^r
def powerChild (P Q : ℂ[X]) (r : ℕ) : ℂ[X] := P^(r-1)*Q
def pairDrop (P Q : ℂ[X]) : ℝ := rootPairSum P P/2-rootPairSum Q Q/2



























end
end DerivativeChainDivisorAnchor


