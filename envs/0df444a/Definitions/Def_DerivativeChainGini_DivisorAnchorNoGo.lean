-- Prove2me | Definitions.Def_DerivativeChainGini_DivisorAnchorNoGo
-- name    : DerivativeChainGini_DivisorAnchorNoGo
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:33:25.932866+00:00
-- url     : https://prove2.me/theorems/8ae7dd31-9497-464c-bdcd-2442a9579a5d
-- title:
--   Explicit unequal-orbit obstruction family and anchor cost
-- statement:
--   Using $q_k=4k^4$, $a_k=1/k^2$, and the previously defined child radius $b_k$, define the actual source and child by the unequal-orbit construction at index $q_k-2$. For $k\ge3$ these simplify to $B_k=(X^{q_k}-a_k^{q_k})(X^{q_k}-1)^{k-1}$ and $Q_k=X^{q_k-1}(X^{q_k}-1)^{k-2}(X^{q_k}-b_k^{q_k})$. Define $A_k=A(B_k,Q_k)$ and $C_k=(d_{B_k}-1)W(B_k,Q_k)$.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorAnchorNoGo.lean, lines 10-10, SHA-256 92c050c87bcf8bfe92676d362fb4304d232323d6882ed3da175723476b2518ba. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorAnchorNoGo.lean, lines 11-11, SHA-256 92c050c87bcf8bfe92676d362fb4304d232323d6882ed3da175723476b2518ba. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorAnchorNoGo.lean, lines 12-12, SHA-256 92c050c87bcf8bfe92676d362fb4304d232323d6882ed3da175723476b2518ba. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorAnchorNoGo.lean, lines 13-14, SHA-256 92c050c87bcf8bfe92676d362fb4304d232323d6882ed3da175723476b2518ba. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorActualFamily
import Definitions.Def_DerivativeChainGini_DivisorAnchorFunctional
import Definitions.Def_DerivativeChainGini_DivisorParameters
import Definitions.Def_DerivativeChainGini_DivisorRootTransport
import Definitions.Def_DerivativeChainGini_GiniBinomialFamily
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

def obstructionSource (k : ℕ) : ℂ[X] := anchorSource (orbitCount k-2) k (innerRadius k)
def obstructionChild (k : ℕ) : ℂ[X] := anchorChild (orbitCount k-2) k (childRadius k)
def obstructionAnchor (k : ℕ) : ℝ := rootAnchor (obstructionSource k) (obstructionChild k)
def obstructionCost (k : ℕ) : ℝ := (((obstructionSource k).natDegree:ℝ)-1)*
  uniformRootW1 (obstructionSource k) (obstructionChild k)






























end
end DerivativeChainDivisorAnchor


