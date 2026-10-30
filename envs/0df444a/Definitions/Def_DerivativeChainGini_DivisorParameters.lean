-- Prove2me | Definitions.Def_DerivativeChainGini_DivisorParameters
-- name    : DerivativeChainGini_DivisorParameters
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:32:50.643409+00:00
-- url     : https://prove2.me/theorems/26cb77e2-0c72-41dc-943c-95e340ae8a90
-- title:
--   Exact radii and orbit count for the transport obstruction
-- statement:
--   For natural $k$, define $q_k=4k^4$, $a_k=1/k^2$, $c_k=[1+(k-1)a_k^{q_k}]/k$, and $b_k=\operatorname{Real.rpow}(c_k,1/q_k)$. The obstruction results use $k\ge3$ and prove $0<a_k,b_k<1$, the exact power relation for $b_k$, and the elementary geometric-sum bound $q_k(1-b_k)\le k-1$.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorParameters.lean, lines 11-11, SHA-256 05f005ed42370b97ccf5a0f3c4842762723eb6fcae45b7da40c2513dfd710389. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorParameters.lean, lines 7-7, SHA-256 05f005ed42370b97ccf5a0f3c4842762723eb6fcae45b7da40c2513dfd710389. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorParameters.lean, lines 8-8, SHA-256 05f005ed42370b97ccf5a0f3c4842762723eb6fcae45b7da40c2513dfd710389. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorParameters.lean, lines 9-10, SHA-256 05f005ed42370b97ccf5a0f3c4842762723eb6fcae45b7da40c2513dfd710389. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

import Mathlib
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
namespace DerivativeChainDivisorAnchor
noncomputable section

def orbitCount (k : ℕ) : ℕ := 4*k^4
def innerRadius (k : ℕ) : ℝ := 1/(k:ℝ)^2
def childRadiusPower (k : ℕ) : ℝ :=
  (1+((k:ℝ)-1)*innerRadius k ^ orbitCount k)/(k:ℝ)
def childRadius (k : ℕ) : ℝ := childRadiusPower k ^ ((orbitCount k : ℝ)⁻¹)



















end
end DerivativeChainDivisorAnchor


