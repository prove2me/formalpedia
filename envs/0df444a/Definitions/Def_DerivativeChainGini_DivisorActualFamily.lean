-- Prove2me | Definitions.Def_DerivativeChainGini_DivisorActualFamily
-- name    : DerivativeChainGini_DivisorActualFamily
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:31:58.672972+00:00
-- url     : https://prove2.me/theorems/38c644b8-9aad-48d2-a82b-3bc3a3957bea
-- title:
--   Unequal-orbit source and child polynomials
-- statement:
--   Let $F_n=X^{n+2}-1$. For natural $k$ and real radii $a,b$, define $P_{n,k,a}=\operatorname{scaleRoots}(F_n,a)F_n^{k-1}$ and $Q_{n,k,b}=X^{n+1}F_n^{k-2}\operatorname{scaleRoots}(F_n,b)$. The source is the product of an inner orbit and a repeated outer orbit. Subsequent bridge theorems identify its exact derivative when $b^{n+2}=[1+(k-1)a^{n+2}]/k$. Natural subtractions in these definitions are interpreted in $\mathbb N$; the obstruction theorems impose $k\ge3$.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorActualFamily.lean, lines 21-22, SHA-256 9557ef1636f6669f928453ab9b9ca60695735ae8cfbe01b0db9bb987c90869c6. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorActualFamily.lean, lines 23-24, SHA-256 9557ef1636f6669f928453ab9b9ca60695735ae8cfbe01b0db9bb987c90869c6. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

import Mathlib
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



def anchorSource (n k : ℕ) (a : ℝ) : ℂ[X] :=
  (base n).scaleRoots (a:ℂ) * (base n)^(k-1)
def anchorChild (n k : ℕ) (b : ℝ) : ℂ[X] :=
  X^(n+1)*(base n)^(k-2)*(base n).scaleRoots (b:ℂ)















end
end DerivativeChainDivisorAnchor


