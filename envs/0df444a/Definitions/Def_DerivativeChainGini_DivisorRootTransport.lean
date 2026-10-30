-- Prove2me | Definitions.Def_DerivativeChainGini_DivisorRootTransport
-- name    : DerivativeChainGini_DivisorRootTransport
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:32:33.331596+00:00
-- url     : https://prove2.me/theorems/fc68b2bd-30fa-488c-96b2-a29b8727a6bf
-- title:
--   Optimal Euclidean transport of uniform actual root slots
-- statement:
--   For complex polynomials $P,Q$, a uniform root coupling is a real array on their complete root-slot types satisfying nonnegativity, row sums $1/d_P$, and column sums $1/d_Q$, where $d_T=T.\mathrm{natDegree}$. Its cost is $\sum_{i\in R_P,j\in R_Q}q_{ij}|i-j|$. Define $W(P,Q)$ to be the real infimum of all such costs. These are fractional couplings between root occurrences, without an additional barycentric or matching restriction; positive-degree bridge lemmas exhibit a feasible product coupling.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorRootTransport.lean, lines 12-13, SHA-256 a89578b569d7880522341af1db3f795dacf9eb5b54dd27008909bb5cbbe53319. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorRootTransport.lean, lines 14-15, SHA-256 a89578b569d7880522341af1db3f795dacf9eb5b54dd27008909bb5cbbe53319. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorRootTransport.lean, lines 9-11, SHA-256 a89578b569d7880522341af1db3f795dacf9eb5b54dd27008909bb5cbbe53319. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

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
open Polynomial DerivativeChainGiniFamily
namespace DerivativeChainDivisorAnchor
noncomputable section
attribute [local instance] Classical.propDecidable

def UniformRootCoupling (P Q : ℂ[X]) (q : P.roots → Q.roots → ℝ) : Prop :=
  (∀ i j, 0 ≤ q i j) ∧ (∀ i, ∑ j, q i j = 1/(P.natDegree:ℝ)) ∧
    (∀ j, ∑ i, q i j = 1/(Q.natDegree:ℝ))
def uniformRootTransportCost (P Q : ℂ[X]) (q : P.roots → Q.roots → ℝ) : ℝ :=
  ∑ i, ∑ j, q i j*‖(i:ℂ)-(j:ℂ)‖
def uniformRootW1 (P Q : ℂ[X]) : ℝ :=
  sInf {t : ℝ | ∃ q, UniformRootCoupling P Q q ∧ uniformRootTransportCost P Q q=t}





















end
end DerivativeChainDivisorAnchor


