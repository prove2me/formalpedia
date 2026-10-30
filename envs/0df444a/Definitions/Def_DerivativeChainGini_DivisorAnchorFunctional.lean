-- Prove2me | Definitions.Def_DerivativeChainGini_DivisorAnchorFunctional
-- name    : DerivativeChainGini_DivisorAnchorFunctional
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:32:16.379085+00:00
-- url     : https://prove2.me/theorems/5747d67e-0413-480b-8ea8-a113d4f50b35
-- title:
--   Literal root-pair distance sums and divisor anchor
-- statement:
--   For complex polynomials $P,Q$, define $S(P,Q)=\sum_{x\in R_P}\sum_{y\in R_Q}|x-y|$, with every multiset occurrence retained, and define
--
--   $$A(P,Q)=\frac{S(P,P)-S(P,Q)}{P.\mathrm{natDegree}}.$$
--
--   Thus the first numerator term is twice the unordered parent pair-distance sum, with zero diagonal terms included. Also define unnormalized sums over a scaled finite orbit and pairs of such orbits for the exact signed-divisor cancellation identity.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorAnchorFunctional.lean, lines 10-10, SHA-256 0145f6beff4555edcf249ecf73c839cf7f8f5e66597b96b0eff9895df3bf0bd3. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorAnchorFunctional.lean, lines 11-11, SHA-256 0145f6beff4555edcf249ecf73c839cf7f8f5e66597b96b0eff9895df3bf0bd3. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorAnchorFunctional.lean, lines 13-14, SHA-256 0145f6beff4555edcf249ecf73c839cf7f8f5e66597b96b0eff9895df3bf0bd3. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorAnchorFunctional.lean, lines 15-16, SHA-256 0145f6beff4555edcf249ecf73c839cf7f8f5e66597b96b0eff9895df3bf0bd3. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorAnchorFunctional.lean, lines 9-9, SHA-256 0145f6beff4555edcf249ecf73c839cf7f8f5e66597b96b0eff9895df3bf0bd3. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

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

def rootSum (P : ℂ[X]) (f : ℂ → ℝ) : ℝ := (P.roots.map f).sum
def rootPairSum (P Q : ℂ[X]) : ℝ := rootSum P (fun x => rootSum Q (fun y => ‖x-y‖))
def rootAnchor (P Q : ℂ[X]) : ℝ := (rootPairSum P P-rootPairSum P Q)/P.natDegree

def orbitSum {ι : Type} [Fintype ι] (z : ι → ℂ) (R : ℝ) (f : ℂ → ℝ) : ℝ :=
  ∑ i, f ((R:ℂ)*z i)
def pairSum {ι : Type} [Fintype ι] (z : ι → ℂ) (R S : ℝ) : ℝ :=
  ∑ i, ∑ j, ‖(R:ℂ)*z i-(S:ℂ)*z j‖

















end
end DerivativeChainDivisorAnchor


