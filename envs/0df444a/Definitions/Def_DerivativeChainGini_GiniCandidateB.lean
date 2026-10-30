-- Prove2me | Definitions.Def_DerivativeChainGini_GiniCandidateB
-- name    : DerivativeChainGini_GiniCandidateB
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:31:10.80581+00:00
-- url     : https://prove2.me/theorems/69cd14dd-ec0e-4f47-8b12-6bdde368674c
-- title:
--   Empirical root expectations, variance, and Gini dispersion
-- statement:
--   For a complex polynomial $P$ of degree $d_P=P.\mathrm{natDegree}$, define the normalized finite root expectation $E_P(f)=d_P^{-1}\sum_{x\in R_P}f(x)$, where $R_P$ retains root multiplicity. Define the centered variance using the multiset centroid and define $G(P)=E_P(x\mapsto E_P(y\mapsto|x-y|))$. For the binomial-power family, define $\varepsilon_n=(n+1)/(16(n+2)-1)$, the root-slot coordinate map, and the parent, child, and uniform-unit Gini statistics used to compare the finite laws with these actual empirical quantities.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniCandidateB.lean, lines 10-10, SHA-256 92a353f1b6fb5dfa9cec8d6d22771e399a14cf2bd3ded30821e3fb3265bd35de. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 5, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniCandidateB.lean, lines 12-13, SHA-256 92a353f1b6fb5dfa9cec8d6d22771e399a14cf2bd3ded30821e3fb3265bd35de. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 5, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniCandidateB.lean, lines 134-135, SHA-256 92a353f1b6fb5dfa9cec8d6d22771e399a14cf2bd3ded30821e3fb3265bd35de. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 5, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniCandidateB.lean, lines 15-16, SHA-256 92a353f1b6fb5dfa9cec8d6d22771e399a14cf2bd3ded30821e3fb3265bd35de. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 5, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniCandidateB.lean, lines 152-153, SHA-256 92a353f1b6fb5dfa9cec8d6d22771e399a14cf2bd3ded30821e3fb3265bd35de. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 5, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniCandidateB.lean, lines 17-17, SHA-256 92a353f1b6fb5dfa9cec8d6d22771e399a14cf2bd3ded30821e3fb3265bd35de. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 5, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniCandidateB.lean, lines 18-18, SHA-256 92a353f1b6fb5dfa9cec8d6d22771e399a14cf2bd3ded30821e3fb3265bd35de. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 5, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniCandidateB.lean, lines 9-9, SHA-256 92a353f1b6fb5dfa9cec8d6d22771e399a14cf2bd3ded30821e3fb3265bd35de. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 5, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteNormMean
import Definitions.Def_DerivativeChainGini_GiniBinomialFamily
import Definitions.Def_DerivativeChainGini_GiniFamilyTransport
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
open Polynomial DerivativeChainContinuation
namespace DerivativeChainGiniFamily
noncomputable section

def epsilon (n : ℕ) : ℝ := (n+1 : ℝ)/(16*(n+2)-1)
def rootSlot (n : ℕ) (i : Slots n) : ℂ := i

def empiricalExpectation (P : ℂ[X]) (f : ℂ → ℝ) : ℝ :=
  (P.roots.map f).sum / P.natDegree

def uniformGini (n : ℕ) : ℝ :=
  finiteGini (fun _ : Slots n => 1/(n+2 : ℝ)) (rootSlot n)
def parentGini (n : ℕ) : ℝ := finiteGini parentMass (point (rootSlot n))
def childGini (n : ℕ) : ℝ := finiteGini (childMass (epsilon n)) (point (rootSlot n))



























def empiricalVariance (P : ℂ[X]) : ℝ :=
  empiricalExpectation P (fun z => ‖z-P.roots.sum/(P.natDegree : ℂ)‖^2)







def empiricalGini (P : ℂ[X]) : ℝ :=
  empiricalExpectation P (fun x => empiricalExpectation P (fun y => ‖x-y‖))











end
end DerivativeChainGiniFamily


