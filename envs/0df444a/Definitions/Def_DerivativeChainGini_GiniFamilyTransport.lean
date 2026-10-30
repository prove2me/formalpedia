-- Prove2me | Definitions.Def_DerivativeChainGini_GiniFamilyTransport
-- name    : DerivativeChainGini_GiniFamilyTransport
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:30:25.684427+00:00
-- url     : https://prove2.me/theorems/e0e5db0e-78ef-4a71-8a14-c9de2be3b556
-- title:
--   Finite transport between a uniform unit law and its radial mixture
-- statement:
--   For a finite index type $I$ and complex points $z_i$, adjoin a distinguished point $\ast$ with value $0$. Define parent weights $p_\ast=0$, $p_i=1/|I|$ and, for a real parameter $\varepsilon$, child weights $c_\ast=\varepsilon$, $c_i=(1-\varepsilon)/|I|$. Define all nonnegative coupling arrays with exactly these row and column sums, their Euclidean costs, and the real cost infimum. The specified radial array retains $(1-\varepsilon)/|I|$ on each slot's diagonal and sends $\varepsilon/|I|$ from that slot to $\ast$. Normalization and feasibility theorems impose nonemptiness and $0\le\varepsilon\le1$; these are not built into the unrestricted weight definitions.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniFamilyTransport.lean, lines 13-15, SHA-256 49c1d38ab6422dd500efe5ec85804a0a48d5a127cd8167aecd546d3c70a21b2c. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 5, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniFamilyTransport.lean, lines 17-19, SHA-256 49c1d38ab6422dd500efe5ec85804a0a48d5a127cd8167aecd546d3c70a21b2c. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 5, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniFamilyTransport.lean, lines 21-23, SHA-256 49c1d38ab6422dd500efe5ec85804a0a48d5a127cd8167aecd546d3c70a21b2c. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 5, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniFamilyTransport.lean, lines 24-25, SHA-256 49c1d38ab6422dd500efe5ec85804a0a48d5a127cd8167aecd546d3c70a21b2c. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 5, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniFamilyTransport.lean, lines 26-27, SHA-256 49c1d38ab6422dd500efe5ec85804a0a48d5a127cd8167aecd546d3c70a21b2c. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 5, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniFamilyTransport.lean, lines 29-32, SHA-256 49c1d38ab6422dd500efe5ec85804a0a48d5a127cd8167aecd546d3c70a21b2c. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 5, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniFamilyTransport.lean, lines 9-11, SHA-256 49c1d38ab6422dd500efe5ec85804a0a48d5a127cd8167aecd546d3c70a21b2c. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 5, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.

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
namespace DerivativeChainGiniFamily
noncomputable section
variable {ι : Type} [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable

def point (z : ι → ℂ) : Option ι → ℂ
  | none => 0
  | some i => z i

def parentMass : Option ι → ℝ
  | none => 0
  | some _ => 1 / Fintype.card ι

def childMass (ε : ℝ) : Option ι → ℝ
  | none => ε
  | some _ => (1-ε) / Fintype.card ι

def IsCoupling (ε : ℝ) (q : Option ι → Option ι → ℝ) : Prop :=
  (∀ i j, 0 ≤ q i j) ∧ (∀ i, ∑ j, q i j = parentMass i) ∧
    (∀ j, ∑ i, q i j = childMass ε j)
def transportCost (z : ι → ℂ) (q : Option ι → Option ι → ℝ) : ℝ :=
  ∑ i, ∑ j, q i j * ‖point z i - point z j‖
def optimalW1 (z : ι → ℂ) (ε : ℝ) : ℝ :=
  sInf {t : ℝ | ∃ q, IsCoupling ε q ∧ transportCost z q = t}

def radialCoupling (ε : ℝ) : Option ι → Option ι → ℝ
  | none, _ => 0
  | some _, none => ε / Fintype.card ι
  | some i, some j => if i = j then (1-ε) / Fintype.card ι else 0














end
end DerivativeChainGiniFamily


