-- Prove2me | Definitions.Def_DerivativeChainGini_GiniPolygon36
-- name    : DerivativeChainGini_GiniPolygon36
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:35:34.481671+00:00
-- url     : https://prove2.me/theorems/d566176f-6baf-4a9e-9d9f-e0e5e5240cd3
-- title:
--   Primitive-root coordinates for the actual regular 36-gon
-- statement:
--   Define $\zeta=\exp(2\pi i/36)$ and $z_j=\zeta^{\operatorname{val}(j)}$ for $j\in\mathbb Z/36\mathbb Z$. The primitive-root and complete multiset bridge theorems identify these cyclic coordinates with every root occurrence of $X^{36}-1$. They support an exact finite chord-sum evaluation, rather than a numerical polygon approximation.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniPolygon36.lean, lines 8-8, SHA-256 bafc088e81a920fe5df206c3a5f6597baa54e954a1de1b0a02a81eacf57e3a99. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 6, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniPolygon36.lean, lines 9-9, SHA-256 bafc088e81a920fe5df206c3a5f6597baa54e954a1de1b0a02a81eacf57e3a99. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 6, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.

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
open Polynomial DerivativeChainGiniFamily DerivativeChainDivisorAnchor
namespace DerivativeChainGiniCircle
noncomputable section

def unityRoot : ℂ := Complex.exp (2*Real.pi*Complex.I/36)
def polygonPoint (i : ZMod 36) : ℂ := unityRoot ^ i.val

































end
end DerivativeChainGiniCircle


