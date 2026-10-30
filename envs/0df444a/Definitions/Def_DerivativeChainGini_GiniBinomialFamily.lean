-- Prove2me | Definitions.Def_DerivativeChainGini_GiniBinomialFamily
-- name    : DerivativeChainGini_GiniBinomialFamily
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:30:40.448586+00:00
-- url     : https://prove2.me/theorems/79604b8e-8c88-4012-bf7c-614b5ebf62ba
-- title:
--   Actual binomial-power sources and their root-slot types
-- statement:
--   For $n\in\mathbb N$, put $F_n=X^{n+2}-1$, $P_n=F_n^{16}$, and $Q_n=X^{n+1}F_n^{15}$. Define $I_n$ to be the finite type of occurrences in the multiset $F_n.\mathrm{roots}$, retaining every multiplicity. The bundle also proves the degree and cardinality facts used by its nonempty-instance construction, so importing the type does not depend on an unproved theorem stub.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniBinomialFamily.lean, lines 10-10, SHA-256 58bbc846e5b7caced11fed674deea51385f12056bd14cbb09da78960de026c18. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 5, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniBinomialFamily.lean, lines 11-11, SHA-256 58bbc846e5b7caced11fed674deea51385f12056bd14cbb09da78960de026c18. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 5, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniBinomialFamily.lean, lines 16-18, SHA-256 58bbc846e5b7caced11fed674deea51385f12056bd14cbb09da78960de026c18. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 5, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniBinomialFamily.lean, lines 20-21, SHA-256 58bbc846e5b7caced11fed674deea51385f12056bd14cbb09da78960de026c18. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 5, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniBinomialFamily.lean, lines 23-24, SHA-256 58bbc846e5b7caced11fed674deea51385f12056bd14cbb09da78960de026c18. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 5, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniBinomialFamily.lean, lines 8-8, SHA-256 58bbc846e5b7caced11fed674deea51385f12056bd14cbb09da78960de026c18. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 5, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniBinomialFamily.lean, lines 9-9, SHA-256 58bbc846e5b7caced11fed674deea51385f12056bd14cbb09da78960de026c18. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 5, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.

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
open Polynomial
namespace DerivativeChainGiniFamily
noncomputable section

def base (n : ℕ) : ℂ[X] := X^(n+2)-1
def source (n : ℕ) : ℂ[X] := base n ^ 16
def normalizedChild (n : ℕ) : ℂ[X] := X^(n+1)*base n^15
abbrev Slots (n : ℕ) := (base n).roots



theorem base_degree (n : ℕ) : (base n).natDegree = n+2 := by
  change (X^(n+2)-C (1 : ℂ)).natDegree = n+2
  exact natDegree_X_pow_sub_C

theorem slots_card (n : ℕ) : Fintype.card (Slots n) = n+2 := by
  rw [Multiset.card_coe, ← (IsAlgClosed.splits (base n)).natDegree_eq_card_roots, base_degree]

instance slots_nonempty (n : ℕ) : Nonempty (Slots n) :=
  Fintype.card_pos_iff.mp (by rw [slots_card]; omega)























end
end DerivativeChainGiniFamily


