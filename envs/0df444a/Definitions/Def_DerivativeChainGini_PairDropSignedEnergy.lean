-- Prove2me | Definitions.Def_DerivativeChainGini_PairDropSignedEnergy
-- name    : DerivativeChainGini_PairDropSignedEnergy
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:33:55.189748+00:00
-- url     : https://prove2.me/theorems/5a305058-5bca-41fe-98c4-727353d66a84
-- title:
--   Signed root divisors and their Euclidean distance energy
-- statement:
--   Define the ordered distance sum of two finite complex multisets. For the unequal-orbit source, define the positive divisor as the scaled inner root multiset plus the outer root multiset, and the negative divisor as the child-radius root multiset plus $n+1$ zero slots. Define
--
--   $$\mathcal E(P,Q)=S(P,Q)-\tfrac12 S(P,P)-\tfrac12 S(Q,Q).$$
--
--   The exact cancellation theorem removes the shared outer roots before bounding the absolute energy.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/PairDropSignedEnergy.lean, lines 60-61, SHA-256 57fd2bc6033ac8b7ccbf84566a3261affa8428115ba9997491d9ec0206473e16. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Section 6, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/PairDropSignedEnergy.lean, lines 62-63, SHA-256 57fd2bc6033ac8b7ccbf84566a3261affa8428115ba9997491d9ec0206473e16. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Section 6, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/PairDropSignedEnergy.lean, lines 64-65, SHA-256 57fd2bc6033ac8b7ccbf84566a3261affa8428115ba9997491d9ec0206473e16. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Section 6, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.; New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/PairDropSignedEnergy.lean, lines 8-9, SHA-256 57fd2bc6033ac8b7ccbf84566a3261affa8428115ba9997491d9ec0206473e16. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Section 6, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorAnchorFunctional
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

def multisetPair (s t : Multiset ℂ) : ℝ :=
  (s.map (fun x => (t.map (fun y => ‖x-y‖)).sum)).sum





















def positiveDivisor (n : ℕ) (a : ℝ) : Multiset ℂ :=
  (base n).roots.map (fun z => (a:ℂ)*z)+(base n).roots
def negativeDivisor (n : ℕ) (b : ℝ) : Multiset ℂ :=
  (base n).roots.map (fun z => (b:ℂ)*z)+(n+1) • ({0}:Multiset ℂ)
def divisorEnergy (P Q : ℂ[X]) : ℝ :=
  rootPairSum P Q-rootPairSum P P/2-rootPairSum Q Q/2

















end
end DerivativeChainDivisorAnchor


