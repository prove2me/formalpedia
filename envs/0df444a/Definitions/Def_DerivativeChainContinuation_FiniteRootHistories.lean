-- Prove2me | Definitions.Def_DerivativeChainContinuation_FiniteRootHistories
-- name    : DerivativeChainContinuation_FiniteRootHistories
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:30:25.893982+00:00
-- url     : https://prove2.me/theorems/8b200bcf-4349-4ebd-a043-f33de9a8ce4a
-- title:
--   Squared edge energy of a finite root history
-- statement:
--   For $h\in\mathbb N$ and $z:\mathbb N\to\mathbb C$, define
--
--   $$E_h(z)=\sum_{k=0}^{h-1}|z(k+1)-z(k)|^2.$$
--
--   This is the exact energy tracked by the finite mean-preserving root history law.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/FiniteRootHistories.lean#L9-L10

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators

noncomputable def historyEnergy (h : ℕ) (z : ℕ → ℂ) : ℝ :=
  ∑ k ∈ Finset.range h, ‖z (k+1)-z k‖^2



end DerivativeChainContinuation


