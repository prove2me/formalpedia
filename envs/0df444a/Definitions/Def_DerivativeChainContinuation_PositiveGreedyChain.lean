-- Prove2me | Definitions.Def_DerivativeChainContinuation_PositiveGreedyChain
-- name    : DerivativeChainContinuation_PositiveGreedyChain
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T20:14:03.744077+00:00
-- url     : https://prove2.me/theorems/8964dbb0-681c-40b0-8e24-b3f2f6e35fc5
-- title:
--   A complex location history extended by zero
-- statement:
--   For z∈ℂ^(n+1) and j∈ℕ, define complexHistoryOf(z,j)=z_j if j<n+1, and zero otherwise. Every actual-row use in the theorems is separately bounded to the original finite history.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/positive/PositiveGreedyChain.lean, lines 10-11, SHA-256 58c5c71ff2fb47b0e8104dc20db7e478834107a3be76a063f1be761fb21e1c74.

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

def complexHistoryOf {n : ℕ} (z : Fin (n+1) → ℂ) (j : ℕ) : ℂ :=
  if h : j<n+1 then z ⟨j,h⟩ else 0















end DerivativeChainContinuation


