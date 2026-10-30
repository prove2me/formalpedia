-- Prove2me | Definitions.Def_DerivativeChainContinuation_GreedyTower
-- name    : DerivativeChainContinuation_GreedyTower
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T20:13:20.336695+00:00
-- url     : https://prove2.me/theorems/718c6018-e995-4cf1-85b4-012280bf500f
-- title:
--   Length of a finite real location history
-- statement:
--   For x: ℕ → ℝ and n∈ℕ, define greedyCost(x,n)=Σ_(k=0)^(n-1) |x_(k+1)-x_k|. For n=0 the empty sum is zero. No root or nearest-parent condition is included in this length definition.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/GreedyTower.lean, lines 8-9, SHA-256 8b40116c462af4a8a43ad41639ccc897e8a071b5f6821b4a44f21f48d5c9b196.

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators

noncomputable def greedyCost (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, |x (k+1)-x k|






























end DerivativeChainContinuation


