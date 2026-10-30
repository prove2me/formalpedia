-- Prove2me | Definitions.Def_DerivativeChainContinuation_GreedyReal
-- name    : DerivativeChainContinuation_GreedyReal
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T20:14:33.885223+00:00
-- url     : https://prove2.me/theorems/a7b29065-c6c6-4c01-848e-fe667dbfb8c0
-- title:
--   Extreme real-row roots and nearest-parent row histories
-- statement:
--   A real tower has r_k: Fin(k+1) → ℝ. Define rightRow(r,k)=r_k(k) and leftRow(r,k)=r_k(0). For x: ℕ → ℝ, GreedyRowsTo(r,n,x) means that for every 0 ≤ k ≤ n, x_k equals some entry of row r_k; and for every k<n and j∈Fin(k+2), |x_(k+1)-x_k| ≤ |r_(k+1)(j)-x_k|. Only the prefix through row n is constrained. Root values may repeat, and all local nearest-parent ties are allowed. The separate RealRowStep predicate supplies the actual derivative relation.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/GreedyReal.lean, lines 173-173, SHA-256 186feed2d495e8a1a66a0ecd5c2a2fbad651f03f45bd1d7f1a175d09e35fe59e.; Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/GreedyReal.lean, lines 174-174, SHA-256 186feed2d495e8a1a66a0ecd5c2a2fbad651f03f45bd1d7f1a175d09e35fe59e.; Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/GreedyReal.lean, lines 176-178, SHA-256 186feed2d495e8a1a66a0ecd5c2a2fbad651f03f45bd1d7f1a175d09e35fe59e.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators















abbrev rightRow (r : RealRows) (k : ℕ) := r k (Fin.last k)
abbrev leftRow (r : RealRows) (k : ℕ) := r k 0

def GreedyRowsTo (r : RealRows) (n : ℕ) (x : ℕ → ℝ) : Prop :=
  (∀ k≤n, ∃ i : Fin (k+1), x k=r k i) ∧
  ∀ k<n, ∀ i : Fin (k+2), |x (k+1)-x k|≤|r (k+1) i-x k|












end DerivativeChainContinuation


