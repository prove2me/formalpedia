-- Prove2me | Definitions.Def_MasulloRepair_geometricCellTrace
-- name    : MasulloRepair_geometricCellTrace
-- status  : Definition
-- author  : @ibecca
-- created : 2026-11-21T20:39:20.162477+00:00
-- url     : https://prove2.me/theorems/5c7ac08c-3eb6-4231-9c11-0d481c4cdeb1
-- title:
--   Finite geometric cell trace profile
-- statement:
--   For a complex ratio r, a sequence of cell samples c₁,c₂,…, and a nonnegative cell index j, define the finite geometric cell profile\n$$D_j=(1-r^2)\sum_{k=1}^{j}(r^2)^{j-k}c_k,$$\nwith D₀=0. The definition records the finite causal accumulation of earlier samples under repeated multiplication by r². It contains no convergence or operator-theoretic assertion; those are proved separately.
-- source:
--   Yi, 'The full local log-prime circle convolution is recoverable from actual global two-variable cell blocks', mission discussion comment 2f2f1d62-3a43-44d0-a05b-3ddd9702b1d0, displayed diagonal-block recurrence, 21 November 2026.

import Mathlib

open scoped BigOperators

namespace MasulloRepair

def geometricCellTrace (r : ℂ) (c : ℕ → ℂ) (j : ℕ) : ℂ :=
  (1 - r ^ 2) * ∑ k ∈ Finset.range j, (r ^ 2) ^ (j - 1 - k) * c (k + 1)

end MasulloRepair


