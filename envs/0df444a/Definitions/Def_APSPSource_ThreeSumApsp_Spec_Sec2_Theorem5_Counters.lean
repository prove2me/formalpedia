-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Counters
-- name    : APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Counters
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:22:22.12118+00:00
-- url     : https://prove2.me/theorems/70447e3d-ebef-4bb4-8556-83d397efbc69
-- title:
--   Band, block, and row-offset counters
-- statement:
--   A counter is a triple of natural numbers $(b,k,o)$ giving a band's index, the block within that band, and the row offset within that block. For $k_0$ blocks per band and $n_0$ rows per block, the counter attached to row $I$ is
--
--   $$C(I)=\left(\left\lfloor\frac{I}{k_0n_0}\right\rfloor,\ \left\lfloor\frac{I}{n_0}\right\rfloor\bmod k_0,\ I\bmod n_0\right).$$
--
--   The update function uses comparisons and increments:
--
--   $$\operatorname{step}(b,k,o)=\begin{cases}(b,k,o+1),&o+1<n_0,\\(b,k+1,0),&o+1\ge n_0\ \text{and}\ k+1<k_0,\\(b+1,0,0),&\text{otherwise}.\end{cases}$$
--
--   For positive block dimensions these are the usual quotient/remainder coordinates of a row in nested bands and blocks. They specify the counters maintained by later array routines; the theorem relating one update to the next row is separate.
--
--   **Formalization Note** Both functions are defined for all natural parameters, including zero, using Lean's total natural-number division and remainder.
--
--   References:
--
--   1. [Source formalization: counter structure and operations](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Counters.lean#L23-L40).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Counters.lean#L23-L40

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.Order.Ring.Int

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Quotients and remainders by counters

The word RAM has no division.  A program that runs through the rows `I = 0, 1, …, N - 1` of a matrix
can still know, for each row, its band, its block within the band and its offset within the block
(Section 2.3.4), that is `I / (K₀ N₀)`, `I / N₀ % K₀` and `I % N₀`: it keeps three counters and
steps them (`stepCtr`, `ctrAt_succ`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-- The band of a row, its block within the band, and its offset within the block. -/
structure Ctr where
  /-- The band of the row. -/
  band : ℕ
  /-- The block of the row within its band. -/
  block : ℕ
  /-- The offset of the row within its block. -/
  off : ℕ

/-- The band, block and offset of row `I`, for bands of `k₀` blocks of `n₀` rows. -/
def ctrAt (k₀ n₀ I : ℕ) : Ctr := ⟨I / (k₀ * n₀), I / n₀ % k₀, I % n₀⟩

/-- From the band, block and offset of a row to those of the next row: comparisons and additions of
1 only. -/
def stepCtr (k₀ n₀ : ℕ) (s : Ctr) : Ctr :=
  if s.off + 1 < n₀ then { s with off := s.off + 1 }
  else if s.block + 1 < k₀ then { s with block := s.block + 1, off := 0 }
  else ⟨s.band + 1, 0, 0⟩




















end ThreeSumApsp.Spec


