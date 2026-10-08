-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Util_CountingSort
-- name    : APSPSource_ThreeSumApsp_Util_CountingSort
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:36:50.110473+00:00
-- url     : https://prove2.me/theorems/fc1420c5-0f9d-41f8-b807-559e822db878
-- title:
--   Counts and positions for stable sorting by natural keys
-- statement:
--   Let $k:\mathbb N\to\mathbb N$ assign a key to each item. For a key $t$ and prefix length $j$, define
--
--   $$E(t,j)=|\{i<j:k(i)=t\}|,\qquad L(t,j)=|\{i<j:k(i)<t\}|.$$
--
--   For $N$ items, the specified sorted position of item $j$ is
--
--   $$\operatorname{pos}(N,j)=L(k(j),N)+E(k(j),j).$$
--
--   The first term counts all items with smaller keys; the second counts earlier items with the same key. This is the position formula used to specify stable counting sort. Bounds, injectivity, and correctness of an implementing routine are separate results.
--
--   References:
--
--   1. [Source formalization, lines 27–34](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/CountingSort.lean#L27-L34).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/CountingSort.lean#L27-L34

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.SuccPred

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The pure side of counting sort

`N` items `0, …, N - 1` have keys `kf 0, …, kf (N - 1)`.  A stable sort by key puts item `j` at the
place `sortPos kf N j`: the number of items with a smaller key plus the number of earlier items with
the same key.

This is a bijection of `{0, …, N - 1}` (`eq_of_sortPos_eq`, `exists_sortPos_eq`) that is increasing
for the order "smaller key, or same key and earlier" (`sortPos_lt_sortPos_iff`).
-/

@[expose] public section

namespace ThreeSumApsp

/-- The number of items `i < j` with key `t`. -/
def cntEq (kf : ℕ → ℕ) (t j : ℕ) : ℕ := Nat.count (fun i => kf i = t) j

/-- The number of items `i < j` with a key smaller than `t`. -/
def cntLt (kf : ℕ → ℕ) (t j : ℕ) : ℕ := Nat.count (fun i => kf i < t) j

/-- The place of item `j` after a stable sort of the items `0, …, N - 1` by key. -/
def sortPos (kf : ℕ → ℕ) (N j : ℕ) : ℕ := cntLt kf (kf j) N + cntEq kf (kf j) j

section
variable (kf : ℕ → ℕ)






























end

variable {kf : ℕ → ℕ} {N K : ℕ}



























































end ThreeSumApsp


