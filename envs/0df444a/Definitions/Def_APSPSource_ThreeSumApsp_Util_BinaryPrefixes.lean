-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Util_BinaryPrefixes
-- name    : APSPSource_ThreeSumApsp_Util_BinaryPrefixes
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:36:41.974079+00:00
-- url     : https://prove2.me/theorems/c97e3863-1ded-4a34-8abc-a6403021ba3e
-- title:
--   Binary prefix and remainder update formulas
-- statement:
--   For natural numbers $L,\ell$ and an integer $z$, define a prefix and a scaled remainder by
--
--   $$Q_\ell(z)=\left\lfloor\frac{z}{2^\ell}\right\rfloor,\qquad R_{L,\ell}(z)=(z\bmod2^\ell)2^{L\mathbin{\dot-}\ell},$$
--
--   where $L\mathbin{\dot-}\ell=\max\{L-\ell,0\}$ is natural-number subtraction. For integers $P,q,r$, the one-step update functions are
--
--   $$q'=\begin{cases}2q,&2r<P,\\2q+1,&2r\ge P,\end{cases}\qquad
--   r'=\begin{cases}2r,&2r<P,\\2r-P,&2r\ge P.\end{cases}$$
--
--   These functions expose the prefix-and-remainder arithmetic used to append a binary digit without a machine shift instruction. Their relation to successive prefixes under the relevant bounds is a later theorem.
--
--   References:
--
--   1. [Source formalization, lines 30–40](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/BinaryPrefixes.lean#L30-L40).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/BinaryPrefixes.lean#L30-L40

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The prefixes of a binary representation, one bit at a time

The prefixes `⌊z/2^ℓ⌋` of a number `0 ≤ z < 2^L` are computed without division, from the level
`ℓ = L` down to `ℓ = 0`.  Next to the prefix `q = ⌊z/2^ℓ⌋` (`prefQ`) one keeps the rest of the
number, moved to the top: `r = (z mod 2^ℓ) 2^(L-ℓ) < 2^L` (`prefR`).  One step doubles `r`; if the
result reaches `2^L`, then the next bit of `z` is 1 (`pref_step`).  The bit is the binary digit
number `ℓ` of `z` (`testBit_iff_shift`).  One step on lists of numbers is `zipWith_shiftQ` and
`map_shiftR`.
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## Prefixes, one bit at a time -/

/-- The prefix `⌊z/2^ℓ⌋`. -/
def prefQ (ℓ : ℕ) (z : ℤ) : ℤ := z / 2 ^ ℓ

/-- The rest `z mod 2^ℓ`, moved to the top of `L` bits. -/
def prefR (L ℓ : ℕ) (z : ℤ) : ℤ := z % 2 ^ ℓ * 2 ^ (L - ℓ)

/-- The new prefix after one step: the old one with the next bit appended. -/
def shiftQ (P q r : ℤ) : ℤ := if 2 * r < P then 2 * q else 2 * q + 1

/-- The new rest after one step. -/
def shiftR (P r : ℤ) : ℤ := if 2 * r < P then 2 * r else 2 * r - P










































































/-! ## The lists of the prefixes and of the rests -/




















end ThreeSumApsp


