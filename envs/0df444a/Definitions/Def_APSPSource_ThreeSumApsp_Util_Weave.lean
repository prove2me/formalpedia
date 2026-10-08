-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Util_Weave
-- name    : APSPSource_ThreeSumApsp_Util_Weave
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:36:58.248894+00:00
-- url     : https://prove2.me/theorems/dbc28f25-dc97-4ab6-8e9a-55e88f086356
-- title:
--   Interleaving digit lists along a Boolean mask
-- statement:
--   Let $m$ be a Boolean mask and let $o,i$ be outer and inner lists of natural-number digits. The interleaving function takes the next inner digit at a true position and the next outer digit at a false position:
--
--   $$\begin{aligned}
--   W([],o,i)&=[],\\
--   W(\mathrm{true}::m,o,i)&=\operatorname{head}_0(i)::W(m,o,\operatorname{tail}(i)),\\
--   W(\mathrm{false}::m,o,i)&=\operatorname{head}_0(o)::W(m,\operatorname{tail}(o),i).
--   \end{aligned}$$
--
--   Here $\operatorname{head}_0$ returns zero for an empty list, and an empty list has empty tail. Thus the output has one digit for each mask position, with missing input digits replaced by zero.
--
--   This operation reconstructs a complete string from its inner and outer parts at the selected levels.
--
--   References:
--
--   1. [Source formalization, lines 25–31](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Weave.lean#L25-L31).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Weave.lean#L25-L31

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
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Count
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Interleaving two strings of digits along a mask

A mask is a list of truth values, one for each level.  `weaveList mask outer inner` runs through the
levels and takes the next digit of `inner` at a level with the entry `true` and the next digit of
`outer` at a level with the entry `false`.  A program that forms the number with these digits by
Horner's rule needs one pass over the mask and two pointers: at level `ℓ` the pointer into `inner`
has passed as many digits as there are entries `true` among the first `ℓ` entries of the mask, and
the pointer into `outer` as many as there are entries `false` (`getD_weaveList`).
-/

@[expose] public section

namespace ThreeSumApsp

/-- Two lists of digits interleaved along a mask: at a level with the entry `true` stands the next
digit of `inner`, at a level with the entry `false` the next digit of `outer`.  A missing digit
counts as 0. -/
def weaveList : List Bool → List ℕ → List ℕ → List ℕ
  | [], _, _ => []
  | true :: mask, outer, inner => inner.headD 0 :: weaveList mask outer inner.tail
  | false :: mask, outer, inner => outer.headD 0 :: weaveList mask outer.tail inner












































end ThreeSumApsp


