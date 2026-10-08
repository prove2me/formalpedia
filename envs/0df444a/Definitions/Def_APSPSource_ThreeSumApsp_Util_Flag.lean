-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
-- name    : APSPSource_ThreeSumApsp_Util_Flag
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:13:33.647603+00:00
-- url     : https://prove2.me/theorems/3ff52b0c-6cdb-49df-9a61-7bb014a1119d
-- title:
--   Integer encoding of decision-problem answers
-- statement:
--   For a proposition $p$, its integer indicator records a yes answer as $1$ and a no answer as $0$:
--
--   $$\chi(p)=\begin{cases}1,&p\text{ holds},\\0,&p\text{ does not hold}.\end{cases}$$
--
--   This convention is used in the specifications of decision routines underlying the Exact Triangle and APSP algorithms. The accompanying equations give $\chi(p)=1$ under the hypothesis $p$ and $\chi(p)=0$ under the hypothesis $\neg p$; these equations are required by subsequent specification definitions.
--
--   References:
--
--   1. [Source formalization: integer answer indicators](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Flag.lean#L21-L29).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Flag.lean#L21-L29

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Init
public import Mathlib.Algebra.Order.Ring.Int

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The answer of a decision problem as a number

A routine for a decision problem returns 1 for yes and 0 for no: `flag p` is this number for the
proposition `p`.
-/

@[expose] public section

namespace ThreeSumApsp

open Classical in
/-- The answer of a decision problem as a number: 1 for yes, 0 for no. -/
noncomputable def flag (p : Prop) : ℤ := if p then 1 else 0

/-- The answer yes is written as 1. -/
theorem flag_of {p : Prop} (h : p) : flag p = 1 := if_pos h

/-- The answer no is written as 0. -/
theorem flag_of_not {p : Prop} (h : ¬ p) : flag p = 0 := if_neg h

















end ThreeSumApsp


