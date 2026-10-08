-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
-- name    : APSPSource_ThreeSumApsp_Lang_Regions
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:48:50.422234+00:00
-- url     : https://prove2.me/theorems/63d032f3-42eb-4c24-a03f-e72b7096cd78
-- title:
--   Memory regions, preservation predicates, and segment writes
-- statement:
--   Let a memory be a function $\mu:\mathbb N\to\mathbb Z$. A region starting at address $a$ with length $n$ consists of the half-open interval $[a,a+n)$. Membership, exclusion, disjointness of two regions, and agreement on a set of addresses are defined by
--
--   $$
--   \begin{aligned}
--   \operatorname{Inside}(a,n,b)&\iff a\le b<a+n,\\
--   \operatorname{Outside}(a,n,b)&\iff b<a\ \lor\ a+n\le b,\\
--   \operatorname{Apart}(a,n,a',n')&\iff a+n\le a'\ \lor\ a'+n'\le a,\\
--   \operatorname{SameOn}(K,\mu,\mu')&\iff\forall b,\ K(b)\Rightarrow\mu'(b)=\mu(b).
--   \end{aligned}
--   $$
--
--   The bundle specializes agreement to addresses outside one, two, or three regions, and to addresses below a free pointer, optionally excepting an output region. An ordered list of regions requires consecutive regions to lie in order without overlap and its final endpoint to be at most a specified bound.
--
--   For a destination $d$, values $f:\mathbb N\to\mathbb Z$, and a number $j$ of completed writes, the resulting memory is
--
--   $$\operatorname{wrote}(\mu,d,f,j)(b)=\begin{cases}f(b-d),&d\le b<d+j,\\\mu(b),&\text{otherwise}.\end{cases}$$
--
--   These predicates describe which memory cells a routine may change and which previously stored data it preserves.
--
--   References:
--
--   1. [Source formalization: region and preservation predicates](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Regions.lean#L54-L93).
--   2. [Source formalization: completed segment writes](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Regions.lean#L123-L125).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Regions.lean#L54-L69; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Regions.lean#L73-L93; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Regions.lean#L123-L125

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Function.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Regions of the memory, and the cells that a step leaves alone

A region is given by its first address `a` and its number `n` of cells.  `Inside a n b` says that
the cell `b` lies in it, `Outside a n b` that it does not, and `Apart a n a' n'` that two regions do
not meet.  `InOrder top [(a, n), (a', n'), …]` says that the listed regions lie one behind the other
and end at or below `top`.  All of these abbreviate linear inequalities.

`SameOn K μ μ'` says that the memory `μ'` agrees with `μ` on every cell that satisfies `K`.  It is
the one notion of "these cells are unchanged": a routine promises `SameOn K μ μ'` for the cells
`K` that it leaves alone.  (It is `Set.EqOn μ' μ {b | K b}`, stated with a predicate: the conditions
`K b` that occur are linear inequalities between addresses and are used as such.)  The usual choices
of `K` have names.

* `SameOutside μ μ' a n`: all cells outside one region; `SameOutside2` and `SameOutside3`: all cells
  outside two or three regions.
* `Kept μ μ' fr`: all cells below the free pointer `fr`.
* `KeptBut μ μ' fr out len`: all cells below `fr` outside the region of an output.

## How a fact is carried from one memory to a later one

A predicate `X` about a memory has one lemma of the name `X.keep` and of the form

  `theorem X.keep (h : X μ …) (hs : SameOn K μ μ' := by light_keep) : X μ' …`

where `K` describes the cells that `X` reads; `Seg.keep` is the model.  The argument `hs` has a
default proof.  So `h.keep`, with no argument, stands for "`h` still holds in the memory that is
asked for here".  The default proof `light_keep` uses every hypothesis of the form `SameOn _ ν ν'`
in the context, that is, the promises of the steps that were taken since `h` was obtained, and the
inequalities in the context that say where the regions lie.  In the proofs a promise is named when
the step is taken, as `same₂` in `rintro _ μ₂ ⟨sY, same₂⟩`.

`wrote μ dst f j` is the memory `μ` after a loop has written `f 0`, …, `f (j - 1)` to the cells from
`dst`.
-/

@[expose] public section

namespace Light

/-! ## Regions -/

/-- The cell `b` is among the `n` cells from address `a`. -/
abbrev Inside (a n b : ℕ) : Prop := a ≤ b ∧ b < a + n

/-- The cell `b` is not among the `n` cells from address `a`. -/
abbrev Outside (a n b : ℕ) : Prop := b < a ∨ a + n ≤ b

/-- Two regions of the memory, of `n` cells from `a` and of `n'` cells from `a'`, do not meet. -/
abbrev Apart (a n a' n' : ℕ) : Prop := a + n ≤ a' ∨ a' + n' ≤ a

/-- A map of a part of the memory: the regions of the list lie one behind the other, in the order of
the list, and the last one ends at or below `top`.  A region of the list is the pair of its first
address and its number of cells. -/
abbrev InOrder (top : ℕ) : List (ℕ × ℕ) → Prop
  | [] => True
  | [r] => r.1 + r.2 ≤ top
  | r :: r' :: rs => r.1 + r.2 ≤ r'.1 ∧ InOrder top (r' :: rs)

/-! ## Memories that agree on some cells -/

/-- The memory `μ'` agrees with `μ` on every cell that satisfies `K`. -/
def SameOn (K : ℕ → Prop) (μ μ' : ℕ → ℤ) : Prop := ∀ b, K b → μ' b = μ b

/-- The memory `μ'` agrees with `μ` outside the `n` cells from address `a`. -/
abbrev SameOutside (μ μ' : ℕ → ℤ) (a n : ℕ) : Prop := SameOn (Outside a n) μ μ'

/-- The memory `μ'` agrees with `μ` outside the `n` cells from `a` and the `m` cells from `b`. -/
abbrev SameOutside2 (μ μ' : ℕ → ℤ) (a n b m : ℕ) : Prop :=
  SameOn (fun x => Outside a n x ∧ Outside b m x) μ μ'

/-- The memory `μ'` agrees with `μ` outside three regions: `n` cells from `a`, `m` cells from `b`,
and `k` cells from `c`. -/
abbrev SameOutside3 (μ μ' : ℕ → ℤ) (a n b m c k : ℕ) : Prop :=
  SameOn (fun x => Outside a n x ∧ Outside b m x ∧ Outside c k x) μ μ'

/-- No cell below the free pointer has changed. -/
abbrev Kept (μ μ' : ℕ → ℤ) (fr : ℕ) : Prop := SameOn (· < fr) μ μ'

/-- No cell below the free pointer has changed, except the `len` cells from `out`. -/
abbrev KeptBut (μ μ' : ℕ → ℤ) (fr out len : ℕ) : Prop :=
  SameOn (fun x => x < fr ∧ Outside out len x) μ μ'

variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}























/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}

/-- The memory `μ` after `f 0`, …, `f (j - 1)` have been written to the cells from `dst`. -/
def wrote (μ : ℕ → ℤ) (dst : ℕ) (f : ℕ → ℤ) (j : ℕ) : ℕ → ℤ :=
  fun a => if dst ≤ a ∧ a < dst + j then f (a - dst) else μ a










































/-! ## The tactics -/









































end Light


