-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Scale
-- name    : APSPSource_ThreeSumApsp_Util_Asymptotics_Scale
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T08:22:01.377857+00:00
-- url     : https://prove2.me/theorems/fb244789-933c-4d42-9351-8b704b461669
-- title:
--   Multivariate cost scales with a hidden polynomial factor
-- statement:
--   Let $X$ be a parameter type and $I$ a finite index set. A scale consists of a domain predicate $D(x)$, a hidden factor $h:X\to\mathbb R$, and explicit bases $b_i:X\to\mathbb R$, with $h(x)\ge1$ and $b_i(x)\ge1$ on the domain. A constructor with no hidden growth takes $h=1$.
--
--   For natural exponents $e_i$, define the monomial and the scale-relative bound on a natural count $t$ by
--
--   $$M_e(x)=\prod_{i\in I}b_i(x)^{e_i},$$
--   $$t\in\widetilde O_{\mathrm{scale}}(M_e)\iff\exists c\in\mathbb N\ \exists C\ge0,\ \forall x,\ D(x)\Rightarrow t(x)\le C\,h(x)^cM_e(x).$$
--
--   The hidden factor is an arbitrary part of the scale, not necessarily a logarithm. This interface records multivariate cost bounds while tracking powers of the explicit parameters and allowing an unspecified natural power of the chosen hidden quantity.
--
--   References:
--
--   1. [Source formalization, lines 54–65](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Asymptotics/Scale.lean#L54-L65).
--   2. [Source formalization, lines 69–76](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Asymptotics/Scale.lean#L69-L76).
--   3. [Source formalization, lines 80–86](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Asymptotics/Scale.lean#L80-L86).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Asymptotics/Scale.lean#L54-L65; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Asymptotics/Scale.lean#L69-L76; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Asymptotics/Scale.lean#L80-L86

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Dominated
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Orders of growth of counts

The time and the need of a program are natural numbers, given by explicit expressions in the
parameters of the input.  Only their order of growth is needed.  This file has one calculus
that reads the order of growth off such an expression, so that no constant is ever written out.

A *scale* (`Scale α ι`) fixes the parameters `x : α` for which bounds are claimed (`dom`) and some
quantities that are at least 1 there: the *bases* `base i`, whose powers are counted, and one more,
`hidden`, whose powers are not.  `s.SoftO t e` says that the count `t` is at most a constant times a
power of `hidden` times the monomial `∏ i, base i ^ e i`.  Three examples:

* bases `n`, `√D`, `κ log n` and `hidden = 1`: `s.SoftO t ![2, 1, 1]` is `t = O(n² √D κ log n)`;
* one base `√n` and `hidden = log n`: `s.SoftO t ![3]` is `t = Õ(n^{3/2})`;
* no base and `hidden = n U`: `s.SoftO t ![]` says that `t` is polynomially bounded.

So `SoftO` is `O` up to powers of `hidden`: it is `O` itself if `hidden = 1`, and `Õ` if `hidden` is
a logarithm.  The bounds hold on the whole domain and not only from some point on.

The exponents follow the expression.  A constant has the exponents 0 (`SoftO.const`), a sum the
larger ones (`SoftO.add`), a product their sum (`SoftO.mul`), a power their multiple (`SoftO.pow`).
Exponents may be raised (`SoftO.mono`), and the count may be replaced by a smaller one
(`SoftO.of_le`, `SoftO.of_forall_le`).  If every base is at most `2 ^ hidden`, the binary logarithm
of a bounded count has the exponents 0 (`SoftO.log2`).

The tactic `growth [h₁, h₂, …]` applies these rules from the outside to the inside of the
expression.  The facts `hᵢ` bound the quantities at which the rules stop: parameters, and functions
whose bound is a lemma of its own.  A function that is to be followed into its definition is
unfolded first.

A bound leaves the calculus by `SoftO.exists_le`, or as a `Dominated` statement by
`SoftO.dominated`.
-/

@[expose] public section

namespace ThreeSumApsp

/-- What upper bounds are measured in: quantities that are at least 1 on a domain. -/
structure Scale (α ι : Type*) where
  /-- The parameters for which bounds are claimed. -/
  dom : α → Prop
  /-- The quantity whose powers are not counted. -/
  hidden : α → ℝ
  /-- The quantities whose powers are counted. -/
  base : ι → α → ℝ
  /-- `hidden ≥ 1` on the domain. -/
  one_le_hidden : ∀ x, dom x → 1 ≤ hidden x
  /-- Every base is at least 1 on the domain. -/
  one_le_base : ∀ i x, dom x → 1 ≤ base i x

namespace Scale

/-- The scale with the given bases in which nothing is hidden. -/
def ofBases {α ι : Type*} (dom : α → Prop) (base : ι → α → ℝ)
    (h : ∀ i x, dom x → 1 ≤ base i x) : Scale α ι where
  dom := dom
  hidden _ := 1
  base := base
  one_le_hidden _ _ := le_rfl
  one_le_base := h

variable {α ι : Type*} [Fintype ι] (s : Scale α ι)

/-- The monomial `∏ i, base i ^ e i`. -/
noncomputable def mon (e : ι → ℕ) (x : α) : ℝ := ∏ i, s.base i x ^ e i

/-- The count `t` is at most a constant times a power of `hidden` times the monomial with the
exponents `e`, on the domain of the scale. -/
def SoftO (t : α → ℕ) (e : ι → ℕ) : Prop :=
  ∃ c : ℕ, Dominated s.dom (fun x => (t x : ℝ)) fun x => s.hidden x ^ c * s.mon e x












variable {s} {x : α} {e e' : ι → ℕ} {c c' : ℕ}
















namespace SoftO

variable {t t₁ t₂ : α → ℕ} {e₁ e₂ : ι → ℕ}

/-! ### Entering and leaving -/































/-! ### The rules -/
























































































































end SoftO

end Scale








































end ThreeSumApsp


