-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Sec4_BoxesFromLeaves
-- name    : APSPSource_ThreeSumApsp_Sec4_BoxesFromLeaves
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T08:27:45.796146+00:00
-- url     : https://prove2.me/theorems/0c84f288-61de-4738-9e41-e74a093f0a3b
-- title:
--   Constructing a box by starring lower distinguished terms
-- statement:
--   For an output string $\eta$ and a leaf $\tau$, let $Q$ be the inner levels of $\eta$ and let $Z\subseteq Q$ be those where $\tau$ uses the distinguished term $P_0$. Let $F$ be the initial segment of $Q$ lying below every level of $Q\setminus Z$; when $Z=Q$, take $F=Q$.
--
--   Define
--
--   $$\operatorname{starBelow}(\eta,\tau)=\operatorname{starAt}(F,\tau).$$
--
--   Thus the selected lower $P_0$ positions become stars, while other leaf symbols remain unchanged. This is the box construction from a contributing leaf used in Section 4.2.
--
--   References:
--
--   1. [Source formalization, lines 44–49](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/BoxesFromLeaves.lean#L44-L49).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/BoxesFromLeaves.lean#L44-L49

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Boxes
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Lemma27_28
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The boxes of an output string, from its leaves of order exactly `t` (Section 4.2)

Let `η` be an output string (the paper's w) with inner set `Q` of `m` levels. The boxes of `η` are
the cubes of the sets `𝓑_V`, over all `V ⊆ Q` with `|V| = m - t`. This file proves two passages of
the running text of Section 4.2 about them.

* *Every box of `η` has exactly `m - t` symbols that are `P₀` or stars*
  (`card_starLevels_add_card_P0Levels`).
* *The second description.* Take a leaf of order exactly `t` contributing to `η` and replace its
  `P₀` by a star at every level of `Q` below the lowest level of `Q` at which it chooses another
  term, or at every level of `Q` if `t = 0` (`starBelow`). For such a leaf this is the box of the
  leaf (`boxOfLeaf_eq_starBelow`), so it is a box of `η` (`starBelow_mem`). Replacing the stars with
  `P₀` gives the leaf back (`starsToP0_starBelow`), and it turns every box of `η` into a leaf of
  order exactly `t` contributing to `η` (`starsToP0_of_mem`). So each box of `η` arises exactly once
  (`existsUnique_starBelow_eq`).
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

variable {L m t : ℕ} {η : OutStr L} {τ : Leaf L}









/-- Section 4.2, for a leaf `τ` of order exactly `t` contributing to `η`: "consider the lowest level
of Q at which it chooses a term other than P₀, and replace its P₀ by a star at every lower level of
Q (or at every level of Q, if t = 0)." With `Z` the set of the levels of `Q` at which `τ` chooses
`P₀`, these lower levels are those of `F_Z`, which is all of `Q` if `Z = Q`. -/
def starBelow (η : OutStr L) (τ : Leaf L) : Cube L :=
  Cube.starAt (FV (innerSetO η) (Zof (innerSetO η) τ)) τ























































end ThreeSumApsp


