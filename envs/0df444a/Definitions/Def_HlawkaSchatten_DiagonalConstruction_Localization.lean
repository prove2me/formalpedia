-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
-- name    : HlawkaSchatten_DiagonalConstruction_Localization
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-28T15:36:34.862988+00:00
-- url     : https://prove2.me/theorems/408307c3-c8cb-4264-a00b-541ee217f047
-- title:
--   The cyclic coordinate box and the triple deficit restricted to it
-- statement:
--   Four definitions describe a single $3\times3$ real matrix, a fixed box of such matrices, and the Hlawka deficit restricted to that box.
--
--   `Triple` is the type of $3\times3$ real matrices, columns first: a value $X:\mathrm{Triple}$ assigns a real number $X(j,i)$ to each column index $j\in\{0,1,2\}$ and coordinate index $i\in\{0,1,2\}$.
--
--   `cyclicCenter` is the fixed sign matrix with $-1$ on the diagonal and $+1$ off it,
--   $$
--   \operatorname{cyclicCenter}(j,i) = \begin{cases} -1 & i=j \\ 1 & i\neq j,\end{cases}
--   $$
--   equivalently $J-2I$ for the $3\times3$ all-ones matrix $J$ and identity matrix $I$.
--
--   `entryBox` is the set of matrices within entrywise distance $19/100$ of `cyclicCenter`:
--   $$
--   \operatorname{entryBox} = \{X:\mathrm{Triple} \mid \forall j,i,\ |X(j,i)-\operatorname{cyclicCenter}(j,i)|\le 19/100\}.
--   $$
--
--   `tripleDeficit` applies the Hlawka deficit (`hlawkaDeficit`, from the `Normalization` bundle) to the three columns of a matrix, read as three vectors in $\mathbb{R}^3$: for a candidate constant $K$ and exponent $p$,
--   $$
--   \operatorname{tripleDeficit}(p,K,X) = \operatorname{hlawkaDeficit}\big(p,K,\,X(0,\cdot),\,X(1,\cdot),\,X(2,\cdot)\big).
--   $$
--
--   These definitions frame the localization step of the sharp diagonal construction: a theorem in the same source module shows that, for $p\ge256$ and the constant $K=K_p$ (`cyclicConstant`), any triple $x,y,z\in\mathbb{R}^3$ with $\operatorname{hlawkaDeficit}(p,K_p,x,y,z)<0$ can be relabeled, rescaled, and permuted with signs into a matrix $X\in\operatorname{entryBox}$ with $\operatorname{tripleDeficit}(p,K_p,X)<0$. Later convexity and averaging arguments then work on this one fixed compact set rather than on an unbounded family of triples.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/Localization.lean#L12-L20

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # A strict counterexample lies in the cyclic coordinate box -/

namespace HlawkaSchatten.DiagonalConstruction

/-- Columns first, then coordinates within each column. -/
abbrev Triple := Fin 3 → Fin 3 → ℝ

def cyclicCenter : Triple := fun j i ↦ if i = j then -1 else 1

def entryBox : Set Triple := {X | ∀ j i, |X j i - cyclicCenter j i| ≤ 19 / 100}

noncomputable def tripleDeficit (p K : ℝ) (X : Triple) : ℝ :=
  hlawkaDeficit p K (X 0) (X 1) (X 2)







end HlawkaSchatten.DiagonalConstruction


