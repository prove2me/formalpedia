-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalConstruction_OrbitAveraging
-- name    : HlawkaSchatten_DiagonalConstruction_OrbitAveraging
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-28T16:20:20.413891+00:00
-- url     : https://prove2.me/theorems/136fa439-01d8-4b59-bba1-41c3579cd800
-- title:
--   Averaging a matrix triple over simultaneous coordinate permutations
-- statement:
--   Five definitions implement averaging a $3\times3$ real matrix (`Triple`, from the `Localization` bundle) over the six simultaneous permutations of its column and coordinate indices by one common permutation.
--
--   `conjugate` applies a permutation $e$ of $\{0,1,2\}$ to both indices of a matrix at once:
--   $$
--   \operatorname{conjugate}(e,X)(j,i) = X\big(e(j),e(i)\big).
--   $$
--   Both indices are permuted by the same $e$; permuting them separately is not the operation used here.
--
--   `permutations` (marked `private`) lists the six elements of the symmetric group on $\{0,1,2\}$: the identity, the three transpositions, and the two $3$-cycles obtained by composing transpositions.
--
--   `orbitAverage` is the average of a matrix over its orbit under all six of these simultaneous permutations:
--   $$
--   \operatorname{orbitAverage}(X) = \frac16\sum_{k=0}^{5} \operatorname{conjugate}\big(\operatorname{permutations}(k),\,X\big).
--   $$
--
--   `averageDiagonal` and `averageOffDiagonal` are the average of the three diagonal entries and the average of the six off-diagonal entries of a matrix,
--   $$
--   \begin{gathered}
--   \operatorname{averageDiagonal}(X) = \frac{X(0,0)+X(1,1)+X(2,2)}{3}, \\
--   \qquad
--   \operatorname{averageOffDiagonal}(X) = \frac{X(0,1)+X(0,2)+X(1,0)+X(1,2)+X(2,0)+X(2,1)}{6}.
--   \end{gathered}
--   $$
--
--   By a theorem in the same source module, $\operatorname{orbitAverage}(X)$ is determined by exactly these two averages, with every diagonal entry equal to $d=\operatorname{averageDiagonal}(X)$ and every off-diagonal entry equal to $o=\operatorname{averageOffDiagonal}(X)$. When $X\in\operatorname{entryBox}$, $d<0<o$ and $-d/o\in[1/2,2]$, so the average is $o$ times the cyclic witness triple at parameter $-d/o$. An arbitrary triple need not have these signs. Together with convexity of the triple deficit on the cyclic coordinate box (`entryBox`), Jensen's inequality applied to this six-fold average is what lets a bound proved for the cyclic family transfer to every matrix in the box.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/OrbitAveraging.lean#L29-L58

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Simultaneous permutation averaging on the cyclic box -/

namespace HlawkaSchatten.DiagonalConstruction



def conjugate (e : Equiv.Perm (Fin 3)) (X : Triple) : Triple :=
  fun j i ↦ X (e j) (e i)



private def permutations : Fin 6 → Equiv.Perm (Fin 3) :=
  ![Equiv.refl _, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
    (Equiv.swap 0 1).trans (Equiv.swap 1 2), (Equiv.swap 1 2).trans (Equiv.swap 0 1)]



noncomputable def orbitAverage (X : Triple) : Triple :=
  ∑ k : Fin 6, (1 / 6 : ℝ) • conjugate (permutations k) X

noncomputable def averageDiagonal (X : Triple) : ℝ := (X 0 0 + X 1 1 + X 2 2) / 3

noncomputable def averageOffDiagonal (X : Triple) : ℝ :=
  (X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1) / 6

















end HlawkaSchatten.DiagonalConstruction


