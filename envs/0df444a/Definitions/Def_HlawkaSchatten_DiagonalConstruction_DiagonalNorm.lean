-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalConstruction_DiagonalNorm
-- name    : HlawkaSchatten_DiagonalConstruction_DiagonalNorm
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-28T16:12:48.023196+00:00
-- url     : https://prove2.me/theorems/22f803d6-9af0-4af6-a634-6a3c52be2bed
-- title:
--   The complex linear operator with prescribed diagonal entries (diagonalOperator)
-- statement:
--   For a finite index set $\iota$ and a family of complex numbers $d=(d_i)_{i\in\iota}$, `diagonalOperator` defines the $\mathbb{C}$-linear operator on the finite-dimensional Hilbert space $\mathbb{C}^\iota$ (`EuclideanSpace ℂ ι`) that acts diagonally by $d$:
--
--   $$
--   \mathrm{diagonalOperator}(d)\,x = (d_i\,x_i)_{i\in\iota}.
--   $$
--
--   It exists to connect the coordinate-vector form of the Hlawka-type inequality (stated for `lpNorm`) to the operator-theoretic Schatten $p$-quantity `schattenPNorm`: the coordinate basis is an eigenbasis of the associated Gram operator, with eigenvalues $|d_i|^2$, so the singular values of $\mathrm{diagonalOperator}(d)$ are exactly $|d_i|$, and — for $p>0$ — its Schatten $p$-quantity agrees with $\|d\|_p$ (`lpNorm`). This is the bridge that lets a result proved by the coordinate argument be read as a genuine statement about singular values.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/DiagonalNorm.lean#L23-L26

import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Diagonal operators and coordinate power sums

This connects the coordinate proof to the singular-value Schatten norm
used in the publication boundary. The Gram operator has the coordinate
basis as an eigenbasis, with eigenvalues equal to squared entry norms.
-/

namespace HlawkaSchatten.DiagonalConstruction

open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The complex operator with the prescribed diagonal. -/
noncomputable def diagonalOperator (d : ι → ℂ) :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι :=
  Matrix.toEuclideanLin (Matrix.diagonal d)













end HlawkaSchatten.DiagonalConstruction


