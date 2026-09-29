-- Prove2me | Definitions.Def_HlawkaSchatten_SpectralLift
-- name    : HlawkaSchatten_SpectralLift
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-27T16:42:21.196551+00:00
-- url     : https://prove2.me/theorems/9281213e-c5f4-40b1-aa53-c307564891da
-- title:
--   The nonnegative overlap coefficient between two orthonormal bases
-- statement:
--   Fix a complex inner product space $E$ and finite index types $\iota,\kappa$ (Lean states `[Fintype ι] [Fintype κ] [NormedAddCommGroup E] [InnerProductSpace ℂ E]`, with no explicit `[FiniteDimensional ℂ E]` — though supplying a finite orthonormal basis below forces it in practice). For orthonormal bases $e=(e_i)_{i\in\iota}$ and $f=(f_j)_{j\in\kappa}$ of $E$:
--
--   - `orthonormalBasisOverlap e f (i,j)` $:= \bigl\|\langle e_i,f_j\rangle\bigr\|^2$ — the squared magnitude of the inner product between the $i$-th vector of one basis and the $j$-th vector of the other. For the associated rank-one spectral projections $P_i=\lvert e_i\rangle\langle e_i\rvert$, $Q_j=\lvert f_j\rangle\langle f_j\rvert$, this is $\mathrm{Tr}(P_iQ_j)$.
--
--   This single nonnegative real coefficient is the bridge used to lift a pointwise scalar comparison between two real-weighted diagonals (in possibly different bases) to a comparison between the traces built from those diagonals: since the coefficients $w_{ij}$ are nonnegative with each row and each column summing to one, an overlap-weighted sum of a two-sided scalar bound is again bounded by the same two constants.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/SpectralLift.lean#L70-L75

import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Sign.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Nonnegative weighted lift of the scalar comparison

The Hermitian spectral argument writes both divergences as finite sums with
weights `Tr(Pᵢ Qⱼ) ≥ 0`.  This file isolates the ordered-algebraic step which
lifts the pointwise scalar bounds through those sums.
-/

namespace HlawkaSchatten

open scoped InnerProductSpace





section SpectralOverlap

variable {ι κ E : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The nonnegative coefficient relating two orthonormal spectral bases.
For rank-one spectral projections this is `Tr(Pᵢ Qⱼ)`. -/
noncomputable def orthonormalBasisOverlap
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ E)
    (ij : ι × κ) : ℝ :=
  ‖(⟪e ij.1, f ij.2⟫_ℂ)‖ ^ 2









end SpectralOverlap

end HlawkaSchatten


