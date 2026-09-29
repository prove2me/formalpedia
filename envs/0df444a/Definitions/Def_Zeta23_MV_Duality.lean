-- Prove2me | Definitions.Def_Zeta23_MV_Duality
-- name    : Zeta23_MV_Duality
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:08:09.499776+00:00
-- url     : https://prove2.me/theorems/115e333c-6a50-4dfc-a2b8-e51edfaa4b93
-- title:
--   Normalized Hilbert kernel $k_{rs}$ and the Hermitian matrix $M = iK$ (MV step 4)
-- statement:
--   This bundle provides the spectral-reduction layer of the project's self-contained proof of the Montgomery–Vaughan weighted Hilbert inequality. For a finite index type $\iota$ with frequencies $\lambda_r$ (`freq`) and weights $\delta_r$:
--
--   - `MV.kfun` is the normalized kernel $k_{rs} := \sqrt{\delta_r}\sqrt{\delta_s}/(\lambda_r - \lambda_s)$ for $r \neq s$, and $0$ on the diagonal; the lemma `kfun_antisymm` records that $k$ is antisymmetric.
--   - `MV.Mmat` is the complex matrix $M := iK$ with entries $k_{rs}\, i$, and `Mmat_isHermitian` proves $M$ is Hermitian (since $K$ is real antisymmetric).
--   - `MV.EigenBound C` packages the conclusion of step 3 (`eigen_bound`) as a proposition: for all admissible $(\lambda, \delta)$ (in the sense of `MV.Adm`), every unit vector $u$ and real $\mu$ satisfying the normalized eigen-relation $\sum_{n \neq m} k_{mn} u_n = \mu\, i\, u_m$ for all $m$ has $|\mu| \le C$.
--
--   Role: with `EigenBound 13` supplied by the eigenvalue analysis, expanding $y^{*} M y$ in the eigenbasis of $M$ gives $|y^{*} M y| \le 13\, \|y\|^2$, and the substitution $y_r := x_r/\sqrt{\delta_r}$ lands exactly on `MVDiag 13`, the diagonal Montgomery–Vaughan inequality of `Zeta23/MV.lean`; polarization then yields the bilinear H-MV hypothesis consumed on the prime side.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/MV/Duality.lean

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_MV
import Definitions.Def_Zeta23_MV_Spacing

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# MV step 4 — spectral reduction: `eigen_bound` ⇒ `MVDiag 13` ⇒ `∃ C, MVHilbert C`

With `k_{rs} := √δ_r √δ_s/(λ_r − λ_s)` (0 on the diagonal; real antisymmetric) the matrix
`M := i·K` is Hermitian.  Every eigen-pair `(ν, v)` of `M` (unit `v`, from Mathlib's
`Matrix.IsHermitian.eigenvectorBasis`) satisfies the eigen-relation of `eigen_bound` with `μ := −ν`,
so `|ν| ≤ 13` for all eigenvalues (step 3).  Expanding in the eigenbasis
(`y* M y = Σ_i ν_i |(U*y)_i|²`, `Σ_i |(U*y)_i|² = Σ_i |y_i|²`) gives `|y* M y| ≤ 13 ‖y‖²`;
substituting `y_r := x_r/√δ_r` lands exactly on `MVDiag 13` (the literature / diagonal form of the
Montgomery–Vaughan weighted Hilbert inequality, Zeta23/MV.lean), and polarization
`exists_MVHilbert_of_diag` yields the bilinear H-MV of `Hypotheses.lean`.
-/

noncomputable section

open Finset Complex Matrix Unitary
open scoped BigOperators ComplexConjugate

namespace Zeta23
namespace MV

/-- The conclusion of step 3 (`Zeta23.MV.eigen_bound`, Eigen.lean) as a `Prop` with a general
constant: every solution of the normalized eigen-relation with a unit vector has `|μ| ≤ C`. -/
def EigenBound (C : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (freq δ : ι → ℝ), Adm freq δ →
    ∀ (u : ι → ℂ), ∑ n, ‖u n‖ ^ 2 = 1 → ∀ (μ : ℝ),
      (∀ m, ∑ n ∈ Finset.univ.erase m,
        ((Real.sqrt (δ m) * Real.sqrt (δ n) / (freq m - freq n) : ℝ) : ℂ) * u n
          = (μ : ℂ) * Complex.I * u m) → |μ| ≤ C

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The normalized kernel `k_{rs} = √δ_r √δ_s/(freq r − freq s)`, `0` on the diagonal. -/
def kfun (freq δ : ι → ℝ) (r s : ι) : ℝ :=
  if r = s then 0 else Real.sqrt (δ r) * Real.sqrt (δ s) / (freq r - freq s)

omit [Fintype ι] in
lemma kfun_antisymm (freq δ : ι → ℝ) (r s : ι) : kfun freq δ s r = -kfun freq δ r s := by
  unfold kfun
  by_cases h : r = s
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h, ← neg_div_neg_eq, neg_sub]; ring

/-- `M := i·K`, a Hermitian complex matrix. -/
def Mmat (freq δ : ι → ℝ) : Matrix ι ι ℂ := fun r s => (kfun freq δ r s : ℂ) * Complex.I

omit [Fintype ι] in
lemma Mmat_isHermitian (freq δ : ι → ℝ) : (Mmat freq δ).IsHermitian := by
  refine Matrix.IsHermitian.ext fun r s => ?_
  simp only [Mmat, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I,
    kfun_antisymm freq δ r s]
  push_cast
  ring








end MV
end Zeta23

end


