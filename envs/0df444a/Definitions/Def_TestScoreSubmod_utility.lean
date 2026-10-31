-- Prove2me | Definitions.Def_TestScoreSubmod_utility
-- name    : TestScoreSubmod_utility
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:42.600378+00:00
-- url     : https://prove2.me/theorems/d0046cf9-68ef-4f8c-b4a0-ca58f41596c0
-- title:
--   Stochastic submodular set function $u(S)=\mathbb E[g(M_S(X))]$, eq. (4)
-- statement:
--   Each item $i$ has a nonnegative random performance $X_i\sim P_i$, and the performances are independent. For a value function $g$, the **utility** of a set $S$ of items is
--
--   $$
--   u(S)=\mathbb E\bigl[g(M_S(X_1,\dots,X_n))\bigr],
--   $$
--
--   the expected value of $g$ at the performance vector in which every item outside $S$ contributes $\varphi=0$.
--
--   The optimization problem of the paper is to maximize $u(S)$ over the sets with $|S|=k$.
--
--   **Formalization Note** Independence is the product measure `Measure.pi P` on $\mathbb R_{\ge0}^{\iota}$. The expectation is the Bochner integral, which is $0$ for a non-integrable integrand; every theorem using $u$ carries hypotheses from which integrability follows.
-- source:
--   Sekar, Vojnovic, Yun, A Test Score Based Approach to Stochastic Submodular Optimization, arXiv:1605.07172v4, §2.1, eq. (4), p.11; §2.2, eq. (5), p.11

import Mathlib
import Definitions.Def_TestScoreSubmod_mask

open scoped NNReal
open MeasureTheory

namespace TestScoreSubmod

/-- **Stochastic submodular set function `u(S) = E[g(M_S(X₁, …, Xₙ))]`** (Sekar, Vojnovic, Yun,
arXiv:1605.07172v4, §2.1, eq. (4), p.11; §2.2, eq. (5)).

Each item `i` has a nonnegative random performance `Xᵢ ∼ Pᵢ`, drawn independently. The utility
of a set `S` of items is the expected value of `g` at the performance vector in which the items
outside `S` are replaced by `φ = 0`.

**Formalization Note** Independence is the product measure `Measure.pi P` on `ι → ℝ≥0`; the
performance laws `P i` are measures on `ℝ≥0` (probability measures wherever the utility is
used). The expectation is the Bochner integral, which is `0` for a non-integrable integrand;
every theorem using `utility` carries hypotheses from which integrability follows. -/
noncomputable def utility {ι : Type*} [Fintype ι] [DecidableEq ι] (g : (ι → ℝ≥0) → ℝ)
    (P : ι → Measure ℝ≥0) (S : Finset ι) : ℝ :=
  ∫ x, g (mask S x) ∂(Measure.pi P)

end TestScoreSubmod


