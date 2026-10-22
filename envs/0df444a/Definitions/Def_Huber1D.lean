-- Prove2me | Definitions.Def_Huber1D
-- name    : Huber1D
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-09T05:23:22.708549+00:00
-- url     : https://prove2.me/theorems/1be55de1-5e21-453b-a0fc-7bbab49893f6
-- title:
--   The one-dimensional Huber function of the matching lower bound
-- statement:
--   This module introduces the one-dimensional extremizer of §20 that attains the bound of Theorem A. With the half-width
--
--   $$c = \frac{R}{2d_N+1}$$
--
--   (source (20.1)) the Huber function is $f(x) = x^2/2$ for $|x| \le c$ and $f(x) = c|x| - c^2/2$ for $|x| \ge c$ (source (20.2)), with $0$ as its unique minimiser and the whole NAG trajectory staying in the positive linear branch. Its gradient is the clipping `huberClamp c x = max (-c) (min c x)` of $x$ to the interval $[-c, c]$, and `huberE` records the coefficient sequence $e_j$ along the trajectory, where $y_j = R - e_j c$ with $e_0 = 0$ and $e_{j+1} = d_j + 1$. The function `huber` is stated for an arbitrary cutoff $c$; every property carries the hypothesis $0 \le c$ or $0 < c$ that the source's quotient by the positive $2d_N+1$ always satisfies.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §20 (matching lower bound), source lines 1817-2046, eq. (20.1)-(20.4); Lean: FullFormalization.Huber1D lines 1-177

-- Generated from F:/20261008/FullFormalization\FullFormalization\Huber1D.lean by skeleton subtraction (Phase 3-4):
-- every unselected declaration deleted, project imports rewritten.
/-
  FullFormalization.Huber1D

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, section 20
  (「定理 A 的 matching lower bound」, lines 1817-2046).

  The source fixes `L = 1`, `x⋆ = 0`, `x₀ = R > 0`, sets

      c = R / (2 d_N + 1)                                    (20.1)

  and defines the one-dimensional Huber function

      f x = x²/2            if |x| ≤ c
      f x = c |x| - c²/2    if |x| ≥ c                       (20.2)

  It then states (lines 1853-1858) that `f` is convex, differentiable, has a
  globally 1-Lipschitz gradient and has `0` as its unique minimizer, and proves
  the NAG trajectory identity

      x_j = R - d_j c                                        (20.3)

  together with the observation that the whole trajectory stays in the positive
  linear branch (`x_j ≥ c` for `j ≤ N`, source 20.2), whence

      (f(x_N) - f⋆) / R² = 2 / (N² + 7 N + 4)                (20.4)

  i.e. exactly `tau N` of `FullFormalization.Coefficients`.  This is the
  matching lower bound: the upper bound (19.1) is attained.

  ## Representation choices

  * The constant `c` is called `huberC` here: `d` is the coefficient sequence of
    `FullFormalization.Coefficients`, and `c` is used as a bound variable
    throughout the project, so a global `c` would be confusing.

  * `huber c : ℝ → ℝ` is stated for an arbitrary `c`; every property below
    carries the hypothesis `0 ≤ c` (or `0 < c`) that the source's `c`, being a
    quotient by the positive `2 d_N + 1`, always satisfies.

  * The gradient of `huber c` is the clipping `huberClamp c x = max (-c) (min c x)`
    of `x` to `[-c, c]`.  Its 1-Lipschitz property is `huberClamp_lipschitz`;
    it is monotone, which is how convexity of `huber c` is obtained (through
    `MonotoneOn.convexOn_of_deriv`).  Differentiability is proved by gluing the
    two branches at the kinks `±c`, where the one-sided derivatives agree.

  * **Index range of (20.3).**  The source writes `x_j = R - d_j c` for the
    iterates of the method.  The induction only ever queries `x_0, …, x_N`
    (the method stops at `x_N`), and it uses the branch hypothesis `x_j ≥ c`,
    which is *false* for `j > N`.  Accordingly `huber_traj` below is stated for
    `j ≤ N`, which is exactly the range on which (20.3) is true.  (For `N = 1`,
    `R = 1` one gets `c = 1/3`, `x_3 = -2/15` while `R - d_3 c = -1/4`: the
    unrestricted statement is false.)
-/

import Mathlib
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_RationalNAG

open scoped Gradient RealInnerProductSpace
open Set
set_option linter.unusedSectionVars false

namespace FullFormalization

/-! ## Section 20.0: the Huber function -/

/-- (20.1) `c = R / (2 d_N + 1)`, the half-width of the quadratic region. -/
noncomputable def huberC (N : ℕ) (R : ℝ) : ℝ := R / (2 * d N + 1)

/-- (20.2) the one-dimensional Huber function:
`x²/2` on `|x| ≤ c` and `c |x| - c²/2` outside. -/
noncomputable def huber (c x : ℝ) : ℝ :=
  if |x| ≤ c then x ^ 2 / 2 else c * |x| - c ^ 2 / 2

/-- The gradient of `huber c`: the clipping of `x` to the interval `[-c, c]`. -/
noncomputable def huberClamp (c x : ℝ) : ℝ := max (-c) (min c x)

/-- The coefficient `e_j` with `y_j = R - e_j c` along the NAG trajectory:
`e_0 = 0` and `e_{j+1} = d_j + 1` (source 20.1, where `y_1 = R - c`). -/
noncomputable def huberE (j : ℕ) : ℝ := if j = 0 then 0 else d (j - 1) + 1

/-! ## Elementary values of `huber`, `huberClamp` and the coefficients -/

































/-! ## Elementary derivatives of the two branches -/







/-! ## Section 20, lines 1853-1858: the analytic properties of `huber`

The derivative is computed by gluing the two branches at the two kinks `±c`;
the one-sided derivatives agree there (both are `±c`), so the gluing goes
through `HasDerivWithinAt.union`. -/

















/-! ## Source line 1857-1858: `0` is the unique minimizer -/






/-! ## Section 20.1-20.2: the NAG trajectory -/







/-! ## Section 20.3: the attained value (20.4) -/







/-! ## Theorem A, lower bound: the Huber function attains the bound -/



end FullFormalization


