-- Prove2me | Definitions.Def_GradientStrategies
-- name    : GradientStrategies
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-09T05:15:10.413978+00:00
-- url     : https://prove2.me/theorems/0fa16fb7-6062-40b9-9465-806f84bbbded
-- title:
--   Fixed-step gradient descent strategies (steps 1/L and 1/(2L))
-- statement:
--   This module defines the two gradient-descent strategies of the portfolio, matching the frozen implementation statement for statement. The shared fixed-step iteration from the origin is
--
--   $$p_0 = 0, \qquad p_{k+1} = p_k - \eta\,\nabla f(p_k),$$
--
--   with exactly one oracle call per step, the $k$-th call being spent at $p_{k-1}$. Strategy 1 (`GD`) uses the step $\eta = 1/L$ and strategy 2 (`halfGD`) the declared conservative step $\eta = 1/(2L)$; each is packaged as a step size `step`, the iterate family `point` and the output `out = p_N`, the final iterate after the $N$-step budget. Both start at the origin, so — as the implementation's own docstring observes — the only difference between them is the step size.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §21 strategies 1 and 2, source lines 2079-2080 (implementation semantics per §19 and §35); Lean: FullFormalization.GradientStrategies lines 1-148

-- Generated from F:/20261008/FullFormalization\FullFormalization\GradientStrategies.lean by skeleton subtraction (Phase 3-4):
-- every unselected declaration deleted, project imports rewritten.
/-
  FullFormalization.GradientStrategies

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, section 21,
  strategies 1 and 2 (source lines 2079-2080):

      1. GD, step `1/L`;
      2. GD, step `1/(2L)`.

  Implementation semantics (source §19 authorises the frozen implementation,
  and §35's cross-check script imports it):
  `F:\Hardy_Run_2026-10-07_001215\workflow\hgcore\blackbox_algos.py`,
  `_gd_fixed_1_over_L` and `_gd_fixed_declared_steps`:

      point = _origin(spec)                      -- the origin
      for _ in range(spec.query_budget):         -- one query per step
          answer = oracle.query(point)
          point = point - size * answer["gradient"]
      oracle.finish(point)                       -- the final point is the output

  with `size = 1/L` for the first strategy and `size = 1/(2L)` for the second.
  Both start from the origin, so — as the implementation's own docstring says —
  the only difference between them is the step size.

  In the normalized coordinates of section 21 the starting point is `z = 0`,
  i.e. `x = x_init`; the two strategies below are written on the raw oracle and
  in normalized coordinates, which is the same thing since `z = 0` is the
  origin of `E`.

  Query bookkeeping: the loop body queries *then* steps, so the `N` queries are
  the iterates `p_0, ..., p_{N-1}` and the reported point is `p_N`.  There is no
  query at the output point (matching §5: no off-by-one, and matching source
  line 312-319 where `g_N` is a proof variable only for the NAG method).
-/

import Mathlib
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_PortfolioDefinitions

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The shared fixed-step descent -/

/-- The iterates of fixed-step gradient descent from the origin:
`p_0 = 0` and `p_{k+1} = p_k - η • ∇f(p_k)`.  One oracle call per step, and the
`k`-th call is spent at `p_{k-1}`. -/
noncomputable def descentPoint (o : Oracle E) (η : ℝ) : ℕ → E
  | 0 => 0
  | k + 1 => descentPoint o η k - η • o.gradient (descentPoint o η k)







/-! ### Strategy 1: gradient descent with step `1/L` -/

namespace GD

/-- Strategy 1's step size: `1/L`. -/
noncomputable def step (L : ℝ) : ℝ := 1 / L

/-- The `k`-th iterate of strategy 1. -/
noncomputable def point (o : Oracle E) (L : ℝ) (k : ℕ) : E := descentPoint o (step L) k



/-- Strategy 1's output: the final iterate `p_N`. -/
noncomputable def out (o : Oracle E) (L : ℝ) (N : ℕ) : E := point o L N

















end GD

/-! ### Strategy 2: gradient descent with step `1/(2L)` -/

namespace halfGD

/-- Strategy 2's step size: `1/(2L)`, declared rather than derived — the
conservative constant of the frozen implementation. -/
noncomputable def step (L : ℝ) : ℝ := (1 / 2) / L

/-- The `k`-th iterate of strategy 2. -/
noncomputable def point (o : Oracle E) (L : ℝ) (k : ℕ) : E := descentPoint o (step L) k



/-- Strategy 2's output: the final iterate `p_N`. -/
noncomputable def out (o : Oracle E) (L : ℝ) (N : ℕ) : E := point o L N



















end halfGD

/-! ### The two strategies are a controlled comparison

Both start at the origin and differ only in the step size, exactly as the
frozen implementation's docstring says.  A half step is a step of the doubled
smoothness constant. -/







end FullFormalization


