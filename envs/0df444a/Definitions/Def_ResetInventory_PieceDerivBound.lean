-- Prove2me | Definitions.Def_ResetInventory_PieceDerivBound
-- name    : ResetInventory_PieceDerivBound
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:19:44.562627+00:00
-- url     : https://prove2.me/theorems/c7e3c136-a2a7-438d-8e0f-110afa785c3c
-- title:
--   Derivative property of one piece of the value function (corrected)
-- statement:
--   A function $p$ (one piece of the value function) has the **derivative property with bound $M_t$ and Lipschitz condition $\Lambda$** if there is a function $D$ such that
--
--   1. $D(x)$ is the derivative of $p$ at every $x\in[0,c_{\max}]$, within $[0,c_{\max}]$ (one-sided at the ends);
--   2. $D$ is continuous on $[0,c_{\max}]$;
--   3. $|D(x)|\le M_t$ for every $x\in[0,c_{\max}]$;
--   4. if $\Lambda$ holds, $D$ is Lipschitz on $[0,c_{\max}]$: $|D(x)-D(y)|\le C|x-y|$ for some $C\ge0$.
--
--   This is the property Proposition 6 asserts for each piece of (28), in its corrected form.
--
--   **Formalization Note** The paper says each piece "has a Lipschitz derivative" unconditionally, which is false for the third piece of (28) under Assumption 2 as printed. For that piece the theorems take $\Lambda$ = "$\partial_xH(\cdot,t)$ is Lipschitz on $[0,c_{\max}]$"; for the first two they take $\Lambda$ = true, so the paper's claim stands unconditionally. The Lipschitz constant is existential, as in the paper.
-- source:
--   Lee, Mintz, Aswani, Shen, Yang, Optimal Policy for Inventory Management with Periodic and Controlled Resets, arXiv:2209.03571v1, Proposition 6, p.21; proof, p.35

import Mathlib

namespace ResetInventory

/-- The derivative property of one piece `p` of the value function in Proposition 6 (Lee, Mintz,
Aswani, Shen, Yang, arXiv:2209.03571v1, p.21), in its corrected form: `p` has a derivative `D`
within `[0, c_max]` at every point of `[0, c_max]`, `D` is continuous on `[0, c_max]` and
`|D| ≤ M_t` there; and **if** the condition `lipCond` holds, `D` is Lipschitz on `[0, c_max]`.

**Formalization Note** The paper asserts that each piece "has a Lipschitz derivative"
unconditionally. For the third piece of (28) that is false under Assumption 2 as printed
(`∂ₓₓH ≥ m_t` is only a lower bound), so for that piece the theorems pass `lipCond` =
"`∂ₓH(·, t)` is Lipschitz on `[0, c_max]`" (`HDerivLipschitz`): its derivative is continuous and
bounded by `M_t` unconditionally, and Lipschitz under that extra condition. The first two pieces
keep the paper's claim unconditionally (`lipCond := True`). The Lipschitz constant is existential,
as in the paper. -/
def PieceDerivBound (cmax Mt : ℝ) (lipCond : Prop) (p : ℝ → ℝ) : Prop :=
  ∃ D : ℝ → ℝ,
    (∀ x ∈ Set.Icc 0 cmax, HasDerivWithinAt p (D x) (Set.Icc 0 cmax) x) ∧
    ContinuousOn D (Set.Icc 0 cmax) ∧
    (∀ x ∈ Set.Icc 0 cmax, |D x| ≤ Mt) ∧
    (lipCond → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Set.Icc 0 cmax, ∀ y ∈ Set.Icc 0 cmax, |D x - D y| ≤ C * |x - y|)

end ResetInventory


