-- Prove2me | Definitions.Def_PlatformCournot_Assumption1
-- name    : PlatformCournot_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:26.2802+00:00
-- url     : https://prove2.me/theorems/9477b519-4995-45c9-bc88-c0367a1f33cb
-- title:
--   Assumption 1 — convex costs, differentiable on $(0,\infty)$, zero on $(-\infty,0]$
-- statement:
--   A cost function profile $C=(C_1,\dots,C_n)$, $C_i:\mathbb R\to\mathbb R_+$, satisfies **Assumption 1** when every $C_i$
--
--   1. is convex on $\mathbb R$;
--   2. is differentiable on $(0,\infty)$;
--   3. satisfies $C_i(x)=0$ for all $x\le 0$;
--   4. is nonnegative (its codomain is $\mathbb R_+$).
--
--   These are the cost functions of the paper: every result of the mission is stated for them.
--
--   **Formalization Note** Firms are `Fin n` (0-based). Condition 4 is the codomain $\mathbb R_+$ of p.8; it follows from 1 and 3 (a convex function that vanishes on $(-\infty,0]$ is nondecreasing on $[0,\infty)$), so it excludes nothing.
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, §2.1 Producer model and Assumption 1, p.8

import Mathlib

namespace PlatformCournot

/-- **Assumption 1 on the cost function profile.**
Pang et al., arXiv:1903.04574v3, §2.1, p.8: "Ci : R → R+ denotes each firm's production cost
function … Assumption 1. Each firm's cost function Ci is assumed to be convex, differentiable on
(0,∞), and satisfy Ci(x) = 0 for all x ≤ 0."

`Assumption1 C` holds for a profile `C = (C₁, …, Cₙ)` of real functions when every `Cᵢ` is convex
on `ℝ`, differentiable on `(0, ∞)`, zero on `(−∞, 0]` and nonnegative.

**Formalization Note** Firms are `Fin n` (0-based). The last conjunct is the codomain `ℝ₊` of
p.8; it follows from the other three (a convex function vanishing on `(−∞, 0]` is nondecreasing
on `[0, ∞)`), so it excludes nothing. -/
def Assumption1 {n : ℕ} (C : Fin n → ℝ → ℝ) : Prop :=
  ∀ i, ConvexOn ℝ Set.univ (C i) ∧ DifferentiableOn ℝ (C i) (Set.Ioi 0) ∧
    (∀ x ≤ 0, C i x = 0) ∧ ∀ x, 0 ≤ C i x

end PlatformCournot


