-- Prove2me | Definitions.Def_RollingProbeQN_Convex_Config
-- name    : RollingProbeQN_Convex_Config
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:01.416204+00:00
-- url     : https://prove2.me/theorems/d63c6027-d44c-4617-be25-c52a735402b9
-- title:
--   The fixed data of Algorithm 1: partition, pattern, $L_1$, $L_2$, allowance $b$, $\sigma$
-- statement:
--   A configuration of Algorithm 1 records its fixed data: the column-to-group map of the partition, the pattern $\mathcal S$, the bounds $L_1,L_2$ of Assumption 2.1, the finite-difference allowance $b>0$ of (4)–(5), and the parameter $\sigma\in(0,1)$ of the relative proximal condition (2). The headline results take $b=L_2R$.
--
--   **Formalization Note** Positivity of the constants is assumed in the statements, not in the structure.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Algorithm 1 and §3.1, p. 9

import Mathlib

namespace RollingProbeQN.Convex

/-- **The fixed data of Algorithm 1.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 1 and §3.1, p. 9: "Fix `b > 0`, `σ ∈ (0, 1)`, and `M_{−1} = 0`; the headline
bounds take `b = L2 R`", together with the partition `g_1, …, g_χ`, the pattern `S` and the bounds
`L1, L2` of Assumption 2.1.

A configuration records the group map `grp`, the pattern `S`, the constants `L₁, L₂`, the
finite-difference allowance `b` of (4)–(5) and the HPE parameter `σ`.

**Formalization Note.** Positivity of the constants is not part of the structure; the statements
that use a configuration assume it. -/
structure Config (d χ : ℕ) where
  /-- the group of each column (0-based, reading R5) -/
  grp : Fin d → Fin χ
  /-- the sparsity pattern `S` -/
  S : Set (Fin d × Fin d)
  /-- the bound `L₁` on the Hessian -/
  L₁ : ℝ
  /-- the Lipschitz constant `L₂` of the Hessian -/
  L₂ : ℝ
  /-- the finite-difference allowance `b` -/
  b : ℝ
  /-- the HPE parameter `σ` -/
  σ : ℝ

end RollingProbeQN.Convex


