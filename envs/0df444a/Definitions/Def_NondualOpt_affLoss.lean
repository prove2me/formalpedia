-- Prove2me | Definitions.Def_NondualOpt_affLoss
-- name    : NondualOpt_affLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:57:41.032004+00:00
-- url     : https://prove2.me/theorems/4eb13209-60e6-41da-8837-16602584118a
-- title:
--   The affine loss $\ell_z(u)=\langle g,u\rangle+b$
-- statement:
--   For $z=(g,b)$ the **affine loss** indexed by $z$ is
--   $$
--   \ell_z(u)=\langle g,u\rangle+b .
--   $$
--   The loss class of Assumption 3 is $\mathcal F=\{\ell_z:z\in Z_{X,H}\}$.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, (7) and Assumption 3, p.9

import Mathlib

namespace NondualOpt

/-- The affine loss `ℓ_z(u) = ⟨g, u⟩ + b` indexed by `z = (g, b)`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, (7), p.9, and the loss class
`F = {x ↦ ⟨g, x⟩ + b : (g, b) ∈ Z_{X,H}}` of Assumption 3, p.9. -/
def affLoss {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (pair : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) (z : F × ℝ) (u : E) : ℝ :=
  pair z.1 u + z.2

end NondualOpt


