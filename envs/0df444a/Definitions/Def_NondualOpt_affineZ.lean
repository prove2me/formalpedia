-- Prove2me | Definitions.Def_NondualOpt_affineZ
-- name    : NondualOpt_affineZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:35.800241+00:00
-- url     : https://prove2.me/theorems/6a413a02-6b9d-4651-8c1a-e7c6a118b883
-- title:
--   The affine sample space $Z_{X,H}=H\times[-\Lambda_{X,H},\Lambda_{X,H}]$
-- statement:
--   The **affine sample space** is
--   $$
--   Z_{X,H}=H\times[-\Lambda_{X,H},\Lambda_{X,H}] .
--   $$
--   A point $z=(g,b)\in Z_{X,H}$ indexes the affine loss $u\mapsto\langle g,u\rangle+b$; the adversary of the affine max-regret game plays points of $Z_{X,H}$.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, (7), p.9

import Mathlib
import Definitions.Def_NondualOpt_crossDuality

namespace NondualOpt

/-- The affine sample space `Z_{X,H} = H × [−Λ_{X,H}, Λ_{X,H}]`: a pair `(g, b)` indexes the
affine loss `u ↦ ⟨g, u⟩ + b`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, (7), p.9. -/
def affineZ {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (pair : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) (X : Set E) (H : Set F) : Set (F × ℝ) :=
  H ×ˢ Set.Icc (-crossDuality pair X H) (crossDuality pair X H)

end NondualOpt


