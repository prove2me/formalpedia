-- Prove2me | Definitions.Def_NondualOpt_unitZ
-- name    : NondualOpt_unitZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:57:49.683505+00:00
-- url     : https://prove2.me/theorems/fae6cf87-87db-478c-b3fc-be16c4bac2e5
-- title:
--   The normalized sample space $H\times[-1,1]$
-- statement:
--   The set $H\times[-1,1]$, which is the affine sample space $Z_{X,H}$ when $\Lambda_{X,H}=1$ (the normalization of §C.1).
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, (7), p.9; §C.1, p.30

import Mathlib

namespace NondualOpt

/-- The normalized affine sample space `H × [−1, 1]`, which is `Z_{X,H}` when `Λ_{X,H} = 1`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, (7), p.9, and §C.1, p.30 ("we assume
that `Λ_{X,H} = 1`"). -/
def unitZ {F : Type*} (H : Set F) : Set (F × ℝ) :=
  H ×ˢ Set.Icc (-1 : ℝ) 1

end NondualOpt


