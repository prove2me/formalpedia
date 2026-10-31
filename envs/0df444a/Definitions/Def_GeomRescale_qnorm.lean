-- Prove2me | Definitions.Def_GeomRescale_qnorm
-- name    : GeomRescale_qnorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:14:37.614352+00:00
-- url     : https://prove2.me/theorems/17a4f435-5763-47bf-9942-686bcba3bc6a
-- title:
--   The norm $\|x\|_Q$
-- statement:
--   $$\|x\|_Q = \sqrt{\langle x, x \rangle_Q}.$$
--
--   This is the norm induced by $Q$; the rescaling of Algorithm 2 changes it.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §2, p.3

import Mathlib
import Definitions.Def_GeomRescale_qdot

namespace GeomRescale

/-- The norm `‖x‖_Q = √⟨x, x⟩_Q` (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §2, p.3). -/
noncomputable def qnorm {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  √(qdot Q x x)

end GeomRescale


