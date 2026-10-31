-- Prove2me | Definitions.Def_DualRCD_blockInj
-- name    : DualRCD_blockInj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:45:26.556987+00:00
-- url     : https://prove2.me/theorems/6a042176-b15c-4380-a86e-7d7a30ef16c3
-- title:
--   The block embedding $U_i t$
-- statement:
--   For a block index $i\in[m]$ and $t\in\mathbb R^n$, $U_it\in\mathbb R^{mn}$ is the block vector with $t$ in block $i$ and $0$ in every other block. Here $U_i$ is the $i$th block matrix of $I_{mn}$, as usual in the coordinate descent literature. A coordinate step on block $i$ is a move $y\mapsto y+U_it$.
-- source:
--   Necoara & Fercoq, Linear convergence of dual coordinate descent on non-polyhedral convex problems, arXiv:1911.06014v1, §4, p.14

import Mathlib
import Definitions.Def_DualRCD_DualSpace

namespace DualRCD

/-- The block embedding `Uᵢ t`: the vector of `ℝ^{mn}` with `t ∈ ℝⁿ` in block `i` and `0` in every
other block (Necoara & Fercoq, arXiv:1911.06014v1, §4, p.14: "`Ui` … denotes the `i`th block matrix
of `I_{mn}`"). -/
noncomputable def blockInj {n m : ℕ} (i : Fin m) (t : EuclideanSpace ℝ (Fin n)) : DualSpace n m :=
  WithLp.toLp 2 (Pi.single i t)

end DualRCD


