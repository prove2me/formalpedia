-- Prove2me | Definitions.Def_GeomRescale_St
-- name    : GeomRescale_St
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:17.689004+00:00
-- url     : https://prove2.me/theorems/3d01b927-00e0-4bb9-a3ac-2473863ae3ec
-- title:
--   The state of Algorithm 2
-- statement:
--   A state of Rescaling-SFM holds the matrices $Q$ and $R$, the ghost set $\Gamma$, the number of rescalings performed, the control point, and the registers of Algorithm 1, which include $\mu$, $W$ and the counters of the whole run.
--
--   **Formalization Note** $\Gamma$ is a list; the set of the paper is its underlying finite set.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 2, p.10

import Mathlib
import Definitions.Def_GeomRescale_VN
import Definitions.Def_GeomRescale_Mode

namespace GeomRescale

/-- The state of Algorithm Rescaling-SFM (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 2, p.10): the matrices `Q`, `R`, the set
`Γ`, the count `i` of completed rescalings, the control point `mode`, and the registers `vn`.

**Formalization Note.** `vn` holds `μ` and `W` of Algorithm 2, which are the values passed to and
returned from the call of line 5, the data `g₁, …, g_k, x, y` of the last call, and the counters of
the whole run. `Γ` is a ghost, as on p.9 ("its main purpose is for clarity during the analysis"); it
is a list, so a vector found twice appears twice, and the set `Γ` is `Γ.toFinset`. -/
structure St (n : ℕ) where
  vn : VN n
  Q : Matrix (Fin n) (Fin n) ℝ
  R : Matrix (Fin n) (Fin n) ℝ
  Γ : List (Fin n → ℝ)
  i : ℕ
  mode : Mode n

end GeomRescale


