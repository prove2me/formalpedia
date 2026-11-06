-- Prove2me | Definitions.Def_DRSub4633_pLarge
-- name    : DRSub4633_pLarge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:20.01708+00:00
-- url     : https://prove2.me/theorems/260c43fc-3566-4117-a9cc-5396000be341
-- title:
--   The recovered large coordinate $p_i=v_i/(b+v_i)$
-- statement:
--   For the state $x$ and a large coordinate $i$ (with $v=x_L$),
--   $$p_i=\frac{v_i}{b+v_i}.$$
--
--   **Formalization Note** The formula is defined for every coordinate and used only for large ones.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eq. (10), p.10

import Mathlib
import Definitions.Def_DRSub4633_bPar

namespace DRSub4633

/-- **The recovered large coordinate `pᵢ = vᵢ/(b + vᵢ)`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, Eq. (10),
p.10, with `v = x_L`.

**Formalization Note.** `pLarge x j = x_j/(b + x_j)` is defined for every coordinate `j`; it is used
only for large coordinates (`x_j > s`). The dummy large coordinate (state `1`, see `largePos`) has
`p = 1/(b + 1)`; it never enters a formula with a nonzero coefficient. -/
noncomputable def pLarge {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) : ℝ :=
  x j / (bPar + x j)

end DRSub4633


