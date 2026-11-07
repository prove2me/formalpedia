-- Prove2me | Definitions.Def_QuasiStrictNE_Cm
-- name    : QuasiStrictNE_Cm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:08:21.251436+00:00
-- url     : https://prove2.me/theorems/22c1f0ab-5ce4-45f2-9af3-e6a5b3a23462
-- title:
--   The complex $\mathcal C_m$ of faces of the regions $P_j$
-- statement:
--   $\mathcal C_m$ consists of all nonempty faces of the nonempty best-response regions $P_j\subseteq\Delta_m$, $j\in N$. It is a polyhedral complex covering $\Delta_m$ (p.10).
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), §3, p.10

import Mathlib
import Definitions.Def_ProxFlatIP_Spindle
import Definitions.Def_QuasiStrictNE_Pregion

namespace QuasiStrictNE

/-- **The polyhedral complex `Cm` on player 1's simplex** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, §3, p.10: "let Cm consist of
all nonempty faces of the nonempty Pj").

`Cm B` is the set of all nonempty faces of the nonempty best-response regions `Pregion B j`,
`j ∈ N`.

**Formalization Note** Faces are the public `ProxFlatIP.IsFace` (nonempty exposed subsets), which for
a polytope given by linear inequalities are exactly the faces of Definition 3. -/
def Cm {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) : Set (Set (Fin m → ℝ)) :=
  {F | ∃ j, (Pregion B j).Nonempty ∧ ProxFlatIP.IsFace (Pregion B j) F}

end QuasiStrictNE


