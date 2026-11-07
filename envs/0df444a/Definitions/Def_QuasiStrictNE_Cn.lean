-- Prove2me | Definitions.Def_QuasiStrictNE_Cn
-- name    : QuasiStrictNE_Cn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:08:06.918331+00:00
-- url     : https://prove2.me/theorems/160058de-5fc4-4de2-88c6-edc5c76109ea
-- title:
--   The complex $\mathcal C_n$ of faces of the regions $Q_i$
-- statement:
--   $\mathcal C_n$ consists of all nonempty faces of the nonempty best-response regions $Q_i\subseteq\Delta_n$, $i\in M$. It is a polyhedral complex covering $\Delta_n$ (p.10).
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), §3, p.10

import Mathlib
import Definitions.Def_ProxFlatIP_Spindle
import Definitions.Def_QuasiStrictNE_Qregion

namespace QuasiStrictNE

/-- **The polyhedral complex `Cn` on player 2's simplex** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, §3, p.10: "Let Cn consist of
all nonempty faces of the nonempty Qi").

`Cn A` is the set of all nonempty faces of the nonempty best-response regions `Qregion A i`,
`i ∈ M`.

**Formalization Note** Faces are the public `ProxFlatIP.IsFace` (nonempty exposed subsets), which for
a polytope given by linear inequalities are exactly the faces of Definition 3. -/
def Cn {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Set (Set (Fin n → ℝ)) :=
  {G | ∃ i, (Qregion A i).Nonempty ∧ ProxFlatIP.IsFace (Qregion A i) G}

end QuasiStrictNE


