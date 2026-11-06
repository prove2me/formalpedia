-- Prove2me | Definitions.Def_DRSub4633_Pminus
-- name    : DRSub4633_Pminus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:01:01.588699+00:00
-- url     : https://prove2.me/theorems/28f69d24-9ca2-4305-b610-004b06cf2a17
-- title:
--   The lower prefix vector $P_i^-$
-- statement:
--   For the state $x$ and $0\le i\le m$, the large vector $P_i^-$ equals $p$ on the large coordinates with label at most $i$ and $0$ on the others. Hence $P_0^-=\mathbf 0_L$ and $P_m^-=p$.
--
--   **Formalization Note** As for $P_i^+$: only large coordinates are read and the dummy coordinate is not represented.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, p.10

import Mathlib
import Definitions.Def_DRSub4633_sPar
import Definitions.Def_DRSub4633_largePos
import Definitions.Def_DRSub4633_pLarge

namespace DRSub4633

/-- **The lower prefix vector `P⁻ᵢ`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, p.10: "the vector `P⁻ᵢ` has its
first `i` coordinates equal to `p` and all remaining coordinates zero."

`Pminus x i j = p_j` if the large coordinate `j` has label `≤ i`, and `0` otherwise.

**Formalization Note.** As for `Pplus`: only the values on large coordinates are read, and the dummy
coordinate (label `1`) is dropped. -/
noncomputable def Pminus {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (i : ℕ) : Fin n → ℝ :=
  fun j => if sPar < x j ∧ largePos x j ≤ i then pLarge x j else 0

end DRSub4633


