-- Prove2me | Definitions.Def_DRSub4633_Pplus
-- name    : DRSub4633_Pplus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:19.005116+00:00
-- url     : https://prove2.me/theorems/31b3cf71-7e27-4ceb-aba4-03fbee5c4e0f
-- title:
--   The upper prefix vector $P_i^+$
-- statement:
--   For the state $x$ and $0\le i\le m$, the large vector $P_i^+$ equals $p$ on the large coordinates with label at most $i$ and $1$ on the others. Hence $P_0^+=\mathbf 1_L$ and $P_m^+=p$.
--
--   **Formalization Note** Large vectors are represented on all coordinates; only their large coordinates are read. The dummy coordinate is not represented, so $P_0^+$ and $P_1^+$ coincide.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, p.10

import Mathlib
import Definitions.Def_DRSub4633_sPar
import Definitions.Def_DRSub4633_largePos
import Definitions.Def_DRSub4633_pLarge

namespace DRSub4633

/-- **The upper prefix vector `P⁺ᵢ`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, p.10: "The vector `P⁺ᵢ` has the
same first `i` coordinates [equal to `p`] and all remaining coordinates equal to one."

`Pplus x i j = p_j` if the large coordinate `j` has label `≤ i`, and `1` otherwise.

**Formalization Note.** A large vector is represented by a function on all of `Fin n`; only its
values on the large coordinates are read (`mergePt`). The dummy coordinate (label `1`) is dropped:
no function is evaluated at it. Hence `P⁺₀` and `P⁺₁` agree on the original coordinates. -/
noncomputable def Pplus {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (i : ℕ) : Fin n → ℝ :=
  fun j => if sPar < x j ∧ largePos x j ≤ i then pLarge x j else 1

end DRSub4633


