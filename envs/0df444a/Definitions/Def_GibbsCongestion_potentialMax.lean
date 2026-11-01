-- Prove2me | Definitions.Def_GibbsCongestion_potentialMax
-- name    : GibbsCongestion_potentialMax
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:02:06.837+00:00
-- url     : https://prove2.me/theorems/db65760c-dbd2-476b-97fa-949b08b7b3f2
-- title:
--   $\Phi_{\max}$, the maximum of Rosenthal's potential over $\mathcal P^n$
-- statement:
--   $$\Phi_{\max}=\max_{r\in\mathcal P^n}\Phi(r),$$
--   the largest value of Rosenthal's potential over all strategy profiles of $n$ players with common strategy set $\mathcal P$. It enters the mixing-time bound of the relaxed logit dynamics through $T\Phi_{\max}$.
--
--   **Formalization Note** Written as a supremum over the finite set of profiles; it is the maximum whenever that set is nonempty, as it is for every extension parallel family. For an empty strategy set with $n>0$ the supremum of the empty family is the value $0$; no statement of the mission uses that case.
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, Theorem 4.4, p.16

import Mathlib
import Definitions.Def_GibbsCongestion_potential

namespace GibbsCongestion

/-- `Φmax = max_{r ∈ Pⁿ} Φ(r)`, the largest value of Rosenthal's potential over all strategy
profiles (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, Theorem 4.4, p.16).

**Formalization Note** Written as a supremum over the finite type of profiles `Fin n → P`. It is
the maximum whenever that type is nonempty, which holds for every extension parallel family
(it is nonempty). For an empty strategy set and `n > 0` the supremum of the empty family is the
junk value `0`; no statement of the mission uses that case. -/
noncomputable def potentialMax {E : Type*} [Fintype E] [DecidableEq E] (P : Finset (Finset E)) (n : ℕ)
    (c : E → ℕ → ℝ) : ℝ :=
  ⨆ r : Fin n → P, potential c r

end GibbsCongestion


