-- Prove2me | Definitions.Def_NieYangPareto_MOP_V
-- name    : NieYangPareto_MOP_V
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:46.0956+00:00
-- url     : https://prove2.me/theorems/3915c418-24bb-45b3-93e4-84424d560eb3
-- title:
--   The degree $d$ of the objectives and the set $\mathcal V$ of (3.4)
-- statement:
--   Let $d$ be the maximum degree of the objectives $f_1,\dots,f_m$. The set $\mathcal V$ is
--
--   $$
--   \mathcal V:=\Big\{v=(v_1,\dots,v_m)\ \Big|\ v_i>\langle f_i,y\rangle,\ i=1,\dots,m,\ \ y_0=1,\ y\in\mathscr R_d(K)\Big\}.
--   $$
--
--   Thus $v\in\mathcal V$ when $v$ strictly dominates, coordinate by coordinate, the vector of means of the $f_i$ under some probability measure on $K$. Theorem 3.2 identifies $\mathcal V$ with the interior of $\operatorname{conv}(\mathcal U)$.
--
--   **Formalization Note** $d$ is computed from the $f_i$; it is not a parameter of $\mathcal V$. It equals $0$ when $m=0$.
-- source:
--   Nie–Yang, The multi-objective polynomial optimization, arXiv:2108.04336v2, §3.2 after (3.2), p.8 (d); eq. (3.4), p.8

import Mathlib
import Definitions.Def_NieYangPareto_MOP
import Definitions.Def_NieYangPareto_momentCone

namespace NieYangPareto

variable {n m : ℕ} {E I : Type*}

/-- The degree `d` of §3.2: "Let `d` be the maximum degree of objectives `f_i`", Nie–Yang,
arXiv:2108.04336v2, §3.2 after (3.2), p.8.

**Formalization Note** `Finset.sup` of the total degrees; it is `0` when `m = 0`. -/
noncomputable def MOP.d (P : MOP n m E I) : ℕ :=
  Finset.univ.sup fun i => (P.f i).totalDegree

/-- **The set `𝒱` (3.4).** Nie–Yang, arXiv:2108.04336v2, eq. (3.4), p.8: the `v` such that
`v_i > ⟨f_i, y⟩` for `i = 1, …, m`, `y₀ = 1`, `y ∈ ℛ_d(K)`, for `d` the maximum degree of the
objectives. -/
noncomputable def MOP.V (P : MOP n m E I) : Set (Fin m → ℝ) :=
  {v | ∃ y ∈ momentCone P.K P.d, y (TmsIndex.zero n P.d) = 1 ∧ ∀ i, pair (P.f i) y < v i}

end NieYangPareto


