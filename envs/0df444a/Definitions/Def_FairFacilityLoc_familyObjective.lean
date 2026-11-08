-- Prove2me | Definitions.Def_FairFacilityLoc_familyObjective
-- name    : FairFacilityLoc_familyObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:50.559603+00:00
-- url     : https://prove2.me/theorems/f7ba8f4c-9f88-447a-a742-a79cd1a5b343
-- title:
--   Weighted total distance and objective over a family
-- statement:
--   Under a weight vector $a$, the weighted total distance at $p\in\mathbb R^d$ is $C_a(p)=\sum_{i\in N}a_i\|x_i-p\|_2$. The objective over a family $W$ is $F_W(p)=\max_{a\in W}C_a(p)$.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), §3.3, p.47 (PDF p.49)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E

namespace FairFacilityLoc

/-- The **weighted total distance** `C_a(p) = ∑_{i ∈ N} a_i ∥x_i − p∥₂` (Yan, Zhou, manuscript, sha256
642a1268…, §3.3, p.47, PDF p.49). -/
noncomputable def weightedDistance {n d : ℕ} (x : Fin n → GeoSemialgCSP.E d) (a : Fin n → ℝ) (p : GeoSemialgCSP.E d) : ℝ :=
  ∑ i, a i * ‖x i - p‖

/-- The **objective over a family** `F_W(p) = max_{a ∈ W} C_a(p)`, §3.3, p.47, PDF p.49.

**Formalization Note.** `sSup` over a finite family is a maximum when `W` is nonempty, as it is in every
statement. -/
noncomputable def familyObjective {n d : ℕ} (x : Fin n → GeoSemialgCSP.E d) (W : Finset (Fin n → ℝ)) (p : GeoSemialgCSP.E d) : ℝ :=
  sSup ((fun a => weightedDistance x a p) '' (W : Set (Fin n → ℝ)))

end FairFacilityLoc


