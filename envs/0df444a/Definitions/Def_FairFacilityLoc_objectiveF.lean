-- Prove2me | Definitions.Def_FairFacilityLoc_objectiveF
-- name    : FairFacilityLoc_objectiveF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:11:59.509494+00:00
-- url     : https://prove2.me/theorems/9199f321-073a-42e7-9d46-7398d7a25351
-- title:
--   The objective $F$ and the optimal value $\mathrm{OPT}$, (2.1)
-- statement:
--   When the facility is at $y$, group $j$ has the distance vector $u_j(y)=(\|x_i-y\|_2)_{i\in G_j}$. The objective and the optimal value are
--   $$F(y;x,\mathcal G)=\max_j E_j(u_j(y)),\qquad \mathrm{OPT}(x,\mathcal G)=\inf_{y\in\mathbb R^d}F(y;x,\mathcal G).$$
--
--   The planner wants to minimize the largest group effect.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), (2.1), p.15 (PDF p.17); distance vector §2.1, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E
import Definitions.Def_FairFacilityLoc_GroupStructure

open scoped NNReal

namespace FairFacilityLoc

/-- The **distance vector** `u_j(y) = (∥x_i − y∥₂)_{i ∈ G_j}` of group `j` (§2.1, p.14, PDF p.16). -/
noncomputable def distanceVector {n m d : ℕ} (G : GroupStructure n m) (x : Fin n → GeoSemialgCSP.E d) (y : GeoSemialgCSP.E d)
    (j : Fin m) : ↥(G.G j) → ℝ≥0 :=
  fun i => ‖x i - y‖₊

/-- **The objective** `F(y; x, G) = max_j E_j(u_j(y))` (Yan, Zhou, manuscript, sha256 642a1268…, (2.1),
p.15, PDF p.17).

**Formalization Note.** `Finset.sup` in `ℝ≥0` over the nonempty `Fin m` is the maximum. -/
noncomputable def objectiveF {n m d : ℕ} (G : GroupStructure n m) (x : Fin n → GeoSemialgCSP.E d) (y : GeoSemialgCSP.E d) : ℝ≥0 :=
  Finset.univ.sup fun j => G.E j (distanceVector G x y j)

/-- **The optimal value** `OPT(x, G) = inf_{y ∈ ℝ^d} F(y; x, G)`, (2.1), p.15, PDF p.17.

**Formalization Note.** The infimum in `ℝ≥0` is over a nonempty index type of a family bounded below by
`0`, so it is the true infimum. -/
noncomputable def optValue {n m d : ℕ} (G : GroupStructure n m) (x : Fin n → GeoSemialgCSP.E d) : ℝ≥0 :=
  ⨅ y : GeoSemialgCSP.E d, objectiveF G x y

end FairFacilityLoc


