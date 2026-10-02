-- Prove2me | Definitions.Def_ServiceParts_RealTime_ESAM
-- name    : ServiceParts_RealTime_ESAM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T23:56:57.837992+00:00
-- url     : https://prove2.me/theorems/97dffabc-0749-41fc-98a1-c5f9dabb9d7f
-- title:
--   The extended stock allocation model ESAM_i (10.38)–(10.42) with regular and expedited shipments
-- statement:
--   For one item $i$, the **extended stock allocation model** $\mathrm{ESAM}_i$ chooses nonnegative integers $y^r_{ijt}$ and $y^e_{ijt}$, the units shipped from the depot warehouse to base $j$ in period $t = 0, \dots, T_{i0}$ by regular and by expedited transport. The cumulative supply at base $j$ through period $t$ is
--   $$S_{ijt} = \tilde S_{ijt} + \sum_{t'=0}^{\min(t - T^e_{ij},\, T_{i0})} y^e_{ijt'}, \qquad t = T^e_{ij}, \dots, T^r_{ij} - 1, \tag{10.40}$$
--   $$S_{ijt} = \tilde S_{ij(T^r_{ij}-1)} + \sum_{t'=0}^{t - T^r_{ij}} y^r_{ijt'} + \sum_{t'=0}^{\min(t - T^e_{ij},\, T_{i0})} y^e_{ijt'}, \qquad t = T^r_{ij}, \dots, T^r_{ij} + T_{i0}. \tag{10.41}$$
--   A plan is feasible when
--   $$\tilde S_{i0t} \ge \sum_{j \in J} \sum_{t'=0}^{t} \big(y^r_{ijt'} + y^e_{ijt'}\big), \qquad t = 0, \dots, T_{i0}, \tag{10.39}$$
--   and $\mathrm{ESAM}_i$ minimizes
--   $$\sum_{j\in J} \Big\{ \sum_{t = T^e_{ij}}^{T^r_{ij}+T_{i0}} G_{ijt}(S_{ijt}) + Q_{ij}\big(S_{ij(T^r_{ij}+T_{i0})}\big) + \sum_{t=0}^{T_{i0}} e_{ij}\, y^e_{ijt} \Big\} \tag{10.38}$$
--   over feasible plans. An optimal solution is a feasible plan whose objective is at most that of every feasible plan.
--
--   **Formalization Note** Shipments are functions `J → ℕ → ℕ`; the cumulative supply is one function of $t$ with the two cases (10.40) and (10.41), used for $t = T^e_{ij}, \dots, T^r_{ij} + T_{i0}$.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 243, Section 10.5.1, (10.38)-(10.42)

import Mathlib
import Definitions.Def_ServiceParts_RealTime_Model

open MeasureTheory

namespace ServiceParts.RealTime

variable {J : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The cumulative supply `S_{ijt}` at base `j` through period `t` in the extended stock
allocation model, for regular shipments `yr j t' = y^r_{ijt'}` and expedited shipments
`ye j t' = y^e_{ijt'}` (constraints (10.40)–(10.41), p. 243):
for `t = T^e_{ij}, …, T^r_{ij} - 1`,
`S_{ijt} = S̃_{ijt} + Σ_{t'=0}^{min(t - T^e_{ij}, T_{i0})} y^e_{ijt'}`;
for `t = T^r_{ij}, …, T^r_{ij} + T_{i0}`,
`S_{ijt} = S̃_{ij(T^r_{ij}-1)} + Σ_{t'=0}^{t - T^r_{ij}} y^r_{ijt'}
  + Σ_{t'=0}^{min(t - T^e_{ij}, T_{i0})} y^e_{ijt'}`. -/
def esamStock (M : ItemModel J Ω P) (yr ye : J → ℕ → ℕ) (j : J) (t : ℕ) : ℤ :=
  if t < M.Tr j then
    M.baseSupply j t + ∑ t' ∈ Finset.range (min (t - M.Te j) M.T0 + 1), (ye j t' : ℤ)
  else
    M.baseSupply j (M.Tr j - 1) + ∑ t' ∈ Finset.range (t - M.Tr j + 1), (yr j t' : ℤ)
      + ∑ t' ∈ Finset.range (min (t - M.Te j) M.T0 + 1), (ye j t' : ℤ)

/-- Feasibility for `ESAM_i` (10.39)–(10.42), p. 243: regular and expedited shipments are
nonnegative integers (the type `ℕ`), and for `t = 0, …, T_{i0}`,
`S̃_{i0t} ≥ Σ_{j∈J} Σ_{t'=0}^{t} (y^r_{ijt'} + y^e_{ijt'})`. -/
def ESAMFeasible [Fintype J] (M : ItemModel J Ω P) (yr ye : J → ℕ → ℕ) : Prop :=
  ∀ t : ℕ, t ≤ M.T0 →
    ∑ j, ∑ t' ∈ Finset.range (t + 1), ((yr j t' : ℤ) + (ye j t' : ℤ)) ≤ M.depotSupply t

/-- The objective (10.38) of `ESAM_i`, p. 243:
`Σ_{j∈J} { Σ_{t=T^e_{ij}}^{T^r_{ij}+T_{i0}} G_{ijt}(S_{ijt}) + Q_{ij}(S_{ij(T^r_{ij}+T_{i0})})
  + Σ_{t=0}^{T_{i0}} e_{ij} y^e_{ijt} }`. -/
noncomputable def esamObjective [Fintype J] (M : ItemModel J Ω P) (yr ye : J → ℕ → ℕ) : ℝ :=
  ∑ j, ((∑ t ∈ Finset.Icc (M.Te j) (M.Tr j + M.T0), M.G j t (esamStock M yr ye j t))
    + M.Q j (esamStock M yr ye j (M.Tr j + M.T0))
    + ∑ t ∈ Finset.range (M.T0 + 1), M.e j * (ye j t : ℝ))

/-- `(yr, ye)` is an optimal solution of `ESAM_i`: feasible, with objective value at most that
of every feasible solution. -/
def IsESAMOptimal [Fintype J] (M : ItemModel J Ω P) (yr ye : J → ℕ → ℕ) : Prop :=
  ESAMFeasible M yr ye ∧
    ∀ yr' ye' : J → ℕ → ℕ, ESAMFeasible M yr' ye' →
      esamObjective M yr ye ≤ esamObjective M yr' ye'

end ServiceParts.RealTime


