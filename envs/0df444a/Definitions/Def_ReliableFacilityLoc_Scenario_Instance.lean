-- Prove2me | Definitions.Def_ReliableFacilityLoc_Scenario_Instance
-- name    : ReliableFacilityLoc_Scenario_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:19.511117+00:00
-- url     : https://prove2.me/theorems/51d98657-49b8-4ec7-bba5-4a18456c5bf7
-- title:
--   Data of the reliable facility location model with an emergency facility
-- statement:
--   **Data** (Cui, Ouyang and Shen, §3.1, pp. 7–8). There are $I$ customers $i = 0,\dots,I-1$ with demand rates $\lambda_i \ge 0$, and $J$ candidate facility sites $j = 0,\dots,J-1$ with fixed location costs $f_j$ and failure probabilities $0 \le q_j < 1$. Facility failures are independent. Shipping a unit of demand from site $j$ to customer $i$ costs $d_{ij}$, and every unit of missed demand of customer $i$ costs a penalty $\phi_i$. Each customer is assigned to up to $R \ge 1$ regular facilities.
--
--   An **emergency facility**, indexed $j = J$, models the penalty: it has fixed cost $f_J = 0$, failure probability $q_J = 0$ and unit cost $d_{iJ} = \phi_i$. The extended data are
--   $$d_{ij}\ (0 \le j \le J-1),\quad d_{iJ} = \phi_i, \qquad q_j\ (0 \le j \le J-1),\quad q_J = 0.$$
--
--   These are the data shared by the compact formulation (RUFL) and the scenario-based stochastic program (SSP) of this mission.
--
--   **Formalization Note** Indices are 0-based; the emergency facility is the last of the $J+1$ facility indices, and $d_{iJ} = \phi_i$, $q_J = 0$ are definitions, not hypotheses. The paper calls $\lambda_i$ a demand rate without stating its sign; $\lambda_i \ge 0$ is added as the standing convention for a rate. No sign is assumed on $d$, $\phi$ or $f$.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), §3.1, pp. 7–8 (PDF 9–10)

import Mathlib

open Finset

namespace ReliableFacilityLoc.Scenario

/-- The data of the reliability uncapacitated facility location problem of Cui, Ouyang and Shen,
*Reliable Facility Location Design under the Risk of Disruptions*, UCTC-FR-2010-02 (Feb. 2010),
§3.1, pp. 7–8 (PDF 9–10): `I` customers `i : Fin I` with demand rates `lam i ≥ 0`; `J` candidate
(regular) facility sites `j : Fin J` with fixed location costs `f j` and failure probabilities
`0 ≤ q j < 1` (p. 8, "the probability of failure 0 ≤ q_j < 1"); unit shipping costs `d i j`; the
penalty `phi i` per unit of missed demand of customer `i`; and the number `R ≥ 1` of regular
assignments (p. 8, "Each customer is assigned to up to R ≥ 1 facilities"), so that the assignment
levels are `r = 0, …, R`.

Formalization Note: the paper's emergency facility `J` (fixed cost `f_J = 0`, failure probability
`q_J = 0`, unit cost `d_iJ = φ_i`, p. 8) is not a field: it is the index `Fin.last J` of
`Fin (J+1)`, and its data are built into `dExt` and `qExt` below, so these conventions are
definitional. The paper calls `λ_i` a demand rate and never states its sign; `0 ≤ λ_i` is added as
the standing convention for a rate. No sign is assumed on `d`, `phi` or `f`. Facility failures are
independent (p. 8); this enters through the transition probabilities (1f) of (RUFL) and the product
form of the scenario probabilities of (SSP). -/
structure Instance (I J R : ℕ) where
  /-- demand rate `λ_i` -/
  lam : Fin I → ℝ
  /-- unit cost `d_ij` from regular facility `j` to customer `i` -/
  d : Fin I → Fin J → ℝ
  /-- penalty `φ_i` per unit of missed demand -/
  phi : Fin I → ℝ
  /-- fixed location cost `f_j` -/
  f : Fin J → ℝ
  /-- failure probability `q_j` -/
  q : Fin J → ℝ
  lam_nonneg : ∀ i, 0 ≤ lam i
  q_nonneg : ∀ j, 0 ≤ q j
  q_lt_one : ∀ j, q j < 1
  one_le_R : 1 ≤ R

namespace Instance

variable {I J R : ℕ} (D : Instance I J R)

/-- The unit cost `d_ij` extended to all `J + 1` facilities: `d_iJ = φ_i` for the emergency
facility `J = Fin.last J` (p. 8). -/
def dExt (i : Fin I) : Fin (J + 1) → ℝ :=
  Fin.lastCases (D.phi i) (fun j => D.d i j)

/-- The failure probability extended to all `J + 1` facilities: `q_J = 0` for the emergency
facility (p. 8). -/
def qExt : Fin (J + 1) → ℝ :=
  Fin.lastCases 0 D.q

end Instance

end ReliableFacilityLoc.Scenario


