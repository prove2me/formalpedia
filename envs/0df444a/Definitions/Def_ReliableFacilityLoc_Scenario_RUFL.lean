-- Prove2me | Definitions.Def_ReliableFacilityLoc_Scenario_RUFL
-- name    : ReliableFacilityLoc_Scenario_RUFL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:57.560976+00:00
-- url     : https://prove2.me/theorems/3690b6a4-2d31-4746-8213-9b2244d95a2b
-- title:
--   The compact reliability UFL formulation (RUFL) (1a)–(1g), its feasibility and optimality
-- statement:
--   Fix the data of the reliable facility location model: customers $i = 0,\dots,I-1$ with demand rates $\lambda_i \ge 0$, regular sites $j = 0,\dots,J-1$ with fixed costs $f_j$ and failure probabilities $0 \le q_j < 1$, unit costs $d_{ij}$, and the emergency facility $J$ with $f_J = 0$, $q_J = 0$, $d_{iJ} = \phi_i$; levels $r = 0,\dots,R$ with $R \ge 1$. A level-$r$ assignment serves the customer exactly when all her assignments at levels $0,\dots,r-1$ have failed.
--
--   **Variables.** $X_j \in \{0,1\}$ (site $j$ open, $0 \le j \le J-1$), $Y_{ijr} \in \{0,1\}$ (facility $j$ assigned to customer $i$ at level $r$) and $P_{ijr}$ (the probability that facility $j$ serves customer $i$ at level $r$), for $0 \le j \le J$, $0 \le r \le R$.
--
--   **(RUFL).** Minimize
--   $$\Phi(X,Y,P) = \sum_{j=0}^{J-1} f_j X_j + \sum_{i=0}^{I-1}\sum_{j=0}^{J}\sum_{r=0}^{R} \lambda_i d_{ij} P_{ijr} Y_{ijr} \qquad (1a)$$
--   subject to, for every customer $i$:
--   1. $\sum_{j=0}^{J} Y_{ijr} + \sum_{s=0}^{r-1} Y_{iJs} = 1$ for $0 \le r \le R$ (1b);
--   2. $\sum_{r=0}^{R-1} Y_{ijr} \le X_j$ for $0 \le j \le J-1$ (1c);
--   3. $\sum_{r=0}^{R} Y_{iJr} = 1$ (1d);
--   4. $P_{ij0} = 1 - q_j$ for $0 \le j \le J$ (1e);
--   5. $P_{ijr} = (1-q_j)\sum_{k=0}^{J-1} \frac{q_k}{1-q_k} P_{i,k,r-1} Y_{i,k,r-1}$ for $0 \le j \le J$, $1 \le r \le R$ (1f);
--   6. $X_j, Y_{ijr} \in \{0,1\}$ (1g).
--
--   A triple $(X,Y,P)$ is **feasible** if it satisfies (1b)–(1g), and **optimal** if it is feasible and $\Phi(X,Y,P) \le \Phi(X',Y',P')$ for every feasible $(X',Y',P')$.
--
--   This is the compact, polynomial-size formulation of the mission; Proposition 1 compares its optimal value with that of the scenario-based program (SSP).
--
--   **Formalization Note** The page prints the first sum of (1b) with upper limit $J-1$ (regular facilities only). That is a typo: with it, the level holding the emergency facility would also have to hold a regular facility, contradicting the paper's own reading of (1b) on p. 9 ("either $i$ is assigned to a regular facility at level $r$ or she is assigned to the emergency facility $J$ at certain level $s < r$") and "$j(i,r)$ is the unique facility that serves customer $i$ at level $r$" (A.1, p. 33). Here the sum runs to $J$. The $P_{ijr}$ are variables pinned down by (1e)–(1f) for every facility, assigned or not. $X$ is indexed by the regular sites only; $X$, $Y$ are real-valued with each entry $0$ or $1$.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), §3.1, pp. 8–9 (PDF 10–11), (RUFL) (1a)–(1g); (1b) corrected

import Definitions.Def_ReliableFacilityLoc_Scenario_Instance

open Finset

namespace ReliableFacilityLoc.Scenario

namespace Instance

variable {I J R : ℕ} (D : Instance I J R)

/-- The objective (1a) of (RUFL), Cui–Ouyang–Shen, UCTC-FR-2010-02 (Feb. 2010), p. 8 (PDF 10):
`Φ(X, Y, P) = Σ_{j=0}^{J-1} f_j X_j + Σ_{i=0}^{I-1} Σ_{j=0}^{J} Σ_{r=0}^{R} λ_i d_ij P_ijr Y_ijr`.

Formalization Note: `X` is indexed by the regular facilities only (the emergency facility has
`f_J = 0` and the printed first sum stops at `J - 1`); `Y` and `P` are indexed by customer,
facility in `Fin (J+1)` (the last index is the emergency facility) and level in `Fin (R+1)`. -/
def ruflObjective (X : Fin J → ℝ) (Y P : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) : ℝ :=
  ∑ j, D.f j * X j + ∑ i, ∑ j, ∑ r, D.lam i * D.dExt i j * P i j r * Y i j r

/-- Feasibility for (RUFL), constraints (1b)–(1g), pp. 8–9 (PDF 10–11).

Formalization Note: (1b) is printed as `Σ_{j=0}^{J-1} Y_ijr + Σ_{s=0}^{r-1} Y_iJs = 1`, with the
first sum over the regular facilities only. It is stated here with the first sum over **all**
facilities `j = 0, …, J`, including the emergency facility. With the printed range, the level at
which the emergency facility is assigned would also have to hold a regular facility, contradicting
the paper's own reading on p. 9 ("either i is assigned to a regular facility at level r or she is
assigned to the emergency facility J at certain level s < r"), the assignment it describes on p. 8
(regular facilities at levels `0, …, R-1`, then `J` at level `R`), and "j(i,r) is the unique
facility that serves customer i at level r" (A.1, p. 33). The sum over `s < r` is empty for
`r = 0`, as the paper stipulates. In (1f) the level `r ∈ {1, …, R}` is written `r.succ` for
`r : Fin R`, and `r - 1` is `r.castSucc`; the sum is over the regular facilities `k = 0, …, J-1`, as
printed, and (1f) is imposed for every facility `j = 0, …, J`, assigned or not. `P` is a variable
pinned down by (1e)–(1f), as in the paper. (1g) keeps `X`, `Y` real-valued and requires each entry
to be `0` or `1`. -/
structure IsRUFLFeasible (X : Fin J → ℝ) (Y P : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) :
    Prop where
  /-- (1b), with the first sum over all `j = 0, …, J` -/
  level_one : ∀ i r, ∑ j, Y i j r + ∑ s ∈ Iio r, Y i (Fin.last J) s = 1
  /-- (1c): `Σ_{r=0}^{R-1} Y_ijr ≤ X_j` for regular `j` -/
  open_only : ∀ i (j : Fin J), ∑ r ∈ Iio (Fin.last R), Y i j.castSucc r ≤ X j
  /-- (1d): `Σ_{r=0}^{R} Y_iJr = 1` -/
  emergency_once : ∀ i, ∑ r, Y i (Fin.last J) r = 1
  /-- (1e): `P_ij0 = 1 - q_j` -/
  prob_zero : ∀ i j, P i j 0 = 1 - D.qExt j
  /-- (1f): `P_ijr = (1 - q_j) Σ_{k=0}^{J-1} q_k/(1-q_k) P_{i,k,r-1} Y_{i,k,r-1}` for `1 ≤ r ≤ R` -/
  prob_succ : ∀ i j (r : Fin R), P i j r.succ =
    (1 - D.qExt j) * ∑ k : Fin J,
      D.q k / (1 - D.q k) * P i k.castSucc r.castSucc * Y i k.castSucc r.castSucc
  /-- (1g): `X_j ∈ {0, 1}` -/
  X_binary : ∀ j, X j = 0 ∨ X j = 1
  /-- (1g): `Y_ijr ∈ {0, 1}` -/
  Y_binary : ∀ i j r, Y i j r = 0 ∨ Y i j r = 1

/-- An optimal solution of (RUFL): a feasible `(X, Y, P)` whose objective (1a) is at most that of
every feasible solution. -/
def IsRUFLOptimal (X : Fin J → ℝ) (Y P : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) : Prop :=
  D.IsRUFLFeasible X Y P ∧
    ∀ X' Y' P', D.IsRUFLFeasible X' Y' P' → D.ruflObjective X Y P ≤ D.ruflObjective X' Y' P'

end Instance

end ReliableFacilityLoc.Scenario


