-- Prove2me | Definitions.Def_ReliableFacilityLoc_LevelOrder_RUFL
-- name    : ReliableFacilityLoc_LevelOrder_RUFL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:21.281713+00:00
-- url     : https://prove2.me/theorems/bde58118-63bd-4c64-b6b8-7a860e9e9e86
-- title:
--   The reliability UFL problem (RUFL) (1a)–(1g) with the emergency facility, its objective, feasibility and optimality
-- statement:
--   **Data** (Cui, Ouyang and Shen, §3.1, pp. 7–8). There are $I$ customers $i = 0,\dots,I-1$ with demand rates $\lambda_i \ge 0$ and $J$ candidate facility sites $j = 0,\dots,J-1$ with fixed location costs $f_j$ and failure probabilities $0 \le q_j < 1$; facility failures are independent. Shipping a unit of demand from site $j$ to customer $i$ costs $d_{ij}$, and every unit of unserved demand of customer $i$ costs a penalty $\phi_i$. An **emergency facility**, indexed $j = J$, never fails and serves at the penalty: $f_J = 0$, $q_J = 0$, $d_{iJ} = \phi_i$. Each customer is assigned at levels $r = 0,\dots,R$ with $R \ge 1$; a level-$r$ assignment serves her exactly when all her assignments at levels $0,\dots,r-1$ have failed.
--
--   **Variables.** $X_j \in \{0,1\}$ (site $j$ open), $Y_{ijr} \in \{0,1\}$ (facility $j$ assigned to customer $i$ at level $r$) and $P_{ijr}$ (the probability that facility $j$ serves customer $i$ at level $r$), for $0 \le j \le J$ and $0 \le r \le R$.
--
--   **(RUFL).** Minimize
--   $$\Phi(X,Y,P) = \sum_{j=0}^{J-1} f_j X_j + \sum_{i=0}^{I-1}\sum_{j=0}^{J}\sum_{r=0}^{R} \lambda_i d_{ij} P_{ijr} Y_{ijr} \qquad (1a)$$
--   subject to, for all $i$,
--   1. $\sum_{j=0}^{J} Y_{ijr} + \sum_{s=0}^{r-1} Y_{iJs} = 1$ for $0 \le r \le R$ (1b): at each level the customer has one facility, unless she already reached the emergency facility;
--   2. $\sum_{r=0}^{R-1} Y_{ijr} \le X_j$ for $0 \le j \le J-1$ (1c): only open sites are used, each at most once;
--   3. $\sum_{r=0}^{R} Y_{iJr} = 1$ (1d): the emergency facility is assigned at exactly one level;
--   4. $P_{ij0} = 1 - q_j$ for $0 \le j \le J$ (1e);
--   5. $P_{ijr} = (1-q_j)\sum_{k=0}^{J-1} \frac{q_k}{1-q_k} P_{i,k,r-1} Y_{i,k,r-1}$ for $0 \le j \le J$, $1 \le r \le R$ (1f);
--   6. $X_j, Y_{ijr} \in \{0,1\}$ (1g).
--
--   A solution $(X,Y,P)$ is **feasible** if it satisfies (1b)–(1g), and **optimal** if it is feasible and $\Phi(X,Y,P) \le \Phi(X',Y',P')$ for every feasible $(X',Y',P')$.
--
--   This is the model of every statement in the mission; Proposition 2 is a statement about its optimal solutions.
--
--   **Formalization Note** Indices are 0-based; the emergency facility is the last index of the $J+1$ facilities, and the extended costs $d_{iJ} = \phi_i$, $q_J = 0$ are definitions, not hypotheses. $X$ is indexed by the regular sites only. The page prints the first sum of (1b) up to $J-1$; that is a typo (with it, (1b) would force a regular facility at the same level as the emergency facility, so the assignment the paper describes on p. 8, regular facilities at levels $0,\dots,R-1$ and then $J$ at level $R$, would be infeasible; the paper's own reading of (1b) on p. 9 is the corrected one), and the sum here runs to $J$. $X$ and $Y$ are real-valued with each entry required to be $0$ or $1$.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), §3.1, pp. 7–9 (PDF 9–11), (RUFL) (1a)–(1g); (1b) corrected

import Mathlib

open Finset

namespace ReliableFacilityLoc.LevelOrder

/-- The data of the reliability uncapacitated facility location problem (RUFL) of Cui, Ouyang and
Shen, *Reliable Facility Location Design under the Risk of Disruptions*, UCTC-FR-2010-02 (Feb. 2010),
§3.1, pp. 7–8 (PDF 9–10): `I` customers `i : Fin I` with demand rates `lam i ≥ 0`; `J` candidate
(regular) facility sites `j : Fin J` with fixed costs `f j` and failure probabilities `0 ≤ q j < 1`;
unit transportation costs `d i j`; the per-unit penalty `phi i` of not serving customer `i`; and the
number `R ≥ 1` of assignment levels beyond level `0` (levels are `r = 0, …, R`).

Formalization Note: the paper's emergency facility `J` (fixed cost `0`, failure probability `0`,
unit cost `φ_i`, p. 8) is not a field: it is the index `Fin.last J` of `Fin (J+1)`, and its data
are built into `dExt` and `qExt` below. No sign is assumed on `d`, `phi` or `f`. Facility failures
are independent (p. 8); this is encoded by the product form of the transition probabilities (1f). -/
structure Instance (I J R : ℕ) where
  /-- demand rate `λ_i` -/
  lam : Fin I → ℝ
  /-- unit cost `d_ij` from regular facility `j` to customer `i` -/
  d : Fin I → Fin J → ℝ
  /-- penalty `φ_i` per unit of unserved demand -/
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

/-- The failure probability extended to all `J + 1` facilities: `q_J = 0` (p. 8). -/
def qExt : Fin (J + 1) → ℝ :=
  Fin.lastCases 0 D.q

/-- The objective (1a) of (RUFL), p. 8:
`Φ(X, Y, P) = Σ_{j=0}^{J-1} f_j X_j + Σ_{i=0}^{I-1} Σ_{j=0}^{J} Σ_{r=0}^{R} λ_i d_ij P_ijr Y_ijr`.

Formalization Note: `X` is indexed by the regular facilities only (the emergency facility has
`f_J = 0` and the printed sum stops at `J - 1`); `Y` and `P` are indexed by customer, facility in
`Fin (J+1)` and level in `Fin (R+1)`. -/
def objective (X : Fin J → ℝ) (Y P : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) : ℝ :=
  ∑ j, D.f j * X j + ∑ i, ∑ j, ∑ r, D.lam i * D.dExt i j * P i j r * Y i j r

/-- Feasibility for (RUFL), constraints (1b)–(1g), pp. 8–9 (PDF 10–11).

Formalization Note: (1b) is printed with the first sum over `j = 0, …, J - 1`; it is stated here
with the sum over **all** facilities `j = 0, …, J`, including the emergency facility. With the
printed range, (1b) would force a regular facility at the same level as `J`, so the assignment
§3.1 describes on p. 8 (regular facilities at levels `0, …, R-1`, then `J` at level `R`) would be
infeasible; the paper's own reading of (1b) on p. 9 ("either i is assigned to a regular facility at
level r or she is assigned to the emergency facility J at certain level s < r") is the corrected one. The sum over `s < r` is empty
for `r = 0`, as the paper stipulates. In (1f) the level `r ∈ {1, …, R}` is written `r.succ` for
`r : Fin R`, and `r - 1` is `r.castSucc`; the sum is over the regular facilities `k = 0, …, J-1`,
as printed. (1g) keeps `X`, `Y` real-valued and requires each entry to be `0` or `1`. -/
structure IsFeasible (X : Fin J → ℝ) (Y P : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) : Prop where
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
def IsOptimal (X : Fin J → ℝ) (Y P : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) : Prop :=
  D.IsFeasible X Y P ∧
    ∀ X' Y' P', D.IsFeasible X' Y' P' → D.objective X Y P ≤ D.objective X' Y' P'

end Instance

end ReliableFacilityLoc.LevelOrder


