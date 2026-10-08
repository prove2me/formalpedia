-- Prove2me | Definitions.Def_ReliableFacilityLoc_RRSP_RSP
-- name    : ReliableFacilityLoc_RRSP_RSP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:24.01015+00:00
-- url     : https://prove2.me/theorems/7f97aae4-46fe-4920-84c7-06b72d8b00d8
-- title:
--   The relaxed subproblem (RSP$_i$) (4a)–(4h): level assignments, transitional probabilities, objective
-- statement:
--   Fix one customer $i$ of the reliable uncapacitated facility location model of Cui, Ouyang and Shen. The data are the demand rate $\lambda_i$, the unit costs $d_{ij}$ to the regular facilities $j = 0,\dots,J-1$, the penalty $\varphi_i$ per unit of unserved demand, the failure probabilities $q_j$ of the regular facilities, the Lagrange multipliers $\mu_{ij}$ of the relaxed constraints (1c), and the number $R$ of backup levels (levels are $r = 0,\dots,R$). An **emergency facility** with index $J$ is added, with $d_{iJ} = \varphi_i$ and $q_J = 0$. As in the paper, the customer index is dropped from the variables.
--
--   1. A **level assignment** is an array $Y_{jr} \in \{0,1\}$ ($j = 0,\dots,J$, $r = 0,\dots,R$), where $Y_{jr} = 1$ means that facility $j$ serves the customer at level $r$, satisfying
--      - (4b) $\sum_{j=0}^{J} Y_{jr} + \sum_{s=0}^{r-1} Y_{Js} = 1$ for every level $r$;
--      - (4c) $\sum_{r=0}^{R-1} Y_{jr} \le 1$ for every regular facility $j$;
--      - (4d) $\sum_{r=0}^{R} Y_{Jr} = 1$.
--
--      So the customer has distinct regular facilities at levels $0,\dots,s-1$ and the emergency facility at some level $s \le R$, and nothing after it.
--   2. Given a level assignment $Z$, the **transitional probabilities** $P_{jr}$ and the **linearization variables** $W_{jr}$ satisfy
--      - (4e) $P_{j0} = 1 - q_j$;
--      - (4f) $P_{jr} = (1-q_j)\sum_{k=0}^{J-1} \frac{q_k}{1-q_k} W_{k,r-1}$ for $1 \le r \le R$;
--      - (4h) = (2a)–(2d): $W_{jr} \le P_{jr}$, $W_{jr} \le Z_{jr}$, $W_{jr} \ge 0$, $W_{jr} \ge P_{jr} + Z_{jr} - 1$.
--
--      These force $W_{jr} = P_{jr} Z_{jr}$, the probability that facility $j$ actually serves the customer at level $r$.
--   3. $(Y,P,W)$ is **feasible for (RSP$_i$)** if $Y$ is a level assignment and $P$, $W$ satisfy item 2 with $Z = Y$.
--   4. The objective of (RSP$_i$) is
--
--   $$
--   \Phi_i(Y,W) = \sum_{j=0}^{J}\sum_{r=0}^{R} \lambda_i d_{ij} W_{jr} + \sum_{j=0}^{J-1}\sum_{r=0}^{R-1} \mu_{ij} Y_{jr}.
--   $$
--
--   (RSP$_i$) is the customer-$i$ part of the Lagrangian relaxation of the reliable facility location problem obtained by dualizing (1c). The level-assignment constraints are shared by the fixed-probability reformulation (RRSP$_i$) and by the split formulation of the proof of Proposition 4.
--
--   **Formalization Note** Facilities are `Fin (J+1)` with `Fin.last J` the emergency facility, levels `Fin (R+1)`; $Y$, $P$, $W$ are real arrays with $Y$ binary. Constraint (4b) is printed with the first sum stopping at $J-1$; it is formalized with the sum over all $j = 0,\dots,J$, as the paper's own reading of (1b) on p. 9 requires (with the printed range a regular facility would have to share the emergency facility's level). Level $r \ge 1$ is written `r.succ` for `r : Fin R`.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), pp. 12–13 (PDF 14–15), (RSP_i) (4a)–(4h); linearization (2a)–(2d) p. 9 (PDF 11); emergency facility and standing assumptions p. 8 (PDF 10)

import Mathlib
import Definitions.Def_ReliableFacilityLoc_Supermod_RSP

open Finset

namespace ReliableFacilityLoc.RRSP

/-- The level-assignment constraints shared by (RSP_i), (RRSP_i) and the split problem of A.4
(UCTC-FR-2010-02, (4b)–(4d), (4g), pp. 12–13, PDF 14–15; identically (7b)–(7e), p. 14, PDF 16;
and (19c)–(19e), (19l), pp. 37–38, PDF 39–40). `Y j r = 1` means that facility `j` is assigned to
the customer at level `r`. Facilities are `Fin (J + 1)`, with `Fin.last J` the emergency facility
`J`; levels are `Fin (R + 1)` (`r = 0, …, R`).

Formalization Note: (4b) (and (7b), (19c)) is printed
`Σ_{j=0}^{J-1} Y_jr + Σ_{s=0}^{r-1} Y_Js = 1`; here the first sum runs over **all** facilities
`j = 0, …, J`, including the emergency facility. With the printed range, (4b) at the level where
`J` is assigned would force a regular facility to share that level with `J`, contradicting the
paper's own reading of (1b) on p. 9 ("either i is assigned to a regular facility at level r or she
is assigned to the emergency facility J at certain level s < r"). The sums `Σ_{r=0}^{R-1}` are
sums over `r : Fin R` of the level `r.castSucc`. `Y` is real-valued with every entry `0` or `1`. -/
structure IsLevelAssignment {J R : ℕ} (Y : Fin (J + 1) → Fin (R + 1) → ℝ) : Prop where
  /-- (4b)/(7b)/(19c), with the first sum over all `j = 0, …, J` -/
  level_one : ∀ r, ∑ j, Y j r + ∑ s ∈ Iio r, Y (Fin.last J) s = 1
  /-- (4c)/(7c)/(19d): `Σ_{r=0}^{R-1} Y_jr ≤ 1` for every regular `j` -/
  regular_once : ∀ j : Fin J, ∑ r : Fin R, Y j.castSucc r.castSucc ≤ 1
  /-- (4d)/(7d)/(19e): `Σ_{r=0}^{R} Y_Jr = 1` -/
  emergency_once : ∑ r, Y (Fin.last J) r = 1
  /-- (4g)/(7e)/(19l): `Y_jr ∈ {0, 1}` -/
  binary : ∀ j r, Y j r = 0 ∨ Y j r = 1

/-- The transitional-probability and linearization constraints of (RSP_i), driven by a level
assignment `Z` (UCTC-FR-2010-02, (4e), (4f), (4h) = (2a)–(2d), pp. 9 and 13, PDF 11 and 15; in the
split problem of A.4 these are (19f)–(19k), p. 38, PDF 40, with `Z` the facility whose failure
probability is used at each level). `P j r` is the probability that facility `j` serves the
customer at level `r`, and the linearization forces `W j r = P j r * Z j r`.

Formalization Note: in (4f) the level `r ∈ {1, …, R}` is `r.succ` for `r : Fin R`, and the level
`r − 1` is `r.castSucc`; the sum runs over the regular facilities `k = 0, …, J − 1`, as printed.
The printed (19g) has the stray index `W_{i,k,r−1}`; it is `W_{k,r−1}`. -/
structure IsProbLinearization {J R : ℕ} (q : Fin J → ℝ)
    (Z P W : Fin (J + 1) → Fin (R + 1) → ℝ) : Prop where
  /-- (4e)/(19f): `P_j0 = 1 − q_j` for every `j = 0, …, J` -/
  prob_zero : ∀ j, P j 0 = 1 - ReliableFacilityLoc.Supermod.qExt q j
  /-- (4f)/(19g): `P_jr = (1 − q_j) Σ_{k=0}^{J-1} q_k/(1 − q_k) W_{k,r−1}`, `1 ≤ r ≤ R` -/
  prob_succ : ∀ j (r : Fin R), P j r.succ =
    (1 - ReliableFacilityLoc.Supermod.qExt q j) * ∑ k : Fin J, q k / (1 - q k) * W k.castSucc r.castSucc
  /-- (2a)/(19h): `W_jr ≤ P_jr` -/
  w_le_p : ∀ j r, W j r ≤ P j r
  /-- (2b)/(19i): `W_jr ≤ Z_jr` -/
  w_le_z : ∀ j r, W j r ≤ Z j r
  /-- (2c)/(19j): `W_jr ≥ 0` -/
  w_nonneg : ∀ j r, 0 ≤ W j r
  /-- (2d)/(19k): `W_jr ≥ P_jr + Z_jr − 1` -/
  w_ge : ∀ j r, P j r + Z j r - 1 ≤ W j r

/-- Feasibility of `(Y, P, W)` for the relaxed subproblem (RSP_i) of one customer `i`
(UCTC-FR-2010-02, §3.3, (4b)–(4h), pp. 12–13, PDF 14–15): `Y` is a level assignment and `P`, `W`
are the transitional probabilities and linearization variables it drives. -/
def IsRSPFeasible {J R : ℕ} (q : Fin J → ℝ) (Y P W : Fin (J + 1) → Fin (R + 1) → ℝ) : Prop :=
  IsLevelAssignment Y ∧ IsProbLinearization q Y P W

/-- The objective (4a) of (RSP_i) (UCTC-FR-2010-02, p. 12, PDF 14):
`Φ_i = Σ_{j=0}^{J} Σ_{r=0}^{R} λ_i d_ij W_jr + Σ_{j=0}^{J-1} Σ_{r=0}^{R-1} µ_ij Y_jr`, with
`d_iJ = φ_i`; `lam` is `λ_i`, `mu j` is the Lagrange multiplier `µ_ij` of constraint (1c). -/
def rspObjective {J R : ℕ} (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (mu : Fin J → ℝ)
    (Y W : Fin (J + 1) → Fin (R + 1) → ℝ) : ℝ :=
  ∑ j, ∑ r, lam * ReliableFacilityLoc.Supermod.dExt d phi j * W j r + ∑ j : Fin J, ∑ r : Fin R, mu j * Y j.castSucc r.castSucc

end ReliableFacilityLoc.RRSP


