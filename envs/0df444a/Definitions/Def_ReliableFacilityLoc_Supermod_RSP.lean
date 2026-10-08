-- Prove2me | Definitions.Def_ReliableFacilityLoc_Supermod_RSP
-- name    : ReliableFacilityLoc_Supermod_RSP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:14:11.680261+00:00
-- url     : https://prove2.me/theorems/7aa5c126-d1b5-4076-a06b-f9cd110af4c3
-- title:
--   (5a)–(5c): the set function $\Phi_i(S)$ of the relaxed subproblem (RSP$_i$)
-- statement:
--   Fix one customer $i$ of the reliable facility location model of Cui, Ouyang and Shen. The data are the demand rate $\lambda_i$, the unit costs $d_{ij}$ to the regular facilities $j = 0,\dots,J-1$, the penalty $\varphi_i$ per unit of unserved demand, the failure probabilities $q_j$ of the regular facilities, the Lagrange multipliers $\mu_{ij}$, and the number $R$ of backup levels (levels are $r = 0,\dots,R$). An **emergency facility** with index $J$ is added, with $d_{iJ} = \varphi_i$ and $q_J = 0$.
--
--   The variables are $Y_{jr} \in \{0,1\}$ ("facility $j$ serves the customer at level $r$"), $P_{jr}$ and $W_{jr}$ for $j = 0,\dots,J$ and $r = 0,\dots,R$. For a set $S \subseteq \{0,\dots,J-1\}$ of regular facilities, the point $(Y,P,W)$ is **feasible** if
--
--   1. (4b) $\sum_{j=0}^{J} Y_{jr} + \sum_{s=0}^{r-1} Y_{Js} = 1$ for every level $r$;
--   2. (4c) $\sum_{r=0}^{R-1} Y_{jr} \le 1$ for every regular $j$;
--   3. (4d) $\sum_{r=0}^{R} Y_{Jr} = 1$;
--   4. (4e) $P_{j0} = 1 - q_j$ and (4f) $P_{jr} = (1-q_j)\sum_{k=0}^{J-1} \frac{q_k}{1-q_k} W_{k,r-1}$ for $1 \le r \le R$;
--   5. (4g) every $Y_{jr}$ is $0$ or $1$;
--   6. (4h) $W_{jr} \le P_{jr}$, $W_{jr} \le Y_{jr}$, $W_{jr} \ge 0$, $W_{jr} \ge P_{jr} + Y_{jr} - 1$;
--   7. (5c) $\sum_{r=0}^{R-1} Y_{jr} = 0$ for every regular $j \notin S$.
--
--   Then
--
--   $$
--   \Phi_i(S) = \min\Big\{ \sum_{j=0}^{J}\sum_{r=0}^{R} \lambda_i d_{ij} W_{jr} + \sum_{j\in S} \mu_{ij} \;:\; (Y,P,W) \text{ feasible} \Big\},
--   $$
--
--   the minimum cost of serving customer $i$ using only facilities of $S$ (plus the emergency facility). Under $0 \le q_j < 1$ the constraints force $W_{jr} = P_{jr} Y_{jr}$, so $W_{jr}$ is the probability that facility $j$ serves the customer at level $r$, and the objective is expected transportation-plus-penalty cost.
--
--   This set function is the object of Proposition 3; the customer's assignment problem (RSP$_i$) is the minimization of $\Phi_i$ over $|S| \le R$.
--
--   **Formalization Note** Facilities are `Fin (J+1)` with `Fin.last J` the emergency facility, levels `Fin (R+1)`, and the customer index is dropped. Three printed typos are corrected: (4b) is printed with the first sum stopping at $J-1$ (the emergency facility must be counted, as the paper's own reading of (1b) on p. 9 says); (5b) is printed "(4b)–(4g)" and omits (4h), without which $W$ is unconstrained; (5c) is printed for $j \in \{1,\dots,J-1\}\setminus S$ instead of $\{0,\dots,J-1\}\setminus S$. The objective (5a) is printed with $h_i$, which is $\lambda_i$. The minimum is taken as the infimum (`sInf`) of the set of feasible objective values; this set is nonempty (the emergency facility at level $0$) and bounded below ($0 \le W \le Y \le 1$), and finite, so the infimum is the minimum.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), pp. 12–13 (PDF 14–15), (RSP_i) (4a)–(4h) and (5a)–(5c); emergency facility and standing assumptions p. 8 (PDF 10)

import Mathlib

open Finset

namespace ReliableFacilityLoc.Supermod

/-- The unit cost `d_ij` of one customer `i`, extended to all `J + 1` facilities: the emergency
facility `J` (here `Fin.last J`) has `d_iJ = φ_i` (Cui, Ouyang & Shen, *Reliable Facility Location
Design under the Risk of Disruptions*, UCTC-FR-2010-02 (Feb. 2010), §3.1, p. 8, PDF 10).

Formalization Note: the customer index `i` is dropped, as in (RSP_i) (p. 12): `d j` is `d_ij` for
the regular facility `j : Fin J` and `phi` is `φ_i`. -/
def dExt {J : ℕ} (d : Fin J → ℝ) (phi : ℝ) : Fin (J + 1) → ℝ :=
  Fin.lastCases phi d

/-- The failure probability extended to all `J + 1` facilities: the emergency facility has
`q_J = 0` (UCTC-FR-2010-02, §3.1, p. 8, PDF 10). -/
def qExt {J : ℕ} (q : Fin J → ℝ) : Fin (J + 1) → ℝ :=
  Fin.lastCases 0 q

/-- Feasibility of `(Y, P, W)` for the program (5) defining `Φ_i(S)`: constraints (4b)–(4h) of the
relaxed subproblem (RSP_i) (UCTC-FR-2010-02, §3.3, pp. 12–13, PDF 14–15) together with (5c)
(§3.3.1, p. 13, PDF 15). The customer index `i` is omitted, as in the paper. Facilities are
`Fin (J + 1)`, with `Fin.last J` the emergency facility `J`; levels are `Fin (R + 1)`
(`r = 0, …, R`); `S` is a set of regular facilities.

Formalization Note (corrections of printed typos, recorded in the mission's moderation notes):
1. (4b) is printed `Σ_{j=0}^{J-1} Y_jr + Σ_{s=0}^{r-1} Y_Js = 1`; here the first sum runs over all
   facilities `j = 0, …, J`, including the emergency facility. With the printed range, (4b) at the
   level `r` where `J` is assigned forces a regular facility to share level `r` with `J`, which
   contradicts the paper's own reading of (1b) on p. 9 ("either i is assigned to a regular facility
   at level r or she is assigned to the emergency facility J at certain level s < r").
2. (5b) is printed "(4b) − (4g)"; the linearization constraints (4h) = (2a)–(2d) are included,
   since without them `W` is unconstrained and the minimum in (5a) is `−∞`.
3. (5c) is printed for `j ∈ {1, …, J − 1} \ S`; it is stated here for every regular facility
   `j ∈ {0, …, J − 1} \ S`.
In (4f) the level `r ∈ {1, …, R}` is `r.succ` for `r : Fin R`, and level `r − 1` is
`r.castSucc`; the sum runs over the regular facilities `k = 0, …, J − 1`, as printed. Sums
`Σ_{r=0}^{R-1}` are sums over `r : Fin R` of level `r.castSucc`. (4g) keeps `Y` real-valued with
every entry `0` or `1`. -/
structure IsFeasible {J : ℕ} (q : Fin J → ℝ) (R : ℕ) (S : Finset (Fin J))
    (Y P W : Fin (J + 1) → Fin (R + 1) → ℝ) : Prop where
  /-- (4b), with the first sum over all `j = 0, …, J` -/
  level_one : ∀ r, ∑ j, Y j r + ∑ s ∈ Iio r, Y (Fin.last J) s = 1
  /-- (4c): `Σ_{r=0}^{R-1} Y_jr ≤ 1` for every regular `j` -/
  regular_once : ∀ j : Fin J, ∑ r : Fin R, Y j.castSucc r.castSucc ≤ 1
  /-- (4d): `Σ_{r=0}^{R} Y_Jr = 1` -/
  emergency_once : ∑ r, Y (Fin.last J) r = 1
  /-- (4e): `P_j0 = 1 − q_j` for every `j = 0, …, J` -/
  prob_zero : ∀ j, P j 0 = 1 - qExt q j
  /-- (4f): `P_jr = (1 − q_j) Σ_{k=0}^{J-1} q_k/(1 − q_k) W_{k,r−1}` for `j = 0, …, J`, `1 ≤ r ≤ R` -/
  prob_succ : ∀ j (r : Fin R), P j r.succ =
    (1 - qExt q j) * ∑ k : Fin J, q k / (1 - q k) * W k.castSucc r.castSucc
  /-- (4g): `Y_jr ∈ {0, 1}` -/
  binary : ∀ j r, Y j r = 0 ∨ Y j r = 1
  /-- (4h) = (2a): `W_jr ≤ P_jr` -/
  w_le_p : ∀ j r, W j r ≤ P j r
  /-- (4h) = (2b): `W_jr ≤ Y_jr` -/
  w_le_y : ∀ j r, W j r ≤ Y j r
  /-- (4h) = (2c): `W_jr ≥ 0` -/
  w_nonneg : ∀ j r, 0 ≤ W j r
  /-- (4h) = (2d): `W_jr ≥ P_jr + Y_jr − 1` -/
  w_ge : ∀ j r, P j r + Y j r - 1 ≤ W j r
  /-- (5c): `Σ_{r=0}^{R-1} Y_jr = 0` for every regular `j ∉ S` -/
  outside_S : ∀ j : Fin J, j ∉ S → ∑ r : Fin R, Y j.castSucc r.castSucc = 0

/-- The objective (5a) of the program defining `Φ_i(S)` (UCTC-FR-2010-02, p. 13, PDF 15):
`Σ_{j=0}^{J} Σ_{r=0}^{R} λ_i d_ij W_jr + Σ_{j∈S} µ_ij`, with `d_iJ = φ_i`.

Formalization Note: (5a) is printed with `h_i` in place of `λ_i`; `h_i` is not defined anywhere
in the paper, and (4a), of which (5a) is the restriction, has `λ_i`. -/
def objective {J R : ℕ} (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (mu : Fin J → ℝ)
    (S : Finset (Fin J)) (W : Fin (J + 1) → Fin (R + 1) → ℝ) : ℝ :=
  ∑ j, ∑ r, lam * dExt d phi j * W j r + ∑ j ∈ S, mu j

/-- The set of objective values (5a) over the feasible points of (5b)–(5c). -/
def feasibleValues {J : ℕ} (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (mu : Fin J → ℝ) (R : ℕ) (S : Finset (Fin J)) : Set ℝ :=
  {v | ∃ Y P W : Fin (J + 1) → Fin (R + 1) → ℝ,
    IsFeasible q R S Y P W ∧ v = objective lam d phi mu S W}

/-- `Φ_i(S)`, "the minimum cost to serve customer i, using only facilities in S"
(UCTC-FR-2010-02, §3.3.1, p. 13, PDF 15, (5a)–(5c)): the minimum of (5a) subject to (4b)–(4h)
and (5c), for one customer with demand rate `lam` = `λ_i`, unit costs `d` = `d_ij` (`j < J`),
penalty `phi` = `φ_i`, failure probabilities `q`, Lagrange multipliers `mu` = `µ_ij`, and `R`
the highest level.

Formalization Note: `Φ_i(S)` is the infimum (`sInf`) of `feasibleValues`. Under the paper's
standing assumption `0 ≤ q_j < 1` this set is nonempty (assign the emergency facility at level 0)
and bounded below (`0 ≤ W_jr ≤ Y_jr ≤ 1` by (2b), (2c), (4g)); it is moreover finite, because
`Y` is binary and (4e), (4f), (4h) determine `P` and `W` from `Y`. So the infimum is the minimum
the paper takes, never the junk value of `sInf` on an empty or unbounded set. Nonemptiness and
boundedness below are proved in the mission's sanity-check file. `Φ_i` is defined by the program
(5), not by its closed form; the closed form is a milestone. -/
noncomputable def Phi {J : ℕ} (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (mu : Fin J → ℝ) (R : ℕ) (S : Finset (Fin J)) : ℝ :=
  sInf (feasibleValues lam d phi q mu R S)

end ReliableFacilityLoc.Supermod


