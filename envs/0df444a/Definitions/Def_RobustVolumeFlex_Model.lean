-- Prove2me | Definitions.Def_RobustVolumeFlex_Model
-- name    : RobustVolumeFlex_Model
-- status  : Definition
-- author  : @jorengijsbrechts
-- created : 2026-11-04T08:44:22.009205+00:00
-- url     : https://prove2.me/theorems/6bf4142e-08a0-4e3c-a3fc-6f5d7c9e6214
-- title:
--   Robust capacitated sourcing with volume flexibility: LP (4), base stocks, shifting need and the LPS order
-- statement:
--   The robust rolling-horizon model of capacitated sourcing with volume flexibility, as solved in one decision period $t$.
--
--   The planning horizon $\{t,\dots,t+H-1\}$ is indexed by $n\in\{0,\dots,H-1\}$, with $n=0$ the current period. The data are:
--
--   1. holding cost $h$, backorder penalty $b$, contracted unit cost $c$ and flexibility premium $c_p$;
--   2. the starting net inventory $x=x_{t-1}$;
--   3. base capacities $k_n$;
--   4. a demand uncertainty set $\Omega\subseteq\mathbb{R}^H$.
--
--   The worst-case cumulative demands are
--   $$\underline D_n=\inf_{d\in\Omega}\sum_{i\le n}d_i,\qquad \overline D_n=\sup_{d\in\Omega}\sum_{i\le n}d_i.$$
--
--   A triple $(q,y,z)$ is **feasible** for the linear program (4) if, for all $n$:
--
--   - $y_n\ge h(x+\sum_{i\le n}q_i-\underline D_n)$;
--   - $y_n\ge -b(x+\sum_{i\le n}q_i-\overline D_n)$;
--   - $z_n\ge c_p(q_n-k_n)$;
--   - $z_n\ge 0$ and $q_n\ge 0$.
--
--   It is **robustly optimal** if it is feasible and minimizes $\sum_n(c\,q_n+y_n+z_n)$ over all feasible triples.
--
--   The uncapacitated system has cumulative base stock
--   $$\hat S_n=\max\Bigl(\frac{b\overline D_n+h\underline D_n}{b+h},\,x\Bigr).$$
--   Its orders are $\hat q_0=\hat S_0-x$ and $\hat q_n=\hat S_n-\hat S_{n-1}$ in every period with $c\le b(H-n)$, and $\hat q_n=0$ in the remaining final periods. The **shifting need** with lookahead $s$ is
--   $$\tau^s=\Bigl(\max_{1\le i\le s}\sum_{j=1}^{i}(\hat q_j-k_j)\Bigr)^{+}.$$
--
--   The **Lookahead Peak-Shaving order** is
--   $$q^{\mathrm{LPS}}=\begin{cases}\hat S_0-x & x<\hat S_0-k_0,\\ k_0 & \hat S_0-k_0\le x<\hat S_0+\tau^s-k_0,\\ \hat S_0+\tau^s-x&\text{otherwise.}\end{cases}$$
--
--   These are the shared definitions for every statement drawn from the paper.
--
--   **Formalization Note** $\underline D_n,\overline D_n$ are real infima/suprema, so theorems using them assume $\Omega$ nonempty and bounded. The positive part in $\tau^s$ is a fold of $\max$ starting at $0$. Boundary cases of the policy go to the later case, where the order is continuous. In eq. (6) the published end-of-horizon index ranges are inconsistent; here ordering stops in exactly the periods where one unit costs more than backlogging it to the horizon end, $c>b(H-n)$.
-- source:
--   J. Gijsbrechts, C. Imdahl, R. N. Boute, J. A. Van Mieghem, Optimal robust inventory management with volume flexibility: Matching capacity and demand with the lookahead peak-shaving policy, Production and Operations Management 32 (2023) 3357-3373, https://doi.org/10.1111/poms.14069, Section 3.2 eqs. (3)-(4); Section 4.1 eqs. (6)-(8); Section 4.2 Definition 1, Definition 2 eq. (11)

import Mathlib

/-!
# Robust capacitated sourcing with volume flexibility — the model

J. Gijsbrechts, C. Imdahl, R. N. Boute, J. A. Van Mieghem (2023),
"Optimal robust inventory management with volume flexibility: Matching capacity and demand
with the lookahead peak-shaving policy", *Production and Operations Management*,
https://doi.org/10.1111/poms.14069.

One period `t` of the rolling-horizon robust model of Section 3.2. The planning horizon
`ℕ_t^{t+H-1}` is indexed by `Fin H`, where index `0` is the current period `t` and index `n`
is period `t + n`.
-/

namespace RobustVolumeFlex

open Finset

/-- Data of the robust problem solved in one period (Sections 3.1–3.2):
holding cost `h`, backorder penalty `b`, contracted unit sourcing cost `c`,
flexibility (overtime) premium `cp`, starting net inventory `x = x_{t-1}`,
base capacities `k n = k_{t+n}` and the demand uncertainty set `Ω = Ω_t ⊆ ℝ^H`. -/
structure Params (H : ℕ) where
  h : ℝ
  b : ℝ
  c : ℝ
  cp : ℝ
  x : ℝ
  k : Fin H → ℝ
  Ω : Set (Fin H → ℝ)

variable {H : ℕ}

/-- Partial sum `∑_{i=t}^{t+n} v_i` of a vector over the planning horizon. -/
def cumSum (v : Fin H → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ univ.filter (fun i : Fin H => i.val ≤ n), v i

/-- Minimum cumulative demand `D̲_{t+n} = min_{d ∈ Ω} ∑_{i=t}^{t+n} d_i` (eq. (3)). -/
noncomputable def minCumDemand (P : Params H) (n : ℕ) : ℝ :=
  sInf ((fun d => cumSum d n) '' P.Ω)

/-- Maximum cumulative demand `D̄_{t+n} = max_{d ∈ Ω} ∑_{i=t}^{t+n} d_i` (eq. (3)). -/
noncomputable def maxCumDemand (P : Params H) (n : ℕ) : ℝ :=
  sSup ((fun d => cumSum d n) '' P.Ω)

/-- Feasibility for the linear program (4): order quantities `q`, worst-case inventory
mismatch costs `y` and premium sourcing costs `z` satisfying the constraint sets
`𝓗` (holding), `𝓑` (backlog), `𝓕` (flexibility) and the sign constraints. -/
def IsFeasible (P : Params H) (q y z : Fin H → ℝ) : Prop :=
  (∀ n : Fin H, P.h * (P.x + cumSum q n - minCumDemand P n) ≤ y n) ∧
  (∀ n : Fin H, -P.b * (P.x + cumSum q n - maxCumDemand P n) ≤ y n) ∧
  (∀ n : Fin H, P.cp * (q n - P.k n) ≤ z n) ∧
  (∀ n : Fin H, 0 ≤ z n) ∧
  (∀ n : Fin H, 0 ≤ q n)

/-- The robust objective of (4): `∑_n (c q_n + y_n + z_n)`. -/
def objective (P : Params H) (q y z : Fin H → ℝ) : ℝ :=
  ∑ n : Fin H, (P.c * q n + y n + z n)

/-- `(q, y, z)` is an optimal solution of the linear program (4). -/
def IsRobustlyOptimal (P : Params H) (q y z : Fin H → ℝ) : Prop :=
  IsFeasible P q y z ∧
    ∀ q' y' z' : Fin H → ℝ, IsFeasible P q' y' z' → objective P q y z ≤ objective P q' y' z'

/-- Cumulative base-stock level of the uncapacitated system,
`Ŝ_{t+n} = max((b D̄_{t+n} + h D̲_{t+n}) / (b + h), x_{t-1})` (eq. (7)). -/
noncomputable def baseStock (P : Params H) (n : ℕ) : ℝ :=
  max ((P.b * maxCumDemand P n + P.h * minCumDemand P n) / (P.b + P.h)) P.x

/-- Optimal order quantities `q̂_{t+n}` of the uncapacitated system (eq. (6)): in period
`t + n` the cumulative order is raised to `Ŝ_{t+n} - x_{t-1}` as long as ordering one unit
there is not more expensive than backlogging it until the end of the planning horizon,
i.e. `c ≤ b · (H - n)`; in the remaining final periods (the last `u` periods, where
`u b < c ≤ (u + 1) b`) nothing is ordered. -/
noncomputable def uncapOrder (P : Params H) (n : Fin H) : ℝ :=
  if P.c ≤ P.b * ((H : ℝ) - n.val) then
    baseStock P n.val - (if n.val = 0 then P.x else baseStock P (n.val - 1))
  else 0

/-- Shifting need over a lookahead horizon of `s` periods (Definition 1):
`τ_t^s = (max_{i ∈ ℕ_{t+1}^{t+s}} ∑_{j=t+1}^{i} (q̂_j - k_j))⁺`.
Written as a fold of `max` starting from `0`, which equals the positive part of the
maximum when `s ≥ 1`. -/
noncomputable def shiftingNeed (P : Params H) (s : ℕ) : ℝ :=
  (Icc 1 s).fold max 0 (fun i =>
    ∑ j ∈ univ.filter (fun j : Fin H => 1 ≤ j.val ∧ j.val ≤ i), (uncapOrder P j - P.k j))

/-- Order quantity in the current period `t` under the Lookahead Peak-Shaving policy with
lookahead horizon `s` (Definition 2, eq. (11)): a generalized base-stock policy with lower
base-stock level `Ŝ_t` and upper base-stock level `Ŝ_t + τ_t^s`. The three cases are
continuous at their boundaries, so assigning the boundary points to the next case does
not change the value. -/
noncomputable def lpsOrder [NeZero H] (P : Params H) (s : ℕ) : ℝ :=
  if P.x < baseStock P 0 - P.k 0 then baseStock P 0 - P.x
  else if P.x < baseStock P 0 + shiftingNeed P s - P.k 0 then P.k 0
  else baseStock P 0 + shiftingNeed P s - P.x

end RobustVolumeFlex


