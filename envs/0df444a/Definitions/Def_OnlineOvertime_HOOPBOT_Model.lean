-- Prove2me | Definitions.Def_OnlineOvertime_HOOPBOT_Model
-- name    : OnlineOvertime_HOOPBOT_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:10.793084+00:00
-- url     : https://prove2.me/theorems/907b1794-fc75-407c-931a-2f1b221236a7
-- title:
--   §2–§3, pp. 10–15 — online scheduling with budgeted overtime: instance, (P), (D), parameters (1), θ∗ (11), Algorithm 1 (HOOP-BOT) and its run
-- statement:
--   This file fixes the model of online advance scheduling with budgeted overtime of Keyvanshokooh, Shi and Van Oyen, the offline benchmark (P), its dual (D), the parameters of the competitive ratio, and the online primal-dual algorithm HOOP-BOT (Algorithm 1).
--
--   **Instance.** There are $n$ servers $i$, $T$ days $t$ and $m$ customers $j$, the customers numbered in their order of arrival. Server $i$ on day $t$ has a regular capacity $B_{i,t}$ and an overtime budget $U_{i,t}$; server $i$ pays $d_i$ per unit of overtime. Customer $j$ has service time $b_{i,j}$ and reward $c_{i,j}$ at server $i$. The **standing assumptions** are $n, T, m \ge 1$, $B_{i,t} > 0$, $U_{i,t} \ge 0$, $d_i \ge 0$, $b_{i,j} > 0$, the normalization $c_{i,j}/b_{i,j} \ge 1$, and $R_{\max} < 1$ (below).
--
--   **Parameters.** With $c_{i,j}$, $b_{i,j}$, $d_i$, $B_{i,t}$ as above,
--   $$\gamma_{\max} = \max_{i,j}\frac{c_{i,j}}{b_{i,j}},\quad d_{\max}=\max_i d_i,\quad R_{\max}=\max_{i,j,t}\frac{b_{i,j}}{B_{i,t}},\quad \alpha=(1+R_{\max})^{1/R_{\max}},$$
--   $$\lambda=\max\Big(\max_{i,j}\Big\{\frac{c_{i,j}}{b_{i,j}}-d_i\Big\},0\Big),\qquad \zeta=\min(d_{\max},\gamma_{\max}),$$
--   the balancing point
--   $$\theta^*=\frac{(1+R_{\max})(\zeta+\lambda)+\sqrt{(1+R_{\max})^2(\zeta+\lambda)^2+4(1+R_{\max})(\alpha-(1+R_{\max}))\zeta\lambda}}{2(\alpha-(1+R_{\max}))},$$
--   Lemma 1's coefficient $\theta_1=\zeta/(\alpha-1)$, the ratio $r=(1-2\gamma_{\max}R_{\max})/(1+\theta^*)$, and $\bar c_{i,j}=c_{i,j}-d_ib_{i,j}$.
--
--   **Offline problem (P)** (integer program): maximize $\sum_{t}\sum_i\sum_j c_{i,j}y_{i,j,t}-\sum_t\sum_i d_iv_{i,t}$ subject to $\sum_t\sum_i y_{i,j,t}\le 1$ for every $j$, $\sum_j b_{i,j}y_{i,j,t}\le B_{i,t}+v_{i,t}$, $v_{i,t}\le U_{i,t}$, $v_{i,t}\ge 0$ and $y_{i,j,t}\in\{0,1\}$.
--
--   **Dual (D)** of its LP relaxation: minimize $\sum_t\sum_i(B_{i,t}x_{i,t}+U_{i,t}u_{i,t})+\sum_j z_j$ subject to $b_{i,j}x_{i,t}+z_j\ge c_{i,j}$, $x_{i,t}-u_{i,t}\le d_i$ and $x_{i,t},u_{i,t},z_j\ge 0$.
--
--   **Algorithm 1 (HOOP-BOT)** with coefficients $\theta_1,\theta_2$. Initially $x_{i,t}=v_{i,t}=0$ and $u_{i,t}=1$. For each arriving customer $j$:
--   1. choose $(i^*,t^*)$ maximizing $c_{i,j}-b_{i,j}x_{i,t}$ (ties broken by a given selector);
--   2. if $c_{i^*,j}-b_{i^*,j}x_{i^*,t^*}\ge 0$, set $z_j$ to this value and $y_{i^*,j,t^*}=1$; then
--      - if $0\le x_{i^*,t^*}<d_{i^*}$, apply rule (I) $x\leftarrow x(1+b_{i^*,j}/B_{i^*,t^*})+\theta_1c_{i^*,j}/B_{i^*,t^*}$, and rule (II): if the new $x$ exceeds $d_{i^*}$, set it to $d_{i^*}$;
--      - otherwise apply rule (III) $u\leftarrow u(1+b_{i^*,j}/(B_{i^*,t^*}+U_{i^*,t^*}))+\theta_2\bar c_{i^*,j}/(B_{i^*,t^*}+U_{i^*,t^*})$, then $x\leftarrow u+d_{i^*}$ and $v\leftarrow v+b_{i^*,j}$;
--   3. otherwise reject $j$: $y_{i,j,t}=0$ for all $(i,t)$ and $z_j=0$.
--
--   The **run** is the state after processing the customers in arrival order; the run after the first $k$ customers is also defined.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Customers are $0,\dots,m-1$ (`Fin m`), and the paper's $b_{i,j}$, $c_{i,j}$, $y_{i,j,t}$ are written customer first. All quantities are real. Maxima over the finite index sets are suprema, which equal the maxima because the sets are nonempty. The paper writes $B_{i,t}\in\mathbb R_+$; positivity is assumed since $R_{\max}$ divides by it. Added hypotheses: $n,T,m\ge 1$ (the maxima are over the instance), $b_{i,j}>0$ (the ratios $c/b$, $b/B$), and $R_{\max}<1$ ($\theta^*$ divides by $\alpha-(1+R_{\max})$, which vanishes at $R_{\max}=1$). The tie-break of the argmax is not specified on the page; the algorithm takes a selector as a parameter, and statements quantify over every selector that returns a maximizer. Step 8's "$d_i$" is read as $d_{i^*}$.
-- source:
--   Keyvanshokooh, Shi, Van Oyen, Online Advance Scheduling with Overtime: A Primal-Dual Approach, accepted manuscript (MSOM, accepted May 2019; SSRN 3352166), pp. 10–15, §2.1–§2.2, (1)–(10), Algorithm 1 (p. 14), (11) and λ, ζ (pp. 14–15), θ1 of Lemma 1 (p. 20)

import Mathlib

namespace OnlineOvertime.HOOPBOT

/-- An instance of online scheduling with budgeted overtime (§2.1, pp. 10–11).
`n` servers, `T` days, `m` customers indexed `0, …, m - 1` in arrival order.

* `B i t`: regular capacity of server `i` on day `t` (the paper's `B_{i,t}`);
* `U i t`: overtime budget of server `i` on day `t` (`U_{i,t}`);
* `d i`: per-unit-of-time overtime cost of server `i` (`d_i`);
* `b j i`: service time of customer `j` at server `i` (the paper's `b_{i,j}`, customer first);
* `c j i`: reward of customer `j` at server `i` (the paper's `c_{i,j}`, customer first). -/
structure Instance (n T m : ℕ) where
  B : Fin n → Fin T → ℝ
  U : Fin n → Fin T → ℝ
  d : Fin n → ℝ
  b : Fin m → Fin n → ℝ
  c : Fin m → Fin n → ℝ

variable {n T m : ℕ}

/-- `γmax = max_{i,j} c_{i,j}/b_{i,j}`, (1), p. 11. -/
noncomputable def gammaMax (I : Instance n T m) : ℝ :=
  ⨆ (j : Fin m) (i : Fin n), I.c j i / I.b j i

/-- `dmax = max_i d_i`, (1), p. 11. -/
noncomputable def dMax (I : Instance n T m) : ℝ :=
  ⨆ i : Fin n, I.d i

/-- `Rmax = max_{i,j,t} b_{i,j}/B_{i,t}`, (1), p. 11. -/
noncomputable def Rmax (I : Instance n T m) : ℝ :=
  ⨆ (j : Fin m) (i : Fin n) (t : Fin T), I.b j i / I.B i t

/-- `α = (1 + Rmax)^{1/Rmax}`, (1), p. 11. -/
noncomputable def alpha (I : Instance n T m) : ℝ :=
  (1 + Rmax I) ^ (1 / Rmax I)

/-- `λ = max(max_{i,j} {c_{i,j}/b_{i,j} − d_i}, 0)`, Theorem 1, p. 15. -/
noncomputable def lam (I : Instance n T m) : ℝ :=
  max (⨆ (j : Fin m) (i : Fin n), I.c j i / I.b j i - I.d i) 0

/-- `ζ = min(dmax, γmax)`, Theorem 1, p. 15. -/
noncomputable def zeta (I : Instance n T m) : ℝ :=
  min (dMax I) (gammaMax I)

/-- The balancing point `θ∗`, (11), p. 14:
`θ∗ = [(1 + Rmax)(ζ + λ) + √((1 + Rmax)²(ζ + λ)² + 4(1 + Rmax)(α − (1 + Rmax))ζλ)] / (2(α − (1 + Rmax)))`. -/
noncomputable def thetaStar (I : Instance n T m) : ℝ :=
  ((1 + Rmax I) * (zeta I + lam I) +
      Real.sqrt ((1 + Rmax I) ^ 2 * (zeta I + lam I) ^ 2 +
        4 * (1 + Rmax I) * (alpha I - (1 + Rmax I)) * zeta I * lam I)) /
    (2 * (alpha I - (1 + Rmax I)))

/-- Lemma 1's coefficient `θ1 = ζ/(α − 1)`, p. 20. -/
noncomputable def thetaOne (I : Instance n T m) : ℝ :=
  zeta I / (alpha I - 1)

/-- The competitive ratio of Theorem 1, p. 14: `r = (1 − 2 γmax Rmax)/(1 + θ∗)`. -/
noncomputable def ratio (I : Instance n T m) : ℝ :=
  (1 - 2 * gammaMax I * Rmax I) / (1 + thetaStar I)

/-- `c̄_{i,j} = c_{i,j} − d_i b_{i,j}`, p. 14. -/
def cbar (I : Instance n T m) (j : Fin m) (i : Fin n) : ℝ :=
  I.c j i - I.d i * I.b j i

/-- Standing assumptions (§2.1, pp. 10–11), plus three disclosed additions.

From the page: `B_{i,t} ∈ ℝ₊` (taken positive, since `Rmax` divides by it), `U_{i,t} ≥ 0`,
`d_i ≥ 0`, and the normalization `c_{i,j}/b_{i,j} ≥ 1`, written `b ≤ c`.
Added: at least one server, day and customer (`0 < n`, `0 < T`, `0 < m`); service times
`b_{i,j} > 0`; and `Rmax < 1` (`θ∗` divides by `α − (1 + Rmax)`, which vanishes at `Rmax = 1`). -/
def Instance.Standing (I : Instance n T m) : Prop :=
  0 < n ∧ 0 < T ∧ 0 < m ∧
  (∀ i t, 0 < I.B i t) ∧ (∀ i t, 0 ≤ I.U i t) ∧ (∀ i, 0 ≤ I.d i) ∧
  (∀ j i, 0 < I.b j i) ∧ (∀ j i, I.b j i ≤ I.c j i) ∧
  Rmax I < 1

/-- The primal objective (2), p. 12: `Σ_t Σ_i Σ_j c_{i,j} y_{i,j,t} − Σ_t Σ_i d_i v_{i,t}`.
`y j i t` is the paper's `y_{i,j,t}`. -/
def obj (I : Instance n T m) (y : Fin m → Fin n → Fin T → ℝ) (v : Fin n → Fin T → ℝ) : ℝ :=
  ∑ t, ∑ i, ∑ j, I.c j i * y j i t - ∑ t, ∑ i, I.d i * v i t

/-- Feasibility for the primal integer program (P), constraints (3)–(6), p. 12. -/
def Feasible (I : Instance n T m) (y : Fin m → Fin n → Fin T → ℝ) (v : Fin n → Fin T → ℝ) :
    Prop :=
  (∀ j i t, y j i t = 0 ∨ y j i t = 1) ∧
  (∀ j, ∑ t, ∑ i, y j i t ≤ 1) ∧
  (∀ i t, ∑ j, I.b j i * y j i t ≤ I.B i t + v i t) ∧
  (∀ i t, v i t ≤ I.U i t) ∧
  (∀ i t, 0 ≤ v i t)

/-- The dual objective (7), p. 12: `Σ_t Σ_i (B_{i,t} x_{i,t} + U_{i,t} u_{i,t}) + Σ_j z_j`. -/
def dualObj (I : Instance n T m) (x u : Fin n → Fin T → ℝ) (z : Fin m → ℝ) : ℝ :=
  ∑ t, ∑ i, (I.B i t * x i t + I.U i t * u i t) + ∑ j, z j

/-- Feasibility for the dual (D), constraints (8)–(10), p. 12. -/
def DualFeasible (I : Instance n T m) (x u : Fin n → Fin T → ℝ) (z : Fin m → ℝ) : Prop :=
  (∀ i t j, I.c j i ≤ I.b j i * x i t + z j) ∧
  (∀ i t, x i t - u i t ≤ I.d i) ∧
  (∀ i t, 0 ≤ x i t) ∧ (∀ i t, 0 ≤ u i t) ∧ (∀ j, 0 ≤ z j)

/-- The state of Algorithm 1: dual prices `x, u`, overtime used `v`, assignment `y`
(`y j i t` = the paper's `y_{i,j,t}`) and dual variables `z`. -/
structure State (n T m : ℕ) where
  x : Fin n → Fin T → ℝ
  u : Fin n → Fin T → ℝ
  v : Fin n → Fin T → ℝ
  y : Fin m → Fin n → Fin T → ℝ
  z : Fin m → ℝ

/-- Step 1 of Algorithm 1, p. 14: `x_{i,t} = v_{i,t} = 0`, `u_{i,t} = 1`; `y` and `z` start at `0`. -/
def init : State n T m :=
  ⟨fun _ _ => 0, fun _ _ => 1, fun _ _ => 0, fun _ _ _ => 0, fun _ => 0⟩

/-- `sel` returns a maximizer of every function on `[n] × [T]`: a tie-break for the argmax of
Step 3. -/
def IsArgmaxSelector (sel : (Fin n × Fin T → ℝ) → Fin n × Fin T) : Prop :=
  ∀ (f : Fin n × Fin T → ℝ) (q : Fin n × Fin T), f q ≤ f (sel f)

/-- Overwrite the entry `(i, t)` of a server-date array by `a`. -/
def upd (f : Fin n → Fin T → ℝ) (i : Fin n) (t : Fin T) (a : ℝ) : Fin n → Fin T → ℝ :=
  fun i' t' => if i' = i ∧ t' = t then a else f i' t'

/-- One iteration (Steps 3–13) of Algorithm 1 (HOOP-BOT), p. 14, for arriving customer `j`,
with coefficients `θ1`, `θ2` and argmax tie-break `sel`. -/
noncomputable def step (I : Instance n T m) (θ1 θ2 : ℝ)
    (sel : (Fin n × Fin T → ℝ) → Fin n × Fin T) (s : State n T m) (j : Fin m) : State n T m :=
  -- Step 3: `(i∗, t∗) = argmax_{i,t} {c_{i,j} − b_{i,j} x_{i,t}}`
  let q := sel (fun q => I.c j q.1 - I.b j q.1 * s.x q.1 q.2)
  let i := q.1
  let t := q.2
  let gain := I.c j i - I.b j i * s.x i t
  -- Step 4
  if 0 ≤ gain then
    -- Step 5: `z_j ← c_{i∗,j} − b_{i∗,j} x_{i∗,t∗}`, `y_{i∗,j,t∗} ← 1`
    let z' := Function.update s.z j gain
    let y' := Function.update s.y j (fun i' t' => if i' = i ∧ t' = t then 1 else 0)
    -- Step 6
    if 0 ≤ s.x i t ∧ s.x i t < I.d i then
      -- Step 7, Updating Rule (I)
      let xI := s.x i t * (1 + I.b j i / I.B i t) + θ1 * (I.c j i / I.B i t)
      -- Step 8, Updating Rule (II)
      let xII := if xI > I.d i then I.d i else xI
      { x := upd s.x i t xII, u := s.u, v := s.v, y := y', z := z' }
    else
      -- Step 10, Updating Rule (III)
      let u' := s.u i t * (1 + I.b j i / (I.B i t + I.U i t)) +
        θ2 * (cbar I j i / (I.B i t + I.U i t))
      -- Step 11: `x_{i∗,t∗} ← u_{i∗,t∗} + d_{i∗}`, `v_{i∗,t∗} ← v_{i∗,t∗} + b_{i∗,j}`
      { x := upd s.x i t (u' + I.d i), u := upd s.u i t u',
        v := upd s.v i t (s.v i t + I.b j i), y := y', z := z' }
  else
    -- Step 13: `y_{i,j,t} ← 0` for all `i, t`, `z_j ← 0`
    { x := s.x, u := s.u, v := s.v, y := Function.update s.y j (fun _ _ => 0),
      z := Function.update s.z j 0 }

/-- The state of Algorithm 1 after the first `k` customers `0, …, k − 1` have been processed
(for `k ≥ m`, after all customers). -/
noncomputable def runPrefix (I : Instance n T m) (θ1 θ2 : ℝ)
    (sel : (Fin n × Fin T → ℝ) → Fin n × Fin T) (k : ℕ) : State n T m :=
  ((List.finRange m).take k).foldl (step I θ1 θ2 sel) init

/-- The final state of Algorithm 1 after all `m` customers. -/
noncomputable def run (I : Instance n T m) (θ1 θ2 : ℝ)
    (sel : (Fin n × Fin T → ℝ) → Fin n × Fin T) : State n T m :=
  runPrefix I θ1 θ2 sel m

end OnlineOvertime.HOOPBOT


