-- Prove2me | Definitions.Def_MultistageRUC_Equiv_Setting
-- name    : MultistageRUC_Equiv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:15:17.660408+00:00
-- url     : https://prove2.me/theorems/e3a3cdc1-5833-4b08-adff-85aa2c1f0426
-- title:
--   (1b)–(1k), (2), (3), (5), (1P), (M̃^NR), pp. 5–11 — UC data, commitment set X, dispatch sets, budget set, two-stage and multistage objectives
-- statement:
--   The objects of the unit commitment (UC) model of Lorca, Sun, Litvinov and Zheng, §§2–3.
--
--   A power system has generators $i\in\mathcal N_g$, net-load nodes $j\in\mathcal N_d$, buses, transmission lines $l\in\mathcal N_l$ and periods $t\in\mathcal T=\{1,\dots,T\}$. The data are the no-load, start-up and variable costs $G_i,S_i,C_i$; the generation limits $p_i^{\min},p_i^{\max}$; the ramp rates $RD_i^t,RU_i^t,SD_i^t,SU_i^t$; the minimum up and down times $UT_i,DT_i$; the incidence matrices $B^p,B^d$ of generators and loads; the shift factors $\alpha_l$ and flow limit $f_l^{\max}$ of each line; and the initial on/off status $x_i^0$ and dispatch $p_i^0$.
--
--   1. **Commitment set $X$**: triples $(x,u,v)$ of on/off, start-up and shut-down decisions satisfying (1b)–(1g): binary values; $x_i^t-x_i^{t-1}=u_i^t-v_i^t$; the minimum up-time constraints $\sum_{\tau=t}^{t+UT_i-1}x_i^\tau\ge UT_i u_i^t$ for $t\le T-UT_i+1$ and $\sum_{\tau=t}^{T}(x_i^\tau-u_i^t)\ge0$ for $t\ge T-UT_i+1$; and the analogous minimum down-time constraints with $1-x_i^\tau$, $v_i^t$, $DT_i$.
--   2. **Per-period dispatch set without ramping** $\Omega_t^{NR}(x,d^t)$: dispatches $p^t\in\mathbb R^{N_g}$ with $p_i^{\min}x_i^t\le p_i^t\le p_i^{\max}x_i^t$ (1h), $-f_l^{\max}\le\alpha_l^\top(B^pp^t-B^dd^t)\le f_l^{\max}$ (1j) and $\sum_i p_i^t=\sum_j d_j^t$ (1k).
--   3. **Ramping constraints** (1i): $-RD_i^tx_i^t-SD_i^tv_i^t\le p_i^t-p_i^{t-1}\le RU_i^tx_i^{t-1}+SU_i^tu_i^t$.
--   4. **Budget uncertainty set** (3):
--   $$\mathcal D^t=\Big\{d^t:\sum_{j\in\mathcal N_d}\frac{|d_j^t-\bar d_j^t|}{\hat d_j^t}\le\Gamma\sqrt{N_d},\ d_j^t\in[\bar d_j^t-\Gamma\hat d_j^t,\ \bar d_j^t+\Gamma\hat d_j^t]\ \forall j\Big\},\qquad \mathcal D=\prod_{t\in\mathcal T}\mathcal D^t.$$
--   5. **Two-stage objective** (2) at a commitment: $F(x)+\max_{d\in\mathcal D}\min_{p\in\Omega(x,d)}c(p)$, with $F(x)=\sum_t\sum_i(G_ix_i^t+S_iu_i^t)$, $c(p)=\sum_t\sum_iC_ip_i^t$, and $\Omega(x,d)$ the whole-horizon dispatches satisfying (1h)–(1k); a switch deletes (1i).
--   6. **Policies and non-anticipativity**: a policy assigns to each period $t$ and trajectory $d$ a dispatch $p^t(d)$; it is non-anticipative when $p^t(d)$ depends only on $d^{[t]}=(d^1,\dots,d^t)$.
--   7. **Multistage objective** (5) at a commitment: $F(x)+\min_{p(\cdot)}\max_{d\in\mathcal D}\sum_t\sum_iC_ip_i^t(d^{[t]})$, the minimum over non-anticipative policies satisfying (5b), (5d), (5e) — and (5c) unless deleted by the switch — for every $d\in\mathcal D$.
--   8. **Problem (1P)** objective: $F(x)+\sum_t\max_{d^t\in\mathcal D^t}\min_{p^t\in\Omega_t^{NR}(x,d^t)}\sum_iC_ip_i^t$.
--   9. **Nested value** of $(\widetilde M^{NR})$ from period $k$: $\max_{d^k\in\mathcal D^k}\min_{p^k\in\Omega_k^{NR}(x,d^k)}\{C^\top p^k+\text{(value from }k+1)\}$, and $0$ after the last period.
--
--   These are the objects of Theorem 1, which compares the two-stage and multistage robust UC models when the ramping constraints are removed.
--
--   **Formalization Note** Periods are 0-based (`Fin T`); at the first period $x_i^{t-1}$ and $p^{t-1}$ are the data fields $x^0$, $p^0$, which the paper leaves implicit. The index ranges of (1d)–(1g) are written as $t+UT_i\le T$ and $T\le t+UT_i$ (0-based), so no natural-number subtraction occurs. The commitment variables are real-valued with the $\{0,1\}$ constraint inside $X$. All optimal values are extended reals (`EReal`): a minimum over an empty set is $+\infty$, the paper's convention for an infeasible problem. The two-stage and multistage objectives take a Boolean switch `ramp`; `false` deletes exactly (1i)/(5c). The variable $z$ under the minimum of (5a) is unused in (5) and is omitted.
-- source:
--   Lorca, Sun, Litvinov, Zheng, Multistage adaptive robust optimization for the unit commitment problem, Oper. Res. (2016), doi:10.1287/opre.2015.1456, manuscript of Sept. 29, 2014, pp. 5–7, (1a)–(1k), (2), (3); p. 10, (5), (6); p. 11, (1P), (M̃^NR)

import Mathlib

namespace MultistageRUC.Equiv

/-- Data of the unit commitment model (1), §2.1, pp. 5–6. Generators `Fin Ng`, net-load nodes
`Fin Nd`, buses `Fin Nb`, lines `Fin Nl`, periods `Fin T` (Lean period `t` is the paper's period
`t + 1`).
* `G S C` : no-load, start-up and variable cost of each generator;
* `pmin pmax` : minimum and maximum generation levels;
* `RD RU SD SU` : ramp-down, ramp-up, shut-down and start-up ramp rates (time-indexed as in (1i));
* `UT DT` : minimum up and down times;
* `alpha l` : generation shift factors of line `l` (a vector over buses), `fmax l` its flow limit;
* `Bp Bd` : bus incidence matrices of generators and loads;
* `x0 p0` : the initial on/off status and dispatch, i.e. `x_i^0` and `p_i^0`, used by (1c) and (1i)
  at the first period. -/
structure UCData (Ng Nd Nb Nl T : ℕ) where
  G : Fin Ng → ℝ
  S : Fin Ng → ℝ
  C : Fin Ng → ℝ
  pmin : Fin Ng → ℝ
  pmax : Fin Ng → ℝ
  RD : Fin Ng → Fin T → ℝ
  RU : Fin Ng → Fin T → ℝ
  SD : Fin Ng → Fin T → ℝ
  SU : Fin Ng → Fin T → ℝ
  UT : Fin Ng → ℕ
  DT : Fin Ng → ℕ
  alpha : Fin Nl → Fin Nb → ℝ
  Bp : Matrix (Fin Nb) (Fin Ng) ℝ
  Bd : Matrix (Fin Nb) (Fin Nd) ℝ
  fmax : Fin Nl → ℝ
  x0 : Fin Ng → ℝ
  p0 : Fin Ng → ℝ

variable {Ng Nd Nb Nl T : ℕ}

/-- The on/off status of generator `i` in the period before `t`: `x_i^{t-1}`, which is the
initial status `x0 i` at the first period. -/
def prevX (D : UCData Ng Nd Nb Nl T) (x : Fin Ng → Fin T → ℝ) (t : Fin T) (i : Fin Ng) : ℝ :=
  if h : t.val = 0 then D.x0 i else x i ⟨t.val - 1, by omega⟩

/-- The dispatch of the period before `t`: `p^{t-1}`, which is the initial dispatch `p0` at the
first period. -/
def prevP (D : UCData Ng Nd Nb Nl T) (p : Fin T → Fin Ng → ℝ) (t : Fin T) : Fin Ng → ℝ :=
  if h : t.val = 0 then D.p0 else p ⟨t.val - 1, by omega⟩

/-- The commitment set `X` of (2): commitments `(x, u, v)` satisfying (1b)–(1g). Periods are
0-based: the paper's `t ∈ {1, …, T − UT_i + 1}` is `t.val + UT_i ≤ T`, and the paper's
`t ∈ {T − UT_i + 1, …, T}` is `T ≤ t.val + UT_i` (no natural-number subtraction). -/
def InX (D : UCData Ng Nd Nb Nl T) (x u v : Fin Ng → Fin T → ℝ) : Prop :=
  -- (1b)
  (∀ i t, (x i t = 0 ∨ x i t = 1) ∧ (u i t = 0 ∨ u i t = 1) ∧ (v i t = 0 ∨ v i t = 1)) ∧
  -- (1c)
  (∀ i t, x i t - prevX D x t i = u i t - v i t) ∧
  -- (1d)
  (∀ i (t : Fin T), t.val + D.UT i ≤ T →
    ∑ τ ∈ Finset.univ.filter (fun τ : Fin T => t ≤ τ ∧ τ.val < t.val + D.UT i), x i τ
      ≥ (D.UT i : ℝ) * u i t) ∧
  -- (1e)
  (∀ i (t : Fin T), t.val + D.DT i ≤ T →
    ∑ τ ∈ Finset.univ.filter (fun τ : Fin T => t ≤ τ ∧ τ.val < t.val + D.DT i), (1 - x i τ)
      ≥ (D.DT i : ℝ) * v i t) ∧
  -- (1f)
  (∀ i (t : Fin T), T ≤ t.val + D.UT i →
    ∑ τ ∈ Finset.univ.filter (fun τ : Fin T => t ≤ τ), (x i τ - u i t) ≥ 0) ∧
  -- (1g)
  (∀ i (t : Fin T), T ≤ t.val + D.DT i →
    ∑ τ ∈ Finset.univ.filter (fun τ : Fin T => t ≤ τ), (1 - x i τ - v i t) ≥ 0)

/-- `Ω_t^{NR}(x, d^t)` (p. 11): the dispatches `q` of period `t` satisfying the generation limits
(1h), the line limits (1j) and the energy balance (1k), given the commitment `x` and the period's
net load `e`. The ramping constraints (1i) are not part of it. -/
def OmegaNR (D : UCData Ng Nd Nb Nl T) (x : Fin Ng → Fin T → ℝ) (t : Fin T) (e : Fin Nd → ℝ) :
    Set (Fin Ng → ℝ) :=
  {q | (∀ i, D.pmin i * x i t ≤ q i ∧ q i ≤ D.pmax i * x i t) ∧
       (∀ l, -D.fmax l ≤ dotProduct (D.alpha l) (D.Bp.mulVec q - D.Bd.mulVec e) ∧
             dotProduct (D.alpha l) (D.Bp.mulVec q - D.Bd.mulVec e) ≤ D.fmax l) ∧
       ∑ i, q i = ∑ j, e j}

/-- The ramping constraints (1i) at period `t`, for the dispatch `q` of period `t` and the dispatch
`qprev` of the period before. -/
def rampOK (D : UCData Ng Nd Nb Nl T) (x u v : Fin Ng → Fin T → ℝ) (t : Fin T)
    (qprev q : Fin Ng → ℝ) : Prop :=
  ∀ i, -D.RD i t * x i t - D.SD i t * v i t ≤ q i - qprev i ∧
       q i - qprev i ≤ D.RU i t * prevX D x t i + D.SU i t * u i t

/-- The budget uncertainty set `𝒟^t` of (3), p. 7. -/
def budgetSet (dbar dhat : Fin T → Fin Nd → ℝ) (Γ : ℝ) (t : Fin T) : Set (Fin Nd → ℝ) :=
  {e | ∑ j, |e j - dbar t j| / dhat t j ≤ Γ * Real.sqrt Nd ∧
       ∀ j, e j ∈ Set.Icc (dbar t j - Γ * dhat t j) (dbar t j + Γ * dhat t j)}

/-- The uncertainty set `𝒟 = ∏_{t ∈ 𝒯} 𝒟^t` of net-load trajectories (p. 7). -/
def uncSet (dbar dhat : Fin T → Fin Nd → ℝ) (Γ : ℝ) : Set (Fin T → Fin Nd → ℝ) :=
  Set.univ.pi (budgetSet dbar dhat Γ)

/-- The commitment cost `Σ_t Σ_i (G_i x_i^t + S_i u_i^t)` of (1a). -/
def commitCost (D : UCData Ng Nd Nb Nl T) (x u : Fin Ng → Fin T → ℝ) : ℝ :=
  ∑ t, ∑ i, (D.G i * x i t + D.S i * u i t)

/-- The dispatch cost `Σ_i C_i q_i` of one period. -/
def dispCost (D : UCData Ng Nd Nb Nl T) (q : Fin Ng → ℝ) : ℝ :=
  ∑ i, D.C i * q i

/-- The dispatch set `Ω(x, d)` of the two-stage model (2): whole-horizon dispatches `p` satisfying
(1h), (1j), (1k) at every period, together with the ramping constraints (1i) when `ramp = true`. -/
def twoStageFeas (D : UCData Ng Nd Nb Nl T) (ramp : Bool) (x u v : Fin Ng → Fin T → ℝ)
    (d : Fin T → Fin Nd → ℝ) : Set (Fin T → Fin Ng → ℝ) :=
  {p | ∀ t, p t ∈ OmegaNR D x t (d t) ∧ (ramp = true → rampOK D x u v t (prevP D p t) (p t))}

/-- The objective of the two-stage robust UC (2) at a commitment `(x, u, v)`:
`F(x) + max_{d ∈ 𝒟} min_{p ∈ Ω(x, d)} c(p)`, valued in `EReal` (an empty dispatch set gives `+∞`).
With `ramp = false` the ramping constraints (1i) are deleted. -/
noncomputable def twoStageObj (D : UCData Ng Nd Nb Nl T) (𝒟 : Set (Fin T → Fin Nd → ℝ))
    (ramp : Bool) (x u v : Fin Ng → Fin T → ℝ) : EReal :=
  ((commitCost D x u : ℝ) : EReal) +
    ⨆ d ∈ 𝒟, ⨅ p ∈ twoStageFeas D ramp x u v d, ((∑ t, dispCost D (p t) : ℝ) : EReal)

/-- A dispatch policy: for each period `t` and each net-load trajectory `d`, a dispatch
`p^t(d) ∈ ℝ^{N_g}`. -/
abbrev Policy (Ng Nd T : ℕ) := Fin T → (Fin T → Fin Nd → ℝ) → (Fin Ng → ℝ)

/-- Non-anticipativity `p^t(d^{[t]})` (p. 10): the dispatch at period `t` depends only on the net
loads `d^1, …, d^t` up to and including period `t`. -/
def Nonanticipative (π : Policy Ng Nd T) : Prop :=
  ∀ (t : Fin T) (d d' : Fin T → Fin Nd → ℝ), (∀ s, s ≤ t → d s = d' s) → π t d = π t d'

/-- Robust feasibility of a policy in the multistage model (5): (5b), (5d), (5e) for every
`d ∈ 𝒟` and every period, together with the ramping constraints (5c) when `ramp = true`. -/
def PolicyFeasible (D : UCData Ng Nd Nb Nl T) (𝒟 : Set (Fin T → Fin Nd → ℝ)) (ramp : Bool)
    (x u v : Fin Ng → Fin T → ℝ) (π : Policy Ng Nd T) : Prop :=
  ∀ d ∈ 𝒟, ∀ t, π t d ∈ OmegaNR D x t (d t) ∧
    (ramp = true → rampOK D x u v t (prevP D (fun s => π s d) t) (π t d))

/-- The objective of the multistage robust UC (5) at a commitment `(x, u, v)`: the commitment cost
plus the least worst-case dispatch cost over non-anticipative, robustly feasible policies,
valued in `EReal` (no feasible policy gives `+∞`). With `ramp = false` the ramping constraints
(5c) are deleted. -/
noncomputable def multiStageObj (D : UCData Ng Nd Nb Nl T) (𝒟 : Set (Fin T → Fin Nd → ℝ))
    (ramp : Bool) (x u v : Fin Ng → Fin T → ℝ) : EReal :=
  ((commitCost D x u : ℝ) : EReal) +
    ⨅ π ∈ {π : Policy Ng Nd T | Nonanticipative π ∧ PolicyFeasible D 𝒟 ramp x u v π},
      ⨆ d ∈ 𝒟, ((∑ t, dispCost D (π t d) : ℝ) : EReal)

/-- The per-period worst-case dispatch cost `max_{d^t ∈ 𝒟^t} min_{p^t ∈ Ω_t^{NR}(x, d^t)}
Σ_i C_i p_i^t` of problem (1P), p. 11. -/
noncomputable def perPeriodValue (D : UCData Ng Nd Nb Nl T) (𝒟t : Fin T → Set (Fin Nd → ℝ))
    (x : Fin Ng → Fin T → ℝ) (t : Fin T) : EReal :=
  ⨆ e ∈ 𝒟t t, ⨅ q ∈ OmegaNR D x t e, ((dispCost D q : ℝ) : EReal)

/-- The objective of problem (1P) (p. 11) at a commitment `(x, u, v)`. -/
noncomputable def onePObj (D : UCData Ng Nd Nb Nl T) (𝒟t : Fin T → Set (Fin Nd → ℝ))
    (x u : Fin Ng → Fin T → ℝ) : EReal :=
  ((commitCost D x u : ℝ) : EReal) + ∑ t, perPeriodValue D 𝒟t x t

/-- The nested no-ramping value of `(M̃^{NR})` (p. 11) from period `k` to the end:
`max_{d^k ∈ 𝒟^k} min_{p^k ∈ Ω_k^{NR}(x, d^k)} { C^⊤ p^k + (value from k + 1) }`, and `0` after the
last period. -/
noncomputable def nestedNR (D : UCData Ng Nd Nb Nl T) (𝒟t : Fin T → Set (Fin Nd → ℝ))
    (x : Fin Ng → Fin T → ℝ) (k : ℕ) : EReal :=
  if h : k < T then
    ⨆ e ∈ 𝒟t ⟨k, h⟩, ⨅ q ∈ OmegaNR D x ⟨k, h⟩ e,
      (((dispCost D q : ℝ) : EReal) + nestedNR D 𝒟t x (k + 1))
  else 0
termination_by T - k

end MultistageRUC.Equiv


