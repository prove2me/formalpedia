-- Prove2me | Definitions.Def_MultistageRUC_WitPolicy_Setting
-- name    : MultistageRUC_WitPolicy_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:11.160919+00:00
-- url     : https://prove2.me/theorems/e2453397-4de0-4e13-a834-217232694eb2
-- title:
--   (3), (8c)–(8e), (8g), (10), (19)–(22), pp. 7, 12–13, 18 — budget set, W_it-policy, its robust constraints, extreme total-load scenarios
-- statement:
--   This file fixes the objects of the affine multistage robust unit commitment model of Lorca, Sun, Litvinov and Zheng under the $W_{it}$-policy.
--
--   **Indices and data.** There are $N_g$ generators $i$, $N_d$ load nodes $j$ and $T$ periods $t$. A net-load trajectory is $\mathbf d = (d^t_j)$, and the **total load** of period $t$ is $\sum_{j\in\mathcal N_d} d^t_j$. Generator $i$ has output limits $p^{\min}_i, p^{\max}_i$ and ramp rates $RD^t_i, RU^t_i, SD^t_i, SU^t_i$; the commitment variables are $x^t_i, u^t_i, v^t_i$; the initial state is $x^0_i$ and $p^0_i$.
--
--   **Uncertainty set (3).** Given nominal loads $\bar d^t_j$, deviations $\hat d^t_j$ and a budget parameter $\Gamma$,
--   $$\mathcal D^t=\Big\{\mathbf d^t:\ \sum_{j\in\mathcal N_d}\frac{|d^t_j-\bar d^t_j|}{\hat d^t_j}\le\Gamma\sqrt{N_d},\ \ d^t_j\in[\bar d^t_j-\Gamma\hat d^t_j,\ \bar d^t_j+\Gamma\hat d^t_j]\ \forall j\Big\},\qquad \mathcal D=\prod_{t\in\mathcal T}\mathcal D^t.$$
--
--   **$W_{it}$-policy (10).** The dispatch of generator $i$ at period $t$ is the affine function of the current total load
--   $$p^t_i(\mathbf d)=w^t_i+W_{it}\sum_{j\in\mathcal N_d}d^t_j .$$
--   The dispatch "at period $t-1$" used by the ramping constraints is $p^{t-1}_i(\mathbf d)$, and for the first period it is the initial dispatch $p^0_i$; likewise $x^{t-1}_i$ is $x^0_i$ for the first period.
--
--   **Robust constraints over a set $S$ of trajectories**, for a generator $i$ and a period $t$:
--   1. generation limits (8c): $p^{\min}_i x^t_i\le p^t_i(\mathbf d)\le p^{\max}_i x^t_i$ for all $\mathbf d\in S$;
--   2. ramping down (8d): $p^t_i(\mathbf d)-p^{t-1}_i(\mathbf d)\ge -RD^t_i x^t_i-SD^t_i v^t_i$ for all $\mathbf d\in S$;
--   3. ramping up (8e): $p^t_i(\mathbf d)-p^{t-1}_i(\mathbf d)\le RU^t_i x^{t-1}_i+SU^t_i u^t_i$ for all $\mathbf d\in S$;
--   4. energy balance (8g): $\sum_{i\in\mathcal N_g}p^t_i(\mathbf d)=\sum_{j\in\mathcal N_d}d^t_j$ for all $\mathbf d\in S$ and all $t$.
--
--   **Extreme scenarios (19)–(22).** A trajectory $\mathbf d_{\max}\in S$ is a maximum-load scenario if its total load is maximal over $S$ in every period, and $\mathbf d_{\min}\in S$ is a minimum-load scenario if its total load is minimal over $S$ in every period. For a period $t$,
--   $$\mathbf d_{minmax}(t)=(\mathbf d^1_{\min},\dots,\mathbf d^{t-1}_{\min},\mathbf d^t_{\max},\dots,\mathbf d^T_{\max}),\qquad \mathbf d_{maxmin}(t)=(\mathbf d^1_{\max},\dots,\mathbf d^{t-1}_{\max},\mathbf d^t_{\min},\dots,\mathbf d^T_{\min}).$$
--
--   These are the objects of Propositions 4 and 6 of the paper.
--
--   **Formalization Note.** Periods are 0-based: Lean period `t : Fin T` is the paper's period $t+1$, so "periods $1,\dots,t-1$" of (21)–(22) become the Lean periods `s < t`. The initial state $x^0_i$, $p^0_i$ is data (`x0`, `p0`), since §2.1 does not introduce it explicitly. The commitments $x,u,v$ are arbitrary reals; the paper's $\{0,1\}$ restriction is not needed for the results stated about these objects. The robust constraints are stated directly for the $W_{it}$-policy (10); the $W_i$-policy (9) is the special case $W_{it}=W_i$. Being a maximum- or minimum-load scenario is a property (`IsMaxLoad`, `IsMinLoad`), not a chosen trajectory, matching the paper's "$\in\operatorname{argmax}$".
-- source:
--   Lorca, Sun, Litvinov, Zheng, Multistage adaptive robust optimization for the unit commitment problem, Oper. Res. (2016), doi:10.1287/opre.2015.1456, manuscript of Sept. 29, 2014, p. 7 (3); pp. 12–13 (8c)–(8e), (8g); p. 13 (9)–(10); p. 18 (19)–(22)

import Mathlib
import Definitions.Def_MultistageRUC_Equiv_Setting

namespace MultistageRUC.WitPolicy

variable {Ng Nd T : ℕ}

/-- Total net load `Σ_{j ∈ 𝒩_d} d_j^t` of period `t` of a net-load trajectory `d`.
Periods are 0-based: Lean period `t : Fin T` is the paper's period `t + 1`. -/
def totalLoad (d : Fin T → Fin Nd → ℝ) (t : Fin T) : ℝ :=
  ∑ j, d t j

/-- The `W_it`-policy (10), p. 13: `p_i^t(d^{[t]}) = w_i^t + W_{it} Σ_j d_j^t`. -/
def witDispatch (w W : Fin Ng → Fin T → ℝ) (i : Fin Ng) (t : Fin T)
    (d : Fin T → Fin Nd → ℝ) : ℝ :=
  w i t + W i t * totalLoad d t

/-- The dispatch of generator `i` in the period before `t` under the `W_it`-policy: the initial
dispatch `p0 i` (the paper's `p_i^0`) for the first period, and `w_i^{t-1} + W_{i,t-1} Σ_j d_j^{t-1}`
otherwise. -/
def witPrev (p0 : Fin Ng → ℝ) (w W : Fin Ng → Fin T → ℝ) (i : Fin Ng) (t : Fin T)
    (d : Fin T → Fin Nd → ℝ) : ℝ :=
  if h : t.val = 0 then p0 i else witDispatch w W i ⟨t.val - 1, by omega⟩ d

/-- The commitment status `x_i^{t-1}` of the period before `t`: the initial status `x0 i` for the
first period. -/
def prevCommit (x0 : Fin Ng → ℝ) (x : Fin Ng → Fin T → ℝ) (i : Fin Ng) (t : Fin T) : ℝ :=
  if h : t.val = 0 then x0 i else x i ⟨t.val - 1, by omega⟩

/-- Robust generation limits (8c) under the `W_it`-policy, for generator `i` and period `t`,
over a set `S` of net-load trajectories:
`p_i^min x_i^t ≤ w_i^t + W_{it} Σ_j d_j^t ≤ p_i^max x_i^t` for all `d ∈ S`. -/
def GenLimits (pmin pmax : Fin Ng → ℝ) (x w W : Fin Ng → Fin T → ℝ)
    (S : Set (Fin T → Fin Nd → ℝ)) (i : Fin Ng) (t : Fin T) : Prop :=
  ∀ d ∈ S, pmin i * x i t ≤ witDispatch w W i t d ∧ witDispatch w W i t d ≤ pmax i * x i t

/-- Robust ramping-down limits (8d) under the `W_it`-policy, for generator `i` and period `t`,
over a set `S`: `p_i^t(d) - p_i^{t-1}(d) ≥ -RD_i^t x_i^t - SD_i^t v_i^t` for all `d ∈ S`. -/
def RampDown (RD SD : Fin Ng → Fin T → ℝ) (x v : Fin Ng → Fin T → ℝ) (p0 : Fin Ng → ℝ)
    (w W : Fin Ng → Fin T → ℝ) (S : Set (Fin T → Fin Nd → ℝ)) (i : Fin Ng) (t : Fin T) :
    Prop :=
  ∀ d ∈ S, witDispatch w W i t d - witPrev p0 w W i t d ≥ -RD i t * x i t - SD i t * v i t

/-- Robust ramping-up limits (8e) under the `W_it`-policy, for generator `i` and period `t`,
over a set `S`: `p_i^t(d) - p_i^{t-1}(d) ≤ RU_i^t x_i^{t-1} + SU_i^t u_i^t` for all `d ∈ S`. -/
def RampUp (RU SU : Fin Ng → Fin T → ℝ) (x0 : Fin Ng → ℝ) (x u : Fin Ng → Fin T → ℝ)
    (p0 : Fin Ng → ℝ) (w W : Fin Ng → Fin T → ℝ) (S : Set (Fin T → Fin Nd → ℝ))
    (i : Fin Ng) (t : Fin T) : Prop :=
  ∀ d ∈ S, witDispatch w W i t d - witPrev p0 w W i t d ≤
    RU i t * prevCommit x0 x i t + SU i t * u i t

/-- Robust energy balance (8g) under the `W_it`-policy over a set `S`:
`Σ_i (w_i^t + W_{it} Σ_j d_j^t) = Σ_j d_j^t` for all `d ∈ S` and all `t`. -/
def EnergyBalance (w W : Fin Ng → Fin T → ℝ) (S : Set (Fin T → Fin Nd → ℝ)) : Prop :=
  ∀ d ∈ S, ∀ t, ∑ i, witDispatch w W i t d = totalLoad d t

/-- `dmax` is a trajectory of (19), p. 18: it lies in `S` and maximizes the total load of every
period over `S`. -/
def IsMaxLoad (S : Set (Fin T → Fin Nd → ℝ)) (dmax : Fin T → Fin Nd → ℝ) : Prop :=
  dmax ∈ S ∧ ∀ d ∈ S, ∀ t, totalLoad d t ≤ totalLoad dmax t

/-- `dmin` is a trajectory of (20), p. 18: it lies in `S` and minimizes the total load of every
period over `S`. -/
def IsMinLoad (S : Set (Fin T → Fin Nd → ℝ)) (dmin : Fin T → Fin Nd → ℝ) : Prop :=
  dmin ∈ S ∧ ∀ d ∈ S, ∀ t, totalLoad dmin t ≤ totalLoad d t

/-- The scenario `d_minmax(t) = (d_min^1, …, d_min^{t-1}, d_max^t, …, d_max^T)` of (21), p. 18.
With 0-based periods, it equals `dmin` on the periods `s < t` and `dmax` on the periods `s ≥ t`. -/
def dminmax (dmin dmax : Fin T → Fin Nd → ℝ) (t : Fin T) : Fin T → Fin Nd → ℝ :=
  fun s => if s < t then dmin s else dmax s

/-- The scenario `d_maxmin(t) = (d_max^1, …, d_max^{t-1}, d_min^t, …, d_min^T)` of (22), p. 18.
With 0-based periods, it equals `dmax` on the periods `s < t` and `dmin` on the periods `s ≥ t`. -/
def dmaxmin (dmin dmax : Fin T → Fin Nd → ℝ) (t : Fin T) : Fin T → Fin Nd → ℝ :=
  fun s => if s < t then dmax s else dmin s

end MultistageRUC.WitPolicy


