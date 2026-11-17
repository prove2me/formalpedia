-- Prove2me | Definitions.Def_AnytimeAdaVR_Supplement_alg1Stage
-- name    : AnytimeAdaVR_Supplement_alg1Stage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:29:18.121438+00:00
-- url     : https://prove2.me/theorems/b707e699-41c1-463c-94b8-526eb10a5cfb
-- title:
--   One stage S, M or D of the fixed-budget Algorithm 1
-- statement:
--   Fix a stochastic gradient $g(x;\xi)$ on $\mathbb R^d$, a stage $i\in\{S,M,D\}$, an integer $n\ge1$, a starting point $Y$, a stream of fresh samples $\xi_0,\xi_1,\dots$ and a stream of coins $U_1,U_2,\dots\in[0,1]$. With $N(v)=v/\|v\|$ for $v\neq0$ and $N(0)=0$, the stage sets $x_0=Y$ and, for $t=0,\dots,n-1$:
--
--   1. computes the estimator $v_t$: $v_0=g(x_0;\xi_0)$, and for $t\ge1$
--   $$
--   \begin{aligned}
--   \text{S:}\quad & v_t=(1-\gamma)v_{t-1}+\gamma\, g(x_t;\xi_t), && \gamma=n^{-1/2},\ \eta_S=n^{-3/4},\\
--   \text{M:}\quad & v_t=g(x_t;\xi_t)+(1-\beta)\big[v_{t-1}-g(x_{t-1};\xi_t)\big], && \eta_M=\beta=n^{-2/3},\\
--   \text{D:}\quad & v_t=g(x_t;\xi_t), && \eta_D=n^{-1/2};
--   \end{aligned}
--   $$
--   2. replaces the stage's candidate $X_i$ by $x_t$ if $U_{t+1}\le 1/(t+1)$ (with uniform coins, probability $1/(t+1)$);
--   3. updates $x_{t+1}=x_t-\eta_i N(v_t)$.
--
--   The stage returns its endpoint $x_n$ and its candidate $X_i$. Stage M uses the same fresh sample $\xi_t$ at $x_t$ and at $x_{t-1}$. Every gradient evaluation is counted, so a stage costs $n$ evaluations in S and D and $1+2(n-1)=2n-1$ in M.
--
--   Reservoir sampling makes the candidate uniform on $\{x_0,\dots,x_{n-1}\}$; it is distinct from the endpoint $x_n$, which starts the next stage.
--
--   **Formalization Note** $N$ is the published `GarberOLO.Alg3.unitDir`. The coin of iteration $t$ is $U_{t+1}$; $U_1\le1$ always holds, so $x_0$ is the first candidate. For $n=1$ all parameters equal $1$ and no $t\ge1$ step occurs.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41001434449aea8ba3a6ba5d66658a8f94ea9ffeebad36bbb903374006), Algorithm 1 (lines 2–13), p.5; eqs. (3)–(6), pp.4–5; Output selection, p.5

import Mathlib
import Definitions.Def_AnytimeAdaVR_Path
import Definitions.Def_GarberOLO_Alg3_unitDir
import Definitions.Def_AnytimeAdaVR_Supplement_oracleQuery

namespace AnytimeAdaVR.Supplement

open AnytimeAdaVR

/-- **One stage S, M or D of Algorithm 1.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction
across Smoothness and Noise Conditions* (preprint, 2026), Algorithm 1, lines 2–3 and 5–13, p.5, with
eqs. (3)–(6), pp.4–5: `x_0 ← Y`; for `t = 0, …, n − 1`: draw a fresh sample `ξ_t`; `v_0 ← g(x_0; ξ_0)`
if `t = 0`; for `t ≥ 1`
* stage S (4): `v_t = (1 − γ)v_{t−1} + γ g(x_t; ξ_t)`, `γ = n^{−1/2}`, step `η_S = n^{−3/4}`;
* stage M (5): `v_t = g(x_t; ξ_t) + (1 − β)[v_{t−1} − g(x_{t−1}; ξ_t)]`, `η_M = β = n^{−2/3}`, the
  same fresh sample at `x_t` and `x_{t−1}`;
* stage D (6): `v_t = g(x_t; ξ_t)`, step `η_D = n^{−1/2}`;

"With probability 1/(t + 1), set X_i ← x_t"; `x_{t+1} ← x_t − η_i N(v_t)` with `N` of (3).

`alg1Stage g i n Y ξ U` returns `(x_n, X_i)`: the stage's endpoint and its retained candidate.
The fresh sample of iteration `t` is `ξ t`; the coin of iteration `t` is `U (t + 1)`, and the
candidate is replaced iff `U (t + 1) ≤ 1/(t + 1)`. Every gradient evaluation is an
`oracleQuery`, so the counter grows by `1` at `t = 0`, and at each `t ≥ 1` by `1` in stages S, D
and by `2` in stage M.

**Formalization Note.** `N` is the published `GarberOLO.Alg3.unitDir` (`N(0) = 0`). The loop state
is `(x_t, x_{t−1}, v_{t−1}, X_i)`; at `t = 0` the entries `x_{−1}, v_{−1}` and the initial candidate
are placeholders that are never read, since iteration `0` uses only `x_0` and the coin `U 1 ≤ 1`
always replaces the candidate by `x_0`. With uniform coins on `[0, 1]` the replacement has
probability `1/(t + 1)`, and the candidate is uniform on `{x_0, …, x_{n−1}}` (not the endpoint
`x_n`). Powers of `n` are real powers; `n ≥ 1` in Theorem 1, where `n = 1` gives
`γ = β = η_i = 1` and the `t ≥ 1` iterations do not occur. -/
noncomputable def alg1Stage {d : ℕ} {Ξ : Type*}
    (g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d)) (i : Path) (n : ℕ)
    (Y : EuclideanSpace ℝ (Fin d)) (ξ : ℕ → Ξ) (U : ℕ → unitInterval) :
    StateM ℕ (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  let η : ℝ := match i with
    | .S => (n : ℝ) ^ (-(3 / 4 : ℝ))
    | .M => (n : ℝ) ^ (-(2 / 3 : ℝ))
    | .D => (n : ℝ) ^ (-(1 / 2 : ℝ))
  let γ : ℝ := (n : ℝ) ^ (-(1 / 2 : ℝ))
  let β : ℝ := (n : ℝ) ^ (-(2 / 3 : ℝ))
  let body : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d) → ℕ →
      StateM ℕ (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ×
        EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
    fun s t => do
      let (x, xprev, vprev, X) := s
      let v ← if t = 0 then oracleQuery g x (ξ 0) else
        match i with
        | .S => do
            let q ← oracleQuery g x (ξ t)
            pure ((1 - γ) • vprev + γ • q)
        | .M => do
            let q ← oracleQuery g x (ξ t)
            let q' ← oracleQuery g xprev (ξ t)
            pure (q + (1 - β) • (vprev - q'))
        | .D => oracleQuery g x (ξ t)
      let X' := if ((U (t + 1) : ℝ) ≤ 1 / ((t : ℝ) + 1)) then x else X
      pure (x - η • GarberOLO.Alg3.unitDir v, x, v, X')
  do
    let (x, _, _, X) ← (List.range n).foldlM body (Y, Y, 0, Y)
    pure (x, X)

end AnytimeAdaVR.Supplement


