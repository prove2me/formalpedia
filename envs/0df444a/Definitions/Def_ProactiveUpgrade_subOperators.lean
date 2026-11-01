-- Prove2me | Definitions.Def_ProactiveUpgrade_subOperators
-- name    : ProactiveUpgrade_subOperators
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:45.352002+00:00
-- url     : https://prove2.me/theorems/d07252bb-8f94-4edf-a17d-898907c7b7b7
-- title:
--   The sub-operators $\hat T_i^P$ and $\hat T_i^U$ of (14)
-- statement:
--   For a continuation value $f=\hat v_{t+1}$, the **parallel fulfilment** operator is
--
--   $$
--   \hat T_i^P[\hat v_t(x)]=\begin{cases}\hat v_{t+1}(x)& x_i=0\\ \hat v_{t+1}(x-e_i)+p_i & x_i>0,\end{cases}
--   $$
--
--   and, for $i=1,\dots,m-1$, the **controlled upgrade** operator is
--
--   $$
--   \hat T_i^U[\hat v_t(x)]=\begin{cases}\hat v_{t+1}(x)& x_i=0,\ x_{i+1}=0\\ \max\{\hat v_{t+1}(x),\ \hat v_{t+1}(x-e_{i+1})+p_i\}& x_i=0,\ x_{i+1}>0\\ \hat v_{t+1}(x-e_i)+p_i& x_i>0,\ x_{i+1}=0\\ \max\{\hat v_{t+1}(x-e_i),\ \hat v_{t+1}(x-e_{i+1})\}+p_i& x_i>0,\ x_{i+1}>0.\end{cases}
--   $$
--
--   Also $\bar q_i=1-q_i$ for $i<m$ and $\bar q_m=1$. $\hat T_i^P$ describes a customer who would reject an upgrade, $\hat T_i^U$ one who would accept it; they decompose the operator $\hat T_i$ in Proposition 2.
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, Proposition 2, eq. (14), pp.14–15; Proof of Proposition 2, p.34

import Mathlib
import Definitions.Def_ProactiveUpgrade_Model

namespace ProactiveUpgrade

/-- The "parallel fulfilment" sub-operator `T̂ᵢᴾ[v̂ₜ(x)]` of (14) (Proposition 2, p.14), applied to
`f = v̂_{t+1}`: `f(x)` if `xᵢ = 0`, `f(x − eᵢ) + pᵢ` if `xᵢ > 0`. -/
def TP {m : ℕ} (M : Model m) (f : (Fin m → ℕ) → ℝ) (x : Fin m → ℕ) (i : Fin m) : ℝ :=
  if x i = 0 then f x else f (dec x i) + M.p i

/-- The "controlled upgrade" sub-operator `T̂ᵢᵁ[v̂ₜ(x)]` of (14) (Proposition 2, pp.14–15), for
`i < m`, applied to `f = v̂_{t+1}`:
* `f(x)` if `xᵢ = 0, x_{i+1} = 0`;
* `max{f(x), f(x − e_{i+1}) + pᵢ}` if `xᵢ = 0, x_{i+1} > 0`;
* `f(x − eᵢ) + pᵢ` if `xᵢ > 0, x_{i+1} = 0`;
* `max{f(x − eᵢ), f(x − e_{i+1})} + pᵢ` if `xᵢ > 0, x_{i+1} > 0`. -/
def TU {m : ℕ} (M : Model m) (f : (Fin m → ℕ) → ℝ) (x : Fin m → ℕ) (i : Fin m)
    (h : i.val + 1 < m) : ℝ :=
  if x i = 0 then
    (if x (succIdx i h) = 0 then f x else max (f x) (f (dec x (succIdx i h)) + M.p i))
  else
    (if x (succIdx i h) = 0 then f (dec x i) + M.p i
     else max (f (dec x i)) (f (dec x (succIdx i h))) + M.p i)

/-- `q̄ᵢ = 1 − qᵢ` for `i < m`, and `q̄_m = 1` (Proof of Proposition 2, p.34: "since q̄_m = 1"). -/
def qbar {m : ℕ} (M : Model m) (i : Fin m) : ℝ :=
  if i.val + 1 < m then 1 - M.q i else 1

end ProactiveUpgrade


