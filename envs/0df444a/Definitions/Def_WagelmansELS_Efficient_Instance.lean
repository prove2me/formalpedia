-- Prove2me | Definitions.Def_WagelmansELS_Efficient_Instance
-- name    : WagelmansELS_Efficient_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:42.487992+00:00
-- url     : https://prove2.me/theorems/d7ea4911-c936-4425-a392-a6acfa8dac21
-- title:
--   Section 1 and Equation (1): the lot-sizing data and backward value
-- statement:
--   Fix a planning horizon of $n\ge1$ periods, numbered $1,\dots,n$. Demand $d_i$ is nonnegative, with $d_n>0$; setup costs $f_i$ are nonnegative; marginal production costs $c_i$ are arbitrary real numbers. Values of the data at index zero or beyond the horizon are unused. Define cumulative demand $D(t)=\sum_{j=t}^{n}d_j$, so $D(n+1)=0$. The cost of producing at $i$ up to the next production period $t$ is $f_i+c_i[D(i)-D(t)]$.
--
--   The **backward value** has terminal value $G(n+1)=0$. At a positive-demand period it obeys
--   $$G(i)=\min_{i<t\le n+1}\{f_i+c_i[D(i)-D(t)]+G(t)\}.$$
--   At a zero-demand period the alternative of skipping setup is included:
--   $$G(i)=\min\left\{G(i+1),\ \min_{i+1<t\le n+1}\bigl(f_i+c_i[D(i)-D(t)]+G(t)\bigr)\right\}.$$
--   An empty inner minimum is omitted. The module also defines the setup cost and the candidate score $c_i[D(i)-D(t)]+G(t)$.
--
--   This recursion supplies the values used to construct the lower envelope. The paper identifies $G$ with the optimal lot-sizing cost by the cited zero-inventory property; that identification with Formulations I and II is outside this mission.
--
--   **Formalization Note** The table computes periods backward. Periods are natural numbers, and $n+1$ is the sentinel. The data are real-valued and no sign condition is imposed on $c_i$.
-- source:
--   Wagelmans, Van Hoesel and Kolen, Economic Lot Sizing, Oper. Res. 40 Supp. 1 (1992), pp. S146–S147, Section 1 and Eq. (1)

import Mathlib

namespace WagelmansELS.Efficient

/-- An economic lot sizing instance in Section 2. Only periods `1,...,n` are data. -/
structure Instance where
  n : ℕ
  d : ℕ → ℝ
  f : ℕ → ℝ
  c : ℕ → ℝ
  n_pos : 1 ≤ n
  d_nonneg : ∀ i, 1 ≤ i → i ≤ n → 0 ≤ d i
  d_last_pos : 0 < d n
  f_nonneg : ∀ i, 1 ≤ i → i ≤ n → 0 ≤ f i

namespace Instance
variable (P : Instance)

/-- Demand from `t` to `n`, with `D (n+1)=0`. -/
def D (t : ℕ) : ℝ := ∑ j ∈ Finset.Icc t P.n, P.d j

/-- Cost of a setup at `i` followed by the next setup at `t`. -/
def setupCost (i t : ℕ) (later : ℕ → ℝ) : ℝ :=
  P.f i + P.c i * (P.D i - P.D t) + later t

/-- Backward dynamic-programming table. Stage `m` has computed the last `m` periods. -/
noncomputable def Gtable : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | m + 1 =>
      let i := P.n - m
      let old := Gtable m
      let positiveCost := (Finset.Ioc i (P.n + 1)).inf'
        (by simp; omega) (fun t => P.setupCost i t old)
      let value := if 0 < P.d i then positiveCost
        else min (old (i + 1))
          (if h : (Finset.Ioc (i + 1) (P.n + 1)).Nonempty then
            (Finset.Ioc (i + 1) (P.n + 1)).inf' h (fun t => P.setupCost i t old)
           else old (i + 1))
      fun t => if t = i then value else old t

/-- The backward value `G`, including sentinel `G(n+1)=0`. -/
noncomputable def G (t : ℕ) : ℝ := P.Gtable P.n t

/-- The quantity minimized in the threshold rule, with setup cost omitted. -/
noncomputable def score (i t : ℕ) : ℝ := P.c i * (P.D i - P.D t) + P.G t

end Instance
end WagelmansELS.Efficient


