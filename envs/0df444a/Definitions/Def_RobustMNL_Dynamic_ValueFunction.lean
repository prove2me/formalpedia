-- Prove2me | Definitions.Def_RobustMNL_Dynamic_ValueFunction
-- name    : RobustMNL_Dynamic_ValueFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T14:21:31.543971+00:00
-- url     : https://prove2.me/theorems/b554655c-912c-43a5-a507-856af3c03bbd
-- title:
--   Sec. 4, pp. 15–17 — robust capacity allocation: value function J_t(x) by (Dynamic Robust), marginal value ΔJ_t(x), optimal assortment S*_t(x)
-- statement:
--   A seller allocates capacity over periods $t = 1, \dots, T$; one customer arrives per period. In period $t$ the customer chooses from the offered assortment by a multinomial logit model whose parameter vector $v_t$ is unknown and lies in a compact nonempty uncertainty set $\mathcal V_t \subseteq \mathbb R^{n+1}_{++}$. A purchase of product $i$ earns $r_i$ and consumes one unit of capacity.
--
--   The **value function** $J_t(x)$, the maximum worst-case expected revenue over periods $t, \dots, T$ with $x$ units of capacity at the start of period $t$, is given by the Bellman equation
--   $$J_t(x) = \max_{S_t \subseteq \mathcal A}\ \min_{v_t \in \mathcal V_t} \Big\{ \sum_{i\in S_t} \phi_i(S_t, v_t)\big(r_i + J_{t+1}(x-1)\big) + \Big(1 - \sum_{i\in S_t}\phi_i(S_t,v_t)\Big) J_{t+1}(x) \Big\}$$
--   for $1 \le t \le T$, $x \ge 1$, with boundary conditions $J_t(0) = 0$ and $J_{T+1}(x) = 0$. The **marginal value of capacity** is $\Delta J_t(x) = J_t(x) - J_t(x-1)$ for $x \ge 1$. $S^*_t(x)$ is an assortment attaining the maximum on the right-hand side, with ties broken by the smallest cardinality.
--
--   These objects carry every result of Section 4: concavity of $J_t$ in capacity, the threshold form of $S^*_t(x)$, and the monotonicity of $S^*_t(x)$ in capacity and time.
--
--   **Formalization Note** $J$ is **defined** by the recursion above (through `Jgo`, indexed by periods to go: `J T V r t x = Jgo T V r (T + 1 - t) x`, and with $s+1$ periods to go the current period is $t = T - s$, whose set is `V (T - s)`). The paper obtains the recursion from a max-min policy formulation by a theorem of Iyengar (2005); that formulation and theorem are not formalized. $J_t(x)$ is defined for every $x \in \mathbb N$ (the recursion never uses the initial capacity $C$; the paper's $J_t$ on $\{0,\dots,C\}$ is its restriction). `IsUncertaintySeq T V` is the standing assumption that `V t` is compact, nonempty and positive for $1 \le t \le T$. `marginalValue` uses natural-number subtraction and is only meaningful for $x \ge 1$; every theorem assumes $x \ge 1$. `IsOptAssort T V r t x S` is the predicate "$S = S^*_t(x)$", including the tie-break of the proof of Theorem 4.2 (p. 17).
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, Sec. 4, p. 15 (model, compact V_t ⊆ ℝⁿ⁺¹₊₊), p. 16 (Bellman equation (Dynamic Robust), first line; boundary conditions; ΔJ; S*_t(x)), p. 17 (tie-break, proof of Theorem 4.2)

import Mathlib
import Definitions.Def_RobustMNL_Dynamic_StaticModel

namespace RobustMNL.Dynamic

/-- The standing assumption of Sec. 4 (p. 15): for every period `t = 1, …, T` the uncertainty
set `V t` (the paper's `V_t`) is compact, nonempty and contained in `ℝⁿ⁺¹₊₊`. The values of `V`
at `t = 0` and `t > T` are never used. -/
def IsUncertaintySeq {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ))) : Prop :=
  ∀ t, 1 ≤ t → t ≤ T → IsCompact (V t) ∧ (V t).Nonempty ∧ ∀ p ∈ V t, RobustMNL.Static.IsPos p

/-- The worst case, over `v_t ∈ V_t`, of the expression inside the Bellman equation (Dynamic
Robust) of p. 16 for a fixed assortment `S`, with `a = J_{t+1}(x − 1)` and `b = J_{t+1}(x)`:
`min_{v ∈ V_t} { ∑_{i ∈ S} φ_i(S, v) (r_i + a) + (1 − ∑_{i ∈ S} φ_i(S, v)) b }`.
Written as a real infimum; on a compact nonempty `V_t ⊆ ℝⁿ⁺¹₊₊` it is the attained minimum. -/
noncomputable def stageValue {n : ℕ} (Vt : Set (ℝ × (Fin n → ℝ))) (r : Fin n → ℝ) (a b : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  sInf ((fun p => ∑ i ∈ S, choiceProb S p i * (r i + a)
      + (1 - ∑ i ∈ S, choiceProb S p i) * b) '' Vt)

/-- The value function indexed by the number of periods to go: `Jgo T V r s x` is the paper's
`J_{T+1−s}(x)`. With `s + 1` periods to go the current period is `t = T − s`, whose uncertainty
set is `V (T − s)`. The equations are the first line of (Dynamic Robust), p. 16, with the
boundary conditions `J_{T+1} ≡ 0` and `J_t(0) = 0`: the maximum over **all** assortments
`S ⊆ 𝒜` of the worst case over `V_t`. -/
noncomputable def Jgo {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ))) (r : Fin n → ℝ) :
    ℕ → ℕ → ℝ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | s + 1, x + 1 =>
      (Finset.univ : Finset (Finset (Fin n))).sup' Finset.univ_nonempty
        (fun S => stageValue (V (T - s)) r (Jgo T V r s x) (Jgo T V r s (x + 1)) S)

/-- The value function `J_t(x)` of Sec. 4, p. 16: the maximum worst case total expected revenue
over periods `t, …, T` with `x` units of capacity at the start of period `t`, **defined** by the
Bellman recursion (Dynamic Robust) and its boundary conditions; `J (T + 1) x = 0` and
`J t 0 = 0`. It is defined for every `x ∈ ℕ` (the recursion never uses the initial capacity
`C`); the paper's `J_t` on `{0, …, C}` is its restriction. The policy formulation
`max_π min_ψ E^{π,ψ}[…]` of p. 15 and Iyengar's (2005) theorem that it satisfies this recursion
are not formalized. -/
noncomputable def J {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ))) (r : Fin n → ℝ)
    (t x : ℕ) : ℝ :=
  Jgo T V r (T + 1 - t) x

/-- The marginal value of capacity `ΔJ_t(x) = J_t(x) − J_t(x − 1)` (p. 16). Only used with
`1 ≤ x`: at `x = 0` the natural-number subtraction would give the junk value `0`. -/
noncomputable def marginalValue {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ))) (r : Fin n → ℝ)
    (t x : ℕ) : ℝ :=
  J T V r t x - J T V r t (x - 1)

/-- The right-hand side of the Bellman equation (Dynamic Robust), p. 16, for a fixed assortment
`S` in period `t` with `x ≥ 1` units of capacity:
`min_{v_t ∈ V_t} { ∑_{i ∈ S} φ_i(S, v_t)(r_i + J_{t+1}(x − 1)) + (1 − ∑_{i ∈ S} φ_i(S, v_t)) J_{t+1}(x) }`. -/
noncomputable def bellmanObj {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ))) (r : Fin n → ℝ)
    (t x : ℕ) (S : Finset (Fin n)) : ℝ :=
  stageValue (V t) r (J T V r (t + 1) (x - 1)) (J T V r (t + 1) x) S

/-- `S` is the paper's `S*_t(x)` (p. 16): a maximizer of the right-hand side of the Bellman
equation over all assortments, with ties broken by the smallest cardinality (Proof of
Theorem 4.2, p. 17). Meaningful for `1 ≤ t ≤ T` and `x ≥ 1`. -/
def IsOptAssort {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ))) (r : Fin n → ℝ)
    (t x : ℕ) (S : Finset (Fin n)) : Prop :=
  bellmanObj T V r t x S =
      (Finset.univ : Finset (Finset (Fin n))).sup' Finset.univ_nonempty (bellmanObj T V r t x) ∧
    ∀ S' : Finset (Fin n),
      bellmanObj T V r t x S' =
          (Finset.univ : Finset (Finset (Fin n))).sup' Finset.univ_nonempty (bellmanObj T V r t x) →
        S.card ≤ S'.card

end RobustMNL.Dynamic


