-- Prove2me | Definitions.Def_SeqMechExPost_Optimal_Tradeoff
-- name    : SeqMechExPost_Optimal_Tradeoff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:19.843968+00:00
-- url     : https://prove2.me/theorems/39f960dc-1bba-4c43-a220-8515eefe77fe
-- title:
--   Definitions 1–2, Theorem 7, Lemmas 5–6, pp. 10–12 — tight surplus-utility tradeoff problem, cumulative tradeoff functions ĝ_i, optimizers (X^c_i, P^c_i), the Theorem 7 mechanism
-- statement:
--   The single-day building block of the optimal mechanism and the mechanisms built from it.
--
--   1. **Surplus-utility-tradeoff problem (Definition 1).** Given a law $\nu$ on a type interval $[\underline v, \bar v]$, a real tradeoff function $g$ and a bound $c$, a static mechanism $(x,p)$ has allocation probabilities in $[0,1]$ and is incentive compatible. The utility constraint is $\mathbf E_{v\sim\nu}[vx(v)-p(v)]\le c$; the tight variant requires equality. Definition 1 imposes no non-negative-utility constraint for a general $g$. The objective is
--   $$\sup\ \mathbf E_{v\sim\nu}\big[vx(v) + g(vx(v) - p(v))\big]$$
--   over feasible $(x,p)$. Definition 2 specializes the tight variant to cumulative tradeoff functions, whose value $-\infty$ at negative utility forces $vx(v)-p(v)\ge0$ on the type interval. `TradeoffFeasible` represents this specialization.
--
--   2. **Cumulative tradeoff functions (Definition 2).** Set $\hat g_{k+1}(u) = 0$ for $u \ge 0$. For $i = k, \dots, 2$, $\hat g_i(c)$ is the value of the tight problem for day $i$'s law with tradeoff function $g = \hat g_{i+1}$; and $\hat g_1(c)$ is the value of the tight problem for day 1's law with $g(u) = \hat g_2(u) - u$. A mechanism $(X^c_i, P^c_i)$ is an *optimizer* for day $i$ and bound $c$ if it is feasible for that problem and attains $\hat g_i(c)$.
--
--   3. **The Theorem 7 mechanism.** Given optimizer families $(X^c_i, P^c_i)$ and a starting state $c_0$, define $c_i = v_i X^{c_{i-1}}_i(v_i) - P^{c_{i-1}}_i(v_i)$. On day $i$ the buyer is allocated with probability $X^{c_{i-1}}_i(v_i)$ and pays $v_i X^{c_{i-1}}_i(v_i)$ if $i < k$ and $P^{c_{k-1}}_k(v_k)$ if $i = k$. The adjusted mechanism of Lemma 6 has the same allocations and adjusted payments $\hat p_i = P^{c_{i-1}}_i(v_i)$.
--
--   4. **Continuations and the value (15).** For an adjusted mechanism $(x, \hat p)$ and a day $j$, the *continuation by the optimizers* keeps $(x_i, \hat p_i)$ for $i \le j$ and, from the state $v_j x_j(v_{\le j}) - \hat p_j(v_{\le j})$, runs the optimizers on days $i > j$ with the same state update. The quantity of Lemma 5 is
--   $$\mathbf E_{v_1,\dots,v_j}\Big[\hat p_1(v_1) + \sum_{2\le i\le j} x_i(v_{\le i})v_i + \hat g_{j+1}\big(v_j x_j(v_{\le j}) - \hat p_j(v_{\le j})\big)\Big]. \quad (15)$$
--
--   These objects state Lemmas 5 and 6 and Theorem 7: the optimal dynamic mechanism is assembled from the single-day optimizers by passing the realized utility forward as a state.
--
--   **Formalization Note** Days are 0-based: Lean day $i$ is paper day $i+1$. `gHat I i`, `gNext I j` and `gTail I m` are the finite branches of $\hat g_{i+1}$, $\hat g_{j+2}$ and $\hat g_{k+1-m}$ at non-negative arguments; `gHatFull` and `terminalTradeoff` represent their $-\infty$ branches with `WithBot`. `cState X P c0 n` is the paper's $c_n$. Definition 1's generic and tight feasibility predicates are `SurplusTradeoffFeasible` and `TightSurplusTradeoffFeasible`. The pointwise $u\ge0$ condition applies only in `TradeoffFeasible`, the Definition 2 specialization. Its real supremum is used only at $c\ge0$, where the feasible set contains $x\equiv0$, $p\equiv-c$ and the objective is bounded above; at $c<0$ the real `sSup` would be junk. The paper's "revenue utility tradeoff problem" in Definition 2 refers to Definition 1's surplus-utility-tradeoff problem.
-- source:
--   Ashlagi, Daskalakis, Haghpanah, Sequential Mechanisms with ex-post Participation Guarantees, arXiv:1603.07229v2, p. 10 (PDF 11) Definition 1; p. 11 (PDF 12) Definition 2, (15); p. 12 (PDF 13) Lemma 6, Theorem 7

import Mathlib
import Definitions.Def_SeqMechExPost_Optimal_Model

namespace SeqMechExPost.Optimal

open MeasureTheory

variable {k : ℕ}

/-- A static single-parameter mechanism: allocation probability `x v` and payment `p v`. -/
structure StaticMech where
  /-- allocation probability `x(v)` -/
  x : ℝ → ℝ
  /-- payment `p(v)` -/
  p : ℝ → ℝ

/-- Incentive compatibility on the type interval `[lo, hi]`:
`v x(v) − p(v) ≥ v x(v') − p(v')`. -/
def StaticMech.IC (lo hi : ℝ) (m : StaticMech) : Prop :=
  ∀ v ∈ Set.Icc lo hi, ∀ v' ∈ Set.Icc lo hi, v * m.x v' - m.p v' ≤ v * m.x v - m.p v

/-- Definition 1, p. 10: the surplus-utility-tradeoff problem with the bound
`E[v x(v) − p(v)] ≤ c`. For a general real tradeoff function `g`, Definition 1 does not impose
non-negative utility. Integrability makes both expectations genuine real integrals. -/
def SurplusTradeoffFeasible (ν : Measure ℝ) (lo hi : ℝ) (g : ℝ → ℝ) (c : ℝ)
    (m : StaticMech) : Prop :=
  Measurable m.x ∧ Measurable m.p ∧
  (∀ v ∈ Set.Icc lo hi, m.x v ∈ Set.Icc (0 : ℝ) 1) ∧
  m.IC lo hi ∧
  Integrable m.p ν ∧
  Integrable (fun v => v * m.x v - m.p v) ν ∧
  Integrable (fun v => v * m.x v + g (v * m.x v - m.p v)) ν ∧
  ∫ v, (v * m.x v - m.p v) ∂ν ≤ c

/-- The tight variant in Definition 1 replaces the utility bound by equality. -/
def TightSurplusTradeoffFeasible (ν : Measure ℝ) (lo hi : ℝ) (g : ℝ → ℝ) (c : ℝ)
    (m : StaticMech) : Prop :=
  SurplusTradeoffFeasible ν lo hi g c m ∧
  ∫ v, (v * m.x v - m.p v) ∂ν = c

/-- The tight problem as specialized in Definition 2, p. 11: non-negative utility on the type
interval additionally enforces the `−∞` branch of the recursively defined cumulative tradeoff
functions. This extra condition is specific to Definition 2, not Definition 1 for arbitrary `g`. -/
def TradeoffFeasible (ν : Measure ℝ) (lo hi : ℝ) (g : ℝ → ℝ) (c : ℝ) (m : StaticMech) : Prop :=
  Measurable m.x ∧ Measurable m.p ∧
  (∀ v ∈ Set.Icc lo hi, m.x v ∈ Set.Icc (0 : ℝ) 1) ∧
  m.IC lo hi ∧
  (∀ v ∈ Set.Icc lo hi, 0 ≤ v * m.x v - m.p v) ∧
  Integrable m.p ν ∧
  Integrable (fun v => v * m.x v + g (v * m.x v - m.p v)) ν ∧
  ∫ v, (v * m.x v - m.p v) ∂ν = c

/-- The objective of Definition 1: `E_{v∼ν}[v x(v) + g(v x(v) − p(v))]`. -/
noncomputable def tradeoffObj (ν : Measure ℝ) (g : ℝ → ℝ) (m : StaticMech) : ℝ :=
  ∫ v, (v * m.x v + g (v * m.x v - m.p v)) ∂ν

/-- The real value of the Definition 2 specialization of the tight tradeoff problem. It is used
only at `c ≥ 0`, where the feasible set is nonempty and the objective bounded above. -/
noncomputable def tradeoffValue (ν : Measure ℝ) (lo hi : ℝ) (g : ℝ → ℝ) (c : ℝ) : ℝ :=
  sSup (tradeoffObj ν g '' {m | TradeoffFeasible ν lo hi g c m})

/-- The terminal cumulative tradeoff `ĝ_{k+1}` of Definition 2, including its `−∞` branch. -/
noncomputable def terminalTradeoff (u : ℝ) : WithBot ℝ :=
  if 0 ≤ u then (0 : ℝ) else ⊥

/-- The cumulative tradeoff functions of Definition 2 (p. 11), indexed by the number `m` of
remaining days: `gTail I 0` is the paper's `ĝ_{k+1}` (on `u ≥ 0`, where it is `0`), and
`gTail I (m + 1)` is the paper's `ĝ_{k−m}`, the value of the tight problem for the law of Lean day
`k − 1 − m` with tradeoff function `gTail I m`. -/
noncomputable def gTail (I : Instance k) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | m + 1 =>
    if h : m < k then
      tradeoffValue (I.μ ⟨k - 1 - m, by omega⟩) (I.lo ⟨k - 1 - m, by omega⟩)
        (I.hi ⟨k - 1 - m, by omega⟩) (gTail I m)
    else fun _ => 0

/-- The tradeoff function used on Lean day `i` (paper day `i + 1`) in Definition 2:
`g(u) = ĝ_{i+2}(u)` for paper days `≥ 2`, and `g(u) = ĝ_2(u) − u` on paper day 1. -/
noncomputable def stageG (I : Instance k) (i : Fin k) : ℝ → ℝ :=
  if i.val = 0 then fun u => gTail I (k - 1) u - u else gTail I (k - 1 - i.val)

/-- The finite branch, for `c ≥ 0`, of the cumulative tradeoff function of Lean day `i`,
the paper's `ĝ_{i+1}`. Values at `c < 0` are not used; `gHatFull` supplies that branch. -/
noncomputable def gHat (I : Instance k) (i : Fin k) : ℝ → ℝ :=
  tradeoffValue (I.μ i) (I.lo i) (I.hi i) (stageG I i)

/-- The cumulative tradeoff function `ĝ_{i+1}` of Definition 2, with value `−∞` at negative
utility bounds. The `WithBot` value is real on `c ≥ 0`, where the recursive optimization lives. -/
noncomputable def gHatFull (I : Instance k) (i : Fin k) (c : ℝ) : WithBot ℝ :=
  if 0 ≤ c then (gHat I i c : WithBot ℝ) else ⊥

/-- The continuation tradeoff function after Lean day `j`, the paper's `ĝ_{j+2}` (it is `0` on
`u ≥ 0` after the last day). -/
noncomputable def gNext (I : Instance k) (j : Fin k) : ℝ → ℝ :=
  gTail I (k - 1 - j.val)

/-- `m` solves the tight tradeoff problem of Lean day `i` with utility bound `c`: it is feasible
and attains `ĝ_{i+1}(c)` (the paper's `(X^c_{i+1}, P^c_{i+1})` of Definition 2). -/
def IsOptimizer (I : Instance k) (i : Fin k) (c : ℝ) (m : StaticMech) : Prop :=
  TradeoffFeasible (I.μ i) (I.lo i) (I.hi i) (stageG I i) c m ∧
  tradeoffObj (I.μ i) (stageG I i) m = gHat I i c

/-- The forward utility state when days `n0, n0 + 1, …` follow the optimizer families `X`, `P`
(`X i c v` is `X^c(v)` of Lean day `i`): `runState … 0 v = c v` is the state before day `n0`, and
`runState … (n + 1) v = v_d X_d^{s}(v_d) − P_d^{s}(v_d)` for `d = n0 + n` and the previous state
`s`. -/
noncomputable def runState (X P : Fin k → ℝ → ℝ → ℝ) (n0 : ℕ) (c : (Fin k → ℝ) → ℝ) :
    ℕ → (Fin k → ℝ) → ℝ
  | 0, v => c v
  | n + 1, v =>
    if h : n0 + n < k then
      v ⟨n0 + n, h⟩ * X ⟨n0 + n, h⟩ (runState X P n0 c n v) (v ⟨n0 + n, h⟩)
        - P ⟨n0 + n, h⟩ (runState X P n0 c n v) (v ⟨n0 + n, h⟩)
    else 0

/-- Theorem 7's state: `cState X P c0 i v` is the paper's `c_i` (`c_0` the chosen `c0`); Lean day
`i` reads `cState X P c0 i.val v`. -/
noncomputable def cState (X P : Fin k → ℝ → ℝ → ℝ) (c0 : ℝ) (n : ℕ) (v : Fin k → ℝ) : ℝ :=
  runState X P 0 (fun _ => c0) n v

/-- The mechanism of Theorem 7, step 1 (p. 12): on day `i` allocate with probability
`X^{c_{i−1}}_i(v_i)`; charge `v_i X^{c_{i−1}}_i(v_i)` before the last day and `P^{c_{i−1}}_k(v_k)` on
the last day. -/
noncomputable def thm7Mech (X P : Fin k → ℝ → ℝ → ℝ) (c0 : ℝ) : SeqMech k where
  x i v := X i (cState X P c0 i.val v) (v i)
  p i v :=
    if i.val + 1 < k then v i * X i (cState X P c0 i.val v) (v i)
    else P i (cState X P c0 i.val v) (v i)

/-- The adjusted mechanism of Lemma 6 (p. 12): `x_i = X^{c_{i−1}}_i(v_i)`,
`p̂_i = P^{c_{i−1}}_i(v_i)`. -/
noncomputable def thm7Adj (X P : Fin k → ℝ → ℝ → ℝ) (c0 : ℝ) : AdjMech k where
  x i v := X i (cState X P c0 i.val v) (v i)
  pHat i v := P i (cState X P c0 i.val v) (v i)

/-- The adjusted mechanism that follows `A` on days `≤ j` and, from the state
`u_j = v_j x_j − p̂_j` of day `j`, follows the optimizers `X`, `P` on days `> j`. -/
noncomputable def followFrom (A : AdjMech k) (X P : Fin k → ℝ → ℝ → ℝ) (j : Fin k) :
    AdjMech k where
  x i v :=
    if i ≤ j then A.x i v
    else X i (runState X P (j.val + 1) (fun v => v j * A.x j v - A.pHat j v)
      (i.val - (j.val + 1)) v) (v i)
  pHat i v :=
    if i ≤ j then A.pHat i v
    else P i (runState X P (j.val + 1) (fun v => v j * A.x j v - A.pHat j v)
      (i.val - (j.val + 1)) v) (v i)

/-- The expression (15) of Lemma 5 for Lean day `j` (paper day `j + 1`):
`E[p̂_1(v_1) + ∑_{2 ≤ i ≤ j+1} x_i v_i + ĝ_{j+2}(v_{j+1} x_{j+1} − p̂_{j+1})]`. -/
noncomputable def contValue (I : Instance k) (A : AdjMech k) (j : Fin k) : ℝ :=
  ∫ v, ((∑ i, if i.val = 0 then A.pHat i v else if i ≤ j then v i * A.x i v else 0)
      + gNext I j (v j * A.x j v - A.pHat j v)) ∂I.law

end SeqMechExPost.Optimal


