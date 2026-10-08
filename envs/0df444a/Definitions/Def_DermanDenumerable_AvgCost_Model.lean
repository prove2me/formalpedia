-- Prove2me | Definitions.Def_DermanDenumerable_AvgCost_Model
-- name    : DermanDenumerable_AvgCost_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:01:44.523856+00:00
-- url     : https://prove2.me/theorems/06266044-f5d5-4d58-b3cd-b8430089cac7
-- title:
--   Derman's average-cost model on a denumerable state space: E_R W_t, Q_R(i), equations (1) and (2), g_n, conditions (B)–(F), ε_i^R and policy improvement
-- statement:
--   This file fixes the objects of Derman's *Denumerable State Markovian Decision Processes—Average Cost Criterion* (1966), §1, §3 and §4.
--
--   **The model.** A system is observed at times $t = 0, 1, 2, \dots$ and classified into one of the states of a denumerable set $I$. At state $i$ one of finitely many decisions $k \in A(i)$ is made (condition (A): $K_i < \infty$, with $K_i \ge 1$), a cost $w_{ik}$ is incurred, and the next state is $j$ with probability $q_{ij}(k)$, where $\sum_{j \in I} q_{ij}(k) = 1$. The underlying structure is the published Markov decision chain `SennottDP.AvgFinite.MDC`. A **rule** $R$ of the class $C$ chooses the decision at time $t$ with a probability that may depend on the whole history; $C''$ is the class of stationary deterministic rules ("make decision $k_i$ at state $i$").
--
--   **Costs and criteria.** Condition (B) requires $\{w_{ik}\}$ to be bounded. For a rule $R$ and $Y_0 = i$, $E_R W_t$ is the expected cost at time $t$,
--   $$h_n(i) = \sum_{t=0}^{n} E_R W_t$$
--   is the total expected cost over the periods $0, \dots, n$, and the **average cost** is
--   $$Q_R(i) = \limsup_{T\to\infty} \frac{1}{T+1}\sum_{t=0}^{T} E_R W_t .$$
--   A rule is **optimal over $C$** if $Q_R(i) \le Q_{R'}(i)$ for every rule $R' \in C$ and every $i \in I$; **optimal over $C''$** is the same with $R' \in C''$.
--
--   **Equations.** For a bounded $v = \{v_j\}$, equation (1) is
--   $$g + v_i = \min_k \Big\{ w_{ik} + \sum_{j\in I} q_{ij}(k) v_j \Big\}, \qquad i \in I,$$
--   and, for a rule $R \in C''$ with decisions $k_i$, equation (2) is $g + v_i = w_{ik_i} + \sum_{j} q_{ij}(k_i) v_j$ for all $i$. A rule **minimizes against $v$** if each $k_i$ attains the minimum in (1). The value iteration $g_n$ of (5) is $g_0(i) = \min_k w_{ik}$, $g_{n+1}(i) = \min_k \{w_{ik} + \sum_j q_{ij}(k) g_n(j)\}$.
--
--   **Conditions of §4.** (C): for every $R \in C''$ the Markov chain $p_{ij} = q_{ij}(k_i)$ is irreducible and every state is positive recurrent. (E): a family $\{g^R, v^R_j\}$ solves (2) for every $R \in C''$ and is bounded uniformly in $j$ and $R$. (F): for every $j$, the Cesàro limits $\pi_{ij}(R) = \lim_T (T+1)^{-1}\sum_{t=0}^T P\{Y_t = j \mid Y_0 = i\}$ exist and $\inf_{R \in C'', i \in I} \pi_{ij}(R) > 0$.
--
--   **Policy improvement.** Given the family of (E), the gap of $R$ is
--   $$\varepsilon_i^R = g^R + v_i^R - \Big(w_{ik_i'} + \sum_j q_{ij}(k_i') v_j^R\Big),$$
--   where $k_i'$ are the decisions of the next iterate. A sequence $R_1, R_2, \dots$ of rules of $C''$ is a sequence of policy improvement iterations if each $R_{n+1}$ minimizes $w_{ik} + \sum_j q_{ij}(k) v^{R_n}_j$ at every state. A rule $R^*$ is a **limit point** of the sequence if some subsequence agrees with $R^*$ at each state from some index on (convergence in the product of the finite decision sets).
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note.** The cost field `M.C` of the reused `MDC` is not used: Derman's costs are signed reals and are passed as `w`. $E_R W_t$ is computed as positive part minus negative part, each a sum in $[0,\infty]$ against the published history law `histProb`; under (B) both are finite. $Q_R$ is the real `limsup` with the paper's normalization $(T+1)^{-1}$; under (B) the averages are bounded, so it is genuine and equals the limit when the limit exists. $\sum_j q_{ij}(k) v_j$ is a real series, applied only to bounded $v$, where it converges absolutely. Condition (C) uses the published `Irreducible` and `PositiveRecurrent` of `SennottDP.MarkovCost`. Condition (E) is given as an explicit family `gR`, `vR` because the improvement step depends on $v^R$, which (2) does not determine uniquely. Sequences are indexed from $0$: `R 0` is the paper's $R_1$. A finite $I$ is allowed (`Countable`), which only generalizes the statements.
-- source:
--   Derman, Denumerable State Markovian Decision Processes—Average Cost Criterion, Ann. Math. Statist. 37(6) (1966), pp. 1545–1546 (§1, (A), (B)), p. 1548 ((1), (2)), p. 1549 ((5), (C), (D)), p. 1550 ((E)), p. 1551 (policy improvement, (F), ε_i^R), https://doi.org/10.1214/aoms/1177699146

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_SennottDP_MarkovCost_Chain

namespace DermanDenumerable.AvgCost

open scoped ENNReal NNReal Topology
open Filter SennottDP.AvgFinite

/-! Derman, *Denumerable State Markovian Decision Processes—Average Cost Criterion*,
Ann. Math. Statist. 37(6) (1966) 1545–1553. The model of §1 (pp. 1545–1546) is the published
`SennottDP.AvgFinite.MDC`: a countable state space `S` (Derman's `I`), for each state `i` a finite
nonempty set `M.A i` of decisions (condition (A), `K_i < ∞`), and transition probabilities
`M.P i k j = q_ij(k)`. Rules of the class `C` are `Policy M`, rules of `C''` are
`StationaryPolicy M`. The cost field `M.C` of `MDC` is **not used**: Derman's costs `w_ik` are
signed and are passed separately as `w : S → Act → ℝ`. -/

variable {S Act : Type} [Countable S]

/-- Condition (B) (p. 1546): `{w_ik}` is a bounded set of numbers (over the decisions `k`
available at `i`). -/
def CostBounded (M : MDC S Act) (w : S → Act → ℝ) : Prop :=
  ∃ B : ℝ, ∀ i, ∀ a ∈ M.A i, |w i a| ≤ B

/-- The signed cost `w_{i_t a_t}` of the most recent state-decision pair of a history (the list is
most recent first); `0` on the empty list. -/
def lastCostR (w : S → Act → ℝ) : List (S × Act) → ℝ
  | [] => 0
  | (j, a) :: _ => w j a

/-- `E_R W_t` given `Y_0 = i` (p. 1545): the expectation of the signed cost at time `t` against the
law `histProb θ i` of the length-`(t+1)` state-decision history. It is computed as positive part
minus negative part, each a `[0, ∞]`-valued sum; under condition (B) both parts are finite, so the
value is the genuine expectation (no junk value). -/
noncomputable def expCostR {M : MDC S Act} (θ : Policy M) (w : S → Act → ℝ) (i : S) (t : ℕ) :
    ℝ :=
  (∑' h : List (S × Act),
      if h.length = t + 1 then histProb θ i h * ENNReal.ofReal (lastCostR w h) else 0).toReal -
  (∑' h : List (S × Act),
      if h.length = t + 1 then histProb θ i h * ENNReal.ofReal (-lastCostR w h) else 0).toReal

/-- `h_n(i)` (p. 1549): the total expected cost over the periods `0, 1, ⋯, n` under the rule `θ`
started at `Y_0 = i`. -/
noncomputable def horizonCostR {M : MDC S Act} (θ : Policy M) (w : S → Act → ℝ) (i : S) (n : ℕ) :
    ℝ :=
  ∑ t ∈ Finset.range (n + 1), expCostR θ w i t

/-- `Q_R(i)` (p. 1545): `lim sup_{T→∞} (T + 1)^{-1} Σ_{t=0}^{T} E_R W_t` given `Y_0 = i` (the limit
when it exists). Under (B) the sequence is bounded, so the real `limsup` is genuine. -/
noncomputable def avgCostR {M : MDC S Act} (θ : Policy M) (w : S → Act → ℝ) (i : S) : ℝ :=
  limsup (fun T : ℕ => ((T : ℝ) + 1)⁻¹ * ∑ t ∈ Finset.range (T + 1), expCostR θ w i t) atTop

/-- `Σ_{j ∈ I} q_ij(k) v_j`. Every statement of the mission applies it to a bounded `v`, for which the
series is absolutely summable, so the real `tsum` is the genuine sum. -/
noncomputable def expNext (M : MDC S Act) (i : S) (a : Act) (v : S → ℝ) : ℝ :=
  ∑' j, (M.P i a j).toReal * v j

/-- "A bounded set of numbers `{v_j}`, `j ∈ I`". -/
def BddFun (v : S → ℝ) : Prop := ∃ B : ℝ, ∀ j, |v j| ≤ B

/-- Equation (1) (p. 1548): `g + v_i = min_k {w_ik + Σ_j q_ij(k) v_j}` for every `i ∈ I`, the minimum
being over the finite set `M.A i` (attained and least). -/
def IsACOE (M : MDC S Act) (w : S → Act → ℝ) (g : ℝ) (v : S → ℝ) : Prop :=
  ∀ i, (∃ a ∈ M.A i, g + v i = w i a + expNext M i a v) ∧
       ∀ a ∈ M.A i, g + v i ≤ w i a + expNext M i a v

/-- Equation (2) (p. 1548) for the rule `e ∈ C''` (make decision `k_i = e.f i` at state `i`):
`g + v_i = w_{ik_i} + Σ_j q_ij(k_i) v_j` for every `i ∈ I`. -/
def IsEvaluation (M : MDC S Act) (w : S → Act → ℝ) (e : StationaryPolicy M) (g : ℝ) (v : S → ℝ) :
    Prop :=
  ∀ i, g + v i = w i (e.f i) + expNext M i (e.f i) v

/-- The rule `e ∈ C''` prescribes, at every state `i`, a decision minimizing
`w_ik + Σ_j q_ij(k) v_j` over the decisions `k` available at `i`. -/
def IsMinimizer (M : MDC S Act) (w : S → Act → ℝ) (v : S → ℝ) (e : StationaryPolicy M) : Prop :=
  ∀ i, ∀ a ∈ M.A i, w i (e.f i) + expNext M i (e.f i) v ≤ w i a + expNext M i a v

/-- `g_n(i)` of (5) (p. 1549): `g_0(i) = min_k w_ik` and
`g_{n+1}(i) = min_k {w_ik + Σ_j q_ij(k) g_n(j)}`. -/
noncomputable def valueIter (M : MDC S Act) (w : S → Act → ℝ) : ℕ → S → ℝ
  | 0, i => (M.A i).inf' (M.A_nonempty i) (w i)
  | n + 1, i => (M.A i).inf' (M.A_nonempty i) (fun a => w i a + expNext M i a (valueIter M w n))

/-- `θ` is optimal over `C`: `Q_θ(i) ≤ Q_R(i)` for every rule `R ∈ C` (history-dependent,
randomized) and every initial state `i`. -/
def OptimalOverC {M : MDC S Act} (w : S → Act → ℝ) (θ : Policy M) : Prop :=
  ∀ (R : Policy M) (i : S), avgCostR θ w i ≤ avgCostR R w i

/-- `e ∈ C''` is optimal over `C''`: `Q_e(i) ≤ Q_{e'}(i)` for every `e' ∈ C''` and every `i`. -/
def OptimalOverC'' {M : MDC S Act} (w : S → Act → ℝ) (e : StationaryPolicy M) : Prop :=
  ∀ (e' : StationaryPolicy M) (i : S), avgCostR e.toPolicy w i ≤ avgCostR e'.toPolicy w i

/-- The Markov chain of the rule `e ∈ C''`: transition probabilities `p_ij = q_ij(k_i)` with
`k_i = e.f i` (p. 1548). -/
noncomputable def chainOf (M : MDC S Act) (e : StationaryPolicy M) : SennottDP.MarkovCost.MC S :=
  ⟨fun i j => M.P i (e.f i) j, fun i => M.P_sum i (e.f i)⟩

/-- Condition (C) (p. 1549): for every `R ∈ C''` the resulting Markov chain is positive recurrent,
i.e. all states belong to one communicating class and are positive recurrent states. -/
def CondC (M : MDC S Act) : Prop :=
  ∀ e : StationaryPolicy M, SennottDP.MarkovCost.Irreducible (chainOf M e) ∧
    ∀ j, SennottDP.MarkovCost.PositiveRecurrent (chainOf M e) j

/-- Condition (E) (p. 1550) for a given family `{g^R, v_j^R}`: every `R ∈ C''` satisfies (2) with
`g^R = gR R`, `v^R = vR R`, and these numbers are bounded uniformly over `j ∈ I`, `R ∈ C''`. -/
def IsUniformEvaluation (M : MDC S Act) (w : S → Act → ℝ) (gR : StationaryPolicy M → ℝ)
    (vR : StationaryPolicy M → S → ℝ) : Prop :=
  (∀ e, IsEvaluation M w e (gR e) (vR e)) ∧ ∃ B : ℝ, ∀ e, |gR e| ≤ B ∧ ∀ j, |vR e j| ≤ B

/-- `(T + 1)^{-1} Σ_{t=0}^{T} P{Y_t = j | Y_0 = i}` under the rule `e ∈ C''`, where
`P{Y_t = j | Y_0 = i}` is the `t`-step transition probability of the chain of `e`. -/
noncomputable def cesaro (M : MDC S Act) (e : StationaryPolicy M) (i j : S) (T : ℕ) : ℝ :=
  ((T : ℝ) + 1)⁻¹ *
    ∑ t ∈ Finset.range (T + 1), (SennottDP.MarkovCost.nStep (chainOf M e) t i j).toReal

/-- Condition (F) (p. 1551): for every `j ∈ I`, `inf_{R ∈ C'', i ∈ I} π_ij(R) > 0`, where
`π_ij(R) = lim_{T→∞} (T + 1)^{-1} Σ_{t=0}^{T} P{Y_t = j | Y_0 = i}`. The condition asserts that
these limits exist and are bounded below by a positive `δ` (depending on `j` only). -/
def CondF (M : MDC S Act) : Prop :=
  ∀ j, ∃ δ > 0, ∀ (e : StationaryPolicy M) (i : S),
    ∃ π : ℝ, Tendsto (cesaro M e i j) atTop (𝓝 π) ∧ δ ≤ π

/-- `ε_i^R` (p. 1551) in its second form, `g^R + v_i^R − (w_{ik_i'} + Σ_j q_ij(k_i') v_j^R)`, where
`e` is `R` (with `{g^R, v^R}` from the family `gR, vR`) and `e'` is the rule `R'` with decisions
`k_i'`. -/
noncomputable def gap (M : MDC S Act) (w : S → Act → ℝ) (gR : StationaryPolicy M → ℝ)
    (vR : StationaryPolicy M → S → ℝ) (e e' : StationaryPolicy M) (i : S) : ℝ :=
  gR e + vR e i - (w i (e'.f i) + expNext M i (e'.f i) (vR e))

/-- A sequence of policy improvement iterations (p. 1551): for every `n`, the decisions of
`R (n+1)` minimize `w_ik + Σ_j q_ij(k) v_j^{R n}` at every state (ties broken arbitrarily). The
index is 0-based: `R 0` is the paper's `R_1`. -/
def IsPISequence (M : MDC S Act) (w : S → Act → ℝ) (vR : StationaryPolicy M → S → ℝ)
    (R : ℕ → StationaryPolicy M) : Prop :=
  ∀ n, IsMinimizer M w (vR (R n)) (R (n + 1))

/-- `e` is a limit point of the sequence `R` in `C'' = ∏_i {1, ⋯, K_i}` (p. 1551: a subsequence
`R_{n_ν}` converges to `R*` when, for every state `i`, the decision of `R_{n_ν}` at `i` equals that of
`R*` for all sufficiently large `ν`). -/
def IsLimitPoint {M : MDC S Act} (R : ℕ → StationaryPolicy M) (e : StationaryPolicy M) : Prop :=
  ∃ r : ℕ → ℕ, StrictMono r ∧ ∀ i, ∀ᶠ k in atTop, (R (r k)).f i = e.f i

end DermanDenumerable.AvgCost


