-- Prove2me | Definitions.Def_MultitaskContracts_Instance
-- name    : MultitaskContracts_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:31:43.767251+00:00
-- url     : https://prove2.me/theorems/9ab5ca37-a86f-4b17-ab3c-c0476a7df014
-- title:
--   Multitask principal–agent instance: tasks $K$, $(p_k,q_k,c_k)$, distributions $P_S$ with marginals (1), $P_K(K)>0$
-- statement:
--   A principal delegates a finite set of tasks $K$ to an agent. On each task $k\in K$ the agent exerts effort or shirks; task $k$ succeeds with marginal probability $p_k$ under effort and $q_k$ under shirking, where $0\le q_k<p_k\le 1$, and effort on $k$ costs $c_k>0$. The agent's **strategy** $S\subseteq K$ is the set of tasks he works on, and the observed **performance** $Y\subseteq K$ is the random set of tasks that succeed. Each strategy $S$ induces a probability distribution $P_S$ on the subsets of $K$, whose marginals are the success probabilities:
--   $$\sum_{Y'\subseteq K:\,k\in Y'}P_S(Y')=p_k\ \ (k\in S),\qquad \sum_{Y'\subseteq K:\,k\in Y'}P_S(Y')=q_k\ \ (k\in K\setminus S). \tag{1}$$
--   Full effort succeeds on all tasks with positive probability, $P_K(K)>0$. Effort costs are additive: $c(S)=\sum_{k\in S}c_k$.
--
--   For a contract $t:2^K\to\mathbb R$ write $\mathbb E_{Y\sim P_S}[t(Y)]$ for its expected payment under strategy $S$. The instance is a hidden-action setting with actions and outcomes $2^K$, and inherits from it the notion "$t$ implements $S$" (eq. (4)) and the optima $\mathrm{OPT}^{\mathcal T}_{\mathrm{FixedBudget}}(B)$, $\mathrm{OPT}^{\mathcal T}_{\mathrm{MinPay}}$, $\mathrm{OPT}^{\mathcal T}_{\mathrm{MinBudget}}$ of eqs. (5)–(7), always for the target of full effort $S=K$.
--
--   This structure carries exactly the standing assumptions of Section 2; dependence structures (independence, MMLRP, strongest indicator) are separate predicates.
--
--   **Formalization Note** Strategies and performances are `Finset K`; `P S Y` is $P_S(Y)$; contracts are functions `Finset K → ℝ`. The optima are those of `ContractSetting` with target `Finset.univ` (= $K$), valued in `ℝ≥0∞`.
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), §2, eq. (1), p.6 (PDF p.8) and eqs. (4)–(7), p.7 (PDF p.9)

import Mathlib
import Definitions.Def_MultitaskContracts_ContractSetting

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

/-- An **instance of the multitask principal–agent model** on a finite set of tasks `K`
(§2, p.6, PDF 8). Task `k` succeeds with marginal probability `p k` under effort and `q k`
under shirking, `0 ≤ q k < p k ≤ 1`, and effort on `k` costs `c k > 0`. A strategy
`S ⊆ K` (the tasks worked on) induces the distribution `P S` over performances `Y ⊆ K` (the tasks
that succeed), with the marginals of eq. (1); and `P_K(K) > 0` ("We assume throughout").
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), §2, p.6 (PDF 8), eq. (1).

**Formalization Note.** Strategies and performances are `Finset K`. `P S Y` is `P_S(Y)`. The
fields are exactly §2's standing assumptions: no independence, full support or other dependence
structure is bundled (those are the predicates `IsIndependent`, `MMLRP`, `StrongestIndicator`). -/
structure Instance (K : Type*) [Fintype K] [DecidableEq K] where
  /-- success probability of task `k` under effort -/
  p : K → ℝ
  /-- success probability of task `k` under shirking -/
  q : K → ℝ
  /-- cost of effort on task `k` -/
  c : K → ℝ
  /-- `P S Y = P_S(Y)`: probability that exactly the tasks `Y` succeed under strategy `S` -/
  P : Finset K → Finset K → ℝ
  q_nonneg : ∀ k, 0 ≤ q k
  q_lt_p : ∀ k, q k < p k
  p_le_one : ∀ k, p k ≤ 1
  c_pos : ∀ k, 0 < c k
  P_nonneg : ∀ S Y, 0 ≤ P S Y
  P_sum : ∀ S, ∑ Y, P S Y = 1
  /-- eq. (1), first part: the marginal of task `k ∈ S` is `p k` -/
  marginal_mem : ∀ S k, k ∈ S → ∑ Y ∈ Finset.univ.filter (fun Y => k ∈ Y), P S Y = p k
  /-- eq. (1), second part: the marginal of task `k ∈ K \ S` is `q k` -/
  marginal_not_mem : ∀ S k, k ∉ S → ∑ Y ∈ Finset.univ.filter (fun Y => k ∈ Y), P S Y = q k
  /-- full effort succeeds on all tasks with positive probability, `P_K(K) > 0` -/
  P_univ_univ_pos : 0 < P Finset.univ Finset.univ

namespace Instance

variable {K : Type*} [Fintype K] [DecidableEq K] (I : Instance K)

/-- Additive cost `c(S) := ∑_{k ∈ S} c_k` (§2, p.6). -/
def cost (S : Finset K) : ℝ :=
  ∑ k ∈ S, I.c k

/-- The instance as a hidden-action setting: actions and outcomes are `Finset K`. -/
def toSetting : ContractSetting (Finset K) (Finset K) where
  P := I.P
  cost := I.cost

/-- `E_{Y∼P_S}[t(Y)]`. -/
def expect (S : Finset K) (t : Finset K → ℝ) : ℝ :=
  I.toSetting.expect S t

/-- `t` implements strategy `S`, i.e. `S ∈ S*_t` (eq. (4), p.7). -/
def Implements (t : Finset K → ℝ) (S : Finset K) : Prop :=
  I.toSetting.Implements t S

/-- `OPT^T_FixedBudget(B)` (eq. (5), p.7): the target is full effort `K`. -/
noncomputable def optFixedBudget (T : Set (Finset K → ℝ)) (B : ℝ) : ℝ≥0∞ :=
  I.toSetting.optFixedBudget T Finset.univ B

/-- `OPT^T_MinPay` (eq. (6), p.7) for implementing full effort `K`. -/
noncomputable def optMinPay (T : Set (Finset K → ℝ)) : ℝ≥0∞ :=
  I.toSetting.optMinPay T Finset.univ

/-- `OPT^T_MinBudget` (eq. (7), p.7) for implementing full effort `K`. -/
noncomputable def optMinBudget (T : Set (Finset K → ℝ)) : ℝ≥0∞ :=
  I.toSetting.optMinBudget T Finset.univ

end Instance

end MultitaskContracts


