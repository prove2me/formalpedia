-- Prove2me | Definitions.Def_SubscriptionPlanning_GrandOptimal_Setting
-- name    : SubscriptionPlanning_GrandOptimal_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:02:26.427714+00:00
-- url     : https://prove2.me/theorems/743a0fc9-9dcc-4fcc-97b1-31dfed477611
-- title:
--   §2–§3 and §5, pp. 4–7, 12, 14 (PDF 5–8, 13, 15) — values, per-watch choice, SubGain, Rent, feasible planning (2)–(3), revenue, grand planning, Condition 2, Mechanism 1 lottery
-- statement:
--   This file sets up the subscription-planning model of Alaei, Makhdoumi and Malekian.
--
--   **Model (§2).** There are $n$ user types $i \in \mathcal N = \{1,\dots,n\}$ and $m$ item (movie) types $j \in \mathcal M = \{1,\dots,m\}$. On a probability space $(\Omega, \mathbb P)$, $V_{ij}$ is the value of one watch of item $j$ to user type $i$ and $V_0$ is the value of the outside option. User type $i$ has mass $q_i \ge 0$ with $\sum_i q_i = 1$, usage rate $\lambda_i > 0$, and the subscription period has length $T > 0$. All values are measurable and integrable.
--
--   **Planning (Definition 1).** A subscription planning is a pair $(p, \mathbf r)$ of subscription fees $p : 2^{\mathcal M} \to \mathbb R$ and rental prices $\mathbf r \in \mathbb R^m$.
--
--   **One watch.** A user of type $i$ subscribed to $S \subseteq \mathcal M$ gets utility $V_0$ from the outside option, $V_{ij}$ from an item $j \in S$ and $V_{ij} - r_j$ from an item $j \notin S$ (rented). The best utility is
--   $$\max\{V_{i,\max}(S),\, V_{i,\max}(S^c, \mathbf r),\, V_0\}.$$
--   The chosen option is the first maximizer in the fixed priority order: outside option first, then items $1, \dots, m$.
--
--   **Subscription gain and rent (§3.2).**
--   $$\mathrm{SubGain}(i,S,\mathbf r) = \mathbb E\big[\max\{V_{i,\max}(S), V_{i,\max}(S^c,\mathbf r), V_0\}\big] - \mathbb E\big[\max\{V_{i,\max}(\mathcal M,\mathbf r), V_0\}\big],$$
--   and $\mathrm{Rent}(i,S,\mathbf r)$ is the expected rental price paid per watch, i.e. $\mathbb E[r_J \mathbf 1\{J \notin S\}]$ where $J$ is the chosen option. The relative gain is $g_i(S) = \mathrm{SubGain}(i,S,\mathbf r)/\mathrm{SubGain}(i,\mathcal M,\mathbf r)$.
--
--   **Feasible planning and revenue (Proposition 2).** For fixed $\mathbf r$, fees $p$ with $p(\emptyset) = 0$ and an assignment $i \mapsto S_i$ are feasible when the incentive constraints (3) hold:
--   $$\lambda_i T\,\mathrm{SubGain}(i,S_i,\mathbf r) - p(S_i) \ge \lambda_i T\,\mathrm{SubGain}(i,S,\mathbf r) - p(S) \quad \text{for all } i \text{ and } S \subseteq \mathcal M.$$
--   The revenue (2) is $\sum_i q_i\big(p(S_i) + \lambda_i T\,\mathrm{Rent}(i,S_i,\mathbf r)\big)$. A planning is optimal if it is feasible and no feasible planning has larger revenue.
--
--   **Grand subscription.** Only $\mathcal M$ is offered, at fee $P$; type $i$ subscribes ($\sigma_i$ true) only if $P \le \lambda_i T\,\mathrm{SubGain}(i,\mathcal M,\mathbf r)$ and declines only if $P \ge \lambda_i T\,\mathrm{SubGain}(i,\mathcal M,\mathbf r)$. Its revenue is $\sum_i q_i\,(P + \lambda_i T\,\mathrm{Rent}(i,\mathcal M,\mathbf r))$ over subscribers plus $\sum_i q_i\,\lambda_i T\,\mathrm{Rent}(i,\emptyset,\mathbf r)$ over non-subscribers.
--
--   **Condition 2 (p. 12),** cross-multiplied: for all $i, i'$ and $S$,
--   $$\mathrm{SubGain}(i,S,\mathbf r)\,\mathrm{Rent}(i,\emptyset,\mathbf r) \le \mathrm{SubGain}(i,\mathcal M,\mathbf r)\,\big(\mathrm{Rent}(i,\emptyset,\mathbf r) - \mathrm{Rent}(i,S,\mathbf r)\big),$$
--   $$\mathrm{SubGain}(i,S,\mathbf r)\,\mathrm{SubGain}(i',\mathcal M,\mathbf r) = \mathrm{SubGain}(i',S,\mathbf r)\,\mathrm{SubGain}(i,\mathcal M,\mathbf r).$$
--
--   **Mechanism 1 data (p. 14).** The grand fee at index $k$ is $A_k = \lambda_k T\,\mathrm{SubGain}(k,\mathcal M,\mathbf r)$ and the lottery weight is $\pi_k = g_k(S_k) - g_{k-1}(S_{k-1})$ with $g_0(S_0) = 0$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Options are `WithBot (Fin m)`, whose order (outside option first) is the tie-break priority. With it, Rent equals the printed formula $\sum_{j\notin S} r_j\,\mathbb P[V_{ij} - r_j \ge \max\{\dots\}]$ whenever ties have probability zero; the printed "$\ge$" would count every tied maximizer. The values may have any joint law (the paper draws them independently; nothing in §5 uses independence). The condition $p(\emptyset) = 0$ is the paper's convention that not subscribing costs nothing (proof of Theorem 2, p. 33). Condition 2 is cross-multiplied because Lean's $x/0 = 0$ would change the printed ratios; with positive denominators the two forms are equivalent. In `relGain`, Lean's $x/0 = 0$ applies when $\mathrm{SubGain}(i,\mathcal M,\mathbf r) = 0$.
-- source:
--   Alaei, Makhdoumi, Malekian, Optimal Subscription Planning for Digital Goods, working paper (SSRN 3476296; Operations Research, doi:10.1287/opre.2023.2468), pp. 4–7, 12, 14, §2–§3, Definition 1, SubGain and Rent (p. 7), Proposition 2 (2)–(3), Condition 2 (p. 12), Mechanism 1 (p. 14)

import Mathlib

namespace SubscriptionPlanning.GrandOptimal

open MeasureTheory Classical

/-- §2 (pp. 4–5): `n` user types, `m` item types, the per-watch values `V i j` of item `j` to user
type `i` and the outside option `V0`, as random variables on a probability space `(Ω, P)`, the
masses `q`, the usage rates `lam` and the length `T` of the subscription period. -/
structure Model (n m : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  P : Measure Ω
  V : Fin n → Fin m → Ω → ℝ
  V0 : Ω → ℝ
  q : Fin n → ℝ
  lam : Fin n → ℝ
  T : ℝ

/-- The standing assumptions of §2: `P` is a probability measure, the values are integrable random
variables, the masses are nonnegative and sum to one, the usage rates and the horizon are positive. -/
structure Model.Valid {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model n m Ω) : Prop where
  isProb : IsProbabilityMeasure M.P
  measV : ∀ i j, Measurable (M.V i j)
  measV0 : Measurable M.V0
  intV : ∀ i j, Integrable (M.V i j) M.P
  intV0 : Integrable M.V0 M.P
  q_nonneg : ∀ i, 0 ≤ M.q i
  q_sum : ∑ i, M.q i = 1
  lam_pos : ∀ i, 0 < M.lam i
  T_pos : 0 < M.T

variable {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- Utility of each option for one watch of user type `i` subscribed to `S` at rental prices `r`.
Options are `WithBot (Fin m)`: `⊥` is the outside option, `(j : Fin m)` is item `j`, watched for free
if `j ∈ S` and rented at price `r j` otherwise. -/
noncomputable def util (M : Model n m Ω) (i : Fin n) (S : Finset (Fin m)) (r : Fin m → ℝ) (ω : Ω) :
    WithBot (Fin m) → ℝ :=
  fun o => WithBot.recBotCoe (M.V0 ω) (fun j => if j ∈ S then M.V i j ω else M.V i j ω - r j) o

/-- The best utility of one watch, `max {V_i,max(S), V_i,max(Sᶜ, r), V_0}`. -/
noncomputable def best (M : Model n m Ω) (i : Fin n) (S : Finset (Fin m)) (r : Fin m → ℝ) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (util M i S r ω)

/-- The option chosen on one watch: the first maximizer of the utility in the fixed priority order of
`WithBot (Fin m)` (the outside option first, then items by index). -/
def IsChosen (M : Model n m Ω) (i : Fin n) (S : Finset (Fin m)) (r : Fin m → ℝ) (ω : Ω)
    (o : WithBot (Fin m)) : Prop :=
  util M i S r ω o = best M i S r ω ∧ ∀ o' < o, util M i S r ω o' < best M i S r ω

/-- Rental price paid on one watch: `r j` if the chosen option is an item `j ∉ S`, and `0` otherwise. -/
noncomputable def rentPaid (M : Model n m Ω) (i : Fin n) (S : Finset (Fin m)) (r : Fin m → ℝ)
    (ω : Ω) : ℝ :=
  ∑ j : Fin m, if j ∉ S ∧ IsChosen M i S r ω (j : WithBot (Fin m)) then r j else 0

/-- `SubGain(i, S, r) = E[max{V_i,max(S), V_i,max(Sᶜ, r), V_0}] − E[max{V_i,max(𝓜, r), V_0}]`. -/
noncomputable def subGain (M : Model n m Ω) (i : Fin n) (S : Finset (Fin m)) (r : Fin m → ℝ) : ℝ :=
  (∫ ω, best M i S r ω ∂M.P) - ∫ ω, best M i ∅ r ω ∂M.P

/-- `Rent(i, S, r)`: the expected rental revenue per watch from user type `i` subscribed to `S`. -/
noncomputable def rent (M : Model n m Ω) (i : Fin n) (S : Finset (Fin m)) (r : Fin m → ℝ) : ℝ :=
  ∫ ω, rentPaid M i S r ω ∂M.P

/-- Relative subscription gain `g_i(S) = SubGain(i, S, r) / SubGain(i, 𝓜, r)` (Lean: `x / 0 = 0`). -/
noncomputable def relGain (M : Model n m Ω) (i : Fin n) (S : Finset (Fin m)) (r : Fin m → ℝ) : ℝ :=
  subGain M i S r / subGain M i Finset.univ r

/-- A feasible subscription planning: fees `p` with `p ∅ = 0` and an assignment `S` of sets to user
types satisfying the incentive constraints (3) of Proposition 2. -/
def IsFeasible (M : Model n m Ω) (r : Fin m → ℝ) (p : Finset (Fin m) → ℝ)
    (S : Fin n → Finset (Fin m)) : Prop :=
  p ∅ = 0 ∧ ∀ (i : Fin n) (S' : Finset (Fin m)),
    M.lam i * M.T * subGain M i S' r - p S' ≤ M.lam i * M.T * subGain M i (S i) r - p (S i)

/-- The platform's revenue (2): `∑ᵢ qᵢ (p(Sᵢ) + λᵢ T Rent(i, Sᵢ, r))`. -/
noncomputable def revenue (M : Model n m Ω) (r : Fin m → ℝ) (p : Finset (Fin m) → ℝ)
    (S : Fin n → Finset (Fin m)) : ℝ :=
  ∑ i, M.q i * (p (S i) + M.lam i * M.T * rent M i (S i) r)

/-- An optimal subscription planning for fixed rental prices `r`. -/
def IsOptimal (M : Model n m Ω) (r : Fin m → ℝ) (p : Finset (Fin m) → ℝ)
    (S : Fin n → Finset (Fin m)) : Prop :=
  IsFeasible M r p S ∧
    ∀ (p' : Finset (Fin m) → ℝ) (S' : Fin n → Finset (Fin m)),
      IsFeasible M r p' S' → revenue M r p' S' ≤ revenue M r p S

/-- Grand subscription: only the grand set `𝓜` is offered, at fee `P`; type `i` subscribes iff
`σ i`, and `σ` respects each type's incentives (a type indifferent between subscribing and not may
take either). -/
def IsGrandFeasible (M : Model n m Ω) (r : Fin m → ℝ) (P : ℝ) (σ : Fin n → Bool) : Prop :=
  ∀ i, (σ i = true → P ≤ M.lam i * M.T * subGain M i Finset.univ r) ∧
    (σ i = false → M.lam i * M.T * subGain M i Finset.univ r ≤ P)

/-- Revenue of the grand subscription with fee `P` and subscription decisions `σ`. -/
noncomputable def grandRevenue (M : Model n m Ω) (r : Fin m → ℝ) (P : ℝ) (σ : Fin n → Bool) : ℝ :=
  ∑ i, M.q i * (if σ i then P + M.lam i * M.T * rent M i Finset.univ r
    else M.lam i * M.T * rent M i ∅ r)

/-- Condition 2 (p. 12), both parts cross-multiplied:
1. `SubGain(i,S,r) · Rent(i,∅,r) ≤ SubGain(i,𝓜,r) · (Rent(i,∅,r) − Rent(i,S,r))`;
2. `SubGain(i,S,r) · SubGain(i',𝓜,r) = SubGain(i',S,r) · SubGain(i,𝓜,r)`. -/
def Condition2 (M : Model n m Ω) (r : Fin m → ℝ) : Prop :=
  (∀ (i : Fin n) (S : Finset (Fin m)),
    subGain M i S r * rent M i ∅ r ≤ subGain M i Finset.univ r * (rent M i ∅ r - rent M i S r)) ∧
  (∀ (i i' : Fin n) (S : Finset (Fin m)),
    subGain M i S r * subGain M i' Finset.univ r = subGain M i' S r * subGain M i Finset.univ r)

/-- Fee `A_k = λ_k T SubGain(k, 𝓜, r)` offered for the grand set at lottery index `k` (Mechanism 1). -/
noncomputable def grandFee (M : Model n m Ω) (r : Fin m → ℝ) (k : Fin n) : ℝ :=
  M.lam k * M.T * subGain M k Finset.univ r

/-- Lottery weight `π_k = g_k(S_k) − g_{k-1}(S_{k-1})` of Mechanism 1, with `g_{-1} = 0`. -/
noncomputable def lotteryWeight (M : Model n m Ω) (r : Fin m → ℝ) (S : Fin n → Finset (Fin m))
    (k : Fin n) : ℝ :=
  relGain M k (S k) r -
    (if h : 0 < k.val then relGain M ⟨k.val - 1, by omega⟩ (S ⟨k.val - 1, by omega⟩) r else 0)

end SubscriptionPlanning.GrandOptimal


