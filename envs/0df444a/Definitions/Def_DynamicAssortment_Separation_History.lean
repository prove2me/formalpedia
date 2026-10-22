-- Prove2me | Definitions.Def_DynamicAssortment_Separation_History
-- name    : DynamicAssortment_Separation_History
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T10:11:38.431166+00:00
-- url     : https://prove2.me/theorems/38b1919e-3ec6-41f9-a5ae-df60465f5a73
-- title:
--   Finite purchase histories, nonanticipating policies, the history law ℙ_π, revenue J^π(T, μ) and regret ℛ^π(T, μ)
-- statement:
--   Customers $t=1,\dots,T$ (0-based in Lean) arrive one at a time. A **history** $h$ records, for each customer, the product bought or no purchase: $h_t\in\{\text{none}\}\cup\mathcal N$.
--
--   1. **Policies.** A policy $\pi$ maps each customer $t$ and the purchases $h_0,\dots,h_{t-1}$ of the earlier customers to an assortment $S_t$. This is the paper's nonanticipating policy: $S_t$ is $\mathcal F_{t-1}$-measurable, with $\mathcal F_0$ trivial. `IsAdmissible C π` requires $|S_t|\le C$.
--   2. **Law.** Given the offered assortments, customers choose independently, so
--   $$\mathbb P_\pi(h)=\prod_{t} q(S_t,h_t),\qquad q(S,i)=p_i(S,\mu),\quad q(S,\text{none})=p_0(S,\mu).$$
--   $\mathbb P_\pi(E)=\sum_{h\in E}\mathbb P_\pi(h)$ is the probability of an event $E$ (`prob`).
--   3. **Revenue and regret.** The expected cumulative revenue is $J^\pi(T,\mu)=\mathbb E_\pi\big(\sum_{t=1}^T\sum_{i\in\mathcal N}w_iZ_i^t\big)$, where $Z_i^t=1$ if customer $t$ buys $i$. The regret is
--   $$\mathcal R^\pi(T,\mu)=T-\frac{J^\pi(T,\mu)}{r(S^*(\mu),\mu)}.$$
--
--   The assortment $S_t$ offered along $h$ is `offeredAt π h t`, and `offeredSeq π h u` is the same indexed by $u\in\mathbb N$. `histSeq h u` is $h_u$ indexed by $\mathbb N$. Both return a default (empty assortment, no purchase) for $u\ge T$; no statement of the mission reads them there.
--
--   **Formalization Note** The history space $(\{\text{none}\}\cup\mathcal N)^T$ is finite, so expectations and probabilities are finite sums and no measure space is needed. This finite law is the law of the paper's purchase decisions $(Z^t)$. Under the random-utility model, customer $t$'s shocks are independent of the past, and ties between utilities have probability zero because $F$ has a density. So, given the history up to $t-1$ (which fixes $S_t$), customer $t$ buys $i$ with probability $p_i(S_t,\mu)$ and nothing with probability $p_0(S_t,\mu)$. A deterministic function of past purchases is exactly an $\mathcal F_{t-1}$-measurable choice, since $\mathcal F_0$ is trivial and the past assortments are themselves functions of past purchases.
-- source:
--   Sauré, Zeevi, Optimal Dynamic Assortment Planning with Demand Learning, Manuf. Serv. Oper. Manag. 15(3), 2013, pp. 391–392, §3.3 (Z_i^t, ℱ_t, admissible policies, J^π(T, μ)) and the regret ℛ^π(T, μ), p. 392

import Mathlib
import Definitions.Def_DynamicAssortment_Separation_ChoiceModel

namespace DynamicAssortment.Separation

/-- A horizon-`T` purchase history: `h t = some i` if customer `t` (0-based) buys product `i`,
`h t = none` if customer `t` buys nothing. -/
abbrev History (N T : ℕ) := Fin T → Option (Fin N)

/-- The purchases of the customers before `t`. -/
def histPrefix {N T : ℕ} (h : History N T) (t : Fin T) : Fin t.val → Option (Fin N) :=
  fun u => h (Fin.castLE t.isLt.le u)

/-- A nonanticipating assortment policy for horizon `T`: the assortment offered to customer `t`
is a function of the purchase decisions of customers `0, …, t-1` (and hence, recursively, of the
assortments offered to them). -/
abbrev Policy (N T : ℕ) := (t : Fin T) → (Fin t.val → Option (Fin N)) → Finset (Fin N)

/-- An admissible policy offers only feasible assortments, `S_t ∈ 𝒮`, i.e. `|S_t| ≤ C`. -/
def IsAdmissible {N T : ℕ} (C : ℕ) (π : Policy N T) : Prop :=
  ∀ t pre, (π t pre).card ≤ C

/-- The assortment `S_t` offered to customer `t` along history `h`. -/
def offeredAt {N T : ℕ} (π : Policy N T) (h : History N T) (t : Fin T) : Finset (Fin N) :=
  π t (histPrefix h t)

/-- The same, indexed by `ℕ` (the empty assortment for `u ≥ T`, never used). -/
def offeredSeq {N T : ℕ} (π : Policy N T) (h : History N T) (u : ℕ) : Finset (Fin N) :=
  if hu : u < T then offeredAt π h ⟨u, hu⟩ else ∅

/-- A history indexed by `ℕ` (`none` for `u ≥ T`, never used). -/
def histSeq {N T : ℕ} (h : History N T) (u : ℕ) : Option (Fin N) :=
  if hu : u < T then h ⟨u, hu⟩ else none

/-- Probability of the purchase outcome `o` of one customer offered `S`:
`p_i(S, μ)` for `o = some i`, `p_0(S, μ)` for `o = none`. -/
noncomputable def outcomeProb {N : ℕ} (f : ℝ → ℝ) (μ : Fin N → ℝ) (S : Finset (Fin N)) :
    Option (Fin N) → ℝ
  | none => noPurchaseProb f μ S
  | some i => choiceProb f μ S i

/-- The law of the purchase history under policy `π` and mean utilities `μ`: customers choose
independently given the offered assortments, so
`ℙ_π(h) = ∏_t q(S_t, h_t)` with `S_t = π_t(h_0, …, h_{t-1})`. -/
noncomputable def histProb {N T : ℕ} (f : ℝ → ℝ) (μ : Fin N → ℝ) (π : Policy N T)
    (h : History N T) : ℝ :=
  ∏ t : Fin T, outcomeProb f μ (offeredAt π h t) (h t)

/-- `ℙ_π(E)` for an event `E` on histories (a finite sum). -/
noncomputable def prob {N T : ℕ} (f : ℝ → ℝ) (μ : Fin N → ℝ) (π : Policy N T)
    (E : History N T → Prop) : ℝ := by
  classical
  exact ∑ h : History N T, if E h then histProb f μ π h else 0

/-- Profit of one purchase outcome: `∑_i w_i Z_i^t`. -/
def outcomeProfit {N : ℕ} (w : Fin N → ℝ) : Option (Fin N) → ℝ
  | none => 0
  | some i => w i

/-- Expected cumulative revenue `J^π(T, μ) = 𝔼_π (∑_{t=1}^T ∑_{i ∈ 𝒩} w_i Z_i^t)` (p. 391). -/
noncomputable def expectedRevenue {N T : ℕ} (f : ℝ → ℝ) (w : Fin N → ℝ) (μ : Fin N → ℝ)
    (π : Policy N T) : ℝ :=
  ∑ h : History N T, histProb f μ π h * ∑ t : Fin T, outcomeProfit w (h t)

/-- Regret `ℛ^π(T, μ) = T - J^π(T, μ) / r(S*(μ), μ)` (p. 392), with `Sstar = S*(μ)`. -/
noncomputable def regret {N T : ℕ} (f : ℝ → ℝ) (w : Fin N → ℝ) (μ : Fin N → ℝ)
    (Sstar : Finset (Fin N)) (π : Policy N T) : ℝ :=
  (T : ℝ) - expectedRevenue f w μ π / profit f w μ Sstar

end DynamicAssortment.Separation


