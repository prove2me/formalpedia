-- Prove2me | Definitions.Def_OutlierAssort_ActiveElim_Model
-- name    : OutlierAssort_ActiveElim_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T08:38:40.203114+00:00
-- url     : https://prove2.me/theorems/b015e861-5031-4998-bc70-6bcbcb6e3e76
-- title:
--   §3, pp. 6–8 — MNL choice model (1), outlier choice models, the adaptive adversary of Definition 1 with (A1)–(A2), and the optimal typical revenue R(S*; v)
-- statement:
--   This file sets up the **robust dynamic assortment** model of Chen, Krishnamurthy and Wang.
--
--   There are $N$ items, indexed by $\mathrm{Fin}\,N$, each with a known revenue $r_i \in [0,1]$ and an unknown utility $v_i \in [0,1]$. For weights $w$ (the true utilities $v$ or estimates $\hat v$), the expected revenue of an assortment $S \subseteq [N]$ is
--   $$
--   R(S; w) = \frac{\sum_{i\in S} r_i w_i}{1 + \sum_{i \in S} w_i},
--   $$
--   which is the published MNL objective with no-purchase weight $v_0 = 1$.
--
--   1. **Typical customers** choose by the multinomial-logit model (1): offered $S$, a customer buys $i \in S$ with probability $v_i/(1+\sum_{j\in S} v_j)$ and buys nothing with probability $1/(1+\sum_{j\in S} v_j)$. The outcome space is $\{0\} \cup [N]$, with "no purchase" written `none`.
--   2. **Outlier customers** choose by an arbitrary choice model $Q$: for each offered $S$, $Q(S)$ is a probability distribution on $S \cup \{0\}$.
--   3. An **adaptive adversary** (Definition 1, (A2)) is a pair of deterministic functions that, at period $t$, read the whole public past (types $\phi_s$, offered assortments $S_s$ and purchases $i_s$ for $s < t$) and return the type $\phi_t$ of the next customer (typical or outlier) and the outlier choice model $Q_t$.
--   4. **Assumption (A1)**: the adversary has outlier budget $\varepsilon$ over $T$ periods if, on every public record of the $T$ periods, it sends at most $\varepsilon T$ outliers.
--   5. The **optimal typical revenue** is $R(S^*; v) = \max_{S \subseteq [N],\, |S| \le K} R(S; v)$, and an assortment $S$ is optimal if $|S| \le K$ and $R(S;v) = R(S^*;v)$.
--
--   These objects are the environment against which Algorithm 1 is run and its TOTE regret is measured.
--
--   **Formalization Note.** Periods are numbered $0,\dots,T-1$. The outlier model may depend on the offered assortment, which only enlarges the class of adversaries. The budget is imposed on every public record of the $T$ periods. If an adversary meets it on every record the algorithm can actually produce, changing it off those records (stop sending outliers once the budget is used up) makes it meet the budget everywhere without changing the law of the run.
-- source:
--   Chen, Krishnamurthy, Wang, Robust Dynamic Assortment Optimization in the Presence of Outlier Customers, arXiv:1910.04183v2, pp. 6–8, (1), (A1), (A2), Definition 1, (2)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective

namespace OutlierAssort.ActiveElim

open ChoiceCDLP.MNL

/-- The expected revenue `R(S; w) = (∑_{i ∈ S} r_i w_i) / (1 + ∑_{i ∈ S} w_i)` of the assortment `S`
under the MNL weights `w` (Chen–Krishnamurthy–Wang, arXiv:1910.04183v2, p. 7, and Algorithm 1, line 18,
p. 10), with the no-purchase weight `v₀ = 1`. It is the published `mnlObjective w r 1 S`. Used both for
the true utilities `v` and for the estimates `v̂`. -/
noncomputable def rev {N : ℕ} (r w : Fin N → ℝ) (S : Finset (Fin N)) : ℝ :=
  mnlObjective w r 1 S

/-- The MNL choice model (1), p. 6, with `v₀ = 1`, as a probability mass function on the outcomes
`Option (Fin N)`: `none` is the no-purchase outcome `i_t = 0`, `some i` the purchase of item `i`.
When `S` is offered, `none` has mass `1 / (1 + ∑_{j ∈ S} v_j)`, an item `i ∈ S` has mass
`v_i / (1 + ∑_{j ∈ S} v_j)`, and an item outside `S` has mass `0`. -/
noncomputable def mnlLaw {N : ℕ} (v : Fin N → ℝ) (S : Finset (Fin N)) : Option (Fin N) → ℝ
  | none => 1 / (1 + ∑ j ∈ S, v j)
  | some i => if i ∈ S then v i / (1 + ∑ j ∈ S, v j) else 0

/-- An outlier choice model (p. 6): for every offered assortment `S`, `Q S` is a probability mass
function on `Option (Fin N)` supported on `S ∪ {no purchase}` ("an arbitrary unknown distribution
`Q_t` (marginalized on `S_t ∪ {0}`)"). -/
def IsChoiceModel {N : ℕ} (Q : Finset (Fin N) → Option (Fin N) → ℝ) : Prop :=
  ∀ S : Finset (Fin N), (∀ o, 0 ≤ Q S o) ∧ (∑ o, Q S o) = 1 ∧ ∀ i, i ∉ S → Q S (some i) = 0

/-- One period of the public record of Definition 1 (p. 7): the customer type `φ_t`
(`true` = outlier, `false` = typical), the offered assortment `S_t` and the purchase `i_t`. -/
abbrev PubRec (N : ℕ) := Bool × Finset (Fin N) × Option (Fin N)

/-- An adaptive adversary (Definition 1, item 1, and (A2), p. 7). At period `t` (0-based) it sees the
whole public past `F_{t-1}` (the types, the offered assortments and the purchases of periods
`s < t`) and returns the type `φ_t` of the incoming customer and the outlier choice model
`Q_t`. The adversary is deterministic, as in Definition 1; its past outlier models are functions of
the same past, so they need not be recorded. -/
structure Adversary (N : ℕ) where
  /-- `φ_t`: whether the customer of period `t` is an outlier. -/
  outlier : (t : ℕ) → (Fin t → PubRec N) → Bool
  /-- `Q_t`: the outlier's choice model, given the assortment offered at period `t`. -/
  model : (t : ℕ) → (Fin t → PubRec N) → Finset (Fin N) → Option (Fin N) → ℝ
  /-- Every `Q_t` is a choice model supported on the offered set and the no-purchase option. -/
  model_isChoice : ∀ t p, IsChoiceModel (model t p)

/-- The restriction of a sequence on `Fin t` to its first `s` entries (`s ≤ t`). -/
def restrict {α : Type*} {t : ℕ} (p : Fin t → α) (s : ℕ) (hs : s ≤ t) : Fin s → α :=
  fun u => p (Fin.castLE hs u)

open scoped Classical in
/-- Assumption (A1), p. 7 (bounded adversaries): on every public record of the `T` periods, the
number of periods at which the adversary sends an outlier customer is at most `ε T`. -/
def OutlierBudget {N : ℕ} (adv : Adversary N) (T : ℕ) (eps : ℝ) : Prop :=
  ∀ p : Fin T → PubRec N,
    ((Finset.univ.filter (fun t : Fin T => adv.outlier t.val (restrict p t.val t.isLt.le) = true)).card
      : ℝ) ≤ eps * T

/-- The feasible assortments `{S ⊆ [N] : |S| ≤ K}` (p. 6). It contains `∅`. -/
noncomputable def feasible (N K : ℕ) : Finset (Finset (Fin N)) :=
  (Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card ≤ K)

theorem feasible_nonempty (N K : ℕ) : (feasible N K).Nonempty :=
  ⟨∅, by simp [feasible]⟩

/-- The optimal typical revenue `R(S*; v) = max_{S ⊆ [N], |S| ≤ K} R(S; v)` (p. 8). -/
noncomputable def optRev {N : ℕ} (r v : Fin N → ℝ) (K : ℕ) : ℝ :=
  (feasible N K).sup' (feasible_nonempty N K) (fun S => rev r v S)

/-- `S` is an optimal assortment for typical customers (p. 8): `|S| ≤ K` and `R(S; v) = R(S*; v)`. -/
def IsOptimal {N : ℕ} (r v : Fin N → ℝ) (K : ℕ) (S : Finset (Fin N)) : Prop :=
  S.card ≤ K ∧ rev r v S = optRev r v K

end OutlierAssort.ActiveElim


