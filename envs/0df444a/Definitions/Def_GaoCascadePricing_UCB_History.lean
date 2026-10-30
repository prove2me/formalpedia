-- Prove2me | Definitions.Def_GaoCascadePricing_UCB_History
-- name    : GaoCascadePricing_UCB_History
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T08:13:59.061997+00:00
-- url     : https://prove2.me/theorems/4683c372-27eb-4f18-9e82-bedf2ef583c8
-- title:
--   Full observation histories, randomized policies and empirical counters
-- statement:
--   A length-$n$ public history records the chosen price vector and complete customer path in each of the first $n$ periods. A randomized policy assigns a probability mass function on price vectors to each such history. It has no unknown-parameter argument. Given true cascade parameters, the history probability is the product of the policy's action probabilities and the customer's conditional path probabilities, evaluated successively on the preceding histories. Event probabilities are finite sums of these weights; this is the recursively generated finite-horizon law.
--
--   The counters before period $n+1$ count examinations $n^e$, clicks $n^c$, and purchases $n^b$ separately at each product-price pair. Pooled across prices, $n^\gamma$ counts nonclicks and $n^\zeta$ counts clicks without purchases; the corresponding success counters count continuations. Initialization is complete exactly when all examination and click counters are positive, together with both pooled denominators for every nonterminal product. Terminal continuation counters are not required.
--
--   Empirical parameters are $\widehat\beta=n^c/n^e$, $\widehat\alpha=n^b/n^c$, $\widehat\gamma=n^{\gamma,s}/n^\gamma$ and $\widehat\zeta=n^{\zeta,s}/n^\zeta$, with the two terminal continuation estimates zero. Counts come from the history, rather than free parameters.
--
--   **Formalization Note.** A length-zero history represents the initially empty history. A ratio with zero denominator returns zero as an unavailable estimate. The algorithm's separate initialization guard prevents such a ratio from enabling optimization. Action distributions are normalized PMFs; all expectations here are finite weighted sums.
-- source:
--   Gao, Jasin, Najafi and Zhang (2022), Joint Learning and Optimization for Multi-Product Pricing (and Ranking) Under a General Cascade Click Model, DOI https://doi.org/10.1287/mnsc.2021.4246; published basis, supplied manuscript-paginated PDF; §4, pp. 11–16

import Definitions.Def_GaoCascadePricing_UCB_Cascade

open scoped BigOperators

namespace GaoCascadePricing.UCB

/-- A full public history: prices and all observed customer movements. -/
abbrev History (J K n : ℕ) := Fin n → Action J K × Observation J

/-- A history-dependent randomized rule. There is no unknown-parameter argument. -/
abbrev Policy (J K : ℕ) := ∀ n, History J K n → PMF (Action J K)

def historyPrefix {J K n : ℕ} (h : History J K n) (i : Fin n) : History J K i.val :=
  fun r => h ⟨r.val, Nat.lt_trans r.isLt i.isLt⟩

/-- Recursive finite-horizon law, written as the product of conditional step laws. -/
noncomputable def historyWeight {J K n : ℕ} (θ : Cascade J K) (π : Policy J K)
    (h : History J K n) : ℝ :=
  ∏ i, ((π i.val (historyPrefix h i)) (h i).1).toReal *
    customerWeight θ (h i).1 (h i).2

noncomputable def probability {J K n : ℕ} (θ : Cascade J K) (π : Policy J K)
    (E : History J K n → Prop) : ℝ := by
  classical
  exact ∑ h, if E h then historyWeight θ π h else 0

noncomputable def count {J K n : ℕ} (h : History J K n)
    (P : Action J K → Observation J → Prop) : ℕ := by
  classical
  exact ∑ i, if P (h i).1 (h i).2 then 1 else 0

noncomputable def ne {J K n : ℕ} (h : History J K n) (j : Fin J) (k : Fin K) : ℕ :=
  count h fun p o => p j = k ∧ examined (o j)

noncomputable def nc {J K n : ℕ} (h : History J K n) (j : Fin J) (k : Fin K) : ℕ :=
  count h fun p o => p j = k ∧ clicked (o j)

noncomputable def nb {J K n : ℕ} (h : History J K n) (j : Fin J) (k : Fin K) : ℕ :=
  count h fun p o => p j = k ∧ bought (o j)

noncomputable def ng {J K n : ℕ} (h : History J K n) (j : Fin J) : ℕ :=
  count h fun _ o => nonclick (o j)

noncomputable def ngs {J K n : ℕ} (h : History J K n) (j : Fin J) : ℕ :=
  count h fun _ o => nonclick (o j) ∧ continued (o j)

noncomputable def nz {J K n : ℕ} (h : History J K n) (j : Fin J) : ℕ :=
  count h fun _ o => declined (o j)

noncomputable def nzs {J K n : ℕ} (h : History J K n) (j : Fin J) : ℕ :=
  count h fun _ o => declined (o j) ∧ continued (o j)

/-- Tested before every decision; no terminal continuation counters are required. -/
def Initialized {J K n : ℕ} (h : History J K n) : Prop :=
  (∀ j k, 0 < ne h j k ∧ 0 < nc h j k) ∧
  (∀ j : Fin J, j.val + 1 < J → 0 < ng h j ∧ 0 < nz h j)

/-- Zero for an unavailable estimate; UCBOPT is never enabled by that convention. -/
noncomputable def estimate {J K n : ℕ} (h : History J K n) : Cascade J K where
  beta j k := (nc h j k : ℝ) / ne h j k
  alpha j k := (nb h j k : ℝ) / nc h j k
  gamma j := if j.val + 1 < J then (ngs h j : ℝ) / ng h j else 0
  zeta j := if j.val + 1 < J then (nzs h j : ℝ) / nz h j else 0

end GaoCascadePricing.UCB


