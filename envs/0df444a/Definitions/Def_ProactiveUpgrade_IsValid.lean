-- Prove2me | Definitions.Def_ProactiveUpgrade_IsValid
-- name    : ProactiveUpgrade_IsValid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:46.618656+00:00
-- url     : https://prove2.me/theorems/76af7655-4d94-41ac-a576-dd98dd447135
-- title:
--   Valid model data: positive increasing prices and probabilities
-- statement:
--   Model data $(p,\beta,\beta_0,q,\lambda)$ are **valid** when
--
--   1. prices are positive and strictly increasing, $0<p_1<p_2<\dots<p_m$;
--   2. request probabilities are nonnegative, $\beta_i\ge0$, the no-request probability is positive, $\beta_0>0$, and $\beta_0+\sum_i\beta_i=1$;
--   3. acceptance probabilities satisfy $0\le q_i\le1$ for $i=1,\dots,m-1$;
--   4. the arrival probability satisfies $0\le\lambda\le1$.
--
--   These are the properties of the multinomial-logit data (1)–(3) that the paper's arguments use. The two subproblems into which the problem splits when a product runs out (Lemma 3) satisfy them but are not multinomial-logit data, which is why the structural results of the mission are stated for valid data.
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, §3, pp.6–9; eqs. (1)–(3)

import Mathlib
import Definitions.Def_ProactiveUpgrade_Model

namespace ProactiveUpgrade

/-- **Valid model data** (Chen et al., SSRN 3777846, §3, pp.6–9): positive, strictly increasing
prices `0 < p₁ < ⋯ < p_m` (p.6); request probabilities `βᵢ ≥ 0` and a positive no-request
probability `β₀ > 0` with `β₀ + Σᵢ βᵢ = 1` ((1), (2), p.7); acceptance probabilities
`0 ≤ qᵢ ≤ 1` for `i < m` ((3), p.9); arrival probability `0 ≤ λ ≤ 1` (p.7).

**Formalization Note** These are the properties of the MNL data (1)–(3) that the paper's proofs use
(milestone `mnl_valid`). The subproblems of Lemma 3 (`lowModel`, `highModel`) satisfy them but are
not MNL data, which is why the milestones are stated for valid data. -/
structure IsValid {m : ℕ} (M : Model m) : Prop where
  p_pos : ∀ i, 0 < M.p i
  p_strictMono : StrictMono M.p
  β_nonneg : ∀ i, 0 ≤ M.β i
  β0_pos : 0 < M.β0
  sum_eq_one : M.β0 + ∑ i, M.β i = 1
  q_mem : ∀ i : Fin m, i.val + 1 < m → 0 ≤ M.q i ∧ M.q i ≤ 1
  lam_mem : 0 ≤ M.lam ∧ M.lam ≤ 1

end ProactiveUpgrade


