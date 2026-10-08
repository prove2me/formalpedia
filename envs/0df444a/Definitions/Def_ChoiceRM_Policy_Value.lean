-- Prove2me | Definitions.Def_ChoiceRM_Policy_Value
-- name    : ChoiceRM_Policy_Value
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:46:02.029323+00:00
-- url     : https://prove2.me/theorems/1ec22754-43f2-4eda-bdf3-2ea552e73e9e
-- title:
--   Value function, stage objective and ordered nondominated sets
-- statement:
--   For an arrival probability $\lambda$, choice probabilities $P_j(S)$ and revenues $r_j$, let $V_t(x)$ be the maximum expected revenue with $t$ periods and $x$ units of capacity remaining. Define $\Delta V_t(x)=V_t(x)-V_t(x-1)$ for $x\ge1$, $Q(S)=\sum_{j\in S}P_j(S)$ and $R(S)=\sum_{j\in S}P_j(S)r_j$. The offer-stage objective is
--
--   $$\lambda\bigl(R(S)-Q(S)\Delta V_{t-1}(x)\bigr).$$
--
--   An optimal offer set maximizes this expression over every subset of products. An ordered family $S_1,\ldots,S_m$ lists each nondominated set exactly once, in nondecreasing order of $Q(S_k)$. For a value $v$, the greatest maximizing index is the largest $k$ attaining the maximum of $R(S_k)-Q(S_k)v$.
--
--   These objects connect the Bellman recursion to the paper's ordered frontier and make tie handling explicit.
--
--   **Formalization Note** Time counts periods remaining. The published `RevenueManagement.choiceValueGo` supplies $V_t$; its constant arrival probability is used here. Capacity and time are natural numbers, while marginal and stage objectives are invoked only at $x,t\ge1$.
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), pp. 7, 11–12, equations (1), (3), (7), Proposition 3 and Lemma 2

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_Policy_Dominance

namespace ChoiceRM.Policy

open RevenueManagement

variable {n : ℕ}

/-- The paper's `V_t(x)` with `t` periods remaining. -/
noncomputable def V (lam : ℝ) (P : Finset (Fin n) → Fin n → ℝ)
    (r : Fin n → ℝ) (t x : ℕ) : ℝ :=
  RevenueManagement.choiceValueGo (fun _ => lam) P r 0 t x

/-- `ΔV_t(x)`, used only for positive capacities. -/
noncomputable def deltaV (lam : ℝ) (P : Finset (Fin n) → Fin n → ℝ)
    (r : Fin n → ℝ) (t x : ℕ) : ℝ :=
  V lam P r t x - V lam P r t (x - 1)

/-- The maximand in the Bellman equations (1) and (3), for `t ≥ 1` and `x ≥ 1`. -/
noncomputable def stageObj (lam : ℝ) (P : Finset (Fin n) → Fin n → ℝ)
    (r : Fin n → ℝ) (t x : ℕ) (S : Finset (Fin n)) : ℝ :=
  lam * (expRevenue P r S - purchaseProb P S * deltaV lam P r (t - 1) x)

/-- An offer set attaining the stage maximum in equation (1). -/
def IsOptimalOffer (lam : ℝ) (P : Finset (Fin n) → Fin n → ℝ)
    (r : Fin n → ℝ) (t x : ℕ) (S : Finset (Fin n)) : Prop :=
  ∀ S', stageObj lam P r t x S' ≤ stageObj lam P r t x S

/-- The `m` distinct nondominated sets, listed in nondecreasing purchase-probability order.
The exhaustive field ensures the list is exactly the nondominated family. -/
structure IsOrderedNondominated {m : ℕ} (P : Finset (Fin n) → Fin n → ℝ)
    (r : Fin n → ℝ) (Sq : Fin m → Finset (Fin n)) : Prop where
  mem : ∀ k, IsNondominated P r (Sq k)
  exhaustive : ∀ T, IsNondominated P r T → ∃ k, Sq k = T
  injective : Function.Injective Sq
  mono : Monotone (fun k => purchaseProb P (Sq k))

/-- The greatest index among the maximizers of `R_k - Q_k v` in Lemma 2. -/
def IsLargestMaximizer {m : ℕ} (P : Finset (Fin n) → Fin n → ℝ)
    (r : Fin n → ℝ) (Sq : Fin m → Finset (Fin n)) (v : ℝ) (k : Fin m) : Prop :=
  (∀ l, expRevenue P r (Sq l) - purchaseProb P (Sq l) * v ≤
    expRevenue P r (Sq k) - purchaseProb P (Sq k) * v) ∧
  (∀ l, expRevenue P r (Sq l) - purchaseProb P (Sq l) * v =
    expRevenue P r (Sq k) - purchaseProb P (Sq k) * v → l ≤ k)

end ChoiceRM.Policy


