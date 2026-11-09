-- Prove2me | Definitions.Def_FairShareAlmostAll_Slack_Instance
-- name    : FairShareAlmostAll_Slack_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:54.395488+00:00
-- url     : https://prove2.me/theorems/891eba5f-fc70-4d58-a827-bb4003e5dbb2
-- title:
--   Nonnegative additive instances and original APS targets
-- statement:
--   An instance has $n$ agents, $m$ goods, nonnegative real singleton values $v_i(g)$ and real entitlements $0<b_i\le1$. The total entitlement is $W=\sum_i b_i$. Bounds on $n$ and $W$ belong to theorem hypotheses.
--
--   The original targets and active set are
--   $$t_i=\operatorname{APS}_i(b_i),\qquad N_+=\{i:t_i>0\}.$$
--   APS uses the published price definition without rescaling $b_i$. The auxiliary capped values are $u_i(g)=\min\{v_i(g)/t_i,1\}$; only active agents use them. Independently ranked singleton values define the ordered reduction. Valid prices are nonnegative with sum one, and affordable bundles have price at most the original entitlement. The associated value sets support an explicit attainment obligation.
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 2 (PDF p. 3), §1.1; §1.2, printed p. 3 (PDF p. 4); §1.5; §2.1; source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation

namespace FairShareAlmostAll.Slack

structure Instance (n m : ℕ) where
  value : Fin n → Fin m → ℝ
  entitlement : Fin n → ℝ
  value_nonneg : ∀ i g, 0 ≤ value i g
  entitlement_pos : ∀ i, 0 < entitlement i
  entitlement_le_one : ∀ i, entitlement i ≤ 1

noncomputable def totalEntitlement {n m : ℕ} (X : Instance n m) : ℝ :=
  ∑ i, X.entitlement i

noncomputable def target {n m : ℕ} (X : Instance n m) (i : Fin n) : ℝ :=
  AnyPriceShare.Bidding.anyPrice (X.entitlement i)
    (AnyPriceShare.Bidding.addVal (X.value i)) Finset.univ

noncomputable def active {n m : ℕ} (X : Instance n m) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => 0 < target X i)

noncomputable def capped {n m : ℕ} (X : Instance n m) (i : Fin n) (g : Fin m) : ℝ :=
  min (X.value i g / target X i) 1

noncomputable def cappedValue {n m : ℕ} (X : Instance n m) (i : Fin n)
    (P : Finset (Fin m)) : ℝ := AnyPriceShare.Bidding.addVal (capped X i) P

/-- The published ranked-value function is used only at valid ranks g.val + 1. -/
noncomputable def orderedValue {n m : ℕ} (X : Instance n m) (i : Fin n) (g : Fin m) : ℝ :=
  AnyPriceShare.Bidding.rankedValue (X.value i) Finset.univ (g.val + 1)

def ValidPrice {m : ℕ} (p : Fin m → ℝ) : Prop :=
  (∀ g, 0 ≤ p g) ∧ ∑ g, p g = 1

def Affordable {m : ℕ} (b : ℝ) (p : Fin m → ℝ) (P : Finset (Fin m)) : Prop :=
  (∑ g ∈ P, p g) ≤ b

def affordableValues {m : ℕ} (v : Fin m → ℝ) (b : ℝ) (p : Fin m → ℝ) : Set ℝ :=
  {r | ∃ P, Affordable b p P ∧ r = AnyPriceShare.Bidding.addVal v P}

noncomputable def priceOutcomes {m : ℕ} (v : Fin m → ℝ) (b : ℝ) : Set ℝ :=
  {r | ∃ p, ValidPrice p ∧ r = sSup (affordableValues v b p)}

end FairShareAlmostAll.Slack


