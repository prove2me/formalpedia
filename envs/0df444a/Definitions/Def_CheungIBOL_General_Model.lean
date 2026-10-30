-- Prove2me | Definitions.Def_CheungIBOL_General_Model
-- name    : CheungIBOL_General_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T22:10:35.468612+00:00
-- url     : https://prove2.me/theorems/171a4532-ac4b-438f-bbce-8145913cebb6
-- title:
--   General online allocation model and true outcome means
-- statement:
--   There are $n>0$ resources, a known finite context set of size $c>0$, and a general measurable action space $A$. Resource $i$ has positive integer capacity $b_i$ and reward $0<r_i\le1$. The fixed unknown outcome law $\rho_{x,a}$ is a probability kernel on Boolean vectors $y\in\{0,1\}^n$. Different coordinates of $y$ may be correlated and multiple coordinates may equal one. The true marginal success probability is
--   $$p_{x,a,i}=\int y_i\,d\rho_{x,a}(y).$$
--   No finiteness, countability, compactness, substitutability, no-consumption action, or coordinate-independence condition is imposed on the action model. Resources and contexts are indexed by finite types; capacities use positive natural numbers. The kernel encodes measurability of the probabilistic model, not statistical knowledge supplied to the oracle.
-- source:
--   Cheung, Ma, Simchi-Levi and Wang, Inventory Balancing with Online Learning, arXiv:1810.05640v2 (30 August 2021), PDF/printed pp. 8–10, Section 2 and footnote 2, https://arxiv.org/abs/1810.05640v2

import Mathlib

open MeasureTheory ProbabilityTheory
noncomputable section

namespace CheungIBOL.General

/-- Section 2: a general action can consume several correlated resources. -/
structure Model (n c : ℕ) (A : Type*) [MeasurableSpace A] where
  resource_pos : 0 < n
  context_pos : 0 < c
  capacity : Fin n → ℕ+
  reward : Fin n → ℝ
  reward_pos : ∀ i, 0 < reward i
  reward_le_one : ∀ i, reward i ≤ 1
  law : Kernel (Fin c × A) (Fin n → Bool)
  law_probability : IsMarkovKernel law

attribute [instance] Model.law_probability

/-- True one-coordinate mean under the joint vector law. -/
def Model.prob {n c : ℕ} {A : Type*} [MeasurableSpace A]
    (M : Model n c A) (x : Fin c) (a : A) (i : Fin n) : ℝ :=
  ∫ y, (if y i then (1 : ℝ) else 0) ∂M.law (x, a)

end CheungIBOL.General


