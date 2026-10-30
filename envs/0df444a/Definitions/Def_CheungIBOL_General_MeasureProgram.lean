-- Prove2me | Definitions.Def_CheungIBOL_General_MeasureProgram
-- name    : CheungIBOL_General_MeasureProgram
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T22:10:36.03306+00:00
-- url     : https://prove2.me/theorems/0d24eb56-6d8f-426d-9b9d-e1347af2b45f
-- title:
--   Probability-measure packing linear program
-- statement:
--   A probability-measure packing linear program has a measurable action space $A$, finitely many periods $t<T$ and constraints $i<n$, real data functions $c_t(a)$ and $g_{t,i}(a)$, and budgets $b_i$. A decision assigns a probability measure $s_t$ to each period. Feasibility requires integrability of the objective and constraint functions under these measures and
--   $$\sum_{t<T}\int_A g_{t,i}(a)\,ds_t(a)\le b_i\quad(i<n).$$
--   The objective is $\sum_{t<T}\int_A c_t(a)\,ds_t(a)$. The value is the extended-real supremum of feasible objective values, equal to $-\infty$ when no feasible decision exists. There is no attainment assumption. The data structure itself allows arbitrary real functions; the feasible set imposes the integrability needed to give their integrals their usual meaning.
--
--   This general object is separate from the inventory model. The latter instantiates bounded measurable costs and resource uses, so integrability there follows automatically for every probability allocation. On a discrete action space, $s_t(\{a\})=s_{a,t}$ recovers the source sums and the equality $\sum_a s_{a,t}=1$.
-- source:
--   Cheung, Ma, Simchi-Levi and Wang, Inventory Balancing with Online Learning, arXiv:1810.05640v2 (30 August 2021), PDF/printed pp. 16–17, equations (9)–(12), abstract probability-measure formulation, https://arxiv.org/abs/1810.05640v2

import Mathlib

open MeasureTheory
open scoped BigOperators
noncomputable section

namespace CheungIBOL.General

/-- A probability-measure packing LP, independent of the inventory model. -/
structure MeasureProgram (A : Type*) [MeasurableSpace A] (T n : ℕ) where
  cost : Fin T → A → ℝ
  use : Fin T → Fin n → A → ℝ
  budget : Fin n → ℝ

def MeasureProgram.Feasible {A : Type*} [MeasurableSpace A] {T n : ℕ}
    (L : MeasureProgram A T n) (s : Fin T → Measure A) : Prop :=
  (∀ t, IsProbabilityMeasure (s t)) ∧
  (∀ t, Integrable (L.cost t) (s t)) ∧
  (∀ t i, Integrable (L.use t i) (s t)) ∧
  ∀ i, (∑ t, ∫ a, L.use t i a ∂s t) ≤ L.budget i

def MeasureProgram.objective {A : Type*} [MeasurableSpace A] {T n : ℕ}
    (L : MeasureProgram A T n) (s : Fin T → Measure A) : ℝ :=
  ∑ t, ∫ a, L.cost t a ∂s t

/-- The empty feasible set has value minus infinity; no attainment is assumed. -/
def MeasureProgram.value {A : Type*} [MeasurableSpace A] {T n : ℕ}
    (L : MeasureProgram A T n) : EReal :=
  sSup {z | ∃ s, L.Feasible s ∧ z = (L.objective s : EReal)}

end CheungIBOL.General


