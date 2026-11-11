-- Prove2me | Definitions.Def_PooledTestingAdaptivity_Gap_Instance
-- name    : PooledTestingAdaptivity_Gap_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:23:27.823195+00:00
-- url     : https://prove2.me/theorems/8b7b0192-d1eb-47f7-9d05-8220b9e6289c
-- title:
--   Population, independent health profiles and clearance welfare
-- statement:
--   Let $n\ge1$ be the population size. Person $i$ is independently healthy with real probability $0<q_i\le1$ and has real clearance utility $u_i\ge0$. The integer pool cap is $G\ge1$. A health profile $x$ assigns each person a Boolean bit, with one meaning healthy. An allocation $T$ is an ordered finite list of finite subsets; its admissibility as nonempty pools is imposed separately by feasibility. Define
--
--   $$\mu_J(x)=\prod_i\begin{cases}q_i&x_i=1,\\1-q_i&x_i=0,\end{cases}\quad C(T,x)=\bigcup_{t\text{ in }T:\,x_t=1}t,$$
--   $$w_J(T,x)=\sum_{i\in C(T,x)}u_i,\qquad W_J(T)=\sum_x\mu_J(x)w_J(T,x).$$
--
--   This is clearance welfare, with one payment per person. Health certainty alone earns nothing. Pools may overlap or repeat. The auxiliary empty pool is harmless and is excluded from actual tests by the nonempty pool type and feasible-family conditions. Population indices are `Fin n`, a reindexing of the paper's $[n]$.
-- source:
--   Edwin Lock, Nicholas Lopez, Francisco Marmolejo-Cossío, Jose Roberto Tello Ayala, David Parkes, STOC 2027 submission #1397 (October 2026), §2, printed p. 4, PDF p. 5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1397.pdf

import Mathlib

namespace PooledTestingAdaptivity.Gap

abbrev Profile (n : ℕ) := Fin n → Bool
abbrev Allocation (n : ℕ) := List (Finset (Fin n))
abbrev Pool (n : ℕ) := {t : Finset (Fin n) // t.Nonempty}

/-- §2: one means healthy, utilities are arbitrary nonnegative real numbers. -/
structure Instance (n : ℕ) where
  population_pos : 0 < n
  q : Fin n → ℝ
  u : Fin n → ℝ
  q_pos : ∀ i, 0 < q i
  q_le_one : ∀ i, q i ≤ 1
  u_nonneg : ∀ i, 0 ≤ u i
  cap : ℕ
  cap_pos : 0 < cap

/-- True is a negative pooled test, including the vacuous empty-set test used internally. -/
def negative {n : ℕ} (t : Finset (Fin n)) (x : Profile n) : Bool :=
  decide (∀ i ∈ t, x i = true)

/-- Union of negative pools; certainly healthy but untested people are not cleared. -/
def cleared {n : ℕ} : Allocation n → Profile n → Finset (Fin n)
  | [], _ => ∅
  | t :: ts, x => (if negative t x then t else ∅) ∪ cleared ts x

noncomputable def reward {n : ℕ} (J : Instance n) (T : Allocation n) (x : Profile n) : ℝ :=
  ∑ i ∈ cleared T x, J.u i

/-- Mass of the actual independent heterogeneous Bernoulli health profile. -/
noncomputable def profileMass {n : ℕ} (J : Instance n) (x : Profile n) : ℝ :=
  ∏ i, if x i then J.q i else 1 - J.q i

noncomputable def expectation {n : ℕ} (J : Instance n) (f : Profile n → ℝ) : ℝ :=
  ∑ x, profileMass J x * f x

noncomputable def staticWelfare {n : ℕ} (J : Instance n) (T : Allocation n) : ℝ :=
  expectation J (reward J T)

end PooledTestingAdaptivity.Gap


