-- Prove2me | Definitions.Def_DiscountedDP_Stationary_Model
-- name    : DiscountedDP_Stationary_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:49:45.303199+00:00
-- url     : https://prove2.me/theorems/04f99afc-c879-444e-b5ab-7ec03323903b
-- title:
--   Blackwell's discounted dynamic programming model and history-dependent plans
-- statement:
--   A discounted dynamic programming problem consists of nonempty standard Borel spaces of states $S$ and actions $A$, a probability kernel $q(\cdot\mid s,a)$ on $S$, a bounded Borel reward $r(s,a,s')$, and a discount factor $0\le\beta<1$. The reward may depend on the next state.
--
--   The history before decision $n+1$ consists of $n$ completed state-action pairs and the current state. A **plan** chooses an action by a probability kernel on this full history. A **Markov plan** is a sequence of measurable state-to-action functions. The class of bounded Borel real functions on $S$ is denoted $M(S)$.
--
--   $$H_{n+1}=(S\times A)^n\times S,\qquad \pi_{n+1}\in Q(A\mid H_{n+1}).$$
--
--   These data provide the common domain for all the paper's return and optimality claims.
--
--   **Formalization Note** The paper's Borel sets are represented by nonempty standard Borel types, and its “Baire functions” by measurable functions. Lean indexes decisions from $0$: decision $0$ uses only the initial state. The model structure stores stochasticity, boundedness, measurability, and the full range $0\le\beta<1$.
-- source:
--   Blackwell, Discounted Dynamic Programming, Ann. Math. Statist. 36 (1965), pp. 227–228 (PDF 2–3), Sections 2–3

import Mathlib

namespace DiscountedDP.Stationary

open MeasureTheory ProbabilityTheory

/-- Blackwell's discounted dynamic programming data (Section 3, p. 228).
The state and action types are supplied with nonempty standard Borel structures in statements. -/
structure Problem (S A : Type*) [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] where
  q : Kernel (S × A) S
  q_markov : IsMarkovKernel q
  r : S × A × S → ℝ
  r_measurable : Measurable r
  r_bounded : ∃ C : ℝ, ∀ x, |r x| ≤ C
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1

/-- The history before decision `n+1`: `n` completed state-action pairs and
the current state. The first decision has history `Hist S A 0`. -/
def Hist (S A : Type*) (n : ℕ) := (Fin n → S × A) × S

instance instMeasurableSpaceHist {S A : Type*} [MeasurableSpace S]
    [MeasurableSpace A] (n : ℕ) : MeasurableSpace (Hist S A n) :=
  inferInstanceAs (MeasurableSpace ((Fin n → S × A) × S))

/-- A randomized history-dependent plan: one probability kernel per decision. -/
structure Plan {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] where
  κ : (n : ℕ) → Kernel (Hist S A n) A
  κ_markov : ∀ n, IsMarkovKernel (κ n)

/-- A non-randomized Markov plan, given by measurable state-to-action rules. -/
def MarkovPlan (S A : Type*) [MeasurableSpace S] [MeasurableSpace A] :=
  ℕ → {f : S → A // Measurable f}

/-- A bounded Borel (measurable) real-valued function. -/
def IsBM {S : Type*} [MeasurableSpace S] (u : S → ℝ) : Prop :=
  Measurable u ∧ ∃ C : ℝ, ∀ s, |u s| ≤ C

end DiscountedDP.Stationary


