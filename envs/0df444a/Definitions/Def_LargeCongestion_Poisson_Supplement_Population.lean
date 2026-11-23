-- Prove2me | Definitions.Def_LargeCongestion_Poisson_Supplement_Population
-- name    : LargeCongestion_Poisson_Supplement_Population
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:27:03.93416+00:00
-- url     : https://prove2.me/theorems/2770f949-dacf-4330-ab89-bdfec9942c9e
-- title:
--   §5.1 — general population games, multinomial mixture (24), Palm posterior and equilibrium (25)
-- statement:
--   Let $T$ be a finite set of types and $A_t$ a finite action space for each type. A population game consists of a joint population mass function $\mu$ on $\mathbb N^T$ and a real cost $C(n;t,a)$ on the full vector $n\in\mathbb N^{\{(t,a):a\in A_t\}}$ of other-player action counts. A type-symmetric profile is a probability vector $q_t$ on each $A_t$.
--
--   For $\bar n_t=\sum_{a\in A_t}n_{t,a}$, the induced strategy-count mass and active-player posterior are
--   $$P_{\mu,q}(n)=\mu(\bar n)\prod_t\left(\bar n_t!\prod_{a\in A_t}\frac{q_t(a)^{n_{t,a}}}{n_{t,a}!}\right),\qquad \mu(\bar n\mid t)=\frac{(\bar n_t+1)\mu(\bar n+\delta_t)}{\mathbb E_\mu[N_t]}.$$
--   Equilibrium requires each used action to minimize its expected cost under this posterior, as in (25). Every evaluated cost series must be summable. The population-law validity predicate includes finite positive type means, so the displayed posterior denominator has its ordinary meaning.
--
--   This is a general population-game interface, with arbitrary actions and signed count-vector costs. The congestion specialization is a separate definition. Summability is part of well-defined equilibrium membership, and is not a premise that assumes Poisson integrability in Theorem 3.
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, pp. 21–22, (24)–(25)

import Mathlib
import Definitions.Def_LargeCongestion_Poisson_Game

namespace LargeCongestion.Poisson.Supplement

open Filter
open scoped Topology

variable {T : Type*} [Fintype T] [DecidableEq T]
variable {A : T → Type*} [∀ t, Fintype (A t)] [∀ t, DecidableEq (A t)]

/-- The general population-uncertainty game of §5.1. Actions are arbitrary finite types,
not resource subsets. Costs read the entire other-player strategy-count vector. -/
structure PopulationGame (T : Type*) (A : T → Type*) where
  population : (T → ℕ) → ℝ
  cost : (Sigma A → ℕ) → Sigma A → ℝ

/-- A type-symmetric mixed strategy, §5.1. -/
def IsTypeProfile (q : ∀ t, A t → ℝ) : Prop :=
  (∀ t a, 0 ≤ q t a) ∧ ∀ t, ∑ a, q t a = 1

/-- E_mu[N_t], the denominator in the Palm law. -/
noncomputable def populationMean (μ : (T → ℕ) → ℝ) (t : T) : ℝ :=
  ∑' n, (n t : ℝ) * μ n

/-- A population law with finite positive mean for every type, as required by the Palm
formula. Positive mean excludes the identically zero types (p. 21, footnote 1). -/
def IsPopulationLaw (μ : (T → ℕ) → ℝ) : Prop :=
  (∀ n, 0 ≤ μ n) ∧ HasSum μ 1 ∧
    ∀ t, Summable (fun n => (n t : ℝ) * μ n) ∧ 0 < populationMean μ t

/-- Size-biased active-player posterior, §5.1, p. 21. -/
noncomputable def palm (μ : (T → ℕ) → ℝ) (t : T) (n : T → ℕ) : ℝ :=
  ((n t : ℝ) + 1) * μ (Function.update n t (n t + 1)) / populationMean μ t

/-- Total counts of each type associated with a strategy-count vector. -/
def typeCounts (n : Sigma A → ℕ) (t : T) : ℕ := ∑ a : A t, n ⟨t, a⟩

/-- Multinomial mixture (24). The finite product is over each type's own action space. -/
noncomputable def populationFlowPmf (μ : (T → ℕ) → ℝ) (q : ∀ t, A t → ℝ)
    (n : Sigma A → ℕ) : ℝ :=
  μ (typeCounts n) * ∏ t, (((typeCounts n t).factorial : ℝ) *
    ∏ a : A t, q t a ^ (n ⟨t, a⟩) / ((n ⟨t, a⟩).factorial : ℝ))

/-- Posterior expected action cost, using the Palm population law in (24). -/
noncomputable def populationCost (G : PopulationGame T A) (q : ∀ t, A t → ℝ)
    (p : Sigma A) : ℝ :=
  ∑' n, populationFlowPmf (palm G.population p.1) q n * G.cost n p

/-- Equilibrium (25). Summability belongs to well-defined expected costs, and is a
conclusion of equilibrium membership rather than an assumed Poisson integrability lemma. -/
def PopulationGame.IsEquilibrium (G : PopulationGame T A) (q : ∀ t, A t → ℝ) : Prop :=
  IsTypeProfile q ∧
    (∀ t a, Summable (fun n => populationFlowPmf (palm G.population t) q n * G.cost n ⟨t, a⟩)) ∧
    ∀ t (a b : A t), 0 < q t a → populationCost G q ⟨t, a⟩ ≤ populationCost G q ⟨t, b⟩

end LargeCongestion.Poisson.Supplement


