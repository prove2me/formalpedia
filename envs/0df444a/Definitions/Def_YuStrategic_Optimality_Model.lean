-- Prove2me | Definitions.Def_YuStrategic_Optimality_Model
-- name    : YuStrategic_Optimality_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:22:07.676009+00:00
-- url     : https://prove2.me/theorems/86870e06-e7a9-4cc7-b56b-6cf0e55f5e8a
-- title:
--   Borel-space MDP with an analytic constraint graph $\Gamma$ and Borel transition kernel $q$
-- statement:
--   A **Borel-space MDP in the universal measurability framework** on Borel spaces $\mathbb X$ and $\mathbb A$ consists of:
--   1. a control constraint $A:x\mapsto A(x)\subseteq\mathbb A$, where each $A(x)$ is a nonempty set of admissible actions at state $x$;
--   2. the requirement that the graph $\Gamma=\{(x,a)\mid x\in\mathbb X,\ a\in A(x)\}$ is an **analytic** subset of $\mathbb X\times\mathbb A$;
--   3. state transitions governed by $q(dy\mid x,a)$, a Borel measurable stochastic kernel on $\mathbb X$ given $\mathbb X\times\mathbb A$.
--
--   A set is analytic if it is empty or the image of a Borel subset of a Polish space under a Borel map. Each section $A(x)$ of the analytic set $\Gamma$ is analytic, hence universally measurable. All results of Section 3 of the paper are stated for this model.
--
--   **Formalization Note.** The paper's one-stage cost $c:\Gamma\to\bar{\mathbb R}$ is not part of the structure, since none of the results formalized here uses it. Analyticity is Mathlib's `AnalyticSet` (empty or a continuous image of the Baire space), which agrees with the paper's definition for subsets of a Borel space. $q$ is a Mathlib Markov kernel, i.e. Borel measurable.
-- source:
--   Yu, arXiv:2206.06492v3, §2.2, p. 6 (model assumptions, bullets 1–3); analytic sets p. 5

import Mathlib
import Definitions.Def_YuStrategic_Optimality_PathSpace

namespace YuStrategic.Optimality

open MeasureTheory ProbabilityTheory

/-- A Borel-space MDP in the universal measurability framework (Yu, arXiv:2206.06492v3, §2.2,
p. 6), without its cost. On state space `X` and action space `A` it consists of
1. the control constraint `A : x ↦ A(x) ⊆ A`, with every `A(x)` nonempty;
2. the requirement that the graph `Γ = {(x, a) | x ∈ X, a ∈ A(x)}` is analytic;
3. the state transitions `q(dy | x, a)`, a Borel measurable stochastic kernel on `X` given `X × A`.

**Formalization Note.** The one-stage cost `c : Γ → R̄` of the paper is not part of the
structure: Theorems 3.1–3.3, Lemma 3.1 and Proposition 3.1 never use it, so every model of the
paper is an instance. The spaces `X`, `A` are Borel spaces in the theorems that use the model
(`BertsekasShreve.AnalyticSelection.IsBorelSpace` with their Borel σ-algebras). "Analytic" is
Mathlib's `AnalyticSet` (empty, or a continuous image of the Baire space), which for subsets of
a Borel space agrees with the paper's definition (p. 5). -/
structure Model (X A : Type) [TopologicalSpace X] [MeasurableSpace X]
    [TopologicalSpace A] [MeasurableSpace A] where
  /-- the set `A(x)` of admissible actions at the state `x` -/
  adm : X → Set A
  /-- every `A(x)` is nonempty -/
  adm_nonempty : ∀ x, (adm x).Nonempty
  /-- the graph `Γ` of `A(·)` is analytic -/
  analytic_graph : AnalyticSet {z : X × A | z.2 ∈ adm z.1}
  /-- the Borel measurable state transition kernel `q(dy | x, a)` -/
  q : Kernel (X × A) X
  /-- `q(· | x, a)` is a probability measure for every `(x, a)` -/
  [isMarkov : IsMarkovKernel q]

attribute [instance] Model.isMarkov

/-- The graph `Γ = {(x, a) | x ∈ X, a ∈ A(x)}` of the control constraint (§2.2, p. 6). -/
def Model.graph {X A : Type} [TopologicalSpace X] [MeasurableSpace X]
    [TopologicalSpace A] [MeasurableSpace A] (M : Model X A) : Set (X × A) :=
  {z | z.2 ∈ M.adm z.1}

end YuStrategic.Optimality


