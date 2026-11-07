-- Prove2me | Definitions.Def_ContinualCounting_IsApproxDP
-- name    : ContinualCounting_IsApproxDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:40:58.252237+00:00
-- url     : https://prove2.me/theorems/8bcae554-ec15-4534-9569-00574acef935
-- title:
--   $(\varepsilon,\delta)$-indistinguishability of a family of laws over a neighbouring relation
-- statement:
--   Let $(M_x)_{x\in X}$ be a family of measures on a measurable space $Y$, and let $R$ be a relation on $X$. The family is $(\varepsilon,\delta)$-differentially private with respect to $R$ if for all $x,x'$ with $R(x,x')$ and every measurable $S\subseteq Y$,
--   $$M_x(S)\le e^{\varepsilon}M_{x'}(S)+\delta.$$
--
--   This is the general form of the inequality in Definition 1 of the paper. The same predicate carries the paper's neighbouring relation on $\{0,1\}^n$, the restricted relation of Lemma 4 and the binary relation of Lemma 1.
--
--   **Formalization Note** The range of $\varepsilon,\delta$ and the fact that each $M_x$ is a probability measure are hypotheses of the theorems that use the predicate, since derived mechanisms have parameters such as $e^{\varepsilon}\delta+\delta'$.
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), Definition 1, p.2 (PDF p.3)

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace ContinualCounting

/-- **Approximate differential privacy for a neighbouring relation.** The inequality of Definition 1
of Bairaktari, Dahl, Larsen, *The Binary Tree Mechanism is Optimal for Differentially Private
Continual Counting*, arXiv:2607.00876 (sha256 986e6426…), p.2: `Pr[M(x) ∈ S] ≤ e^ε Pr[M(x′) ∈ S] + δ`
for every measurable `S` and every related pair `x, x′`.

**Formalization Note.** The general object: a family `M` of measures on an arbitrary measurable
space, indexed by an arbitrary input type carrying an arbitrary relation `R`. The relation is the
paper's neighbouring relation in `IsDP`, the restricted one in Lemma 4, and "the two bits differ" in
Lemma 1. The ranges `ε > 0`, `δ ∈ [0, 1)` that Definition 1 fixes are hypotheses of the theorems and
not clauses of the predicate, because derived mechanisms (Lemma 2, Lemma 4) have parameters
`e^ε δ + δ′`, `3δ` that need not stay below `1` a priori. A theorem using this predicate must assume
probability measures: with `M x = 0` the inequality is trivial. -/
def IsApproxDP {α β : Type*} [MeasurableSpace β] (R : α → α → Prop) (M : α → Measure β)
    (ε δ : ℝ) : Prop :=
  ∀ x x', R x x' → ∀ S : Set β, MeasurableSet S →
    M x S ≤ ENNReal.ofReal (Real.exp ε) * M x' S + ENNReal.ofReal δ

end ContinualCounting


