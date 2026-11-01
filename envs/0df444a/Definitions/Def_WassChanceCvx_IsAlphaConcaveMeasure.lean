-- Prove2me | Definitions.Def_WassChanceCvx_IsAlphaConcaveMeasure
-- name    : WassChanceCvx_IsAlphaConcaveMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:25:12.185766+00:00
-- url     : https://prove2.me/theorems/b4178d8d-d983-470f-95e6-99a4ffda0dbf
-- title:
--   α-concave probability measure (Definition 2)
-- statement:
--   Let $E$ be a real vector space with a σ-algebra (in the paper $E=\mathbb R^n$ with its Borel sets) and $\alpha\in[-\infty,+\infty]$. A probability measure $\mathbb P$ on $E$ is **α-concave** if for all measurable sets $A,B\subseteq E$ and all $\theta\in[0,1]$,
--
--   $$
--   \mathbb P\bigl(\theta A+(1-\theta)B\bigr)\ \ge\ m_\alpha\bigl(\mathbb P(A),\mathbb P(B);\theta\bigr),\qquad \theta A+(1-\theta)B:=\{\theta x+(1-\theta)y:\ x\in A,\ y\in B\}.
--   $$
--
--   Gaussian distributions and uniform distributions on convex bodies are examples ($\alpha=0$ and $\alpha=1/n$). The paper's convexity theorem for the Wasserstein-robust chance constraint assumes the reference distribution is α-concave with $\alpha\ge-1$.
--
--   **Formalization Note** The set $\theta A+(1-\theta)B$ need not be Borel; $\mathbb P$ is evaluated on it as Mathlib's outer measure, which equals its completion (Lebesgue-measurable-sets) measure because the set is analytic. No measurability side condition and no convexity of $A,B$ is imposed. The paper's convex set $\Omega$ carrying the measure is replaced by the whole space; the two definitions agree because $m_\alpha$ is nondecreasing in each argument. Values are compared as real numbers (`toReal`), which is exact for probability measures; every statement assumes $\mathbb P$ is a probability measure.
-- source:
--   Shen, Jiang, Convex Chance-Constrained Programs with Wasserstein Ambiguity, arXiv:2111.02486v2, Definition 2 and the display before it, p.5

import Mathlib
import Definitions.Def_KallMayerSLP_GenConcave_genMean

open MeasureTheory
open scoped Pointwise

namespace WassChanceCvx

/-- **α-concave probability measure.**
Shen, Jiang, arXiv:2111.02486v2, Definition 2, p.5: "A probability measure `ℙ` defined on the
Lebesgue subsets of a convex subset `Ω ⊆ ℝⁿ` is said to be α-concave if for any Borel measurable
sets `A, B ⊆ Ω` and for all `θ ∈ [0, 1]`, `ℙ(θA + (1 − θ)B) ≥ m_α(ℙ(A), ℙ(B); θ)`", where
`θA + (1 − θ)B := {θx + (1 − θ)y : x ∈ A, y ∈ B}` (p.5).

`IsAlphaConcaveMeasure α P` says `P(θA + (1 − θ)B) ≥ m_α(P(A), P(B); θ)` for all measurable
`A, B` and all `θ ∈ [0, 1]`.

`m_α(a, b; θ)` is the published `KallMayerSLP.GenConcave.genMean α θ a b` (Definition 1's mean).

**Formalization Note.** The predicate is meant for probability measures (every statement carries
`IsProbabilityMeasure P`), so the values are compared as real numbers through `toReal`. The sets
`A, B` range over all measurable subsets of the whole space (`Ω` = the space): a measure that is
α-concave on the Borel subsets of a convex `Ω` carrying all of its mass is α-concave on all Borel
sets, since `m_α` is nondecreasing in each argument. The Minkowski combination
`θ • A + (1 - θ) • B` need not be Borel; `P` is evaluated on it as Mathlib's outer measure, which
for this analytic (hence universally measurable) set is its completion measure, i.e. the paper's
"Lebesgue subsets" reading. No measurability side condition and no convexity of `A, B` is
imposed. -/
def IsAlphaConcaveMeasure {E : Type*} [AddCommGroup E] [Module ℝ E] [MeasurableSpace E]
    (α : EReal) (P : Measure E) : Prop :=
  ∀ A B : Set E, MeasurableSet A → MeasurableSet B → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
    KallMayerSLP.GenConcave.genMean α θ (P A).toReal (P B).toReal ≤ (P (θ • A + (1 - θ) • B)).toReal

end WassChanceCvx


