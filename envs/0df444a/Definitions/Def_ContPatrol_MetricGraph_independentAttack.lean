-- Prove2me | Definitions.Def_ContPatrol_MetricGraph_independentAttack
-- name    : ContPatrol_MetricGraph_independentAttack
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:13:11.681+00:00
-- url     : https://prove2.me/theorems/25ca36e5-b5a5-4f7b-bd17-af821d3ee9da
-- title:
--   Definitions 2–3: independent sets and the independent attack strategy
-- statement:
--   Fix $\alpha>0$.
--
--   1. A set $I$ of points of $Q$ is **independent** if any two distinct points of $I$ are at distance at least $\alpha$.
--   2. For a set $Y$, $W(Y)$ is the set of points at distance at most $\alpha/2$ from some point of $Y$; $W^c$ is its complement.
--   3. For an independent set $I$ of cardinality $l$ and $W=W(I)$, put
--   $$p=\frac{l\alpha}{\lambda(W^c)+l\alpha}.$$
--   The **independent attack strategy**: with probability $p$, attack an element of $I$ chosen equiprobably, at a start time uniform on $[0,\alpha]$; with probability $1-p$, attack a point of $W^c$ chosen uniformly according to length, at start time $\alpha/2$.
--
--   As a measure on (point, start time):
--   $$\frac{p}{l}\sum_{x\in I}\delta_x\otimes U[0,\alpha]\;+\;(1-p)\,\frac{\lambda|_{W^c}}{\lambda(W^c)}\otimes\delta_{\alpha/2}.$$
--
--   This is the Attacker's optimal strategy on networks with leaves (Theorem 1, Lemma 5, Theorem 6).
--
--   **Formalization Note** $I$ is a finite set (with $\alpha>0$ every independent set in $Q$ is finite). $W(\emptyset)=\emptyset$, so for $l=0$ the strategy is the uniform attack at time $\alpha/2$; if $\lambda(W^c)=0$ then $1-p=0$ and the second part vanishes.
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, Definitions 2–3, p.7

import Mathlib
import Definitions.Def_ContPatrol_MetricGraph_dist
import Definitions.Def_ContPatrol_MetricGraph_lengthMeasure

namespace ContPatrol

namespace MetricGraph

open MeasureTheory

variable {V E : Type}

/-- **Independent sets and the set W(Y) (Definition 2).**
Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, Definition 2,
p.7: "A subset I of Q is called independent if the distance between any two of its points is at
least α. For any subset Y of Q, the set W ≡ W(Y) is the subset of Q consisting of all points at
distance at most α/2 from Y."

**Formalization Note.** An independent set is taken as a `Finset`; with `α > 0` every independent
subset of the compact network Q is finite, so nothing is lost. "Any two of its points" means two
distinct points. -/
def IsIndependent (G : MetricGraph V E) (α : ℝ) (I : Finset G.Point) : Prop :=
  ∀ x ∈ I, ∀ y ∈ I, x ≠ y → α ≤ G.dist x y

/-- The set `W(Y)` of points at distance at most `α/2` from `Y` (Definition 2, p.7).

**Formalization Note.** Written with an explicit witness `y ∈ Y`, so `W(∅) = ∅` (an
`infDist`-based definition would give all of Q for `Y = ∅`). -/
def nbhd (G : MetricGraph V E) (α : ℝ) (Y : Set G.Point) : Set G.Point :=
  {x | ∃ y ∈ Y, G.dist x y ≤ α / 2}

/-- The probability `p = lα / (λ(W^c) + lα)` of Definition 3 (p.7), with `l = |I|` and
`W = W(I)`. -/
noncomputable def attackProb (G : MetricGraph V E) (α : ℝ) (I : Finset G.Point) : ℝ :=
  I.card * α / ((G.lengthMeasure (G.nbhd α I)ᶜ).toReal + I.card * α)

/-- **Independent attack strategy (Definition 3).**
Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, Definition 3,
p.7: "Given an independent set I of cardinality l and the set W ≡ W(I), the independent attack
strategy is as follows for p = lα/(λ(W^c) + lα).
1. With probability p attack at an element of I chosen equiprobably at a start time chosen
uniformly at random in J = [0, α].
2. With probability 1 − p attack uniformly on W^c at start time α/2."

As a measure on pairs (point, start time):
`(p/l) Σ_{x ∈ I} δ_x ⊗ U[0, α] + (1 − p) · (λ restricted to W^c, normalized) ⊗ δ_{α/2}`.

**Formalization Note.** The degenerate cases come out as in the paper: if `l = 0` then `p = 0`, the
first part is an empty sum and the strategy is the uniform attack at time `α/2` (since
`W(∅) = ∅`); if `λ(W^c) = 0` then `1 − p = 0` and the second part is the zero measure
(`0 • μ = 0` even though `(λ(W^c))⁻¹ = ∞`). Uniform on `[0, α]` is Lebesgue measure on `[0, α]`
divided by `α`. -/
noncomputable def independentAttack (G : MetricGraph V E) (α : ℝ) (I : Finset G.Point) :
    Measure (G.Point × ℝ) :=
  ENNReal.ofReal (G.attackProb α I / I.card) •
      ∑ x ∈ I, (Measure.dirac x).prod
        ((ENNReal.ofReal α)⁻¹ • (volume : Measure ℝ).restrict (Set.Icc 0 α)) +
    ENNReal.ofReal (1 - G.attackProb α I) •
      ((G.lengthMeasure (G.nbhd α I)ᶜ)⁻¹ • G.lengthMeasure.restrict (G.nbhd α I)ᶜ).prod
        (Measure.dirac (α / 2))

end MetricGraph

end ContPatrol


