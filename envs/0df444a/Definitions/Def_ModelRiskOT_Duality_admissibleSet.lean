-- Prove2me | Definitions.Def_ModelRiskOT_Duality_admissibleSet
-- name    : ModelRiskOT_Duality_admissibleSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:54:20.402196+00:00
-- url     : https://prove2.me/theorems/55fad339-528f-4259-a5ab-63b8f61c06a3
-- title:
--   $S_\pi=\mathrm{Spt}(\pi_X)\cup\mathrm{Spt}(\pi_Y)$ and the set $E$ of Proposition 7's measures
-- statement:
--   Let $S$ be a topological space with a measurable structure and $\pi$ a measure on $S\times S$ with marginals $\pi_X(\cdot)=\pi(\cdot\times S)$ and $\pi_Y(\cdot)=\pi(S\times\cdot)$. Define the closed set
--
--   $$S_\pi=\mathrm{Spt}(\pi_X)\cup\mathrm{Spt}(\pi_Y).$$
--
--   Given a cost $c$, $f:S\to\mathbb R$ and a probability measure $\mu$ on $S$, let $E$ be the set of probability measures $\pi$ on $S\times S$ such that
--
--   1. (a) $\int c(x,y)\,d\pi(x,y)<\infty$;
--   2. (b) $\int f(y)\,d\pi(x,y)\in(-\infty,\infty)$, i.e. $(x,y)\mapsto f(y)$ is $\pi$-integrable;
--   3. (c) $\pi(A\times S)=\mu(A)$ for every Borel set $A\subseteq S$.
--
--   No budget constraint $\int c\,d\pi\le\delta$ is imposed. $E$ is the convex set over which the proof of Theorem 1(a) applies a minimax theorem, and Lemma 8 takes a supremum over it.
--
--   **Formalization Note** Supports are Mathlib's `Measure.support`; (b) is `Integrable (fun p => f p.2) π`.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 20 (§4.2, S_π; Proposition 7 (a)–(c)); p. 22 (the set E)

import Mathlib

namespace ModelRiskOT.Duality

open MeasureTheory

/-- `S_π := Spt(π_X) ∪ Spt(π_Y)` (Blanchet & Murthy, arXiv:1604.01446v2, §4.2, p. 20): the union
of the supports of the two marginals `π_X = π(· × S)` and `π_Y = π(S × ·)` of a measure `π` on
`S × S`. It is a closed set (`Measure.support` is closed). -/
def supportUnion {S : Type*} [TopologicalSpace S] [MeasurableSpace S] (π : Measure (S × S)) :
    Set S :=
  (π.map Prod.fst).support ∪ (π.map Prod.snd).support

/-- The set `E` of the proof of Theorem 1(a) (arXiv:1604.01446v2, p. 22): probability measures
`π ∈ P(S × S)` satisfying conditions (a)–(c) of Proposition 7 (p. 20):
(a) `∫ c(x, y) dπ(x, y) < ∞`; (b) `∫ f(y) dπ(x, y) ∈ (−∞, ∞)`, i.e. `y ↦ f(y)` is `π`-integrable;
(c) `π(A × S) = μ(A)` for every Borel `A` (the first marginal of `π` is `μ`).
No budget constraint `∫ c dπ ≤ δ` is imposed. -/
def admissibleSet {S : Type*} [MeasurableSpace S] (c : S → S → ℝ) (f : S → ℝ) (μ : Measure S) :
    Set (Measure (S × S)) :=
  {π | IsProbabilityMeasure π ∧ ∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π < ⊤ ∧
    Integrable (fun p => f p.2) π ∧ ∀ A : Set S, MeasurableSet A → π (A ×ˢ Set.univ) = μ A}

end ModelRiskOT.Duality


