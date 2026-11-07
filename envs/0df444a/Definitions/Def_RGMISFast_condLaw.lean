-- Prove2me | Definitions.Def_RGMISFast_condLaw
-- name    : RGMISFast_condLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:02.92538+00:00
-- url     : https://prove2.me/theorems/28eb3805-7002-47e6-9010-f9bde1c02bb9
-- title:
--   Conditional rank laws given $F_\theta$, prescribed ranks on $A$, or the root's rank
-- statement:
--   For $t\ge0$ the censored ranks $F_t=(\min\{r(v),t\})_{v\in V}$ reveal every rank below $t$ and only the fact that each other rank is at least $t$; conditionally on $F_t$ the unrevealed ranks are independent with distribution $t+\mathrm{Exp}(1)$.
--
--   1. A **history** at time $\theta$ is a rank vector $r_0$ with nonnegative values whose revealed values ($r_0(v)<\theta$) are distinct.
--   2. Given a history $r_0$, a set $A$ and prescribed ranks $r_A$, the **conditional law** makes the ranks independent: $r(v)=r_0(v)$ if $r_0(v)<\theta$; otherwise $r(v)=r_A(v)$ if $v\in A$; otherwise $r(v)\sim\theta+\mathrm{Exp}(1)$. With $A=\varnothing$ it is the law of the ranks given $F_\theta$.
--   3. The law **given $r(u^*)=\rho$**: the root has rank $\rho$, all other ranks are i.i.d. Exp(1).
--
--   These laws express the conditioning of Lemmas 5.2, 5.3, 6.1 and of (29).
--
--   **Formalization Note** Conditioning is represented by these explicit product laws, one for each history, instead of a conditional expectation given a σ-algebra; a statement about them holds for every history, which is stronger than almost surely.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), §5.1, p.18 (PDF p.20) (F_t); Lemma 5.3, p.20 (PDF p.22); Proof of Lemma 5.2, p.18 (PDF p.20)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace RGMISFast

/-- A history of the censored-rank filtration at time `θ` (Dalirrooyfard, Makarychev, Mitrović,
Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*, STOC 2027 submission (manuscript
sha256 e93cdfec…), §5.1, p.18: "Ft = (min{r(v), t})v∈V(G). This information reveals every rank
below t and only the fact that each remaining rank is at least t."), given by a representative
rank vector `r₀`: the revealed vertices are those with `r₀ v < θ`, their ranks are `r₀ v`, and
the revealed ranks are nonnegative and distinct (the paper analyses distinct ranks in `[0, ∞)`).

**Formalization Note** The values of `r₀` at unrevealed vertices are only required to be `≥ θ`
(automatic) and nonnegative; they do not affect the conditional law below, nor the active graph
`G_θ` computed from `r₀`, which depends only on the ranks below `θ`. -/
def IsHistory {V : Type*} (r₀ : V → ℝ) (θ : ℝ) : Prop :=
  (∀ v, 0 ≤ r₀ v) ∧ Set.InjOn r₀ {v | r₀ v < θ}

/-- The conditional rank law given the history `r₀` at time `θ` and prescribed ranks `rA` on a
set `A` (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at
Every Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), §5.1, p.18 and Lemma 5.3,
p.20): "Conditional on Ft, all unrevealed ranks … have independent t + Exp(1) distributions";
"Assign the ranks of all vertices of A arbitrarily in [a, ∞). Outside A, the ranks already
revealed by Fθ remain fixed, and the unrevealed ranks remain independent with distribution
θ + Exp(1)."

It is the product measure in which a revealed vertex (`r₀ v < θ`) has rank `r₀ v`, a vertex of
`A` that is not revealed has rank `rA v`, and every other vertex has an independent `θ + Exp(1)`
rank. With `A = ∅` it is the law of the ranks conditional on `F_θ`.

**Formalization Note** Conditioning is represented by this explicit law for each history (not by
`condExp` given a σ-algebra), so statements about it hold for every history, not only almost
surely. -/
noncomputable def condLaw {V : Type*} [Fintype V] [DecidableEq V] (r₀ : V → ℝ) (θ : ℝ)
    (A : Finset V) (rA : V → ℝ) : Measure (V → ℝ) :=
  Measure.pi (fun v => if r₀ v < θ then Measure.dirac (r₀ v)
    else if v ∈ A then Measure.dirac (rA v) else (expMeasure 1).map (fun x => θ + x))

/-- The rank law conditional on the root's rank `r(u∗) = ρ` (Dalirrooyfard, Makarychev,
Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*, STOC 2027 submission
(manuscript sha256 e93cdfec…), Proof of Lemma 5.2, p.18): "all probabilities and expectations are
conditional on r(u∗) = ρ; the other ranks are still independent exponential random variables". -/
noncomputable def rootLaw {V : Type*} [Fintype V] [DecidableEq V] (u : V) (ρ : ℝ) :
    Measure (V → ℝ) :=
  Measure.pi (fun v => if v = u then Measure.dirac ρ else expMeasure 1)

end RGMISFast


