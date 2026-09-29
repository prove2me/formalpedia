-- Prove2me | Definitions.Def_mm_lower
-- name    : mm_lower
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-21T20:24:09.288049+00:00
-- url     : https://prove2.me/theorems/3f884200-6674-489c-98d8-24f0216a75ef
-- title:
--   Bottleneck ratios, distinguishing statistics, and the transition graph
-- statement:
--   This file provides the quantities behind the lower-bound methods of Chapter 7 of Levin–Peres–Wilmer.
--
--   **Bottleneck (conductance) quantities.** For a chain $P$ with stationary mass function $\pi$, the **edge measure** is $Q(x,y)=\pi(x)P(x,y)$, the stationary flow along the ordered pair $(x,y)$. The **bottleneck ratio** of a set of states $S$ is
--   $$\Phi(S)=\frac{Q(S,S^c)}{\pi(S)}=\frac{\sum_{x\in S}\sum_{y\notin S}\pi(x)P(x,y)}{\sum_{x\in S}\pi(x)},$$
--   the conditional probability, at stationarity, of escaping $S$ in one step; and the **bottleneck constant** is
--   $$\Phi_\star=\min\Bigl\{\Phi(S)\;:\;\varnothing\ne S\subseteq V,\ \pi(S)\le\tfrac12\Bigr\}.$$
--   A small $\Phi_\star$ is a bottleneck: some half-space that the chain leaves only reluctantly, forcing slow mixing.
--
--   **Counting and diameter quantities.** The **maximal out-degree** $\Delta=\max_x\#\{y:P(x,y)>0\}$ bounds how many states are reachable in one step, so $\Delta^t$ bounds how many are reachable in $t$ steps. The **transition graph** joins $x\ne y$ whenever $P(x,y)>0$ or $P(y,x)>0$; its graph diameter measures how far apart two starting states can be, giving the diameter lower bound.
--
--   **Distinguishing statistics.** For a mass function $\mu$ and a statistic $f:V\to\mathbb R$, the file defines the mean and variance
--   $$\mathbb E_\mu(f)=\sum_x f(x)\,\mu(x),\qquad \operatorname{Var}_\mu(f)=\sum_x\bigl(f(x)-\mathbb E_\mu(f)\bigr)^2\mu(x),$$
--   and the **pushforward** of $\mu$ along $f$, $(f_*\mu)(b)=\sum_{a:f(a)=b}\mu(a)$ — the law of the statistic. A statistic whose means under $P^t(x,\cdot)$ and under $\pi$ are far apart relative to their standard deviations witnesses a large total-variation distance.
--
--   **The lazy hypercube walk.** The chapter's running example: the lazy simple random walk on the $n$-dimensional hypercube $\{0,1\}^n$ (realized as the torus $\mathbb Z_2^n$), which holds with probability $\tfrac12$ and otherwise flips a uniform coordinate:
--   $$P(x,y)=\tfrac12\ \ (y=x),\qquad \tfrac1{2n}\ \ (y\sim x),\qquad 0\ \ \text{otherwise}.$$
--
--   **Conventions.** Division is total ($r/0=0$, so $\Phi(\varnothing)=0$), and an infimum over an empty family takes the junk value $0$; the theorems supply the hypotheses under which these quantities carry their probabilistic meaning.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Ch. 7, Sections 7.1-7.3, pp. 87-93

import Definitions.Def_mm_mixing
import Definitions.Def_mm_coupling
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
Quantities used in lower bounds on mixing times, following
Levin–Peres–Wilmer, *Markov Chains and Mixing Times*, Chapter 7.
-/

namespace MarkovMixing

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The maximal number of states accessible in one step,
`Δ = max_x |{y : P(x,y) > 0}|` (LPW §7.1.1, Eq. (7.1)). -/
def maxOutDegree (P : Matrix V V ℝ) : ℕ :=
  Finset.univ.sup fun x : V => (Finset.univ.filter fun y : V => 0 < P x y).card

/-- The graph underlying a chain: an edge between `x ≠ y` whenever
`P(x,y) + P(y,x) > 0`; the chain's **diameter** is this graph's diameter
(LPW §7.1.2). -/
def transGraph (P : Matrix V V ℝ) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y => 0 < P x y

/-- The **edge measure** `Q(x,y) = π(x) P(x,y)` (LPW §7.2, Eq. (7.4)). -/
def edgeMeasure (P : Matrix V V ℝ) (π : V → ℝ) (x y : V) : ℝ :=
  π x * P x y

/-- The **bottleneck ratio** `Φ(S) = Q(S, Sᶜ)/π(S)` of a set of states
(LPW §7.2, Eq. (7.5)). -/
def bottleneckRatio (P : Matrix V V ℝ) (π : V → ℝ) (S : Finset V) : ℝ :=
  (∑ x ∈ S, ∑ y ∈ Sᶜ, edgeMeasure P π x y) / ∑ x ∈ S, π x

/-- The **bottleneck ratio of the chain**,
`Φ⋆ = min {Φ(S) : π(S) ≤ 1/2, S ≠ ∅}` (LPW §7.2, Eq. (7.6)). -/
def bottleneckStar (P : Matrix V V ℝ) (π : V → ℝ) : ℝ :=
  ⨅ S : {S : Finset V // S.Nonempty ∧ ∑ x ∈ S, π x ≤ 2⁻¹},
    bottleneckRatio P π S.1

/-- The expectation `E_μ(f) = ∑_x f(x) μ(x)` of a statistic under a
distribution (LPW §7.3). -/
def distExp (μ : V → ℝ) (f : V → ℝ) : ℝ :=
  ∑ x, f x * μ x

/-- The variance `Var_μ(f)` of a statistic under a distribution (LPW §7.3). -/
def distVar (μ : V → ℝ) (f : V → ℝ) : ℝ :=
  ∑ x, (f x - distExp μ f) ^ 2 * μ x

/-- The pushforward `μ f⁻¹` of a distribution under a statistic
`f : Ω → Λ` (LPW §7.3). -/
def pushforward {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (μ : V → ℝ) (f : V → Λ) :
    Λ → ℝ :=
  fun b => ∑ a ∈ Finset.univ.filter fun a : V => f a = b, μ a

/-- The **lazy random walk on the `n`-dimensional hypercube** `{0,1}^n`
(LPW §2.3): the hypercube is the torus `ℤ_2^n`. -/
def hypercubeWalk (n : ℕ) : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℝ :=
  lazy (graphWalk (torusGraph n 2))

end

end MarkovMixing


