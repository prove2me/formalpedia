-- Prove2me | Definitions.Def_PalmQueueing_Formulas_RareEvents
-- name    : PalmQueueing_Formulas_RareEvents
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T00:51:45.921899+00:00
-- url     : https://prove2.me/theorems/d1356f07-4561-4ed1-a7b3-91426fb3c4cd
-- title:
--   Rare events: the Markov setting and the θ_t thinnings
-- statement:
--   Two settings, one for each rare-event result.
--
--   **The Markov setting** (p.204). $\{X(t)\}$ is an irreducible discrete-time Markov chain on a
--   countable state space with transition matrix $K$ and stationary probability measure $\pi$; $\alpha$
--   is a fixed point called the origin; $F$ is a rarely visited set which does not contain the origin.
--   $R \ge 1$ is the first return time to $\alpha$ having first made an excursion to $F$, and
--   $\tau(F)$ the hitting time of $F$. Clearly $R \ge \tau(F)$, but since it takes so long to get to
--   $F$ the extra return time is asymptotically negligible — **Keilson's asymptotic equivalence**
--   $$ \lim_{\pi(F) \to 0} \frac{E_\alpha R}{E_\alpha \tau(F)} = 1 . \tag{3.2.38} $$
--
--   **The stationary setting** (pp.206-207) replaces the chain by a $\theta_t$-compatible process
--   $\{X(t)\}$ and the cycle structure by *thinnings* of the entrance and exit processes of two
--   disjoint regular sets $A$ and $F$. For all sets $E$,
--   $$ \tau(E) = \inf\{t > 0, X(t) \in E\}, \qquad \tau^-(E) = \inf\{t > 0, X(-t) \in E\} .
--   \tag{3.2.42} $$
--   Of the thinnings the book defines, Theorem 3.2.1 needs $N^{F(\to A)}$, whose points are the first
--   entrances into $A$ after $\{X(t)\}$ has left $F$ — "the generalization of that of the cycles
--   considered in the Markov case". Property 3.2.3 gives that all these thinnings share one intensity
--   $\Lambda$ with $0 < \Lambda < \infty$.
--
--   **Formalization Note.** The chain is irreducible (every state leads to every state along a path of
--   positive transition probabilities) and $F$ is non-empty, as the page's $R$ requires. An entrance
--   time into $A$ is, as on p.206, a time $t$ such that $X(t-\epsilon) \notin A$ and
--   $X(t+\epsilon) \in A$ for all $0 < \epsilon < a$, some $a > 0$; exit times are defined analogously.
--   A set $A$ is *regular* (p.207) when $\mathbf{1}_{X(t) \in A}$ is a.s. continuous except at a
--   set of times without accumulation, and the entrance and exit point processes $N^{\to A}$,
--   $N^{A\to}$ both have a finite positive intensity.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, §§3.2.5-3.2.6, pp. 204-209

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# Rare events: the Markov setting and the `θ_t` thinnings (§§3.2.5-3.2.6, pp.204-209)

Two settings, one for each of the two rare-event results.

**The Markov setting** (p.204) is elementary: an irreducible discrete-time Markov chain on a
countable state space, an origin `α`, and a rarely visited set `F` not containing it. `R` is the
first return time to `α` having first made an excursion to `F`, and Keilson's asymptotic
equivalence `(3.2.38)` says `E_α R / E_α τ(F) → 1` as `π(F) → 0`. Lemma 3.2.1 is the closed form
for `E_α R` that makes the equivalence useful.

**The stationary setting** (pp.206-207) replaces the chain by a `θ_t`-compatible process `{X(t)}`
and the cycle structure by *thinnings* of the entrance and exit processes of two disjoint regular
sets `A` and `F`. Of the several the book defines, Theorem 3.2.1 needs `N^{F(→A)}`, whose points
are the first entrances into `A` after `{X(t)}` has left `F`, and its Palm probability
`P⁰_{F(→A)}`. Property 3.2.3 gives that all these thinnings share one intensity `Λ` with
`0 < Λ < ∞`.
-/

namespace PalmQueueing.Formulas

open MeasureTheory Filter Topology
open PalmQueueing.Palm

variable {Ω : Type*} [MeasurableSpace Ω]

section Markov

variable {S : Type*} [Countable S] [MeasurableSpace S]

/-- The Markovian setting of §3.2.5 (p.205): an irreducible discrete-time Markov chain on a
countable state space `S` with transition matrix `K` and stationary probability `π`, a fixed
origin `α`, and a rarely visited set `F` not containing it. `F` is non-empty: `R` is "the first
return time to `α` having first made an excursion to `F`", which does not exist for `F = ∅`. -/
structure RareEventChain (S : Type*) [Countable S] where
  /-- The transition kernel `K`. -/
  K : S → S → ℝ
  /-- Its entries are probabilities. -/
  K_nonneg : ∀ x y, 0 ≤ K x y
  /-- Each row sums to one. -/
  K_sum : ∀ x, ∑' y, K x y = 1
  /-- The stationary probability measure `π`. -/
  pi : S → ℝ
  /-- `π` is non-negative. -/
  pi_nonneg : ∀ x, 0 ≤ pi x
  /-- `π` is a probability. -/
  pi_sum : ∑' x, pi x = 1
  /-- `π` is stationary. -/
  pi_stationary : ∀ y, ∑' x, pi x * K x y = pi y
  /-- The chain is irreducible: every state leads to every state along a path of positive
  transition probabilities. -/
  irreducible : ∀ x y : S, ∃ (n : ℕ) (q : ℕ → S), q 0 = x ∧ q n = y ∧ ∀ j < n, 0 < K (q j) (q (j + 1))
  /-- The origin. -/
  alpha : S
  /-- The rarely visited set, which does not contain the origin. -/
  F : Set S
  /-- `α ∉ F`. -/
  alpha_not_mem : alpha ∉ F
  /-- `F` is non-empty. -/
  F_nonempty : F.Nonempty

end Markov

/-- `(3.2.42)`: `τ(E) = inf{t > 0 ; X(t) ∈ E}`, the hitting time of `E` after the origin. -/
noncomputable def hitFwd {S : Type*} (X : ℝ → Ω → S) (E : Set S) (ω : Ω) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ X t ω ∈ E}

/-- `(3.2.42)`: `τ⁻(E) = inf{t > 0 ; X(−t) ∈ E}`, the hitting time looking backwards. -/
noncomputable def hitBwd {S : Type*} (X : ℝ → Ω → S) (E : Set S) (ω : Ω) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ X (-t) ω ∈ E}

/-- `t` is an **entrance time into `A`** for `{X(t)}` (p.206): for some `a > 0`,
`X(t − ε) ∉ A` and `X(t + ε) ∈ A` for all `0 < ε < a`. -/
def IsEntrance {S : Type*} (X : ℝ → Ω → S) (A : Set S) (t : ℝ) (ω : Ω) : Prop :=
  ∃ a > (0 : ℝ), ∀ ε ∈ Set.Ioo (0 : ℝ) a, X (t - ε) ω ∉ A ∧ X (t + ε) ω ∈ A

/-- `t` is an **exit time out of `A`** for `{X(t)}` (p.206, "defined analogously"): for some
`a > 0`, `X(t − ε) ∈ A` and `X(t + ε) ∉ A` for all `0 < ε < a`. -/
def IsExit {S : Type*} (X : ℝ → Ω → S) (A : Set S) (t : ℝ) (ω : Ω) : Prop :=
  ∃ a > (0 : ℝ), ∀ ε ∈ Set.Ioo (0 : ℝ) a, X (t - ε) ω ∈ A ∧ X (t + ε) ω ∉ A

/-- `A` is **regular** for `{X(t)}` (pp.206-207):
1. the process `1_{X(t) ∈ A}` is a.s. continuous, except at a denumerable set of times of
   discontinuity without accumulation (on every bounded interval it has finitely many
   discontinuities);
2. the point processes `N^{→A}` of entrance times into `A` and `N^{A→}` of exit times out of `A`
   both have a finite and positive intensity. -/
def IsRegular {S : Type*} (P : Measure Ω) (X : ℝ → Ω → S) (A : Set S) : Prop :=
  (∀ᵐ ω ∂P, ∀ a b : ℝ, {t ∈ Set.Icc a b |
      ¬ ContinuousAt (fun s => Set.indicator A (fun _ => (1 : ℝ)) (X s ω)) t}.Finite) ∧
  ∃ (Nin Nout : PointProcess Ω) (lin lout : ℝ),
    (∀ (t : ℝ) (ω : Ω), (∃ n : ℤ, Nin.T n ω = t) ↔ IsEntrance X A t ω) ∧
    (∀ (t : ℝ) (ω : Ω), (∃ n : ℤ, Nout.T n ω = t) ↔ IsExit X A t ω) ∧
    IsIntensity Nin P lin ∧ IsIntensity Nout P lout

/-- `t` is a point of `N^{F(→A)}` (p.207): it is an entrance into `A`, and `{X(t)}` visited `F`
strictly between the previous entrance into `A` and `t` — that is, `t` is the **first entrance into
`A` after `{X(t)}` has left `F`**. -/
def IsFirstEntranceAfter {S : Type*} (X : ℝ → Ω → S) (A F : Set S) (t : ℝ) (ω : Ω) : Prop :=
  IsEntrance X A t ω ∧
  ∃ s < t, X s ω ∈ F ∧ ∀ u ∈ Set.Ioo s t, ¬ IsEntrance X A u ω

/-- `N` is the point process whose points are exactly the first entrances into `A` after a visit to
`F` — the process `N^{F(→A)}` of p.207. -/
def IsRareEventThinning {S : Type*} (X : ℝ → Ω → S) (A F : Set S) (N : PointProcess Ω) : Prop :=
  ∀ (t : ℝ) (ω : Ω), (∃ n : ℤ, N.T n ω = t) ↔ IsFirstEntranceAfter X A F t ω

end PalmQueueing.Formulas


