-- Prove2me | Definitions.Def_Aumann1987_BayesRational_CorrelatedEquilibrium
-- name    : Aumann1987_BayesRational_CorrelatedEquilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T04:39:39.710554+00:00
-- url     : https://prove2.me/theorems/e1030c86-aa97-44fd-9017-0bd82884c834
-- title:
--   Definition 2.1 — correlated strategy n-tuples, correlated equilibrium, distributions and c.e.d.
-- statement:
--   Let $G$ be an $n$-person game in strategic form: each player $i$ has a set $S^i$ of actions, an action $n$-tuple is $s=(s^1,\dots,s^n)\in S=S^1\times\dots\times S^n$, and $h^i(s)\in\mathbb R$ is the payoff to player $i$.
--
--   A **correlated strategy $n$-tuple** is a function $f:\Gamma\to S$ on a finite probability space $(\Gamma,q)$, where $q(\gamma)\ge 0$ and $\sum_{\gamma}q(\gamma)=1$. Write $f^i(\gamma)$ for player $i$'s coordinate of $f(\gamma)$ and
--   $$
--   E h^i(f)=\sum_{\gamma\in\Gamma} q(\gamma)\,h^i(f(\gamma)).
--   $$
--   For a function $g^i:\Gamma\to S^i$, the deviation $(f^{-i},g^i)$ replaces player $i$'s coordinate of $f(\gamma)$ by $g^i(\gamma)$ and leaves the others unchanged.
--
--   1. $f$ is a **correlated equilibrium** (c.e.) if, for every player $i$ and every $g^i$ that is a function of $f^i$, i.e. $g^i=\varphi\circ f^i$ for some $\varphi:S^i\to S^i$,
--   $$
--   E h^i(f)\ \ge\ E h^i(f^{-i},g^i). \qquad (2.2)
--   $$
--   2. The **distribution** of $f$ is the function on $S$ assigning to each $n$-tuple $s$ the number $\operatorname{Prob}\{f^{-1}(s)\}=\sum_{\gamma:\,f(\gamma)=s}q(\gamma)$.
--   3. A function $Q$ on $S$ is a **correlated equilibrium distribution** (c.e.d.) if $Q$ is the distribution of some correlated equilibrium on some finite probability space.
--
--   Deviations are restricted to functions of $f^i$ because player $i$ is informed of $f^i(\gamma)$ only. These notions are the conclusion side of Aumann's Main Theorem.
--
--   **Formalization Note.** The probability vector is `AGT.IsLottery` from the published definition `agt_games`. The probability space $\Gamma$ in the c.e.d. existential ranges over `Type` (universe 0), which loses nothing for finite sets. No finiteness is imposed on the action sets; the distribution uses classical decidability of equality of action profiles.
-- source:
--   Aumann, Correlated Equilibrium as an Expression of Bayesian Rationality, Econometrica 55 (1987), DOI 10.2307/1911154, pp. 3-4 (PDF pp. 4-5), Sect. 2, Definition 2.1 (condition (2.2)), distribution and c.e.d.

import Mathlib
import Definitions.Def_agt_games

/-!
# Aumann (1987), Sect. 2: correlated strategy n-tuples and correlated equilibrium

R. J. Aumann, *Correlated Equilibrium as an Expression of Bayesian Rationality*, Econometrica 55
(1987), no. 1, 1–18, Sect. 2, pp. 3–4 (PDF pp. 4–5), Definition 2.1.

A game `G` in strategic form is given by a type `ι` of players, the action sets `S i` (the paper's
`Sⁱ`) and the payoff functions `h : ι → (∀ i, S i) → ℝ` (the paper's `h = (h¹, …, hⁿ)`, with
`hⁱ(s)` the payoff to `i` at the action `n`-tuple `s`). A *correlated strategy `n`-tuple* is a
function `f : Γ → S` on a finite probability space `(Γ, q)`, where `q : Γ → ℝ` is a probability
vector (`AGT.IsLottery q`).

This bundle defines the expected payoff `Ehⁱ(f)`, the deviation `(f⁻ⁱ, gⁱ)`, correlated equilibrium
(Definition 2.1, condition (2.2)), the distribution of a correlated strategy `n`-tuple, and
correlated equilibrium distributions (c.e.d.).

**Formalization Note.** The game is not bundled. No finiteness is imposed on the action sets `S i`
in this file (nothing here needs it); finiteness of the players `ι` is a hypothesis of the theorems
that use these definitions. Probability spaces are finite types with a real weight vector; no
measure theory is used, since everything in the paper is finite (footnote 5).
-/

namespace Aumann1987.BayesRational

open Finset

variable {ι : Type*} {S : ι → Type*}

/-- **Expected payoff** `Ehⁱ(f)` (Aumann 1987, Sect. 2, p. 4, PDF p. 5: "`E` denotes
'expectation'. If `f` is a correlated strategy `n`-tuple, note that `hⁱ(f)` is a real-valued
random variable"): for a correlated strategy `n`-tuple `f : Γ → S` on the finite probability space
`(Γ, q)`,
`Ehⁱ(f) = ∑_{γ ∈ Γ} q(γ) hⁱ(f(γ))`. -/
def expPayoff {Γ : Type*} [Fintype Γ] (h : ι → (∀ i, S i) → ℝ) (q : Γ → ℝ)
    (f : Γ → ∀ i, S i) (i : ι) : ℝ :=
  ∑ γ, q γ * h i (f γ)

/-- **Unilateral deviation** `(f⁻ⁱ, gⁱ) := (f¹, …, fⁱ⁻¹, gⁱ, fⁱ⁺¹, …, fⁿ)` (Aumann 1987, Sect. 2,
p. 4, PDF p. 5): at each `γ`, player `i`'s action `fⁱ(γ)` is replaced by `gⁱ(γ)` and every other
player's action is unchanged. -/
def deviate [DecidableEq ι] {Γ : Type*} (f : Γ → ∀ i, S i) (i : ι) (g : Γ → S i) :
    Γ → ∀ j, S j :=
  fun γ => Function.update (f γ) i (g γ)

/-- **Correlated equilibrium** (Aumann 1987, Sect. 2, Definition 2.1, condition (2.2), p. 4,
PDF p. 5): a correlated strategy `n`-tuple `f` on the finite probability space `(Γ, q)` is a
correlated equilibrium (c.e.) of the game with payoffs `h` if
`Ehⁱ(f) ≥ Ehⁱ(f⁻ⁱ, gⁱ)`
for each player `i` and each `gⁱ` that is a function of `fⁱ`.

**Formalization Note.** "`gⁱ` is a function of `fⁱ`" is encoded as the paper glosses it right after
the definition: `gⁱ` is the composition `φ ∘ fⁱ` of some function `φ : Sⁱ → Sⁱ` with `fⁱ`
(`fⁱ(γ) = f γ i`). Deviations range neither over all maps `Γ → Sⁱ` nor only over constant maps.
The requirement that `q` be a probability vector is not part of this predicate; it is imposed
wherever a correlated strategy `n`-tuple is quantified over (see `IsCED`). -/
def IsCorrelatedEquilibrium [DecidableEq ι] {Γ : Type*} [Fintype Γ] (h : ι → (∀ i, S i) → ℝ)
    (q : Γ → ℝ) (f : Γ → ∀ i, S i) : Prop :=
  ∀ (i : ι) (φ : S i → S i),
    expPayoff h q (deviate f i (fun γ => φ (f γ i))) i ≤ expPayoff h q f i

/-- **Distribution of a correlated strategy `n`-tuple** (Aumann 1987, Sect. 2, p. 4, PDF p. 5):
"the function that assigns to each `n`-tuple `s` of actions the number `Prob {f⁻¹(s)}`", i.e.
`s ↦ ∑_{γ : f(γ) = s} q(γ)`.

**Formalization Note.** The filter uses classical decidability of equality of action profiles. -/
noncomputable def distr {Γ : Type*} [Fintype Γ] (q : Γ → ℝ) (f : Γ → ∀ i, S i) :
    (∀ i, S i) → ℝ :=
  open Classical in
  fun s => ∑ γ ∈ univ.filter (fun γ => f γ = s), q γ

/-- **Correlated equilibrium distribution** (c.e.d.; Aumann 1987, Sect. 2, p. 4, PDF p. 5: a
distribution that "represent[s] a correlated equilibrium"): a function `Q` on action `n`-tuples is a
c.e.d. of the game with payoffs `h` if there are a finite probability space `(Γ, q)` (Γ finite,
footnote 5; `q ≥ 0`, `∑ q = 1`) and a correlated equilibrium `f : Γ → S` on it whose distribution
is `Q`.

**Formalization Note.** `Γ` ranges over `Type` (universe 0). Since `Γ` is finite this loses
nothing: every finite type is in bijection with some `Fin n`, and the three conditions are invariant
under relabelling `Γ`. The probability vector condition is `AGT.IsLottery` from the published
definition `agt_games`. The equality `distr q f = Q` is an equality of functions on all action
`n`-tuples, not only on a support. -/
def IsCED [DecidableEq ι] (h : ι → (∀ i, S i) → ℝ) (Q : (∀ i, S i) → ℝ) : Prop :=
  ∃ (Γ : Type) (_ : Fintype Γ) (q : Γ → ℝ) (f : Γ → ∀ i, S i),
    AGT.IsLottery q ∧ IsCorrelatedEquilibrium h q f ∧ distr q f = Q

end Aumann1987.BayesRational


