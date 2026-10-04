-- Prove2me | Definitions.Def_Aumann1987_TwoPerson_Model
-- name    : Aumann1987_TwoPerson_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T05:04:26.959984+00:00
-- url     : https://prove2.me/theorems/2a713222-0b9c-40bf-b004-372a7ffbbedb
-- title:
--   Section 2 — two-person correlated equilibria (Definition 2.1), distributions and c.e.d.'s
-- statement:
--   This file fixes the objects of Section 2 of Aumann (1987) for a two-person game in strategic form, the setting of Proposition 2.3.
--
--   Player 1 has a finite set $S^1$ of actions and player 2 a finite set $S^2$; for $j\in S^1$ and $k\in S^2$ write $h^1_{jk}=h^1(j,k)$ and $h^2_{jk}=h^2(j,k)$ for the payoffs of the two players at the action pair $(j,k)$.
--
--   1. **Distribution** (p. 5). A distribution is a family $(p_{jk})_{j\in S^1,\,k\in S^2}$ of real numbers with $p_{jk}\ge 0$ for all $j,k$ and $\sum_j\sum_k p_{jk}=1$.
--   2. **Correlated strategy pair** (p. 3). A finite probability space $(\Gamma,\mu)$ is a finite set $\Gamma$ with weights $\mu(\gamma)\ge0$ summing to $1$. A correlated strategy pair is a pair of functions $f^1:\Gamma\to S^1$, $f^2:\Gamma\to S^2$: chance draws $\gamma$ and suggests the action $f^i(\gamma)$ to player $i$.
--   3. **Correlated equilibrium** (Definition 2.1, condition (2.2), p. 4). The pair $f=(f^1,f^2)$ is a correlated equilibrium if no player gains by any deviation that depends only on his own suggestion: for every $\varphi:S^1\to S^1$ and every $\psi:S^2\to S^2$,
--   $$\mathbb E\,h^1\big(\varphi(f^1),f^2\big)\le \mathbb E\,h^1(f^1,f^2),\qquad \mathbb E\,h^2\big(f^1,\psi(f^2)\big)\le \mathbb E\,h^2(f^1,f^2),$$
--   the expectations being taken with respect to $\mu$.
--   4. **Distribution of a correlated strategy pair** (p. 4). It assigns to $(j,k)$ the probability $\mu\{\gamma: f^1(\gamma)=j,\ f^2(\gamma)=k\}$.
--   5. **Correlated equilibrium distribution (c.e.d.)** (p. 4). A family $p$ is a c.e.d. if it is the distribution of some correlated equilibrium on some finite probability space.
--   6. **Equilibrium conditions written on a distribution** (p. 4). For a family $p$, player 1's condition is $\sum_j\sum_k p_{jk}\,h^1_{\varphi(j)k}\le\sum_j\sum_k p_{jk}\,h^1_{jk}$ for every $\varphi:S^1\to S^1$; player 2's is $\sum_j\sum_k p_{jk}\,h^2_{j\psi(k)}\le\sum_j\sum_k p_{jk}\,h^2_{jk}$ for every $\psi:S^2\to S^2$.
--   7. **Conditional payoffs** (proof of Proposition 2.3, p. 6). For a suggestion $j$ to player 1 and an action $q\in S^1$,
--   $$H^1(q\mid j)=\frac{\sum_k h^1_{qk}\,p_{jk}}{\sum_k p_{jk}},$$
--   and for a suggestion $k$ to player 2 and $r\in S^2$, $H^2(r\mid k)=\sum_j h^2_{jr}\,p_{jk}\big/\sum_j p_{jk}$. These are player $i$'s expected payoffs from playing $q$ (resp. $r$) given the suggestion; the paper uses them only for *possible* suggestions, those of positive probability.
--
--   Proposition 2.3 characterizes the c.e.d.'s of a two-person game by finitely many linear inequalities in $p$.
--
--   **Formalization Note** Definition 2.1 is stated in the paper for $n$ players; this is its case $n=2$. The deviations "$g^i$ that is a function of $f^i$" are encoded as compositions $\varphi\circ f^i$ with $\varphi:S^i\to S^i$, the paper's own gloss. The probability spaces in "c.e.d." range over finite types in the lowest universe; every finite probability space is isomorphic to one on $\{0,\dots,N-1\}$, so nothing is lost. The predicate `IsCE` does not itself require $\mu$ to be a probability vector; `IsCED` and the theorems require it separately. In $H^1(q\mid j)$ and $H^2(r\mid k)$ a zero denominator gives the value $0$ by Lean's convention $x/0=0$; every statement that uses them assumes the suggestion is possible.
-- source:
--   Aumann, Correlated Equilibrium as an Expression of Bayesian Rationality, Econometrica 55 (1987), DOI 10.2307/1911154, pp. 3-6 (PDF pp. 4-7), Sect. 2: Definition 2.1 and condition (2.2) (p. 4), distribution and c.e.d. (p. 4), distributions (p. 5), H^1(q|j) (Proposition 2.3, proof, p. 6)

import Mathlib

/-!
# Aumann (1987), Section 2: two-person correlated equilibria and their distributions

Aumann, *Correlated Equilibrium as an Expression of Bayesian Rationality*, Econometrica 55 (1987),
DOI 10.2307/1911154, Section 2, pp. 3–6 (PDF pp. 4–7): correlated strategy pairs, Definition 2.1
(correlated equilibrium) at `n = 2`, distributions, correlated equilibrium distributions, and the
conditional payoffs `H¹(q|j)`, `H²(r|k)` of the proof of Proposition 2.3.

This is a definition bundle: every `def` below is one object of Section 2.
-/

open Finset

namespace Aumann1987.TwoPerson

variable {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]

/-- **Distribution** (Aumann 1987, Sect. 2, p. 5, PDF p. 6): an `lm`-tuple `(p_{jk})`, `j ∈ S¹`,
`k ∈ S²`, with `p_{jk} ≥ 0` for all `j, k` and `∑_j ∑_k p_{jk} = 1`.

Formalization Note: `p j k` is `p_{jk}`. -/
def IsDistribution (p : S₁ → S₂ → ℝ) : Prop :=
  (∀ j k, 0 ≤ p j k) ∧ ∑ j, ∑ k, p j k = 1

/-- A **finite probability space** `Γ` (Aumann 1987, Sect. 2, p. 3, PDF p. 4, with footnote 5):
the probability of the point `γ` is `μ γ`; the weights are nonnegative and sum to `1`.

Formalization Note: a finite probability space is encoded as a finite type with a probability
vector on its points; every event's probability is the sum of the weights of its points. -/
def IsProbVec {Γ : Type*} [Fintype Γ] (μ : Γ → ℝ) : Prop :=
  (∀ γ, 0 ≤ μ γ) ∧ ∑ γ, μ γ = 1

/-- **Correlated equilibrium** (Aumann 1987, Definition 2.1, condition (2.2), p. 4, PDF p. 5),
for two players. The correlated strategy pair is `f = (f₁, f₂) : Γ → S¹ × S²` on the finite
probability space `(Γ, μ)`; `h₁ j k`, `h₂ j k` are the payoffs `h¹(j,k)`, `h²(j,k)`. Condition
(2.2) `E hⁱ(f) ≥ E hⁱ(f⁻ⁱ, gⁱ)` is required for each player `i` and each `gⁱ` that is a function
of `fⁱ`, i.e. (as the paper glosses it) a composition `gⁱ = φ ∘ fⁱ` with `φ : Sⁱ → Sⁱ`.

Formalization Note: Definition 2.1 is stated for `n` players; this is its case `n = 2`, the case
of Proposition 2.3. Deviations range over all `φ : Sⁱ → Sⁱ`; values of `φ` off the range of `fⁱ`
do not matter. That `μ` is a probability vector is not part of this predicate; it is required
separately (`IsProbVec μ`) wherever a correlated strategy pair is meant. -/
def IsCE (h₁ h₂ : S₁ → S₂ → ℝ) {Γ : Type*} [Fintype Γ] (μ : Γ → ℝ)
    (f₁ : Γ → S₁) (f₂ : Γ → S₂) : Prop :=
  (∀ φ : S₁ → S₁, ∑ γ, μ γ * h₁ (φ (f₁ γ)) (f₂ γ) ≤ ∑ γ, μ γ * h₁ (f₁ γ) (f₂ γ)) ∧
  (∀ ψ : S₂ → S₂, ∑ γ, μ γ * h₂ (f₁ γ) (ψ (f₂ γ)) ≤ ∑ γ, μ γ * h₂ (f₁ γ) (f₂ γ))

/-- The **distribution** of a correlated strategy pair `(f₁, f₂)` on `(Γ, μ)` (Aumann 1987,
Sect. 2, p. 4, PDF p. 5): the function assigning to each action pair `(j, k)` the number
`Prob {f⁻¹(j, k)} = ∑_{γ : f₁ γ = j, f₂ γ = k} μ γ`. -/
def distr [DecidableEq S₁] [DecidableEq S₂] {Γ : Type*} [Fintype Γ] (μ : Γ → ℝ)
    (f₁ : Γ → S₁) (f₂ : Γ → S₂) : S₁ → S₂ → ℝ :=
  fun j k => ∑ γ ∈ univ.filter (fun γ => f₁ γ = j ∧ f₂ γ = k), μ γ

/-- **Correlated equilibrium distribution** (c.e.d.) (Aumann 1987, Sect. 2, p. 4, PDF p. 5): `p`
is the distribution of some correlated equilibrium, i.e. there are a finite probability space
`(Γ, μ)` and a correlated strategy pair `(f₁, f₂)` on it that is a correlated equilibrium
(Definition 2.1) and whose distribution is `p`.

Formalization Note: the probability space ranges over `Γ : Type` with a `Fintype` instance; every
finite probability space is equivalent to one on `Fin N`, so no generality is lost. -/
def IsCED [DecidableEq S₁] [DecidableEq S₂] (h₁ h₂ : S₁ → S₂ → ℝ) (p : S₁ → S₂ → ℝ) : Prop :=
  ∃ (Γ : Type) (_ : Fintype Γ) (μ : Γ → ℝ) (f₁ : Γ → S₁) (f₂ : Γ → S₂),
    IsProbVec μ ∧ IsCE h₁ h₂ μ f₁ f₂ ∧ distr μ f₁ f₂ = p

/-- Player 1's equilibrium condition (2.2) **written on the distribution** `p` (Aumann 1987,
Sect. 2, p. 4, PDF p. 5: "correlated strategy n-tuples can for most practical purposes be
identified with their distributions"): no recoding `φ : S¹ → S¹` of player 1's suggestion raises
player 1's expected payoff, `∑_j ∑_k p_{jk} h¹(φ(j), k) ≤ ∑_j ∑_k p_{jk} h¹(j, k)`. -/
def DevCond₁ (h₁ : S₁ → S₂ → ℝ) (p : S₁ → S₂ → ℝ) : Prop :=
  ∀ φ : S₁ → S₁, ∑ j, ∑ k, p j k * h₁ (φ j) k ≤ ∑ j, ∑ k, p j k * h₁ j k

/-- Player 2's equilibrium condition (2.2) written on the distribution `p` (Aumann 1987,
Sect. 2, p. 4, PDF p. 5): for every `ψ : S² → S²`,
`∑_j ∑_k p_{jk} h²(j, ψ(k)) ≤ ∑_j ∑_k p_{jk} h²(j, k)`. -/
def DevCond₂ (h₂ : S₁ → S₂ → ℝ) (p : S₁ → S₂ → ℝ) : Prop :=
  ∀ ψ : S₂ → S₂, ∑ j, ∑ k, p j k * h₂ j (ψ k) ≤ ∑ j, ∑ k, p j k * h₂ j k

/-- Player 1's **conditional expected payoff** `H¹(q|j)` (Aumann 1987, Proposition 2.3, proof,
p. 6, PDF p. 7): given the suggestion `j`, playing `q` yields `∑_k h¹_{qk} p_{jk} / ∑_k p_{jk}`.

Formalization Note: the paper uses `H¹(q|j)` only for a *possible* suggestion `j`, i.e.
`∑_k p_{jk} > 0`; at an impossible `j` Lean's convention `x / 0 = 0` makes the value `0`, and
every statement using it assumes `0 < ∑_k p_{jk}`. -/
noncomputable def condPayoff₁ (h₁ : S₁ → S₂ → ℝ) (p : S₁ → S₂ → ℝ) (q j : S₁) : ℝ :=
  (∑ k, h₁ q k * p j k) / ∑ k, p j k

/-- Player 2's conditional expected payoff `H²(r|k)` (Aumann 1987, Proposition 2.3, proof, p. 6,
PDF p. 7, "Similarly … for i = 2"): given the suggestion `k`, playing `r` yields
`∑_j h²_{jr} p_{jk} / ∑_j p_{jk}`.

Formalization Note: meaningful only for a possible `k` (`∑_j p_{jk} > 0`); the value at an
impossible `k` is `0` by `x / 0 = 0` and is never used. -/
noncomputable def condPayoff₂ (h₂ : S₁ → S₂ → ℝ) (p : S₁ → S₂ → ℝ) (r k : S₂) : ℝ :=
  (∑ j, h₂ j r * p j k) / ∑ j, p j k

end Aumann1987.TwoPerson


