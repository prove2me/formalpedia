-- Prove2me | Definitions.Def_mm_mcmc
-- name    : mm_mcmc
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-21T15:14:05.925346+00:00
-- url     : https://prove2.me/theorems/f425e3e9-b5ee-4711-a91c-61843fd444a4
-- title:
--   The Metropolis chains and the Glauber dynamics
-- statement:
--   This file constructs the two universal Markov chain Monte Carlo samplers of Chapter 3 of Levin–Peres–Wilmer: the Metropolis chain and the Glauber dynamics. Throughout, $V$ is a finite state space, $\Psi$ a proposal (base) transition matrix on $V$, and $\pi$ a target mass function on $V$.
--
--   **The Metropolis chain for a symmetric base chain.** From the current state $x$, propose a $\Psi$-move to $y$ and accept it with probability $\min\bigl(1,\pi(y)/\pi(x)\bigr)$; a rejected proposal stays at $x$. Concretely, off the diagonal
--   $$M(x,y)=\Psi(x,y)\,\min\!\Bigl(1,\frac{\pi(y)}{\pi(x)}\Bigr)\qquad(y\ne x),$$
--   and the diagonal entry collects all the rejected mass: $M(x,x)=1-\sum_{z\ne x}\Psi(x,z)\min\bigl(1,\pi(z)/\pi(x)\bigr)$.
--
--   **The Metropolis–Hastings chain.** For a base chain that need not be symmetric, the acceptance ratio weighs the two directions of the proposal: a move from $x$ to $y\ne x$ is accepted with probability
--   $$\min\!\Bigl(1,\frac{\pi(y)\,\Psi(y,x)}{\pi(x)\,\Psi(x,y)}\Bigr),$$
--   with the diagonal again absorbing the rejected mass. For symmetric $\Psi$ this reduces to the Metropolis rule above.
--
--   **Glauber dynamics (single-site heat bath).** Here the states are configurations $x:\mathcal V\to S$ assigning a spin from a finite set $S$ to each site of a finite set $\mathcal V$, and $\pi$ is a mass function on configurations. One step: pick a site $v$ uniformly at random and re-sample the spin at $v$ from $\pi$ conditioned to agree with $x$ off $v$. The transition matrix is
--   $$G(x,y)=\frac{1}{|\mathcal V|}\sum_{v\in\mathcal V}\mathbf 1\{y\equiv x\text{ off }v\}\;\frac{\pi(y)}{\sum_{z\,\equiv\,x\text{ off }v}\pi(z)},$$
--   where the normalizing sum runs over the configurations agreeing with $x$ at every site other than $v$. In particular $G(x,y)=0$ when $y$ differs from $x$ at two or more sites, and when $y=x$ all $|\mathcal V|$ sites contribute.
--
--   **Conventions.** Division is total with $r/0=0$, so all three matrices are defined for arbitrary real inputs; that they are genuinely stochastic with stationary distribution $\pi$ is proved in the accompanying theorems under their natural hypotheses (stochastic base chain, positive target).
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Ch. 3, Sections 3.2-3.3, pp. 37-44

import Definitions.Def_mm_basic

/-!
Markov chain Monte Carlo: the Metropolis and Glauber chains, following
Levin–Peres–Wilmer, *Markov Chains and Mixing Times*, Chapter 3.

Given a target distribution `π`, these constructions produce transition
matrices having `π` as a stationary distribution.
-/

namespace MarkovMixing

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **Metropolis chain** for a target distribution `π` and a symmetric
base chain `Ψ`: a move proposed by `Ψ` from `x` to `y ≠ x` is accepted with
probability `1 ∧ π(y)/π(x)` (LPW §3.2.1). -/
def metropolis (Ψ : Matrix V V ℝ) (π : V → ℝ) : Matrix V V ℝ :=
  fun x y =>
    if y = x then 1 - ∑ z ∈ ({x}ᶜ : Finset V), Ψ x z * min 1 (π z / π x)
    else Ψ x y * min 1 (π y / π x)

/-- The **Metropolized chain** for a target distribution `π` and a general
(not necessarily symmetric) base chain `Ψ`: a move proposed by `Ψ` from `x`
to `y ≠ x` is accepted with probability
`(π(y)Ψ(y,x)) / (π(x)Ψ(x,y)) ∧ 1` (LPW §3.2.2, Eq. (3.5)). -/
def metropolized (Ψ : Matrix V V ℝ) (π : V → ℝ) : Matrix V V ℝ :=
  fun x y =>
    if y = x then
      1 - ∑ z ∈ ({x}ᶜ : Finset V), Ψ x z * min 1 (π z * Ψ z x / (π x * Ψ x z))
    else Ψ x y * min 1 (π y * Ψ y x / (π x * Ψ x y))

/-- The (single-site) **Glauber dynamics** for a distribution `π` on a space
of configurations `Vv → S`: pick a vertex `v` uniformly at random, then
re-sample the value at `v` from `π` conditioned on agreeing with the current
configuration off `v` (LPW §3.3.2, Eq. (3.6)).  Rows at configurations
outside the support of `π` are junk. -/
def glauber {Vv S : Type*} [Fintype Vv] [DecidableEq Vv] [Fintype S] [DecidableEq S]
    (π : (Vv → S) → ℝ) : Matrix (Vv → S) (Vv → S) ℝ :=
  fun x y =>
    (Fintype.card Vv : ℝ)⁻¹ *
      ∑ v : Vv,
        if ∀ w : Vv, w ≠ v → y w = x w then
          π y / ∑ z ∈ Finset.univ.filter (fun z : Vv → S => ∀ w : Vv, w ≠ v → z w = x w), π z
        else 0

end

end MarkovMixing


