-- Prove2me | Definitions.Def_KellyReversibility_Reversibility_MarkovChain
-- name    : KellyReversibility_Reversibility_MarkovChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:21:09.641791+00:00
-- url     : https://prove2.me/theorems/11fa92f7-a7ff-475b-b3d7-39ab4ae65f1b
-- title:
--   The stationary Markov chain on a finite state space and its reversibility
-- statement:
--   Let $\mathcal S$ be a finite state space and $P=(p(j,k))_{j,k\in\mathcal S}$ the transition matrix of a time-homogeneous discrete-time Markov chain $X(t)$, $t\in\mathbb Z$.
--
--   1. The $k$-step transition matrix is $P^k$, $k\ge 0$.
--   2. An **equilibrium distribution** of the chain (Kelly, p. 2) is a collection of positive numbers $\pi(j)$, $j\in\mathcal S$, summing to unity that satisfy the equilibrium equations
--   $$\pi(j)=\sum_{k\in\mathcal S}\pi(k)p(k,j),\qquad j\in\mathcal S. \tag{1.1}$$
--   3. The stationary chain with transition matrix $P$ and equilibrium distribution $\pi$ is **reversible** when its finite-dimensional distributions
--   $$P\bigl(X(t_1)=j_1,\dots,X(t_n)=j_n\bigr)=\pi(j_1)\,P^{t_2-t_1}(j_1,j_2)\cdots P^{t_n-t_{n-1}}(j_{n-1},j_n),\qquad t_1\le\dots\le t_n,$$
--   are invariant under $t_r\mapsto\tau-t_r$, as in the definition of reversibility on p. 5.
--
--   These are the objects of Theorems 1.2 and 1.7.
--
--   **Formalization Note** Stochastic matrices, the stationarity equation $\pi P=\pi$ (with $\pi\ge 0$, $\sum\pi=1$) and irreducibility are taken from the published definition file `mm_basic`; positivity of $\pi$ is added, as Kelly's definition requires. Integer lags are converted to natural-number exponents by `Int.toNat`; only the non-negative lags of sorted times are ever used. The state space is finite, a restriction of Kelly's countable state space.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, pp. 1–2, Eq. (1.1); p. 5, Definition (reversible)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_KellyReversibility_Reversibility_StationaryLaw

namespace KellyReversibility.Reversibility

/-- The `k`-step transition matrix `P ^ k` of a discrete-time Markov chain, indexed by an
integer time lag (only lags `k ≥ 0` are used by `fdd`). -/
noncomputable def chainTransition {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) : ℤ → Matrix S S ℝ :=
  fun k => P ^ k.toNat

/-- `π` is an **equilibrium distribution** of the chain with transition matrix `P`
(Kelly, p. 2): positive numbers summing to one that satisfy the equilibrium equations (1.1),
`π(j) = ∑_k π(k) p(k, j)`. -/
def IsChainEquilibrium {S : Type*} [Fintype S] [DecidableEq S] (P : Matrix S S ℝ)
    (π : S → ℝ) : Prop :=
  (∀ j, 0 < π j) ∧ MarkovMixing.IsStationary P π

/-- The stationary Markov chain with transition matrix `P` and equilibrium distribution `π`,
indexed by `ℤ`, is **reversible** (Kelly, p. 5). -/
def ChainReversible {S : Type*} [Fintype S] [DecidableEq S] (P : Matrix S S ℝ)
    (π : S → ℝ) : Prop :=
  IsReversibleLaw (chainTransition P) π

end KellyReversibility.Reversibility


