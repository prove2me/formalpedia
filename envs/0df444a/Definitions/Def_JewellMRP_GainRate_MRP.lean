-- Prove2me | Definitions.Def_JewellMRP_GainRate_MRP
-- name    : JewellMRP_GainRate_MRP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:24:14.362835+00:00
-- url     : https://prove2.me/theorems/269b4746-abd0-46f9-9c3e-d5bdd2967f60
-- title:
--   Finite Markov-renewal program, stationary policies, gain rate (B 7) and time-stationary probabilities (C 12)
-- statement:
--   A **Markov-renewal program** has finitely many states $i = 1, \dots, N$ and, in each state, a set $\mathcal A$ of alternatives $z$. Under alternative $z$ in state $i$ the system moves to state $j$ with probability $p^z_{ij}$ (so $p^z_{ij} \ge 0$ and $\sum_j p^z_{ij} = 1$). The transition $i \to j$ takes a random time $\tau(i,j) \ge 0$ with finite mean $\nu^z_{ij} = E[\tau(i,j)]$, and the transition out of $i$ earns an expected reward $\rho^z_i$. The **mean sojourn time** in state $i$ under $z$ is
--   $$\nu^z_i = \sum_{j=1}^{N} p^z_{ij}\,\nu^z_{ij},$$
--   and it is assumed nonzero, hence positive.
--
--   A **stationary policy** is a map $z$ assigning an alternative $z(i)$ to each state. Its transition matrix is $P^z_{ij} = p^{z(i)}_{ij}$, and we write $\rho_i = \rho^{z(i)}_i$, $\nu_i = \nu^{z(i)}_i$. The program is **ergodic** if $P^z$ is irreducible for every stationary policy $z$ (standing assumption 2; a finite irreducible chain is positive recurrent). A vector $\pi$ is a **stationary probability vector** of a matrix $P$ if $\pi_i \ge 0$, $\sum_i \pi_i = 1$ and $\pi P = \pi$.
--
--   For a policy $z$ with stationary probabilities $\pi$, the **gain rate** (B 7) is
--   $$g = \frac{\sum_{i=1}^{N} \pi_i \rho_i}{\sum_{k=1}^{N} \pi_k \nu_k},$$
--   and the **time-stationary probabilities** (C 12) are
--   $$P_i = \frac{\nu_i}{\sum_{k=1}^{N} \pi_k \nu_k}\,\pi_i, \qquad i = 1, \dots, N.$$
--
--   These objects are the model on which Jewell's policy-iteration algorithm for the infinite-time undiscounted Markov-renewal program operates.
--
--   **Formalization Note** States are `Fin N` (index $0, \dots, N-1$). The transition-time distributions $F^z_{ij}$ and reward functions $R^z_{ij}$ enter the infinite-time undiscounted model only through the means $\nu^z_{ij}$ and $\rho^z_i$ of (I 17), and every nonnegative $\nu^z_{ij}$ and real $\rho^z_i$ arises from some distributions and rewards, so the structure records only these means. The gain rate is defined by its closed form (B 7); its identification with $\lim_{t\to\infty} v_i(t)/t$ ((B 6), Appendix B) is not formalized. `gainRate` and `timeStationaryProb` take $\pi$ as an argument and are meant to be used with $\pi$ stationary for the policy's chain.
-- source:
--   Jewell, Markov-Renewal Programming. II: Infinite Return Models, Example, Oper. Res. 11 (1963), pp. 949-951 (introduction, assumptions 1-3), p. 954 Eq. (B 7), p. 955 (nu_i nonzero and finite), p. 969 Eq. (C 12)

import Mathlib

namespace JewellMRP.GainRate

open Matrix

/-- A finite Markov-renewal program (Jewell, MRP II, pp. 949–951), reduced to the data the
infinite-time undiscounted model depends on. States are `Fin N`, alternatives are `α`.
Under alternative `a` in state `i` the next state is `j` with probability `p i a j`, the
transition `i → j` has mean duration `νij i a j = E[τ(i,j)]` (finite, nonnegative), and the
expected reward earned during a transition out of `i` is `ρ i a` ((I 17)).
The mean sojourn time `ν i a = ∑ j, p i a j * νij i a j` is positive. -/
structure MRP (N : ℕ) (α : Type*) where
  /-- transition probabilities `p^z_{ij}` -/
  p : Fin N → α → Fin N → ℝ
  p_nonneg : ∀ i a j, 0 ≤ p i a j
  p_sum_one : ∀ i a, ∑ j, p i a j = 1
  /-- mean transition times `ν^z_{ij} = E[τ(i,j)]` -/
  νij : Fin N → α → Fin N → ℝ
  νij_nonneg : ∀ i a j, 0 ≤ νij i a j
  /-- expected one-transition rewards `ρ^z_i` -/
  ρ : Fin N → α → ℝ
  /-- the mean sojourn times `ν^z_i = ∑_j p^z_{ij} ν^z_{ij}` are nonzero (hence positive) -/
  ν_pos : ∀ i a, 0 < ∑ j, p i a j * νij i a j

variable {N : ℕ} {α : Type*}

/-- Mean sojourn time `ν^z_i = ∑_j p^z_{ij} ν^z_{ij}` (p. 954, below (B 7)). -/
def MRP.ν (M : MRP N α) (i : Fin N) (a : α) : ℝ := ∑ j, M.p i a j * M.νij i a j

/-- The transition matrix `P^z_{ij} = p^{z(i)}_{ij}` of the stationary policy `z`. -/
def MRP.policyMatrix (M : MRP N α) (z : Fin N → α) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => M.p i (z i) j

/-- Standing assumption 2 (p. 951): the underlying Markov chain is ergodic (irreducible;
positive recurrence is automatic for a finite chain) for every stationary policy. -/
def MRP.IsErgodic (M : MRP N α) : Prop :=
  ∀ z : Fin N → α, (M.policyMatrix z).IsIrreducible

/-- `π` is a stationary probability vector of the matrix `P`:
nonnegative, summing to one, and `π P = π`. -/
def IsStationaryDist (P : Matrix (Fin N) (Fin N) ℝ) (π : Fin N → ℝ) : Prop :=
  (∀ i, 0 ≤ π i) ∧ ∑ i, π i = 1 ∧ π ᵥ* P = π

/-- The gain rate (B 7) of the stationary policy `z`, computed from the stationary
probabilities `π` of its chain: `g = ∑_i π_i ρ_i / ∑_k π_k ν_k`. -/
noncomputable def MRP.gainRate (M : MRP N α) (z : Fin N → α) (π : Fin N → ℝ) : ℝ :=
  (∑ i, π i * M.ρ i (z i)) / (∑ k, π k * M.ν k (z k))

/-- The time-stationary probabilities (C 12) of the stationary policy `z`:
`P_i = (ν_i / ∑_k π_k ν_k) π_i`. -/
noncomputable def MRP.timeStationaryProb (M : MRP N α) (z : Fin N → α) (π : Fin N → ℝ)
    (i : Fin N) : ℝ :=
  M.ν i (z i) / (∑ k, π k * M.ν k (z k)) * π i

end JewellMRP.GainRate


