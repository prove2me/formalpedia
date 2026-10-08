-- Prove2me | Definitions.Def_KellyReversibility_Migration_BlockingRates
-- name    : KellyReversibility_Migration_BlockingRates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:22:38.997335+00:00
-- url     : https://prove2.me/theorems/7ac6af1a-f8eb-44db-9b9d-777430ef6034
-- title:
--   Reversible migration processes: blocking rates (6.2), (6.5), (6.6), product form (6.3), condition (6.4)
-- statement:
--   The model of Chapter 6 of Kelly, *Reversibility and Stochastic Networks*: migration processes in which the rate of moving into a colony may depend on the number already there, which permits blocking.
--
--   There are $J$ colonies. The state is $n = (n_1,\dots,n_J)$, $n_j \in \mathbb{N}$ being the number of individuals in colony $j$. The operators $T_{jk}$, $T_{j\cdot}$ and $T_{\cdot k}$ move one individual from colony $j$ to colony $k$, remove one individual from colony $j$, and add one individual to colony $k$ (these operators are taken from the published definition `KellyStochasticNetworks_Migration`). The model is specified by non-negative parameters $\lambda_{jk}$, $\mu_j$, $\nu_k$ and functions $\varphi_j, \psi_j : \mathbb{N} \to \mathbb{R}$.
--
--   1. **Closed process, rates (6.2).** The only transitions are transfers, at rate
--   $$q(n, T_{jk}n) = \lambda_{jk}\,\varphi_j(n_j)\,\psi_k(n_k).$$
--   2. **Open process, rates (6.2), (6.5), (6.6).** In addition, individuals leave from colony $j$ and enter colony $k$ at rates
--   $$q(n, T_{j\cdot}n) = \mu_j\,\varphi_j(n_j), \qquad q(n, T_{\cdot k}n) = \nu_k\,\psi_k(n_k).$$
--   3. **Product form (6.3).** For constants $\alpha_1,\dots,\alpha_J$, the unnormalized weight
--   $$w(n) = \prod_{j=1}^{J}\Bigl\{\alpha_j^{n_j}\prod_{r=1}^{n_j}\frac{\psi_j(r-1)}{\varphi_j(r)}\Bigr\},$$
--   with the inner product equal to $1$ when $n_j = 0$.
--   4. **Condition (6.4).** $\alpha_j\lambda_{jk} = \alpha_k\lambda_{kj}$ for all $j, k$.
--   5. **Irreducibility requirements (pp. 135–136).** For the closed process, the $\lambda_{jk}$ allow an individual to pass between any two colonies, directly or via a chain of colonies along pairs with $\lambda_{ab} > 0$. For the open process, an individual can reach every colony from outside (enter at a colony $j$ with $\nu_j > 0$ and then follow such a chain) and can leave the system from every colony (follow a chain to a colony $k$ with $\mu_k > 0$).
--
--   These objects are the shared vocabulary of Theorems 6.1 and 6.2. With $\psi_j \equiv 1$ the rates reduce to those of the migration processes of Chapter 2.
--
--   **Formalization Note** Colonies are indexed by `Fin J` and states are functions `Fin J → ℕ`. Each rate function is a single real-valued function of two states, assembled as a sum of indicator terms over the possible transitions, exactly as in `KellyStochasticNetworks_Migration`. A transfer or departure from an empty colony would leave the state space; such terms carry the factor $\varphi_j(0)$, which the theorems assume to be $0$, so they vanish rather than being read through truncated subtraction. The book's $\lambda_{jj} = 0$ and the positivity of $\varphi_j(n)$ ($n>0$) and $\psi_j(n)$ ($n \ge 0$) are hypotheses of the theorems, not built into these definitions.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, pp. 135–136, Eqs. (6.2)–(6.6)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Migration

namespace KellyReversibility.Migration

open KellyStochasticNetworks

/-- The transition rates (6.2) of a **closed reversible migration process** (Kelly, *Reversibility
and Stochastic Networks*, p. 135): the only transitions are `n ↦ T_{jk} n`, one individual moving
from colony `j` to colony `k`, at rate `λ_{jk} φ_j(n_j) ψ_k(n_k)`.  The rate is assembled as a sum
of indicator terms over the possible transitions; a transfer out of an empty colony carries the
factor `φ_j(0)`, which is `0` wherever these rates are used. -/
noncomputable def closedBlockingRates {J : ℕ} (lam : Fin J → Fin J → ℝ) (φ ψ : Fin J → ℕ → ℝ) :
    (Fin J → ℕ) → (Fin J → ℕ) → ℝ := fun n m =>
  ∑ j, ∑ k, if m = Tjk j k n then lam j k * φ j (n j) * ψ k (n k) else 0

/-- The transition rates of an **open reversible migration process** (p. 136): the transfers (6.2)
at rate `λ_{jk} φ_j(n_j) ψ_k(n_k)`, departures (6.5) `n ↦ T_{j·} n` from colony `j` at rate
`μ_j φ_j(n_j)`, and arrivals (6.6) `n ↦ T_{·k} n` into colony `k` at rate `ν_k ψ_k(n_k)`. -/
noncomputable def openBlockingRates {J : ℕ} (lam : Fin J → Fin J → ℝ) (mu nu : Fin J → ℝ)
    (φ ψ : Fin J → ℕ → ℝ) : (Fin J → ℕ) → (Fin J → ℕ) → ℝ := fun n m =>
  closedBlockingRates lam φ ψ n m
    + (∑ j, if m = Tout j n then mu j * φ j (n j) else 0)
    + (∑ k, if m = Tin k n then nu k * ψ k (n k) else 0)

/-- The colony factor `∏_{r=1}^{m} ψ_j(r-1)/φ_j(r)` of (6.3); it equals `1` when `m = 0`. -/
noncomputable def psiPhiProd {J : ℕ} (ψ φ : Fin J → ℕ → ℝ) (j : Fin J) (m : ℕ) : ℝ :=
  ∏ r ∈ Finset.Icc 1 m, ψ j (r - 1) / φ j r

/-- The unnormalized product form (6.3):
`∏_{j=1}^{J} α_j^{n_j} ∏_{r=1}^{n_j} ψ_j(r-1)/φ_j(r)`.  The equilibrium distribution of
Theorems 6.1 and 6.2 is `B` times this, for a normalizing constant `B`. -/
noncomputable def blockingWeight {J : ℕ} (α : Fin J → ℝ) (ψ φ : Fin J → ℕ → ℝ)
    (n : Fin J → ℕ) : ℝ :=
  ∏ j, α j ^ n j * psiPhiProd ψ φ j (n j)

/-- Condition (6.4): `α_j λ_{jk} = α_k λ_{kj}` for all colonies `j, k`. -/
def BlockingBalance {J : ℕ} (lam : Fin J → Fin J → ℝ) (α : Fin J → ℝ) : Prop :=
  ∀ j k, α j * lam j k = α k * lam k j

/-- The closed process's irreducibility requirement (p. 135): the parameters `λ_{jk}` allow an
individual to pass between any two colonies, directly or via a chain of other colonies, i.e.
every colony is reachable from every other along steps `a → b` with `λ_{ab} > 0`. -/
def ClosedConnected {J : ℕ} (lam : Fin J → Fin J → ℝ) : Prop :=
  ∀ j k, Relation.ReflTransGen (fun a b => 0 < lam a b) j k

/-- The open process's irreducibility requirement (p. 136): an individual can reach any colony
from outside the system (enter at some colony `j` with `ν_j > 0`, then move along steps with
`λ_{ab} > 0`) and can leave the system from any colony (move to some colony `k` with `μ_k > 0`). -/
def OpenConnected {J : ℕ} (lam : Fin J → Fin J → ℝ) (mu nu : Fin J → ℝ) : Prop :=
  (∀ k, ∃ j, 0 < nu j ∧ Relation.ReflTransGen (fun a b => 0 < lam a b) j k) ∧
  (∀ j, ∃ k, Relation.ReflTransGen (fun a b => 0 < lam a b) j k ∧ 0 < mu k)

end KellyReversibility.Migration


