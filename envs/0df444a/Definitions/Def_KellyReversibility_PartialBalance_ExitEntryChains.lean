-- Prove2me | Definitions.Def_KellyReversibility_PartialBalance_ExitEntryChains
-- name    : KellyReversibility_PartialBalance_ExitEntryChains
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:43:17.220443+00:00
-- url     : https://prove2.me/theorems/02172b82-8d5e-4f5d-8d73-f4c534062af9
-- title:
--   The Markov chains observed just before leaving and just after entering a set $\mathcal A$
-- statement:
--   The two embedded Markov chains of Theorem 9.5 (vi), for a Markov process on a finite state space $\mathcal S$ with rates $q(j,k)$ and a set $\mathcal A\subseteq\mathcal S$.
--
--   Write $q(j)=\sum_{k}q(j,k)$ and let $P(j,k)=q(j,k)/q(j)$ be the **jump chain**. Let $P_{\mathcal A}$ (resp. $P_{\mathcal S-\mathcal A}$) be $P$ with every entry outside $\mathcal A\times\mathcal A$ (resp. $(\mathcal S-\mathcal A)^2$) set to zero, and define
--   $$G(i,j)=\sum_{n\ge0}P_{\mathcal A}^n(i,j),\qquad H(k,i)=\sum_{n\ge0}\bigl(P_{\mathcal S-\mathcal A}^nP\bigr)(k,i).$$
--   For $i,j\in\mathcal A$, $G(i,j)$ is the expected number of visits to $j$ before the jump chain started at $i$ leaves $\mathcal A$; for $k\notin\mathcal A$, $i\in\mathcal A$, $H(k,i)$ is the probability that the chain started at $k$ first enters $\mathcal A$ at $i$. With $q(j,\mathcal S-\mathcal A)=\sum_{k\notin\mathcal A}q(j,k)$:
--
--   1. The chain observed **just before the process leaves $\mathcal A$** has transition matrix on $\mathcal A$
--   $$M_{\mathrm{exit}}(j,j')=\sum_{k\notin\mathcal A}\frac{q(j,k)}{q(j,\mathcal S-\mathcal A)}\sum_{i\in\mathcal A}H(k,i)\,G(i,j')\,\frac{q(j',\mathcal S-\mathcal A)}{q(j')}.$$
--   2. The chain observed **just after the process enters $\mathcal A$** has transition matrix on $\mathcal A$
--   $$M_{\mathrm{entry}}(i,i')=\sum_{j'\in\mathcal A}G(i,j')\sum_{k\notin\mathcal A}P(j',k)\,H(k,i').$$
--   3. An **equilibrium distribution** of a discrete-time chain $M$ is a non-negative $\mu$ summing to one with $\sum_t\mu(t)M(t,t')=\mu(t')$; *the* equilibrium distribution is the unique one.
--
--   **Formalization Note** States of $\mathcal A$ from which no exit (resp. into which no entry) is possible get a zero row in $M_{\mathrm{exit}}$ (resp. a zero column in $M_{\mathrm{entry}}$ through $H$); they are never observed, and every equilibrium distribution gives them mass zero, so equilibrium distributions here are non-negative rather than positive. The infinite sums are unconditional sums; for an irreducible process and a proper nonempty $\mathcal A$ they converge.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 201, Theorem 9.5 (vi)

import Mathlib
import Definitions.Def_KellyReversibility_PartialBalance_Core

namespace KellyReversibility.PartialBalance

/-- The **jump chain** of the process with rates `q` on a finite state space: from `j` the
process next jumps to `k` with probability `q(j,k) / ∑_{k'} q(j,k')`. -/
noncomputable def jumpProb {S : Type*} [Fintype S] (q : S → S → ℝ) : Matrix S S ℝ :=
  fun j k => q j k / ∑ k' : S, q j k'

open Classical in
/-- The jump-chain matrix `P` with every entry outside `B × B` set to zero: the sub-stochastic
kernel of steps that start and end in `B`. -/
noncomputable def restrictMatrix {S : Type*} (P : Matrix S S ℝ) (B : Set S) : Matrix S S ℝ :=
  fun j k => if j ∈ B ∧ k ∈ B then P j k else 0

/-- `greenWithin q A i j = ∑_{n≥0} (P_A^n)(i,j)`, where `P_A` is the jump chain restricted to
`A`: for `i, j ∈ A` it is the expected number of visits of the jump chain started at `i` to the
state `j` before the chain first leaves `A`. -/
noncomputable def greenWithin {S : Type*} [Fintype S] [DecidableEq S] (q : S → S → ℝ)
    (A : Set S) : Matrix S S ℝ :=
  fun i j => ∑' n : ℕ, ((restrictMatrix (jumpProb q) A) ^ n) i j

/-- `entranceProb q A k i = ∑_{n≥0} (P_{S−A}^n P)(k,i)`: for `k ∈ S − A` and `i ∈ A` it is the
probability that the jump chain started at `k` first enters `A` at the state `i`. -/
noncomputable def entranceProb {S : Type*} [Fintype S] [DecidableEq S] (q : S → S → ℝ)
    (A : Set S) : Matrix S S ℝ :=
  fun k i => ∑' n : ℕ, ((restrictMatrix (jumpProb q) Aᶜ) ^ n * jumpProb q) k i

/-- The total rate `∑_{k∈S−A} q(j,k)` at which the process leaves `A` from the state `j`. -/
noncomputable def exitRate {S : Type*} (q : S → S → ℝ) (A : Set S) (j : S) : ℝ :=
  ∑' k : (Aᶜ : Set S), q j (k : S)

/-- The transition matrix of the Markov chain formed by observing the process at the instants
just before it leaves `A` (Theorem 9.5 (vi)). From the state `j ∈ A` the process jumps to
`k ∈ S − A` with probability `q(j,k) / ∑_{k'∈S−A} q(j,k')`, first re-enters `A` at `i`, and the
next state observed is the state `j'` from which it next leaves `A`. -/
noncomputable def exitChain {S : Type*} [Fintype S] [DecidableEq S] (q : S → S → ℝ)
    (A : Set S) : A → A → ℝ :=
  fun j j' =>
    ∑' k : (Aᶜ : Set S), (q (j : S) (k : S) / exitRate q A (j : S)) *
      ∑' i : A, entranceProb q A (k : S) (i : S) * greenWithin q A (i : S) (j' : S) *
        (exitRate q A (j' : S) / ∑ k' : S, q (j' : S) k')

/-- The transition matrix of the Markov chain formed by observing the process at the instants
just after it enters `A` (Theorem 9.5 (vi)). From the entry state `i ∈ A` the process leaves `A`
from some state `j'`, jumps to `k ∈ S − A`, and the next state observed is the state `i'` at
which it next enters `A`. -/
noncomputable def entryChain {S : Type*} [Fintype S] [DecidableEq S] (q : S → S → ℝ)
    (A : Set S) : A → A → ℝ :=
  fun i i' =>
    ∑' j' : A, greenWithin q A (i : S) (j' : S) *
      ∑' k : (Aᶜ : Set S), jumpProb q (j' : S) (k : S) * entranceProb q A (k : S) (i' : S)

/-- `μ` is an **equilibrium (stationary) distribution** of the discrete-time chain with
transition matrix `M`: non-negative, summing to unity, and `∑_t μ(t) M(t,t') = μ(t')`. -/
def IsStationaryDist {T : Type*} (M : T → T → ℝ) (μ : T → ℝ) : Prop :=
  (∀ t : T, 0 ≤ μ t) ∧ (∑' t : T, μ t) = 1 ∧ ∀ t' : T, ∑' t : T, μ t * M t t' = μ t'

/-- `μ` is **the** equilibrium distribution of the chain `M`: it is stationary and every
stationary distribution of `M` equals it. -/
def IsTheStationaryDist {T : Type*} (M : T → T → ℝ) (μ : T → ℝ) : Prop :=
  IsStationaryDist M μ ∧ ∀ ν : T → ℝ, IsStationaryDist M ν → ν = μ

end KellyReversibility.PartialBalance


