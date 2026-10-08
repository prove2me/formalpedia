-- Prove2me | Definitions.Def_KellyReversibility_PartialBalance_Core
-- name    : KellyReversibility_PartialBalance_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:27:27.49213+00:00
-- url     : https://prove2.me/theorems/b49bfd37-ae31-40ad-8c18-6f251d3630a5
-- title:
--   Equilibrium distributions, partial balance, and the altered processes of Theorem 9.5
-- statement:
--   The objects of Kelly's Theorem 9.5 for a Markov process on a state space $\mathcal S$ with transition rates $q(j,k)$.
--
--   1. **Transition rates.** $q(j,k)\ge 0$ for $j\ne k$, and $q(j,j)=0$ (the convention of §1.1, p. 3).
--   2. **Irreducibility.** Every state $k$ can be reached from every state $j$ by a finite chain $j=j_0,j_1,\dots,j_n=k$ with $q(j_{i-1},j_i)>0$.
--   3. **Equilibrium distribution.** A collection of *positive* numbers $\pi(j)$, $j\in\mathcal S$, summing to unity and satisfying the equilibrium equations
--   $$\pi(j)\sum_{k\in\mathcal S}q(j,k)=\sum_{k\in\mathcal S}\pi(k)q(k,j),\qquad j\in\mathcal S.$$
--   *The* equilibrium distribution of a process is an equilibrium distribution that is the only one.
--   4. **Partial balance** with respect to a set $\mathcal A\subseteq\mathcal S$:
--   $$\pi(j)\sum_{k\in\mathcal A}q(j,k)=\sum_{k\in\mathcal A}\pi(k)q(k,j),\qquad j\in\mathcal A.$$
--   5. **Conditional distribution** on $\mathcal A$: $\pi(j)/\sum_{k\in\mathcal A}\pi(k)$, $j\in\mathcal A$.
--   6. **Rates altered inside $\mathcal A$**: $q(j,k)$ is replaced by $c\,q(j,k)$ for $j,k\in\mathcal A$, all other rates unchanged.
--   7. **Rates altered on exits from $\mathcal A$**: $q(j,k)$ is replaced by $c\,q(j,k)$ for $j\in\mathcal A$, $k\in\mathcal S-\mathcal A$, all other rates unchanged.
--   8. **The distribution of Lemma 1.9**: $B\pi(j)$ for $j\in\mathcal A$ and $Bc\pi(j)$ for $j\in\mathcal S-\mathcal A$, where
--   $$B^{-1}=\sum_{j\in\mathcal A}\pi(j)+c\sum_{j\in\mathcal S-\mathcal A}\pi(j).$$
--
--   The truncation of the process to $\mathcal A$ and the rates $\pi(k)q(k,j)/\pi(j)$ of the time-reversed process are the published definitions `truncatedRates` and `reversedRates`; the equilibrium equations are the published `FullBalance`.
--
--   **Formalization Note** Sums over the state space are unconditional sums (`tsum`), as in the published `FullBalance`; every theorem of this mission takes a finite state space, where they are ordinary finite sums. The truncated process lives on the subtype $\mathcal A$, so transitions leaving $\mathcal A$ are absent rather than zeroed.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 3 (§1.1, equilibrium distribution, (1.3)), p. 25 (Lemma 1.9, truncation), pp. 200–201 (Theorem 9.5 (i)–(iv))

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_LossNetwork

namespace KellyReversibility.PartialBalance

open KellyStochasticNetworks

/-- **Transition rates** (Kelly 1979, §1.1, p. 3): `q j k ≥ 0` is the rate of a jump from `j`
to `k ≠ j`, and the book's convention `q(j, j) = 0` is built in. -/
def IsRateMatrix {S : Type*} (q : S → S → ℝ) : Prop :=
  (∀ j k : S, j ≠ k → 0 ≤ q j k) ∧ ∀ j : S, q j j = 0

/-- **Irreducibility** (§1.1): every state can be reached from every other state by a finite
chain of transitions of positive rate. -/
def IsIrreducible {S : Type*} (q : S → S → ℝ) : Prop :=
  ∀ j k : S, Relation.ReflTransGen (fun a b : S => 0 < q a b) j k

/-- **Equilibrium distribution** (§1.1, p. 3): a collection of positive numbers `π j`, summing
to unity, which satisfies the equilibrium equations (1.3) for the rates `q`. -/
def IsEquilibriumDist {S : Type*} (q : S → S → ℝ) (π : S → ℝ) : Prop :=
  (∀ j : S, 0 < π j) ∧ (∑' j : S, π j) = 1 ∧ FullBalance π q

/-- `π` is **the** equilibrium distribution of the process with rates `q`: it is an equilibrium
distribution, and every equilibrium distribution of `q` equals it. -/
def IsTheEquilibriumDist {S : Type*} (q : S → S → ℝ) (π : S → ℝ) : Prop :=
  IsEquilibriumDist q π ∧ ∀ p : S → ℝ, IsEquilibriumDist q p → p = π

/-- **Partial balance** with respect to a set `A` (§9.4, Theorem 9.5 (i), p. 200):
`π(j) ∑_{k∈A} q(j,k) = ∑_{k∈A} π(k) q(k,j)` for every `j ∈ A`. -/
def IsPartialBalance {S : Type*} (π : S → ℝ) (q : S → S → ℝ) (A : Set S) : Prop :=
  ∀ j : S, j ∈ A → π j * (∑' k : A, q j (k : S)) = ∑' k : A, π (k : S) * q (k : S) j

/-- The **conditional probability distribution** of `π` on `A`:
`π(j) / ∑_{k∈A} π(k)` for `j ∈ A` (Theorem 9.5 (ii)). -/
noncomputable def condDist {S : Type*} (π : S → ℝ) (A : Set S) : A → ℝ :=
  fun j => π (j : S) / ∑' k : A, π (k : S)

open Classical in
/-- The process **altered inside `A`** (Theorem 9.5 (iii)): the rate `q(j,k)` is changed to
`c q(j,k)` for `j, k ∈ A`; every other rate is unchanged. -/
noncomputable def scaleWithin {S : Type*} (q : S → S → ℝ) (A : Set S) (c : ℝ) : S → S → ℝ :=
  fun j k => if j ∈ A ∧ k ∈ A then c * q j k else q j k

open Classical in
/-- The process **altered on exits from `A`** (Theorem 9.5 (iv); Lemma 1.9): the rate `q(j,k)`
is changed to `c q(j,k)` for `j ∈ A`, `k ∈ S − A`; every other rate is unchanged. -/
noncomputable def scaleExit {S : Type*} (q : S → S → ℝ) (A : Set S) (c : ℝ) : S → S → ℝ :=
  fun j k => if j ∈ A ∧ k ∉ A then c * q j k else q j k

open Classical in
/-- The distribution of Theorem 9.5 (iv): `B π(j)` for `j ∈ A` and `B c π(j)` for `j ∈ S − A`,
with normalizing constant `B⁻¹ = ∑_{j∈A} π(j) + c ∑_{j∈S−A} π(j)` (Lemma 1.9, p. 25). -/
noncomputable def exitScaledDist {S : Type*} (π : S → ℝ) (A : Set S) (c : ℝ) : S → ℝ :=
  fun j =>
    (∑' k : A, π (k : S) + c * ∑' k : (Aᶜ : Set S), π (k : S))⁻¹ *
      (if j ∈ A then π j else c * π j)

end KellyReversibility.PartialBalance


