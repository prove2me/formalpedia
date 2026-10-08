-- Prove2me | Definitions.Def_KellyReversibility_Clustering_ClusteringRates
-- name    : KellyReversibility_Clustering_ClusteringRates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:09:23.634649+00:00
-- url     : https://prove2.me/theorems/112a0f53-24fd-4dfa-b36e-8a348dd6a5a8
-- title:
--   Clustering processes: the rates (8.3) and (8.7), and the product forms (8.5) and (8.10)
-- statement:
--   The model of §8.2 of Kelly, *Reversibility and Stochastic Networks*, together with the special case of §8.1.
--
--   **States.** There is a countable collection of cluster types $r$. A state is a vector $m = (m_r)$ of non-negative integers, $m_r$ being the number of $r$-clusters present, with only finitely many $m_r$ non-zero.
--
--   **Operators.** For cluster types $r, s, u$ write
--   $$R^{rs}_u m = m - e_r - e_s + e_u, \qquad R^u_{rs} m = m + e_r + e_s - e_u,$$
--   where $e_r$ is the $r$-th unit vector: $R^{rs}_u$ is the union of an $r$-cluster and an $s$-cluster into a $u$-cluster (when $r = s$, two $r$-clusters unite), and $R^u_{rs}$ is the break-up of a $u$-cluster into an $r$-cluster and an $s$-cluster.
--
--   **Rates (8.3).** Given parameters $\lambda_{rsu}$ and $\mu_{rsu}$, the clustering process jumps
--   $$q(m, R^{rs}_u m) = \lambda_{rsu} m_r m_s \ (r \neq s), \qquad q(m, R^{rr}_u m) = \lambda_{rru} m_r (m_r - 1), \qquad q(m, R^u_{rs} m) = \mu_{rsu} m_u .$$
--   A union is possible only when the uniting clusters are present ($m_r, m_s \ge 1$, or $m_r \ge 2$ when $r = s$), and a break-up only when $m_u \ge 1$. The rate $q(m, m')$ from $m$ to $m' \neq m$ is the sum of the rates of all unions and break-ups that carry $m$ to $m'$, each unordered pair $\{r, s\}$ being counted once. No transition returns to its starting state, so $q(m, m) = 0$.
--
--   **Open process (8.7).** One-clusters may also enter, at rate $\nu$, and leave, at rate $\mu m_1$:
--   $$q(m, m + e_1) = \nu, \qquad q(m, m - e_1) = \mu m_1 \quad (m_1 \ge 1).$$
--
--   **Closed process.** A closed clustering process lives on a finite, non-empty set $\mathcal S$ of states that is closed under the transitions of positive rate and irreducible: every state of $\mathcal S$ can be reached from every other by a chain of transitions of positive rate.
--
--   **Product forms.** For positive numbers $c_r$ write $\Phi(m) = \prod_r c_r^{m_r}/m_r!$ (a finite product, the factors with $m_r = 0$ being $1$). The closed process's candidate distribution (8.5) is
--   $$\pi(m) = B \prod_r \frac{c_r^{m_r}}{m_r!}, \qquad B = \Bigl(\sum_{m' \in \mathcal S} \prod_r \frac{c_r^{m'_r}}{m'_r!}\Bigr)^{-1}, \qquad m \in \mathcal S,$$
--   and the open process's candidate distribution (8.10) is the infinite product
--   $$\pi(m) = \prod_{r} e^{-c_r} \frac{c_r^{m_r}}{m_r!}.$$
--
--   **The social grouping model of §8.1.** Cluster types are the group sizes $i = 1, 2, \dots$. An isolate joins a given group of size $i$ at rate $\alpha$, and a given individual leaves a group of size $i \ge 2$ at rate $\beta$. In terms of (8.3) this is $\lambda_{1,i,i+1} = \lambda_{i,1,i+1} = \alpha$ and $\mu_{1,i,i+1} = \mu_{i,1,i+1} = (i+1)\beta$, all other parameters being zero; so the rate from $m$ to $(m_1 - 1, \dots, m_i - 1, m_{i+1} + 1, \dots)$ is $\alpha m_1 m_i$ for $i \ge 2$, to $(m_1 - 2, m_2 + 1, \dots)$ is $\alpha m_1 (m_1 - 1)$, to $(m_1 + 1, \dots, m_{i-1} + 1, m_i - 1, \dots)$ is $i \beta m_i$ for $i > 2$, and to $(m_1 + 2, m_2 - 1, \dots)$ is $2 \beta m_2$. The number of individuals in state $m$ is $\sum_i i\, m_i$.
--
--   These objects carry every result of the chapter's basic model: Theorems 8.1 and 8.2 and the §8.1 equilibrium (8.2) are statements about them.
--
--   **Formalization Note** Cluster types form an arbitrary type `R` with a linear order; the order is used only to count each unordered pair $\{r, s\}$ once, as $r \le s$, and since $\lambda$, $\mu$ are symmetric it does not affect the rates. States are finitely supported functions `R →₀ ℕ`. The rate is a finite sum over the supports of $m$ and $m'$, which contain every union and break-up of positive rate from $m$ to $m'$; the target of an operator is written with truncated subtraction, but only on states where the subtracted clusters are present. The one-cluster type is a distinguished element `one` of `R`. For §8.1 the types are `ℕ+`. The infinite product (8.10) is Lean's unconditional product `∏'`.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, pp. 161–164, §8.1 (rates before Eq. (8.2)), §8.2 Eqs. (8.3), (8.5), (8.7), (8.10) and the definition of the closed clustering process (p. 163)

import Mathlib

namespace KellyReversibility.Clustering

/-! # The basic clustering model (Kelly, *Reversibility and Stochastic Networks*, §8.2)

Cluster types form a countable type `R`.  A state `m : R →₀ ℕ` records the number `m r` of
`r`-clusters; only finitely many clusters are present.  The type `R` carries a linear order,
used only to count each unordered pair of cluster types `{r, s}` exactly once (as `r ≤ s`). -/

variable {R : Type*} [LinearOrder R]

/-- The operator `R^{rs}_u`: an `r`-cluster and an `s`-cluster unite to form a `u`-cluster
(`m_r, m_s` each drop by one, or `m_r` drops by two when `r = s`, and `m_u` rises by one).
It is only used on states where the clusters that unite are present. -/
noncomputable def joinOp (r s u : R) (m : R →₀ ℕ) : R →₀ ℕ :=
  m - Finsupp.single r 1 - Finsupp.single s 1 + Finsupp.single u 1

/-- The operator `R^u_{rs}`: a `u`-cluster breaks up into an `r`-cluster and an `s`-cluster.
It is only used on states with `m_u ≥ 1`. -/
noncomputable def breakOp (r s u : R) (m : R →₀ ℕ) : R →₀ ℕ :=
  m + Finsupp.single r 1 + Finsupp.single s 1 - Finsupp.single u 1

/-- The rate (8.3) of the union `R^{rs}_u` from state `m`:
`λ_{rsu} m_r m_s` when `r ≠ s` and `λ_{rru} m_r (m_r - 1)` when `r = s`
(computed in `ℝ`, so `m_r - 1` is not truncated). -/
noncomputable def joinRate (lam : R → R → R → ℝ) (r s u : R) (m : R →₀ ℕ) : ℝ :=
  if r = s then lam r r u * (m r : ℝ) * ((m r : ℝ) - 1)
  else lam r s u * (m r : ℝ) * (m s : ℝ)

/-- **The transition rates (8.3) of the clustering process.**  `clusterRates lam mu m m'` is the
total rate of jumping from `m` to `m'`: the sum of the rates of all unions `R^{rs}_u`
(`r ≤ s`, the clusters present, rate `joinRate`) and all break-ups `R^u_{rs}` (`r ≤ s`,
`m_u ≥ 1`, rate `μ_{rsu} m_u`) that carry `m` to `m'`.  The index sets are the supports of `m`
and `m'`, which contain every union or break-up of positive rate leading from `m` to `m'`, so
the sums are finite. -/
noncomputable def clusterRates (lam mu : R → R → R → ℝ) (m m' : R →₀ ℕ) : ℝ :=
  (∑ r ∈ m.support, ∑ s ∈ m.support, ∑ u ∈ m'.support,
      if r ≤ s ∧ (r = s → 2 ≤ m r) ∧ m' = joinOp r s u m then joinRate lam r s u m else 0)
  + ∑ u ∈ m.support, ∑ r ∈ m'.support, ∑ s ∈ m'.support,
      if r ≤ s ∧ m' = breakOp r s u m then mu r s u * (m u : ℝ) else 0

/-- **The transition rates of the open clustering process**: the rates (8.3) together with the
rates (8.7), `q(m, R_{·1} m) = ν` (a one-cluster enters) and `q(m, R_{1·} m) = μ m_1`
(a one-cluster leaves, only when `m_1 ≥ 1`).  The cluster type `one` plays the role of the
one-clusters (type `1` in the book). -/
noncomputable def openClusterRates (lam mu : R → R → R → ℝ) (one : R) (ν μ : ℝ)
    (m m' : R →₀ ℕ) : ℝ :=
  clusterRates lam mu m m'
  + (if m' = m + Finsupp.single one 1 then ν else 0)
  + (if 1 ≤ m one ∧ m' = m - Finsupp.single one 1 then μ * (m one : ℝ) else 0)

/-- **The state space of a closed clustering process** (p. 163): a finite set `S` of states
that is nonempty, closed under the transitions of positive rate, and irreducible (every state
of `S` can be reached from every other through transitions of positive rate). -/
def IsClosedClusteringStateSpace (q : (R →₀ ℕ) → (R →₀ ℕ) → ℝ) (S : Finset (R →₀ ℕ)) : Prop :=
  S.Nonempty ∧ (∀ m ∈ S, ∀ m', 0 < q m m' → m' ∈ S) ∧
    (∀ m ∈ S, ∀ m' ∈ S, Relation.ReflTransGen (fun a b => 0 < q a b) m m')

/-- The unnormalized product form `∏_r c_r^{m_r} / m_r!`; the factors with `m_r = 0` equal `1`,
so the product runs over the support of `m`. -/
noncomputable def productWeight (c : R → ℝ) (m : R →₀ ℕ) : ℝ :=
  ∏ r ∈ m.support, c r ^ m r / ((m r).factorial : ℝ)

/-- The distribution (8.5) of the closed clustering process on its finite state space `S`:
`π(m) = B ∏_r c_r^{m_r}/m_r!`, with normalizing constant
`B = (∑_{m ∈ S} ∏_r c_r^{m_r}/m_r!)⁻¹`. -/
noncomputable def closedClusterPi (c : R → ℝ) (S : Finset (R →₀ ℕ)) (m : S) : ℝ :=
  (∑ m' ∈ S, productWeight c m')⁻¹ * productWeight c m

/-- The distribution (8.10) of the open clustering process:
`π(m) = ∏_{r} e^{-c_r} c_r^{m_r} / m_r!`, an infinite product over all cluster types. -/
noncomputable def openClusterPi (c : R → ℝ) (m : R →₀ ℕ) : ℝ :=
  ∏' r, Real.exp (-c r) * c r ^ m r / ((m r).factorial : ℝ)

/-! ## The social grouping model of §8.1

Groups of individuals; an `i`-cluster is a group of `i` individuals, so cluster types are the
positive integers `ℕ+`. -/

/-- Union parameters of the §8.1 model: an isolate (a `1`-cluster) joins a group of size `i` to
form a group of size `i + 1`, at rate `α` per (isolate, group) pair; every other union has
parameter `0`.  Symmetric in its first two arguments. -/
noncomputable def socialLam (α : ℝ) (r s u : ℕ+) : ℝ :=
  if (r = 1 ∧ (u : ℕ) = s + 1) ∨ (s = 1 ∧ (u : ℕ) = r + 1) then α else 0

/-- Break-up parameters of the §8.1 model: each of the `u` individuals of a group of size `u ≥ 2`
leaves it at rate `β`, so the group splits into an isolate and a group of size `u - 1` at rate
`u β` per group; every other break-up has parameter `0`.  Symmetric in its first two arguments. -/
noncomputable def socialMu (β : ℝ) (r s u : ℕ+) : ℝ :=
  if (r = 1 ∧ (u : ℕ) = s + 1) ∨ (s = 1 ∧ (u : ℕ) = r + 1) then (u : ℝ) * β else 0

/-- **The transition rates of the §8.1 social grouping model** (p. 161): from
`(m_1, …, m_i, m_{i+1}, …)` to `(m_1 - 1, …, m_i - 1, m_{i+1} + 1, …)` at rate `α m_1 m_i`
(`i ≥ 2`); to `(m_1 - 2, m_2 + 1, …)` at rate `α m_1 (m_1 - 1)`; from
`(m_1, …, m_{i-1}, m_i, …)` to `(m_1 + 1, …, m_{i-1} + 1, m_i - 1, …)` at rate `i β m_i`
(`i > 2`); and to `(m_1 + 2, m_2 - 1, …)` at rate `2 β m_2`.  These are the rates (8.3) with the
parameters `socialLam α`, `socialMu β`. -/
noncomputable def socialRates (α β : ℝ) (m m' : ℕ+ →₀ ℕ) : ℝ :=
  clusterRates (socialLam α) (socialMu β) m m'

/-- The number of individuals `∑_i i m_i` in state `m` (the left side of (8.1)). -/
def unitCount (m : ℕ+ →₀ ℕ) : ℕ :=
  ∑ i ∈ m.support, (i : ℕ) * m i

end KellyReversibility.Clustering


