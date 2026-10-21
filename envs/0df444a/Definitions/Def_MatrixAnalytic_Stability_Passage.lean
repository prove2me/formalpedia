-- Prove2me | Definitions.Def_MatrixAnalytic_Stability_Passage
-- name    : MatrixAnalytic_Stability_Passage
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:43:40.695754+00:00
-- url     : https://prove2.me/theorems/af078ea8-52dc-47ef-9855-32afa9908797
-- title:
--   First passage to a lower level — G[k], G, G′(1) (7.2), the restricted chain P^{0} = B + A₀G, the matrix M (7.3)–(7.4), the vector m, and the rate matrix R
-- statement:
--   Let $P$ be a Markov chain on the level–phase states $(n, i)$, and let $\delta_n = \inf\{t \ge 0 : X_t \in \ell(n)\}$ be the first passage time to level $n$. All quantities below are probabilities or expectations computed from the one-step probabilities of $P$ (sums over finite trajectories of products of transition probabilities), with values in $[0, \infty]$.
--
--   1. $G_{ij}[k] = \mathrm P[\delta_n = k,\ X_{\delta_n} = (n, j) \mid X_0 = (n+1, i)]$: the total weight of the trajectories $(n+1, i) = \omega_0, \omega_1, \dots, \omega_k = (n, j)$ with $\omega_0, \dots, \omega_{k-1} \notin \ell(n)$.
--   2. $G = G(1)$, $G_{ij} = \sum_{k \ge 0} G_{ij}[k]$: the probability, starting from $(n+1, i)$, of reaching level $n$ in finite time, and doing so first in $(n, j)$.
--   3. $G'(1)$, by (7.2): $(G'(1))_{ij} = \mathrm E[\delta_n\, \mathcal I\{X_{\delta_n} = (n,j)\} \mid X_0 = (n+1, i)] = \sum_{k \ge 0} k\, G_{ij}[k]$.
--   4. $G$ is **stochastic** if $G\mathbf 1 = \mathbf 1$, and **substochastic** if $G\mathbf 1 \le \mathbf 1$ with at least one strict inequality (p. 148).
--   5. The **restricted chain** on $\ell(0)$ has transition matrix $P^{\{0\}} = B + A_0 G$, with $G$ taken from $\ell(1)$ to $\ell(0)$.
--   6. $M_{ij}$ is the expected number of visits to $(0, j)$, starting from $(0, i)$, before the first return to $(0, i)$ (p. 149); the initial visit counts, so $M_{ii} = 1$ as in (7.4).
--   7. The vector $\boldsymbol m = M(\mathbf 1 + A_0 G'(1)\mathbf 1)$, i.e. $m_i = \sum_j M_{ij}\big(1 + \sum_k (A_0)_{jk} \sum_l (G'(1))_{kl}\big)$.
--   8. The **rate matrix** $R$: $R_{ij}$ is the expected number of visits to $(1, j)$, starting from $(0, i)$, before the first return to $\ell(0)$ (Theorem 6.2.1 at level $0$).
--
--   For a homogeneous QBD these quantities do not depend on $n$; the theorems use $n = 0$, i.e. passage from $\ell(1)$ to $\ell(0)$.
--
--   **Formalization Note** Expected numbers of visits are $\sum_{t \ge 0} \mathrm P[X_t = y,\ X_1, \dots, X_t \notin T \mid X_0 = x]$, each probability a trajectory sum; everything is in `ℝ≥0∞`, so an infinite expectation is $\infty$ and "finite" is the statement $\ne \infty$. None of $G$, $G'(1)$, $M$, $R$ is defined through an equation of the chapter ((7.1), (7.3), $R = A_0N$, or a minimal-solution property). In $P^{\{0\}}$ the entries of $G$ are read as real numbers; they are probabilities, hence finite. Since $M$ and $\boldsymbol m$ are in $[0,\infty]$, a product $0 \cdot \infty$ counts as $0$, the measure-theoretic convention for an expectation over an event of probability $0$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 147–149, Eqs. (7.2)–(7.4); p. 131, Theorem 6.2.1 (R)

import Mathlib
import Definitions.Def_MatrixAnalytic_Stability_QBD

namespace MatrixAnalytic.Stability

noncomputable section

open scoped ENNReal

/-!
The first-passage quantities of §7.1 of Latouche & Ramaswami (pp. 147–149) and the rate matrix
`R` of §6.2, for a Markov chain with transition matrix `P` on the level–phase states `ℕ × ι`.
Every probability is a sum, over finite trajectories, of products of one-step transition
probabilities, and every expectation is a sum of such probabilities; all take values in `ℝ≥0∞`.
None of them is defined through an equation of the chapter.
-/

variable {ι : Type*} [Countable ι] [DecidableEq ι]

/-- The weight `P_{ω₀ω₁} ⋯ P_{ω_{t-1}ω_t}` of a trajectory of length `t`, in `ℝ≥0∞`: the
probability, starting from `ω₀`, that `X₁ = ω₁, …, X_t = ω_t`. -/
def pathWeightE (P : ℕ × ι → ℕ × ι → ℝ) {t : ℕ} (ω : Fin (t + 1) → ℕ × ι) : ℝ≥0∞ :=
  ∏ s : Fin t, ENNReal.ofReal (P (ω s.castSucc) (ω s.succ))

open Classical in
/-- `G_{ij}[k] = P[δ_n = k, X_{δ_n} = (n, j) | X₀ = (n + 1, i)]` (p. 148), where
`δ_n = inf{t ≥ 0 : X_t ∈ ℓ(n)}` is the first passage time to the level `n`: the sum of the weights
of the trajectories `(n + 1, i) = ω₀, ω₁, …, ω_k = (n, j)` with `ω₀, …, ω_{k−1} ∉ ℓ(n)`. -/
def passageProb (P : ℕ × ι → ℕ × ι → ℝ) (n k : ℕ) (i j : ι) : ℝ≥0∞ :=
  ∑' ω : Fin (k + 1) → ℕ × ι,
    if ω 0 = (n + 1, i) ∧ ω (Fin.last k) = (n, j) ∧
        ∀ s : Fin (k + 1), s ≠ Fin.last k → ω s ∉ level n
    then pathWeightE P ω else 0

/-- The first-passage matrix `G = G(1)`, `G_{ij} = Σ_{k ≥ 0} G_{ij}[k]` (p. 148): the probability,
starting from `(n + 1, i)`, of reaching the level `n` in a finite time and doing so first in
`(n, j)`. -/
def matG (P : ℕ × ι → ℕ × ι → ℝ) (n : ℕ) : ι → ι → ℝ≥0∞ :=
  fun i j => ∑' k : ℕ, passageProb P n k i j

/-- `G′(1)`, (7.2) on p. 148: `(G′(1))_{ij} = E[δ_n 𝟙{X_{δ_n} = (n, j)} | X₀ = (n + 1, i)]
= Σ_{k ≥ 0} k G_{ij}[k]`, an element of `[0, ∞]`. -/
def matGderiv (P : ℕ × ι → ℕ × ι → ℝ) (n : ℕ) : ι → ι → ℝ≥0∞ :=
  fun i j => ∑' k : ℕ, (k : ℝ≥0∞) * passageProb P n k i j

/-- `G` is **stochastic**: `G1 = 1`. -/
def IsStochasticE (G : ι → ι → ℝ≥0∞) : Prop :=
  ∀ i : ι, ∑' j : ι, G i j = 1

/-- `G` is **substochastic** in the sense of p. 148: `G1 ≤ 1` with at least one strict
inequality. -/
def IsSubstochasticE (G : ι → ι → ℝ≥0∞) : Prop :=
  (∀ i : ι, ∑' j : ι, G i j ≤ 1) ∧ ∃ i : ι, ∑' j : ι, G i j < 1

/-- The transition matrix `P^{0} = B + A₀G` of the restricted Markov chain on `ℓ(0)` (p. 148),
with `G` the first-passage matrix (its entries are probabilities, read in `ℝ`). -/
def restrictedP (B A₀ : ι → ι → ℝ) (G : ι → ι → ℝ≥0∞) : ι → ι → ℝ :=
  fun i j => B i j + ∑' k : ι, A₀ i k * (G k j).toReal

open Classical in
/-- The expected number of visits to the state `y`, starting from `X₀ = x`, before the first
visit to the set `T` (after time `0`): `Σ_{t ≥ 0} P[X_t = y, X_1 ∉ T, …, X_t ∉ T | X_0 = x]`.
The visit at time `0` counts when `y = x`. -/
def expVisitsAvoid (P : ℕ × ι → ℕ × ι → ℝ) (T : Set (ℕ × ι)) (x y : ℕ × ι) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' ω : Fin (t + 1) → ℕ × ι,
    if ω 0 = x ∧ ω (Fin.last t) = y ∧ ∀ s : Fin (t + 1), s ≠ 0 → ω s ∉ T
    then pathWeightE P ω else 0

/-- The matrix `M` of p. 149: `M_{ij}` is the expected number of visits to the state `(0, j)`,
starting from `(0, i)`, before the first return to `(0, i)`. The initial visit is counted, so
`M_{ii} = 1`, which is (7.4). -/
def matM (P : ℕ × ι → ℕ × ι → ℝ) : ι → ι → ℝ≥0∞ :=
  fun i j => expVisitsAvoid P {((0 : ℕ), i)} (0, i) (0, j)

/-- The vector `m = M(1 + A₀G′(1)1)` of Theorem 7.1.1 (p. 149), with `G = G(1)` and `G′(1)` the
first-passage quantities from `ℓ(1)` to `ℓ(0)`:
`m_i = Σ_j M_{ij} (1 + Σ_k (A₀)_{jk} Σ_l (G′(1))_{kl})`, in `[0, ∞]`. -/
def vecm (P : ℕ × ι → ℕ × ι → ℝ) (A₀ : ι → ι → ℝ) : ι → ℝ≥0∞ :=
  fun i => ∑' j : ι, matM P i j *
    (1 + ∑' k : ι, ennMat A₀ j k * ∑' l : ι, matGderiv P 0 k l)

/-- The rate matrix `R` of §6.2 (Theorem 6.2.1, p. 131, at `n = 0`): `R_{ij}` is the expected
number of visits to `(1, j)`, starting from `(0, i)`, before the first return to `ℓ(0)`. -/
def matR (P : ℕ × ι → ℕ × ι → ℝ) : ι → ι → ℝ≥0∞ :=
  fun i j => expVisitsAvoid P (level 0) (0, i) (1, j)

end

end MatrixAnalytic.Stability


