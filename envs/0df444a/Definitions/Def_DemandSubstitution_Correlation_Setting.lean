-- Prove2me | Definitions.Def_DemandSubstitution_Correlation_Setting
-- name    : DemandSubstitution_Correlation_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:55.02908+00:00
-- url     : https://prove2.me/theorems/3333aa90-a113-4fed-850e-75369f52c1af
-- title:
--   §2, §2.1, (1), (9), pp. 2–3, 7–8 — substitution model, D^s_i, per-realization profits, N(m, S) demand, expected profits, optimal Q, raising one covariance
-- statement:
--   This file fixes the objects of the $n$-product inventory model with demand substitution of Netessine and Rudi, specialised to multivariate normal demand.
--
--   **Data.** There are $n$ products. Product $i$ is bought at unit cost $c_i$, sold at unit price $r_i$ and salvaged at unit value $s_i$, with
--   $$r_i > c_i > s_i > 0 .$$
--   The substitution fraction $a_{ij}\in[0,1]$ is the fraction of the unmet demand for product $i$ that switches to product $j$; $a_{ii}=0$ and $\sum_{j=1}^n a_{ij} < 1$ for every $i$. The unit underage and overage costs are $u_i = r_i - c_i$ and $o_i = c_i - s_i$.
--
--   **Effective demand.** For a demand realization $D=(D_1,\dots,D_n)$ and stocking quantities $Q=(Q_1,\dots,Q_n)$, the demand faced by product $i$ after substitution is
--   $$D^s_i = D_i + \sum_{j\ne i} a_{ji}\,(D_j - Q_j)^+ ,$$
--   with $x^+=\max(0,x)$.
--
--   **Profits for one realization.** The profit of product $i$ (equivalently, of firm $i$ in the competitive model) is
--   $$\pi_i(D) = u_i D^s_i - u_i (D^s_i - Q_i)^+ - o_i (Q_i - D^s_i)^+ ,$$
--   the integrand of (9), and the centralized profit is $\pi(D)=\sum_i \pi_i(D)$, the integrand of (1).
--
--   **Normal demand.** $N(m,S)$ denotes the multivariate normal law on $\mathbb R^n$ with mean vector $m$ and covariance matrix $S$. The expected centralized profit and the expected profit of firm $k$ are
--   $$\pi(Q) = \mathbb E\,\pi(D),\qquad \pi_k(Q) = \mathbb E\,\pi_k(D),\qquad D\sim N(m,S).$$
--   A stocking vector $Q$ is **centrally optimal** if $Q\ge 0$ and $\pi(Q)\ge\pi(Q')$ for every $Q'\ge 0$.
--
--   **Raising one covariance.** A covariance matrix $S^2$ is obtained from $S^1$ by **raising the covariance of the distinct products $i$ and $j$** if $\sigma^1_{ij}\le\sigma^2_{ij}$, both matrices are symmetric in the entries $(i,j)$ and $(j,i)$, and every other entry, in particular every variance, is unchanged.
--
--   These objects are shared by every statement of the mission: the realization-wise submodularity of the profits, the supermodular comparison of normal laws, and the monotonicity of expected profit in correlation (Propositions 2 and 5).
--
--   **Formalization Note.** Products are indexed by `Fin n` (0-based). The paper's standing assumption that demand has a continuous distribution with positive support is not part of this file: the paper drops it for the normal results, and so does this mission. $N(m,S)$ is Mathlib's `multivariateGaussian` on `EuclideanSpace ℝ (Fin n)`, pushed forward to `Fin n → ℝ` along the measurable identification `WithLp.ofLp`; Mathlib returns a Dirac mass when $S$ is not positive semidefinite, so every theorem assumes $S$ positive semidefinite. Expectations are Bochner integrals; the profit integrands are Lipschitz in $D$ and therefore integrable under every normal law.
-- source:
--   Netessine & Rudi, Centralized and Competitive Inventory Models with Demand Substitution, SSRN 303779 (Simon School Working Paper OP 02-01, April 2002), pp. 2–3 (§2, §2.1, (1)), p. 7 (Proposition 2), p. 8 ((9))

import Mathlib

namespace DemandSubstitution.Correlation

open MeasureTheory ProbabilityTheory

/-- The data of the `n`-product substitution model of Netessine & Rudi (§2, pp. 2–3):
unit prices `r i`, unit costs `c i`, unit salvage values `s i` with `r i > c i > s i > 0`, and the
substitution fractions `a i j ∈ [0, 1]`: the fraction of product `i`'s unmet demand that switches
to product `j`, with `a i i = 0` and `∑ j, a i j < 1`. Products are indexed by `Fin n`
(0-based: Lean index `i` is the paper's product `i + 1`). -/
structure Model (n : ℕ) where
  r : Fin n → ℝ
  c : Fin n → ℝ
  s : Fin n → ℝ
  a : Fin n → Fin n → ℝ
  c_lt_r : ∀ i, c i < r i
  s_lt_c : ∀ i, s i < c i
  s_pos : ∀ i, 0 < s i
  a_nonneg : ∀ i j, 0 ≤ a i j
  a_le_one : ∀ i j, a i j ≤ 1
  a_diag : ∀ i, a i i = 0
  a_row_sum_lt_one : ∀ i, ∑ j, a i j < 1

namespace Model

variable {n : ℕ}

/-- Unit underage cost `u i = r i - c i` (p. 3). -/
def u (M : Model n) (i : Fin n) : ℝ := M.r i - M.c i

/-- Unit overage cost `o i = c i - s i` (p. 3). -/
def o (M : Model n) (i : Fin n) : ℝ := M.c i - M.s i

end Model

variable {n : ℕ}

/-- Effective demand of product `i` after substitution (p. 3), for the first-choice demand
realization `x` and the stocking vector `Q`:
`D^s_i = D_i + ∑_{j ≠ i} a_ji (D_j - Q_j)⁺`. Note the index order `a j i`: demand flows from
product `j` to product `i`. -/
def Ds (M : Model n) (Q : Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  x i + ∑ j ∈ Finset.univ.erase i, M.a j i * max (x j - Q j) 0

/-- The profit of product `k` (of firm `k` under competition) for one demand realization `x`:
the integrand of (9), `u_k D^s_k - u_k (D^s_k - Q_k)⁺ - o_k (Q_k - D^s_k)⁺`. -/
def firmProfitAt (M : Model n) (Q : Fin n → ℝ) (x : Fin n → ℝ) (k : Fin n) : ℝ :=
  M.u k * Ds M Q x k - M.u k * max (Ds M Q x k - Q k) 0 - M.o k * max (Q k - Ds M Q x k) 0

/-- The centralized profit for one demand realization `x`: the integrand of (1),
`∑_i [u_i D^s_i - u_i (D^s_i - Q_i)⁺ - o_i (Q_i - D^s_i)⁺]`. -/
def profitAt (M : Model n) (Q : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ k, firmProfitAt M Q x k

/-- The multivariate normal law `N(m, S)` on `Fin n → ℝ`: Mathlib's `multivariateGaussian` on
`EuclideanSpace ℝ (Fin n)` with mean `m`, pushed forward along the (measurable) identification
`WithLp.ofLp` of `EuclideanSpace ℝ (Fin n)` with `Fin n → ℝ`. Mathlib returns a Dirac mass at
`m` when `S` is not positive semidefinite, so every statement about `normalLaw m S` assumes
`S.PosSemidef`. -/
noncomputable def normalLaw (m : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℝ) :
    Measure (Fin n → ℝ) :=
  (multivariateGaussian (WithLp.toLp 2 m) S).map WithLp.ofLp

/-- The centralized expected profit (1) when the demand vector is `N(m, S)`. -/
noncomputable def centralProfit (M : Model n) (m : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → ℝ) : ℝ :=
  ∫ x, profitAt M Q x ∂(normalLaw m S)

/-- The expected profit (9) of firm `k` when the demand vector is `N(m, S)`. -/
noncomputable def firmProfit (M : Model n) (m : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → ℝ) (k : Fin n) : ℝ :=
  ∫ x, firmProfitAt M Q x k ∂(normalLaw m S)

/-- `Q` is an optimal stocking vector of the centralized company under `N(m, S)` demand: it is
nonnegative and maximizes `centralProfit` over all nonnegative stocking vectors. -/
def IsCentralOptimal (M : Model n) (m : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ Q i) ∧
    ∀ Q' : Fin n → ℝ, (∀ i, 0 ≤ Q' i) → centralProfit M m S Q' ≤ centralProfit M m S Q

/-- `S₂` is obtained from `S₁` by raising the covariance of the distinct products `i` and `j`
(in both symmetric entries) and keeping every other entry, in particular every variance, fixed. -/
def RaisesCovariance (S₁ S₂ : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : Prop :=
  i ≠ j ∧ S₁ i j ≤ S₂ i j ∧ S₂ j i = S₂ i j ∧ S₁ j i = S₁ i j ∧
    ∀ k l, ¬((k = i ∧ l = j) ∨ (k = j ∧ l = i)) → S₁ k l = S₂ k l

end DemandSubstitution.Correlation


