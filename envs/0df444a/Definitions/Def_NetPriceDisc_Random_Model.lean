-- Prove2me | Definitions.Def_NetPriceDisc_Random_Model
-- name    : NetPriceDisc_Random_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:49.611719+00:00
-- url     : https://prove2.me/theorems/0c42dcb9-ba1f-46db-9670-1215ba6dfcf6
-- title:
--   §3 and §5 — network pricing with externalities (equilibrium (1), profit, π*, uniform price, regret, fractional regret) and the directed Erdős–Rényi expectation
-- statement:
--   This file fixes the network pricing model of Huang, Mani and Wang (§3) and the directed Erdős–Rényi law of §5.
--
--   **Network and spectral norm.** There are $n$ consumers. The network is a real $n\times n$ matrix $G$, where $G_{ij}$ is the influence of consumer $j$ on consumer $i$. For a square matrix $A$, $\|A\|$ denotes its spectral norm, i.e. the $\ell^2$ operator norm. We write $\mathbf 1\in\mathbb R^n$ for the all-ones vector and
--   $$\mathrm{walks}(A,k)=\mathbf 1^{\mathsf T}A^k\mathbf 1,$$
--   the total weight of walks of length $k$ in $A$ (the number of such walks when $A$ is a $0/1$ matrix).
--
--   **Consumption equilibrium (eq. (1)).** Given a stand-alone utility $a$, a network coefficient $\rho$ and a price vector $p\in\mathbb R^n$, the consumption vector is
--   $$x^*(p)=\tfrac12\Big(I-\tfrac{2\rho}{\|G+G^{\mathsf T}\|}G\Big)^{-1}(a\mathbf 1-p).$$
--
--   **Profit, optimal profit, uniform price.** For a marginal cost $c$, the monopolist's profit is $\pi(p)=(p-c\mathbf 1)^{\mathsf T}x^*(p)$. The optimal (discriminating) profit is
--   $$\pi^*=\sup_{p\in\mathbb R^n}\pi(p),$$
--   the value of the pricing problem $\max_p(p-c\mathbf 1)^{\mathsf T}x^*(p)$. The uniform price vector is $p_0=\frac{a+c}{2}\mathbf 1$.
--
--   **Regret and fractional regret (§3.2).** $R(p_0)=\pi^*-\pi(p_0)$ and $R_F(p_0)=1-\pi(p_0)/\pi^*$.
--
--   **Directed Erdős–Rényi network $G(n,q)$.** Each ordered pair $(i,j)$ with $i\neq j$ is an arc independently with probability $q$, and $G_{ii}=0$. For a function $F$ of the adjacency matrix,
--   $$\mathbb E_G[F(G)]=\sum_{S\subseteq\{(i,j):i\neq j\}}q^{|S|}(1-q)^{n(n-1)-|S|}\,F(A_S),$$
--   where $A_S$ is the $0/1$ matrix with $(A_S)_{ij}=1$ iff $(i,j)\in S$.
--
--   These are the objects every statement of the mission is about: the goal (Theorem 5.1) is a statement about $\mathbb E_G[R(p_0)]$ and $\mathbb E_G[R_F(p_0)]$.
--
--   **Formalization Note.** The spectral norm is Mathlib's $\ell^2$ operator norm on matrices (`Matrix.Norms.L2Operator`); for the symmetric non-negative $G+G^{\mathsf T}$ it is the largest eigenvalue, as on pp. 14 and 17. The consumption vector is formula (1) for every $p\in\mathbb R^n$, exactly as the paper defines $\pi(p)$ ("with $x^*(p)$ defined in (1)", p. 7); no constraint $x\ge0$ is imposed. $\pi^*$ is the supremum of $\pi$ over all of $\mathbb R^n$; that it is attained, with the closed form (3), is a separate theorem of the mission (eq. (3)), so neither $\pi^*$ nor $R$ is defined by a closed form. Lean's division by zero gives $\rho/\|0\|=0$: for the empty network $G=0$ there is no externality, so $\pi^*=\pi(p_0)$ and $R(p_0)=0$, which is the paper's reading of the empty network ("there is no network effect and there is no value of price discrimination", p. 12); the empty network keeps its probability $(1-q)^{n(n-1)}$ in the expectation. $\mathbb E_G$ is a finite sum, whose weights sum to $1$ for $0\le q\le1$ (with $0^0=1$); no measure theory is involved. Matrix inversion of a singular matrix returns $0$ in Lean; under $0<\rho<1$ and $G\ge0$ the matrices inverted here are invertible (p. 6).
-- source:
--   Huang, Mani & Wang, The Value of Price Discrimination in Large Random Networks, SSRN 3368458 (EC '19 submission version), pp. 5–7, §3.1–§3.2, eq. (1); pp. 11–12, §5

import Mathlib
open Matrix
open scoped Matrix.Norms.L2Operator

namespace NetPriceDisc.Random

/-- The spectral norm `‖A‖` of a real square matrix: the `ℓ²` operator norm
(Mathlib's `Matrix.Norms.L2Operator` instance). -/
noncomputable def specNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ := ‖A‖

/-- The all-ones vector `1 ∈ ℝⁿ`. -/
def ones (n : ℕ) : Fin n → ℝ := fun _ => 1

/-- `1ᵀ Aᵏ 1`: the total weight of walks of length `k` in the (weighted) network `A`. -/
def walks {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : ℝ :=
  ones n ⬝ᵥ ((A ^ k) *ᵥ ones n)

/-- The consumption equilibrium, eq. (1), p. 6:
`x*(p) = ½ (I − (2ρ/‖G + Gᵀ‖) G)⁻¹ (a1 − p)`. -/
noncomputable def xStar {n : ℕ} (a ρ : ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ) :
    Fin n → ℝ :=
  (1 / 2 : ℝ) • ((1 - (2 * ρ / specNorm (G + Gᵀ)) • G)⁻¹ *ᵥ (a • ones n - p))

/-- The monopolist's profit under the price vector `p`, p. 7: `π(p) = (p − c1)ᵀ x*(p)`. -/
noncomputable def profit {n : ℕ} (a c ρ : ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ) : ℝ :=
  (p - c • ones n) ⬝ᵥ xStar a ρ G p

/-- The optimal (discriminating) profit `π*`: the supremum of `π(p)` over all price vectors
`p ∈ ℝⁿ` (the pricing problem `max_p (p − c1)ᵀ x*(p)`, p. 6). -/
noncomputable def optProfit {n : ℕ} (a c ρ : ℝ) (G : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup (Set.range (profit a c ρ G))

/-- The uniform price vector `p₀ = ((a + c)/2) 1`, p. 7. -/
noncomputable def uniformPrice (n : ℕ) (a c : ℝ) : Fin n → ℝ := ((a + c) / 2) • ones n

/-- The regret of uniform pricing, p. 7: `R(p₀) = π* − π(p₀)`. -/
noncomputable def regret {n : ℕ} (a c ρ : ℝ) (G : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  optProfit a c ρ G - profit a c ρ G (uniformPrice n a c)

/-- The fractional regret of uniform pricing, p. 7: `R_F(p₀) = 1 − π(p₀)/π*`. -/
noncomputable def fracRegret {n : ℕ} (a c ρ : ℝ) (G : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  1 - profit a c ρ G (uniformPrice n a c) / optProfit a c ρ G

/-- The binary adjacency matrix of the arc set `S`: entry `(i, j)` is `1` iff `(i, j) ∈ S`. -/
def adjOf {n : ℕ} (S : Finset (Fin n × Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if (i, j) ∈ S then 1 else 0

/-- The expectation `E_G[F(G)]` over the directed Erdős–Rényi network `G(n, p)` (pp. 11–12):
each ordered pair `(i, j)` with `i ≠ j` is an arc independently with probability `p`, and
`G_ii = 0`. The arc set `S` ranges over all subsets of the off-diagonal pairs, with weight
`p^|S| (1 − p)^(n(n−1) − |S|)`. -/
noncomputable def erExpect (n : ℕ) (p : ℝ) (F : Matrix (Fin n) (Fin n) ℝ → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin n)).offDiag.powerset,
    p ^ S.card * (1 - p) ^ ((Finset.univ : Finset (Fin n)).offDiag.card - S.card) * F (adjOf S)

end NetPriceDisc.Random


