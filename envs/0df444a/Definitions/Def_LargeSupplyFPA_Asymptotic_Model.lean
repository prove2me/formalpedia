-- Prove2me | Definitions.Def_LargeSupplyFPA_Asymptotic_Model
-- name    : LargeSupplyFPA_Asymptotic_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:02:12.302402+00:00
-- url     : https://prove2.me/theorems/d6bc047e-b0db-45ba-aa9e-442db4be28f9
-- title:
--   Multi-unit first-price auction: interim allocation with uniform ties, ε-BNE, welfare and the k-th highest bid (§2, pp. 5–6; (39), (41))
-- statement:
--   There are $k$ identical units and $n$ unit-demand agents $i\in\{0,\dots,n-1\}$. Agent $i$ has a private value drawn from a probability law $V_i$ on $\mathbb R$, independently across agents. A **strategy** of agent $i$ is a Markov kernel $E_i$ assigning to each value $v$ a law $E_{i,v}$ of non-negative bids; the **marginal bid distribution** is $E_i=\int E_{i,v}\,dV_i(v)$, and bids of different agents are independent.
--
--   The $k$ highest bids win one unit each and pay their bid; ties are broken uniformly at random. For a bid profile $\beta$ of the others, with $m=\#\{j\neq i:\beta_j>b\}$ and $t=\#\{j\neq i:\beta_j=b\}$, agent $i$ bidding $b$ wins with probability
--   $$\min\Big\{\frac{\max\{k-m,0\}}{1+t},\,1\Big\}\qquad\text{(the paper's (41))},$$
--   and the **interim allocation** $x_i(b)$ is its expectation when every $j$ bids independently from $E_j$. The **interim utility** is $u_i(v,b)=(v-b)\,x_i(b)$ and the **optimal utility** is $\bar u_i(v)=\sup_{b\ge 0}u_i(v,b)$.
--
--   $E$ is an **$\epsilon$-approximate Bayes–Nash equilibrium** if for every agent $i$ and every $v$ in the topological support of $V_i$, the expected utility $\mathbb E_{b\sim E_{i,v}}[u_i(v,b)]$ is finite and at least $u_i(v,b)-\epsilon$ for every $b\ge 0$.
--
--   The **expected welfare** is $W(E,A)=\sum_i\mathbb E_{v_i\sim V_i}\big[v_i\,\mathbb E_{b\sim E_{i,v_i}}[x_i(b)]\big]$ (39), the **expected optimal welfare** $O(A)$ is the expected largest total value of at most $k$ agents (the sum of the $k$ highest values), and the welfare ratio is $W/O$. The distribution function of the critical bid $B^{(k)}$ (the $k$-th highest of the $n$ bids) is $B^{(k)}(b)=\Pr[\#\{j:\beta_j>b\}<k]$, and $\mathbb E[T(b)]=\sum_i\Pr_{E_i}[(b,\infty)]$ counts bids strictly above $b$ in expectation.
--
--   **Formalization Note** Bids are reals, and each $E_{i,v}$ puts no mass on $(-\infty,0)$. $x_i$ is computed under `Measure.pi` of the marginals, ignoring agent $i$'s own coordinate. The optimum uses sets of at most $k$ agents; with non-negative values this equals the sum of the $k$ highest values when $k\le n$. Because $x_i\in[0,1]$, the supremum defining $\bar u_i(v)$ is bounded above by $\max(v,0)$ and is attained in the limit, so it is never a junk value. The equilibrium condition in the "for every $b$" form is equivalent to the paper's $\ge\sup_b u_i(v,b)-\epsilon$.
-- source:
--   Hartline, Shah, vonAllmen, Robust Analysis of First-Price Auctions with Large Supply, STOC 2027 submission (manuscript of November 3, 2026, sha256 2ad8363b…), pp. 5–6 (§2, ϵ-approximate BNE definition), p. 7 and p. 10 (critical bid B^(k)), p. 15 (T^(k)), p. 30 (39), p. 32 (41)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace LargeSupplyFPA.Asymptotic

/-- Value laws of the `n` agents of one auction: agent `i`'s value is drawn from the
probability measure `V i` on `ℝ`, independently across agents. -/
def IsValueProfile {n : ℕ} (V : Fin n → Measure ℝ) : Prop :=
  ∀ i, IsProbabilityMeasure (V i)

/-- A mixed strategy profile: agent `i` with value `v` draws its bid from the probability
measure `E i v` (a Markov kernel from values to bids); bids are non-negative. -/
def IsStrategyProfile {n : ℕ} (E : Fin n → Kernel ℝ ℝ) : Prop :=
  ∀ i, IsMarkovKernel (E i) ∧ ∀ v, E i v (Set.Iio 0) = 0

/-- The marginal bid distribution `E_i = ∫ E_{i,v} dV_i(v)` of agent `i`. -/
noncomputable def marginalBid {n : ℕ} (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    (i : Fin n) : Measure ℝ :=
  (V i).bind (E i)

/-- Number of entries of the bid profile `β` strictly above `b`. -/
noncomputable def numAbove {n : ℕ} (b : ℝ) (β : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter (fun j => b < β j)).card

/-- Uniform tie-breaking, the paper's (41): agent `i` bids `b`, the others bid `β j`
(`β i` is ignored). With `m = #{j ≠ i : β j > b}` and `t = #{j ≠ i : β j = b}`, agent `i`
receives a unit with probability `min (max (k - m) 0 / (1 + t)) 1`. -/
noncomputable def tieShare {n : ℕ} (k : ℕ) (i : Fin n) (b : ℝ) (β : Fin n → ℝ) : ℝ :=
  min (max ((k : ℝ) - ((Finset.univ.filter (fun j => j ≠ i ∧ b < β j)).card : ℝ)) 0 /
    (1 + ((Finset.univ.filter (fun j => j ≠ i ∧ β j = b)).card : ℝ))) 1

/-- Interim allocation `x_i(b)` of agent `i` bidding `b` in the `k`-unit first-price auction
when every agent `j` bids independently according to the bid law `μ j`. -/
noncomputable def allocOf {n : ℕ} (k : ℕ) (μ : Fin n → Measure ℝ) (i : Fin n) (b : ℝ) : ℝ :=
  ∫ β, tieShare k i b β ∂(Measure.pi μ)

/-- Interim allocation `x_i(b)` under the strategy profile `E`. -/
noncomputable def alloc {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    (i : Fin n) (b : ℝ) : ℝ :=
  allocOf k (marginalBid V E) i b

/-- Interim utility `u_i(v, b) = v x_i(b) - p_i(b) = (v - b) x_i(b)` (winner pays bid). -/
noncomputable def utility {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    (i : Fin n) (v b : ℝ) : ℝ :=
  (v - b) * alloc k V E i b

/-- Optimal interim utility `sup_{b ≥ 0} u_i(v, b)`. -/
noncomputable def optUtility {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    (i : Fin n) (v : ℝ) : ℝ :=
  ⨆ b : Set.Ici (0 : ℝ), utility k V E i v b

/-- `E` is an `ε`-approximate Bayes–Nash equilibrium of the `k`-unit first-price auction with
value laws `V`: for every agent `i` and every value `v` in the support of `V i`, the expected
utility of the bid law `E i v` is at least `u_i(v, b) - ε` for every bid `b ≥ 0` (equivalently,
at least `sup_{b ≥ 0} u_i(v, b) - ε`); the expected utility is required to be finite. -/
def IsApproxBNE {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ) (ε : ℝ) :
    Prop :=
  ∀ i, ∀ v ∈ (V i).support,
    Integrable (fun b => utility k V E i v b) (E i v) ∧
    ∀ b : ℝ, 0 ≤ b → utility k V E i v b - ε ≤ ∫ b', utility k V E i v b' ∂(E i v)

/-- Expected equilibrium welfare (39):
`W(E, A) = E_v [ ∑_i v_i E_{b ∼ E_{i,v_i}} [x_i(b)] ]`. -/
noncomputable def welfare {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ) :
    ℝ :=
  ∑ i, ∫ v, v * (∫ b, alloc k V E i b ∂(E i v)) ∂(V i)

/-- Largest total value of at most `k` agents (the value of an optimal allocation of `k`
units to unit-demand agents). -/
noncomputable def topKSum {n : ℕ} (k : ℕ) (w : Fin n → ℝ) : ℝ :=
  ⨆ S : {S : Finset (Fin n) // S.card ≤ k}, ∑ i ∈ S.1, w i

/-- Expected optimal welfare `O(A)`: the expected sum of the `k` highest values. -/
noncomputable def optWelfare {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ) : ℝ :=
  ∫ w, topKSum k w ∂(Measure.pi V)

/-- The ratio `W(E, A) / O(A)`. -/
noncomputable def welfareRatio {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ)
    (E : Fin n → Kernel ℝ ℝ) : ℝ :=
  welfare k V E / optWelfare k V

/-- Distribution function of the critical bid `B^(k)`, the `k`-th highest of the `n`
independent equilibrium bids: `B^(k)(b) = Pr[#{j : b_j > b} ≤ k - 1]`. -/
noncomputable def kthBidCDF {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    (b : ℝ) : ℝ :=
  (Measure.pi (marginalBid V E)).real {β | numAbove b β < k}

/-- `E[T(b)] = ∑_i Pr[E_i > b]`, the expected number of equilibrium bids strictly above `b`. -/
noncomputable def expNumAbove {n : ℕ} (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    (b : ℝ) : ℝ :=
  ∑ i, (marginalBid V E i).real (Set.Ioi b)

end LargeSupplyFPA.Asymptotic


