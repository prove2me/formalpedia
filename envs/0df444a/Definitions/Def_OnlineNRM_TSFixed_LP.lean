-- Prove2me | Definitions.Def_OnlineNRM_TSFixed_LP
-- name    : OnlineNRM_TSFixed_LP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:07:57.069619+00:00
-- url     : https://prove2.me/theorems/8af3c1cb-fa56-4de4-9ff0-ef3ebf1e3924
-- title:
--   The linear program LP(d), its optimal value OPT(d), and the constants $p_{\max}$, $p^j_{\max}$
-- statement:
--   This file sets up the deterministic linear program at the heart of TS-fixed (Algorithm 1, step 2) and of the benchmark of Section 3.1.1 in Ferreira, Simchi-Levi and Wang, together with the two instance constants of Section 3.1.2.
--
--   A retailer sells $N$ products using $M$ resources; one unit of product $i$ consumes $a_{ij}$ units of resource $j$. There are $K$ admissible price vectors $p_k=(p_{1k},\dots,p_{Nk})$. For a mean-demand matrix $d=\{d_{ik}\}_{i\in[N],k\in[K]}$ (the mean demand of product $i$ under price vector $p_k$) and per-period capacities $c=(c_1,\dots,c_M)$, the linear program $\mathrm{LP}(d)$ is
--
--   $$
--   \max_{x\in\mathbb R^K}\ \sum_{k=1}^K\Bigl(\sum_{i=1}^N p_{ik}d_{ik}\Bigr)x_k
--   \quad\text{s.t.}\quad \sum_{k=1}^K\Bigl(\sum_{i=1}^N a_{ij}d_{ik}\Bigr)x_k\le c_j\ \ \forall j\in[M],\qquad \sum_{k=1}^K x_k\le 1,\qquad x_k\ge 0\ \ \forall k\in[K].
--   $$
--
--   1. $x$ is **feasible** if it satisfies the three groups of constraints.
--   2. The **objective** of $x$ is $\sum_k(\sum_i p_{ik}d_{ik})x_k$.
--   3. $x$ is **optimal** if it is feasible and no feasible point has a larger objective.
--   4. $\mathrm{OPT}(d)$ is the supremum of the objective over the feasible set.
--   5. $p_{\max}:=\max_{k\in[K]}\sum_{i=1}^N p_{ik}\bar d_i$, the largest revenue achievable in one period when the demand of product $i$ is at most $\bar d_i$.
--   6. $p^j_{\max}:=\max_{i\in[N]:a_{ij}\ne0,\ k\in[K]} p_{ik}/a_{ij}$, the largest revenue obtainable from one extra unit of resource $j$.
--
--   $x_k$ is read as the probability of posting price vector $p_k$ in a period; the remaining probability goes to the shut-off price. TS-fixed solves $\mathrm{LP}(d(t))$ at a sampled mean demand; the benchmark is $\mathrm{OPT}(d)$ at the true mean demand.
--
--   **Formalization Note** Products, resources and price vectors are indexed by `Fin N`, `Fin M`, `Fin K`. $\mathrm{OPT}(d)$ is a real `sSup`; whenever $a\ge0$, $d\ge0$ and $c\ge0$ (always the case in Theorem 1) the feasible set contains $0$ and lies in $[0,1]^K$, so the supremum is over a nonempty bounded set and is attained. $p_{\max}$ is set to $0$ when $K=0$, and $p^j_{\max}$ to $0$ when no product uses resource $j$; in the latter case every $a_{ij}=0$, so the value is only ever multiplied by $0$.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1591, Algorithm 1 step 2 (LP(d(t))); p. 1593, Section 3.1.1 (LP(d), OPT(d)); p. 1593, Section 3.1.2 (p_max, p^j_max)

import Mathlib

namespace OnlineNRM.TSFixed

open scoped BigOperators

variable {N M K : ℕ}

/-- Feasible set of the linear program `LP(d)` of Ferreira–Simchi-Levi–Wang (Algorithm 1,
step 2, and Section 3.1.1): the vector `x ∈ ℝ^K` satisfies the resource constraints
`∑ₖ (∑ᵢ a i j * d i k) * x k ≤ c j` for every resource `j`, the probability constraint
`∑ₖ x k ≤ 1`, and `x k ≥ 0` for every `k`. -/
def lpFeasible (a : Fin N → Fin M → ℝ) (d : Fin N → Fin K → ℝ) (c : Fin M → ℝ)
    (x : Fin K → ℝ) : Prop :=
  (∀ j : Fin M, ∑ k : Fin K, (∑ i : Fin N, a i j * d i k) * x k ≤ c j) ∧
    (∑ k : Fin K, x k ≤ 1) ∧ ∀ k : Fin K, 0 ≤ x k

/-- Objective of `LP(d)`: `∑ₖ (∑ᵢ p i k * d i k) * x k`. -/
def lpObj (p : Fin N → Fin K → ℝ) (d : Fin N → Fin K → ℝ) (x : Fin K → ℝ) : ℝ :=
  ∑ k : Fin K, (∑ i : Fin N, p i k * d i k) * x k

/-- `x` is an optimal solution of `LP(d)`: feasible, and no feasible point has a larger
objective value. -/
def IsLPOptimal (p : Fin N → Fin K → ℝ) (a : Fin N → Fin M → ℝ) (d : Fin N → Fin K → ℝ)
    (c : Fin M → ℝ) (x : Fin K → ℝ) : Prop :=
  lpFeasible a d c x ∧ ∀ y : Fin K → ℝ, lpFeasible a d c y → lpObj p d y ≤ lpObj p d x

/-- `OPT(d)`, the optimal value of `LP(d)`, as the supremum of the objective over the
feasible set. When `a ≥ 0`, `d ≥ 0` and `c ≥ 0` the feasible set contains `0` and lies in
`[0,1]^K`, so the supremum is over a nonempty bounded set and is attained. -/
noncomputable def lpOpt (p : Fin N → Fin K → ℝ) (a : Fin N → Fin M → ℝ)
    (d : Fin N → Fin K → ℝ) (c : Fin M → ℝ) : ℝ :=
  sSup (lpObj p d '' {x | lpFeasible a d c x})

/-- `p_max := max_{k ∈ [K]} ∑ᵢ p i k * dbar i` (Section 3.1.2). The value `0` for `K = 0`
is never used (Theorem 1 assumes `K ≥ 2`). -/
noncomputable def pmax (p : Fin N → Fin K → ℝ) (dbar : Fin N → ℝ) : ℝ :=
  if h : (Finset.univ : Finset (Fin K)).Nonempty then
    Finset.univ.sup' h (fun k => ∑ i : Fin N, p i k * dbar i)
  else 0

/-- `p^j_max := max_{i ∈ [N] : a i j ≠ 0, k ∈ [K]} p i k / a i j` (Section 3.1.2). If no
product uses resource `j` the index set is empty and the value is `0`; then `a i j = 0`
for all `i`, so this value is always multiplied by `0` in Theorem 1. -/
noncomputable def pjmax (p : Fin N → Fin K → ℝ) (a : Fin N → Fin M → ℝ) (j : Fin M) : ℝ :=
  if h : (Finset.univ.filter (fun ik : Fin N × Fin K => a ik.1 j ≠ 0)).Nonempty then
    (Finset.univ.filter (fun ik : Fin N × Fin K => a ik.1 j ≠ 0)).sup' h
      (fun ik => p ik.1 ik.2 / a ik.1 j)
  else 0

end OnlineNRM.TSFixed


