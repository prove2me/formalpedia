-- Prove2me | Definitions.Def_KMedianPP_Tight_Sampling
-- name    : KMedianPP_Tight_Sampling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:02:06.591793+00:00
-- url     : https://prove2.me/theorems/fc1ec364-a8d8-4d09-b24b-c74468694893
-- title:
--   §2 — $D^\ell$-sampling with $k+\Delta$ centers, its exact expected final cost, $\mathrm{OPT}$, and a reference clustering
-- statement:
--   **Instances.** A metric space $(M,d)$, a finite multiset of input points written $x_1,\dots,x_n\in M$ (`X : Fin n → M`; repeats allowed), an integer $k\ge1$ and a distance exponent $\ell>0$. For a finite set of centers $C$ write $d(x,C)=\min_{c\in C}d(x,c)$, and $\mathrm{cost}(Y,C)=\sum_{x\in Y}d(x,C)^\ell$, $\mathrm{cost}(C)=\mathrm{cost}(X,C)$.
--
--   **$D^\ell$-sampling with $k+\Delta$ centers.** The first center is uniform over the $n$ input points (counted with multiplicity). Given current centers $C$, with $D(x)=d(x,C)$, the next center is the input point $x_i$ with probability $D(x_i)^\ell/\mathrm{cost}(C)$, and is added to $C$; if $\mathrm{cost}(C)=0$ the algorithm stops (footnote 4). After $k+\Delta$ centers have been sampled it returns $C_{\mathrm{final}}$. Since only input points are sampled, the centers are recorded as a set $S$ of input indices (`mass X ℓ S i` $=D(x_i)^\ell$, `totalCost X ℓ S` $=\mathrm{cost}(C)$). `expFinalCostFrom X ℓ t S` is the exact expected final cost with $t$ samples left, by conditioning on the next sample, and
--   $$\texttt{expectedCost X ℓ k Δ}=\frac1n\sum_{i=1}^n \texttt{expFinalCostFrom X ℓ (k+Δ-1) \{i\}}=\mathbb E[\mathrm{cost}(C_{\mathrm{final}})].$$
--
--   **OPT.** `costOf X ℓ C` $=\mathrm{cost}(X,C)$ for a finite $C\subseteq M$, and `opt X ℓ k` is the infimum of $\mathrm{cost}(X,C)$ over $C\subseteq M$ with $1\le|C|\le k$ ($k$ centers, possibly coinciding).
--
--   **Reference clustering.** An assignment $\sigma$ of input points to clusters $P_j=\{i:\sigma(i)=j\}$, $j=1,\dots,k$, and centers $c^*_j\in M$; $d^*_x=d(x,c^*_j)$ for $x\in P_j$, $\varphi(P_j)=\sum_{x\in P_j}(d^*_x)^\ell$, `refCost` $=\sum_j\varphi(P_j)$, and `clusterCost X σ ℓ S j` $=\mathrm{cost}(P_j,C)$. The paper fixes an optimal solution; the statements of this mission allow any reference clustering.
--
--   **Formalization Note.** `distTo f C x` is the minimum of $d(x,f(j))$ over $j\in C$ and is $0$ for $C=\emptyset$ (never used). The recursion's division by $\mathrm{cost}(C)$ only happens when $\mathrm{cost}(C)\ne0$. `expectedCost` is used for $k\ge1$, $n\ge1$ ($k+\Delta-1$ is then not truncated). Powers are `Real.rpow` of nonnegative reals.
-- source:
--   Kaplan, Naori, Tight Bounds for k-Median++ and Improved Bounds for k-Means++, STOC 2027 submission (manuscript sha256 f017529e…), p. 9 (PDF 11), §2 Preliminaries and footnote 4

import Mathlib

set_option autoImplicit false

namespace KMedianPP.Tight

open Finset

/-! Kaplan, Naori, *Tight Bounds for k-Median++ and Improved Bounds for k-Means++*, STOC 2027
submission (manuscript sha256 f017529e…), §2 (p. 9): the `k`-clustering cost with distance
exponent `ℓ`, the `D^ℓ`-sampling algorithm (k-means++; k-median++ for `ℓ = 1`) with `k + Δ`
centers and its exact expected final cost, the optimum `OPT`, and a reference clustering
`P_1, …, P_k` with centers `c*_1, …, c*_k`.

The input is a finite multiset of points of a metric space `M`, written `X : Fin n → M`
(point `i` is `X i`; repeated points are allowed). The algorithm only ever picks input points,
so a set of current centers is a `Finset (Fin n)` of input indices. -/

variable {M : Type*} [MetricSpace M]

/-- `d(x, C) = min_{j ∈ C} d(x, f j)`: the distance from `x` to the nearest point of the indexed
set of centers `{f j : j ∈ C}`. Only used for nonempty `C`; the value `0` on `C = ∅` is a
convention that no statement of this mission relies on. -/
noncomputable def distTo {ι : Type*} (f : ι → M) (C : Finset ι) (x : M) : ℝ :=
  if h : C.Nonempty then C.inf' h (fun j => dist x (f j)) else 0

variable {n k : ℕ}

/-- The sampling mass `D(x_i)^ℓ = d(x_i, C)^ℓ` of input point `i` when the current centers are the
input points with indices in `S` (§2–§3: the current cost of `x_i`, and its weight in the next
`D^ℓ`-sampling step). -/
noncomputable def mass (X : Fin n → M) (ℓ : ℝ) (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  distTo X S (X i) ^ ℓ

/-- `cost(C) = cost(X, C) = Σ_{x ∈ X} d(x, C)^ℓ` for the current centers `C = {x_j : j ∈ S}`
(input points counted with multiplicity). -/
noncomputable def totalCost (X : Fin n → M) (ℓ : ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ i, mass X ℓ S i

/-- Exact expected final cost of `D^ℓ`-sampling from the current centers `S` with `t` samples still
to be drawn (§2, p. 9): each sample is input point `i` with probability `D(x_i)^ℓ / cost(C)` and is
added to the centers; if `cost(C) = 0` the algorithm terminates (footnote 4) and the final cost is
the current one. -/
noncomputable def expFinalCostFrom (X : Fin n → M) (ℓ : ℝ) : ℕ → Finset (Fin n) → ℝ
  | 0, S => totalCost X ℓ S
  | t + 1, S =>
      if totalCost X ℓ S = 0 then totalCost X ℓ S
      else ∑ i, mass X ℓ S i / totalCost X ℓ S * expFinalCostFrom X ℓ t (insert i S)

/-- `E[cost(C_final)]` for `D^ℓ`-sampling with `k + Δ` centers (§2, p. 9): the first center is
uniform over the `n` input points (counted with multiplicity), then `k + Δ - 1` further centers
are drawn by `D^ℓ`-sampling (stopping early if the cost is `0`, footnote 4). Used for `k ≥ 1`
and `n ≥ 1`. -/
noncomputable def expectedCost (X : Fin n → M) (ℓ : ℝ) (k Δ : ℕ) : ℝ :=
  ∑ i : Fin n, (1 / (n : ℝ)) * expFinalCostFrom X ℓ (k + Δ - 1) {i}

/-- `cost(X, C) = Σ_{x ∈ X} d(x, C)^ℓ` for an arbitrary set `C ⊆ M` of centers. -/
noncomputable def costOf (X : Fin n → M) (ℓ : ℝ) (C : Finset M) : ℝ :=
  ∑ i, distTo id C (X i) ^ ℓ

/-- `OPT`: the optimal cost with `k` centers in `M`, i.e. the infimum of `cost(X, C)` over sets
`C ⊆ M` of at least one and at most `k` points (`k` centers, possibly coinciding). The set is
nonempty when `M` is nonempty and `k ≥ 1`, and bounded below by `0`. -/
noncomputable def opt (X : Fin n → M) (ℓ : ℝ) (k : ℕ) : ℝ :=
  ⨅ C : {C : Finset M // C.Nonempty ∧ C.card ≤ k}, costOf X ℓ C.1

/-! ### A reference clustering

§2 fixes an optimal solution with clusters `P_1, …, P_k` and centers `c*_1, …, c*_k`. The
analysis never uses optimality, so the statements of this mission take any reference clustering:
an assignment `σ : Fin n → Fin k` of input points to clusters (`P_j = {i : σ i = j}`) and centers
`c : Fin k → M`. -/

/-- The input indices of the cluster `P_j = {i : σ i = j}`. -/
def cluster (σ : Fin n → Fin k) (j : Fin k) : Finset (Fin n) :=
  univ.filter fun i => σ i = j

/-- `d*_x = d(x, c*_j)` for the point `x = x_i` of the cluster `P_j`, `j = σ i`. -/
noncomputable def dstar (X : Fin n → M) (σ : Fin n → Fin k) (c : Fin k → M) (i : Fin n) : ℝ :=
  dist (X i) (c (σ i))

/-- `ϕ(P_j) = Σ_{x ∈ P_j} (d*_x)^ℓ`: the cost of the cluster `P_j` in the reference solution. -/
noncomputable def phi (X : Fin n → M) (σ : Fin n → Fin k) (c : Fin k → M) (ℓ : ℝ) (j : Fin k) :
    ℝ :=
  ∑ i ∈ cluster σ j, dstar X σ c i ^ ℓ

/-- The cost of the reference solution, `Σ_j ϕ(P_j) = Σ_i d(x_i, c*_{σ i})^ℓ` (`OPT` when the
reference solution is optimal). -/
noncomputable def refCost (X : Fin n → M) (σ : Fin n → Fin k) (c : Fin k → M) (ℓ : ℝ) : ℝ :=
  ∑ i, dstar X σ c i ^ ℓ

/-- `cost(P_j, C) = Σ_{x ∈ P_j} D(x)^ℓ`: the current cost (= sampling mass) of the cluster `P_j`
when the current centers are the input points with indices in `S`. -/
noncomputable def clusterCost (X : Fin n → M) (σ : Fin n → Fin k) (ℓ : ℝ)
    (S : Finset (Fin n)) (j : Fin k) : ℝ :=
  ∑ i ∈ cluster σ j, mass X ℓ S i

end KMedianPP.Tight


