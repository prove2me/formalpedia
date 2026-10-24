-- Prove2me | Definitions.Def_ProviderGuarantee_Bound_Model
-- name    : ProviderGuarantee_Bound_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:50.120172+00:00
-- url     : https://prove2.me/theorems/b462b211-c10c-44a0-ae9c-80950658f083
-- title:
--   §2, pp. 7–12 — job allocation to heterogeneous providers: Assumptions 1–2, value loss (1), and the LPs (14)–(15)
-- statement:
--   The allocation model of Gur, Iancu and Warnes (§2, pp. 7–12) and the linear programs of the proof of Theorem 1 (Appendix A, pp. 37–39).
--
--   1. **Jobs and values** (p. 7). A finite set $D$ of jobs carries intrinsic values $v : D \to \mathbb R$, and $v(S) = \sum_{d \in S} v(d)$ for $S \subseteq D$.
--   2. **Allocations and total value** (p. 7). An allocation of jobs to the $n$ providers $N = \{1, \dots, n\}$ is a tuple $A = (A_1, \dots, A_n)$ of subsets of $D$. Provider $i$ has heterogeneity parameter $\gamma_i$, and $A$ generates the total value $\sum_{i=1}^n \gamma_i v(A_i)$. For a set $S$ of allocations, $\max_{A \in S} \sum_i \gamma_i v(A_i)$ is its optimal value, and $A$ is *optimal in $S$* if $A \in S$ attains it; $\mathcal F^*$ and $\mathcal F_G^*$ (p. 35) are the optimal allocations of $\mathcal F$ and $\mathcal F_G$.
--   3. **Assumption 1** (pp. 10–11) on the feasible allocations $\mathcal F$: (i) *indivisibility*, $A_i \cap A_j = \emptyset$ for $i \ne j$; (ii) *symmetry*, every permutation $(A_{\sigma(1)}, \dots, A_{\sigma(n)})$ of a feasible allocation is feasible; (iii) *monotonicity*, if $(A_i, A_{-i})$ is feasible then so is $(B, A_{-i})$ for every $B \subseteq A_i$; (iv) *provider independence*, if $A, B \in \mathcal F$ and $A_i \cap B_j = \emptyset$ for all $j \ne i$, then $(B_1, \dots, B_{i-1}, A_i, B_{i+1}, \dots, B_n) \in \mathcal F$.
--   4. **Assumption 2** (pp. 8, 12). The allocations with guarantees form a subset $\mathcal F_G \subseteq \mathcal F$ such that, whenever $B \in \mathcal F_G$, $A \in \mathcal F$ and $v(A_i) \ge v(B_i)$ for all $i$, also $A \in \mathcal F_G$.
--   5. **Heterogeneity, value loss and the bound** (pp. 7, 8, 16, 39). $\delta = (\gamma_{\max} - \gamma_{\min})/\gamma_{\max}$, and
--   $$\mathbf L_\gamma(\mathcal F, \mathcal F_G) = \frac{\max_{A \in \mathcal F} \sum_{i=1}^n \gamma_i v(A_i) - \max_{B \in \mathcal F_G} \sum_{i=1}^n \gamma_i v(B_i)}{\max_{A \in \mathcal F} \sum_{i=1}^n \gamma_i v(A_i)} \qquad (1).$$
--   The bound of Theorem 1 is $\max\{\delta, \frac{n-1}{n + (1-\delta)(n-1)}\}$, and the value of Lemma 2 is $\max\{\delta, \frac{n-1}{n + n_0 + (1-\delta)(n-n_0) - 1}\}$.
--   6. **The linear program (14)** (p. 38), in variables $x, y \in \mathbb R^n$ and $w \in \mathbb R^{n \times n}$: maximize $\sum_i \gamma_i x_i - \sum_i \gamma_i y_i + \sum_i \sum_j w_{ij}(\gamma_i - \gamma_j)$ subject to $\sum_i \gamma_i x_i + \sum_i \sum_j w_{ij} \gamma_i = 1$, $x_i + w_{ij} - \sum_k w_{kj} - y_j \le 0$ for all $i, j$, and $x, y, w \ge 0$. Its value is the supremum of the objective over the feasible set.
--   7. **The dual (15)** (p. 38): minimize $s$ subject to $s\gamma_i + \sum_j \lambda_{ij} \ge \gamma_i$ for all $i$, $\gamma_j - \gamma_k + s\gamma_k - \sum_{i \ne k} \lambda_{ij} \ge 0$ for all $k, j$, $\gamma_j \ge \sum_i \lambda_{ij}$ for all $j$, and $\lambda \ge 0$. Its value $f(\gamma)$ is the infimum of $s$ over the feasible pairs $(s, \lambda)$.
--   8. **Vertices** (p. 39). For $0 \le n_0 \le n$, the profile whose first $n_0$ entries are $\gamma_{\max}$ and whose other entries are $\gamma_{\min}$.
--
--   These objects carry every statement of the mission: Theorem 1 is about the value loss over all $\mathcal F$, $\mathcal F_G$ satisfying the two assumptions, and the linear programs are the devices of its proof.
--
--   **Formalization Note** An allocation is a function `Fin n → Finset D`; provider $i$ of the paper is the index $i - 1$. Symmetry permutes the providers' bundles, `fun i => A (σ i)`; $(B, A_{-i})$ is `Function.update A i B`. Every set of allocations is finite, so `maxValue` (a real `sSup`) is a true maximum on non-empty sets; it is only applied to $\mathcal F \supseteq \mathcal F_G \ne \emptyset$. The loss uses Lean's division, which returns $0$ when the denominator is $0$ (the page's 0/0 case). `lpValue` and `dualValue` are a real `sSup` and `sInf`; that they are the values of (14) and (15) (non-empty, bounded sets, attained) is stated in the milestones, not assumed here.
-- source:
--   Gur, Iancu & Warnes, Value Loss in Allocation Systems with Provider Guarantees, SSRN 3351509 (version of March 24, 2020), pp. 7–8, §2 and (1); pp. 10–12, Assumptions 1–2; p. 16, (5); p. 35 (F*, F*_G); p. 38, (14)–(15); p. 39, Lemma 2

import Mathlib

namespace ProviderGuarantee.Bound

open Finset

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}

/-- The value of a set of jobs, `v(S) = Σ_{d ∈ S} v(d)` (Gur–Iancu–Warnes, SSRN 3351509, §2, p. 7). -/
def val (v : D → ℝ) (S : Finset D) : ℝ := ∑ d ∈ S, v d

/-- The total value `Σ_{i=1}^n γ_i v(A_i)` generated by the allocation `A = (A_1, …, A_n)`
(p. 7); provider `i` of the paper is the index `i : Fin n`. -/
def totalValue (γ : Fin n → ℝ) (v : D → ℝ) (A : Fin n → Finset D) : ℝ :=
  ∑ i, γ i * val v (A i)

/-- The optimal total value `max_{A ∈ S} Σ_i γ_i v(A_i)` over a set `S` of allocations (p. 7–8).
Every set of allocations is finite (the allocation type is finite), so for non-empty `S` the
supremum is attained; for `S = ∅` Lean's `sSup ∅ = 0` (never used: the paper takes `F_G ≠ ∅`). -/
noncomputable def maxValue (γ : Fin n → ℝ) (v : D → ℝ) (S : Set (Fin n → Finset D)) : ℝ :=
  sSup (totalValue γ v '' S)

/-- `A` is an optimal allocation of `S`: `A ∈ S` and no allocation of `S` has a larger total value.
`IsOptimal γ v F A` is `A ∈ F*` and `IsOptimal γ v FG B` is `B ∈ F*_G` (Appendix A, p. 35). -/
def IsOptimal (γ : Fin n → ℝ) (v : D → ℝ) (S : Set (Fin n → Finset D))
    (A : Fin n → Finset D) : Prop :=
  A ∈ S ∧ ∀ A' ∈ S, totalValue γ v A' ≤ totalValue γ v A

/-- Assumption 1 (pp. 10–11) on the set `F` of feasible allocations:
(i) indivisibility: the bundles of a feasible allocation are pairwise disjoint;
(ii) symmetry: any permutation of a feasible allocation (the bundles move between providers) is
feasible;
(iii) monotonicity: if `(A_i, A_{-i})` is feasible then `(B, A_{-i})` is feasible for every `B ⊆ A_i`;
(iv) provider independence: if `A, B ∈ F` and `A_i ∩ B_j = ∅` for all `j ≠ i`, then
`(B_1, …, B_{i-1}, A_i, B_{i+1}, …, B_n) ∈ F`. -/
def Assumption1 (F : Set (Fin n → Finset D)) : Prop :=
  (∀ A ∈ F, ∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
  (∀ A ∈ F, ∀ σ : Equiv.Perm (Fin n), (fun i => A (σ i)) ∈ F) ∧
  (∀ A ∈ F, ∀ i, ∀ B ⊆ A i, Function.update A i B ∈ F) ∧
  (∀ A ∈ F, ∀ B ∈ F, ∀ i, (∀ j, j ≠ i → Disjoint (A i) (B j)) →
      Function.update B i (A i) ∈ F)

/-- The allocations with guarantees form a subset `F_G ⊆ F` (p. 8) satisfying Assumption 2
(Pareto-efficient provider guarantees, p. 12): if `B ∈ F_G`, `A ∈ F` and `v(A_i) ≥ v(B_i)` for
all `i`, then `A ∈ F_G`. -/
def Assumption2 (v : D → ℝ) (F FG : Set (Fin n → Finset D)) : Prop :=
  FG ⊆ F ∧ ∀ B ∈ FG, ∀ A ∈ F, (∀ i, val v (B i) ≤ val v (A i)) → A ∈ FG

/-- The degree of heterogeneity `δ = (γ_max − γ_min)/γ_max` (p. 7). -/
noncomputable def heterogeneity (γmin γmax : ℝ) : ℝ := (γmax - γmin) / γmax

/-- The value loss under provider guarantees (1), p. 8:
`L_γ(F, F_G) = (max_F Σ γ_i v(A_i) − max_{F_G} Σ γ_i v(B_i)) / max_F Σ γ_i v(A_i)`.
When the denominator is `0`, Lean's division gives `0`. -/
noncomputable def valueLoss (γ : Fin n → ℝ) (v : D → ℝ) (F FG : Set (Fin n → Finset D)) : ℝ :=
  (maxValue γ v F - maxValue γ v FG) / maxValue γ v F

/-- The bound of Theorem 1, (5), p. 16: `max{δ, (n−1)/(n + (1−δ)(n−1))}`. -/
noncomputable def lossBound (n : ℕ) (δ : ℝ) : ℝ :=
  max δ (((n : ℝ) - 1) / ((n : ℝ) + (1 - δ) * ((n : ℝ) - 1)))

/-- The value of Lemma 2, p. 39: `max{δ, (n−1)/(n + n₀ + (1−δ)(n−n₀) − 1)}`. -/
noncomputable def lemma2Value (n n0 : ℕ) (δ : ℝ) : ℝ :=
  max δ (((n : ℝ) - 1) / ((n : ℝ) + (n0 : ℝ) + (1 - δ) * ((n : ℝ) - (n0 : ℝ)) - 1))

/-- Feasibility for the linear program (14), p. 38, in the variables `x, y ∈ ℝⁿ`, `w ∈ ℝ^{n×n}`:
`Σ_i γ_i x_i + Σ_i Σ_j w_ij γ_i = 1`, `x_i + w_ij − Σ_k w_kj − y_j ≤ 0` for all `i, j`, and
`x, y, w ≥ 0`. -/
def PrimalFeasible (γ x y : Fin n → ℝ) (w : Fin n → Fin n → ℝ) : Prop :=
  (∑ i, γ i * x i + ∑ i, ∑ j, w i j * γ i = 1) ∧
  (∀ i j, x i + w i j - ∑ k, w k j - y j ≤ 0) ∧
  (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i) ∧ (∀ i j, 0 ≤ w i j)

/-- The objective of (14), p. 38: `Σ_i γ_i x_i − Σ_i γ_i y_i + Σ_i Σ_j w_ij (γ_i − γ_j)`. -/
def primalObj (γ x y : Fin n → ℝ) (w : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, γ i * x i - ∑ i, γ i * y i + ∑ i, ∑ j, w i j * (γ i - γ j)

/-- The optimal value of the linear program (14) (a maximization), as the supremum of the
objective over the feasible set. -/
noncomputable def lpValue (γ : Fin n → ℝ) : ℝ :=
  sSup {z | ∃ x y : Fin n → ℝ, ∃ w : Fin n → Fin n → ℝ, PrimalFeasible γ x y w ∧ z = primalObj γ x y w}

/-- Feasibility of `(s, λ)` for the dual linear program (15), p. 38:
`s γ_i + Σ_j λ_ij ≥ γ_i` for all `i`; `γ_j − γ_k + s γ_k − Σ_{i ≠ k} λ_ij ≥ 0` for all `k, j`;
`γ_j ≥ Σ_i λ_ij` for all `j`; `λ_ij ≥ 0`. -/
def DualFeasible (γ : Fin n → ℝ) (s : ℝ) (lam : Fin n → Fin n → ℝ) : Prop :=
  (∀ i, γ i ≤ s * γ i + ∑ j, lam i j) ∧
  (∀ k j, 0 ≤ γ j - γ k + s * γ k - ∑ i ∈ Finset.univ.erase k, lam i j) ∧
  (∀ j, ∑ i, lam i j ≤ γ j) ∧ (∀ i j, 0 ≤ lam i j)

/-- The optimal value `f(γ)` of the dual program (15) (equivalently (16)), p. 38, as the infimum of
`s` over the dual feasible pairs `(s, λ)`. -/
noncomputable def dualValue (γ : Fin n → ℝ) : ℝ :=
  sInf {s | ∃ lam : Fin n → Fin n → ℝ, DualFeasible γ s lam}

/-- The vertex of `[γ_min, γ_max]^n` of Lemma 2 (p. 39) whose first `n₀` entries equal `γ_max` and
whose remaining entries equal `γ_min`. Lean's providers are `0, …, n−1`, so "the first `n₀`" are
the indices `i` with `i < n₀`. -/
def vertexProfile (n n0 : ℕ) (γmin γmax : ℝ) : Fin n → ℝ :=
  fun i => if (i : ℕ) < n0 then γmax else γmin

end ProviderGuarantee.Bound


