-- Prove2me | Definitions.Def_TwoStageMatch_Algorithm1
-- name    : TwoStageMatch_Algorithm1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:31:23.252494+00:00
-- url     : https://prove2.me/theorems/5d994092-07c3-415e-bfd3-96e642e60756
-- title:
--   The balancing program $\mathscr P^g$ and the runs of Algorithm 1 (Weighted-Balanced-Utilization)
-- statement:
--   For an instance and a function $g:\mathbb R\to\mathbb R$, the convex program $\mathscr P^g$ is
--   $$\min_x\ \sum_{j\in S}\frac{1}{w_j}\,g\Big(w_j\Big(1-\sum_{i\in N(j)}x_{ij}\Big)\Big)\quad\text{s.t.}\quad \sum_{j\in N(i)}x_{ij}\le 1\ (i\in D_1),\ \ \sum_{i\in N(j)}x_{ij}\le 1\ (j\in S),\ \ x_{ij}\ge 0\ ((i,j)\in E),$$
--   over fractional matchings of the first-stage graph $G[D_1,S]$.
--
--   A **rounding** of a feasible $x$ is a probability distribution $\rho$ on first-stage matchings with edge marginals $x$:
--   $$\Pr_{M_1\sim\rho}[(i,j)\in M_1]=x_{ij}\qquad\text{for every } i\in D_1,\ j\in S,\ (i,j)\in E. \qquad (4)$$
--   A **run of Algorithm 1** for $g$ is a pair $(x^*,\rho)$ where $x^*$ is an optimal solution of $\mathscr P^g$ (step 3) and $\rho$ is a rounding of $x^*$ (step 4). In the second stage Algorithm 1 returns a maximum supply-weighted matching between $\tilde D_2$ and the remaining supplies (step 5), so the **value** of the run is
--   $$\mathrm{ALG}=\mathbb E_{M_1\sim\rho}\,\mathbb E_{\tilde D_2}\Big[w(S_1)+\mathrm{Max\text{-}WeightMatch}^w(\tilde D_2,S\setminus S_1)\Big]=\mathbb E\Big[\sum_{j\in S}w_j\mathbb 1\{j\text{ matched in }M_1\cup M_2\}\Big],$$
--   with $M_1$ independent of $\tilde D_2$ (Algorithm 1 does not look at $D_2$ when choosing $M_1$).
--
--   **Formalization Note** $x$ is a function $D_1\to S\to\mathbb R$ that vanishes off the first-stage edges. The objective is written $(1/w_j)\cdot g(\dots)$; Lean's $1/0=0$ makes a supply of weight $0$ contribute nothing, and on instances with all $w_j>0$ it is exactly the paper's program. Every minimizer and every rounding are allowed: the paper fixes neither.
-- source:
--   Y. Feng, R. Niazadeh, A. Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1 [cs.DS] (preprint, 21 Oct 2022), https://arxiv.org/abs/2210.11648v1, §3.1.1, p.12 (program 𝒫^g, sampling rule (4)); Algorithm 1, p.13

import Mathlib
import Definitions.Def_TwoStageMatch_Instance

open Finset

namespace TwoStageMatch

/-!
# The balancing program `𝒫^g` and the runs of Algorithm 1 (Weighted-Balanced-Utilization)

Feng, Niazadeh & Saberi, arXiv:2210.11648v1, §3.1.1, p.12 (the convex program `𝒫^g` and the
sampling rule (4)) and Algorithm 1, p.13.

**Formalization Note.**
* A fractional first-stage matching is `x : D₁ → S → ℝ`, with `x i j ≥ 0`, `x i j = 0` unless
  `(i, j)` is an edge of `G[D₁, S]`, `Σ_j x_{ij} ≤ 1` for every `i ∈ D₁` and `Σ_i x_{ij} ≤ 1` for
  every `j ∈ S`. Since `x` vanishes off the edges, `Σ_i x_{ij}` is the paper's `Σ_{i ∈ N(j)} x_{ij}`.
* The objective is `Σ_j (1 / w_j) · g(w_j (1 − Σ_i x_{ij}))`. In Lean `1 / 0 = 0`, so a supply of
  weight `0` contributes nothing; on instances with all `w_j > 0` this is exactly the paper's
  program, which is undefined when some `w_j = 0`.
* A *run* of Algorithm 1 for `g` is a pair `(x*, ρ)`: `x*` is an optimal solution of `𝒫^g` (step 3;
  every minimizer is allowed, the paper fixes none) and `ρ` is a probability weight on the finite
  set of first-stage matchings whose edge marginals are `x*` (step 4, equation (4); every such
  rounding is allowed). `ρ` does not depend on the second-stage realization: Algorithm 1 does
  not look at `D₂` when it picks `M₁`.
* The value of a run is `𝔼_{M₁ ∼ ρ} 𝔼_{D̃₂}[w(S₁) + Max-WeightMatch^w(D̃₂, S \ S₁)]`, i.e.
  `𝔼[Σ_j w_j 𝟙{j matched in M₁ ∪ M₂}]` with `M₂` a maximum supply-weighted matching between `D̃₂`
  and the remaining supplies (step 5), and `M₁`, `D̃₂` independent.
-/

variable {D₁ D₂ S : Type*}

/-- `x` is a feasible point of `𝒫^g` (arXiv:2210.11648v1, p.12): a fractional matching in
`G[D₁, S]`. -/
def IsFeasible [Fintype D₁] [Fintype S] (I : Instance D₁ D₂ S) (x : D₁ → S → ℝ) : Prop :=
  (∀ i j, 0 ≤ x i j) ∧
  (∀ i j, ¬ I.E (Sum.inl i) j → x i j = 0) ∧
  (∀ i, ∑ j, x i j ≤ 1) ∧
  (∀ j, ∑ i, x i j ≤ 1)

/-- The objective `Σ_{j ∈ S} (1 / w_j) g(w_j (1 − Σ_{i ∈ N(j)} x_{ij}))` of `𝒫^g`, p.12. -/
noncomputable def objective [Fintype D₁] [Fintype S] (I : Instance D₁ D₂ S) (g : ℝ → ℝ)
    (x : D₁ → S → ℝ) : ℝ :=
  ∑ j, (1 / I.w j) * g (I.w j * (1 - ∑ i, x i j))

/-- `x` is an optimal solution of `𝒫^g`: `{x*_{ij}} ∈ arg min` of p.12, i.e. `x` is feasible and
minimizes the objective over the feasible set. -/
def IsOptimal [Fintype D₁] [Fintype S] (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (x : D₁ → S → ℝ) :
    Prop :=
  IsFeasible I x ∧ IsMinOn (objective I g) {x' | IsFeasible I x'} x

/-- `ρ` is a rounding of `x` (equation (4), p.12, and Algorithm 1 step 4): a probability weight on
`Finset ((D₁ ⊕ D₂) × S)` supported on first-stage matchings, with
`Pr[(i, j) ∈ M₁] = x_{ij}` for every first-stage edge `(i, j) ∈ E`. -/
def IsRounding [Fintype D₁] [Fintype D₂] [Fintype S] [DecidableEq D₁] [DecidableEq D₂]
    [DecidableEq S] (I : Instance D₁ D₂ S) (x : D₁ → S → ℝ)
    (ρ : Finset ((D₁ ⊕ D₂) × S) → ℝ) : Prop :=
  (∀ M, 0 ≤ ρ M) ∧
  (∑ M, ρ M = 1) ∧
  (∀ M, ρ M ≠ 0 → IsFirstStageMatching I M) ∧
  (∀ i j, I.E (Sum.inl i) j →
    ∑ M ∈ (Finset.univ : Finset (Finset ((D₁ ⊕ D₂) × S))).filter (fun M => (Sum.inl i, j) ∈ M),
      ρ M = x i j)

/-- A run of Algorithm 1 (Weighted-Balanced-Utilization, p.13) for the function `g` on the
instance `I`: an optimal solution `x*` of `𝒫^g` (step 3) together with a distribution `ρ` of the
first-stage matching `M₁` with edge marginals `x*` (step 4). -/
structure Run [Fintype D₁] [Fintype D₂] [Fintype S] [DecidableEq D₁] [DecidableEq D₂]
    [DecidableEq S] (I : Instance D₁ D₂ S) (g : ℝ → ℝ) where
  /-- the optimal fractional first-stage matching `x*` -/
  x : D₁ → S → ℝ
  /-- the distribution of `M₁` -/
  ρ : Finset ((D₁ ⊕ D₂) × S) → ℝ
  x_opt : IsOptimal I g x
  ρ_rounding : IsRounding I x ρ

/-- The expected total supply weight of a run (the numerator of Definition 2, p.10):
`𝔼_{M₁ ∼ ρ} 𝔼_{D̃₂}[Σ_j w_j 𝟙{j matched in M₁} + Max-WeightMatch^w(D̃₂, S \ S₁)]`, where the
second stage takes the maximum supply-weighted matching (step 5). -/
noncomputable def Run.value [Fintype D₁] [Fintype D₂] [Fintype S] [DecidableEq D₁]
    [DecidableEq D₂] [DecidableEq S] {I : Instance D₁ D₂ S} {g : ℝ → ℝ} (r : Run I g) : ℝ :=
  ∑ M, r.ρ M * expect I (twoStageWeight I M)

end TwoStageMatch


