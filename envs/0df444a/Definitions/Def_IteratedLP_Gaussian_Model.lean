-- Prove2me | Definitions.Def_IteratedLP_Gaussian_Model
-- name    : IteratedLP_Gaussian_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:20:59.13036+00:00
-- url     : https://prove2.me/theorems/b069f860-0781-445c-952e-9cb31e88f61a
-- title:
--   The Gaussian model, ITERATED-LP (Algorithm 1), empirical trajectory laws and $W_2$
-- statement:
--   Fix a density $\alpha>0$, a number of rounds $K\ge1$ and margins $\kappa_1>\dots>\kappa_K$. For each $N\ge1$ let $M=\lfloor\alpha N\rfloor$, let $A\in\mathbb R^{M\times N}$ have i.i.d. $N(0,1/N)$ entries, and let $v_1,\dots,v_K$ be i.i.d. $N(0,I_N)$ vectors independent of $A$; the probability space for a given $N$ is the product Gaussian law on $\mathbb R^{M\times N}\times(\mathbb R^N)^K$.
--
--   **ITERATED-LP** (Algorithm 1). Set $x^{(0)}=0$ and $B_0=\emptyset$. In round $t=1,\dots,K$, let $x^{(t)}$ be an optimal solution of
--   $$\max_{x\in[-1,1]^N} v_t^\top x\quad\text{subject to}\quad Ax\ge\kappa_t\mathbf 1,\qquad x_j=x^{(t-1)}_j\ (j\in B_{t-1}),$$
--   and freeze the new signs: $B_t=\{j:|x^{(t)}_j|=1\}$, $F_t=[N]\setminus B_t$. A **run** is a sequence $x^{(1)},\dots,x^{(K)}$ in which every $x^{(t)}$ is such an optimal solution; every choice of optimizers produces a run.
--
--   With $u^{(t)}=Ax^{(t)}$, the **empirical laws** of the coordinate and margin trajectories are
--   $$\hat\mu^{\mathrm{col}}_{N,t}=\frac1N\sum_{j=1}^N\delta_{x_j^{(1:t)}},\qquad \hat\mu^{\mathrm{row}}_{N,t}=\frac1M\sum_{i=1}^M\delta_{u_i^{(1:t)}}$$
--   on $\mathbb R^t$. The **quadratic Wasserstein distance** is $W_2(\mu,\nu)^2=\inf\mathbb E\|X-Y\|^2$ over all couplings of $X\sim\mu$, $Y\sim\nu$, with $\|\cdot\|$ the Euclidean norm.
--
--   The **failure event** at size $N$ for target values $q_t$ and target laws $\mu^{\mathrm{col}}_t,\mu^{\mathrm{row}}_t$ and a tolerance $\varepsilon$ is: ITERATED-LP is undefined (some round is infeasible), or some run and some $1\le t\le K$ have $W_2(\hat\mu^{\mathrm{col}}_{N,t},\mu^{\mathrm{col}}_t)>\varepsilon$, or $W_2(\hat\mu^{\mathrm{row}}_{N,t},\mu^{\mathrm{row}}_t)>\varepsilon$, or $\big||B_t|/N-(1-q_t)\big|>\varepsilon$.
--
--   These objects are the setting of Theorem 1.1.
--
--   **Formalization Note.** `RVec t` is `EuclideanSpace ℝ (Fin t)`, so norms are Euclidean. Rounds are 0-based in `Fin K` (`κ t` is $\kappa_{t+1}$); `prevIter` gives $x^{(0)}=0$ before the first round, and since no coordinate of $0$ has absolute value $1$, $B_0=\emptyset$. `W2sq` is the published `RWPI_SqrtLasso_transportCost` with cost $\|x-y\|^2$ (an `ENNReal` infimum over probability couplings with the given marginals), and `W2 = W2sq^{1/2}`. The empirical laws use the weights $1/N$ and $1/M$ in `ENNReal`; when $M=0$ (finitely many $N$, as $\alpha>0$) the row law is the zero measure, its $W_2$ distance to a probability law is $\infty$, and the failure event holds. The matrix law uses the variance argument $(N:\mathbb R_{\ge0})^{-1}$ of `gaussianReal`.
-- source:
--   Zhang, Li, State Evolution and Universality of Iterated Linear Programs for the Binary Perceptron, arXiv:2611.04294v1, p. 3, Algorithm 1; p. 4, §1.4 (model and empirical laws); p. 8, §1.6 (W₂); p. 15, §4.1

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost

open MeasureTheory ProbabilityTheory

namespace IteratedLP.Gaussian

/-- `ℝ^p` with its Euclidean norm (trajectories, histories, laws live here). -/
abbrev RVec (p : ℕ) : Type := EuclideanSpace ℝ (Fin p)

/-- The number of rows `M = ⌊α N⌋` (p. 4). -/
noncomputable def numRows (α : ℝ) (N : ℕ) : ℕ := ⌊α * N⌋₊

/-- The squared quadratic Wasserstein distance `W₂(μ, ν)² = inf E‖X - Y‖²` over all couplings
(§1.6, p. 8), with respect to the norm of `V` (the Euclidean norm on `RVec t`): the published
optimal transport cost `RWPI.SqrtLasso.transportCost` with cost `‖x - y‖²`. -/
noncomputable def W2sq {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V]
    (μ ν : Measure V) : ENNReal :=
  RWPI.SqrtLasso.transportCost (fun x y => ENNReal.ofReal (‖x - y‖ ^ 2)) μ ν

/-- The quadratic Wasserstein distance `W₂(μ, ν) = (W₂(μ, ν)²)^{1/2}`, valued in `[0, ∞]`. -/
noncomputable def W2 {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V]
    (μ ν : Measure V) : ENNReal :=
  W2sq μ ν ^ ((1 : ℝ) / 2)

/-- The standard Gaussian vector `N(0, I_N)` on `ℝ^N` (coordinates i.i.d. `N(0,1)`). -/
noncomputable def stdGaussVec (N : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi (fun _ : Fin N => gaussianReal 0 1)

/-- The law of the matrix `A ∈ ℝ^{M×N}` with `A_ij` i.i.d. `N(0, 1/N)` (Theorem 1.1). -/
noncomputable def gaussMatrixLaw (M N : ℕ) : Measure (Fin M → Fin N → ℝ) :=
  Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin N => gaussianReal 0 ((N : NNReal)⁻¹)))

/-- The law of the objective vectors `v_1, …, v_K` i.i.d. `N(0, I_N)` (Algorithm 1, step 1). -/
noncomputable def objectiveLaw (K N : ℕ) : Measure (Fin K → Fin N → ℝ) :=
  Measure.pi (fun _ : Fin K => stdGaussVec N)

/-- The probability space for a given `N`: `A` and `(v_1, …, v_K)` independent, with the laws
above. -/
noncomputable def modelLaw (M N K : ℕ) :
    Measure ((Fin M → Fin N → ℝ) × (Fin K → Fin N → ℝ)) :=
  (gaussMatrixLaw M N).prod (objectiveLaw K N)

/-- Feasible set of one round of ITERATED-LP (Algorithm 1, step 2): `x ∈ [-1,1]^N`,
`A x ≥ κ 1`, and `x_j = xprev_j` for every coordinate `j` frozen by the previous iterate, i.e.
`j ∈ B_{t-1} = {j : |xprev_j| = 1}`. -/
def feasibleSet {M N : ℕ} (A : Fin M → Fin N → ℝ) (κ : ℝ) (xprev : Fin N → ℝ) :
    Set (Fin N → ℝ) :=
  {x | (∀ j, |x j| ≤ 1) ∧ (∀ i, κ ≤ ∑ j, A i j * x j) ∧ ∀ j, |xprev j| = 1 → x j = xprev j}

/-- Optimal solutions of the round LP `max v⊤x` over `feasibleSet A κ xprev`. -/
def optSet {M N : ℕ} (A : Fin M → Fin N → ℝ) (v : Fin N → ℝ) (κ : ℝ) (xprev : Fin N → ℝ) :
    Set (Fin N → ℝ) :=
  {x | x ∈ feasibleSet A κ xprev ∧
    ∀ y ∈ feasibleSet A κ xprev, ∑ j, v j * y j ≤ ∑ j, v j * x j}

/-- The iterate entering round `t` (0-based index `t : Fin K` = round `t + 1`):
`x^{(0)} = 0` for the first round, `x^{(t)}` afterwards. Since no coordinate of `0` has absolute
value `1`, the first round has `B_0 = ∅`. -/
def prevIter {K N : ℕ} (x : Fin K → Fin N → ℝ) (t : Fin K) : Fin N → ℝ :=
  if h : (t : ℕ) = 0 then 0 else x ⟨(t : ℕ) - 1, by omega⟩

/-- A run of ITERATED-LP (Algorithm 1) for one choice of optimizers: `x t` (0-based) is an
optimal solution of round `t + 1`, with objective `v t`, margin `κ t`, and the coordinates frozen
by the previous iterate held fixed. Every selection of LP optimizers produces such a run, and
every such run arises from a selection. -/
def IsRun {M N K : ℕ} (A : Fin M → Fin N → ℝ) (v : Fin K → Fin N → ℝ) (κ : Fin K → ℝ)
    (x : Fin K → Fin N → ℝ) : Prop :=
  ∀ t : Fin K, x t ∈ optSet A (v t) (κ t) (prevIter x t)

open scoped Classical in
/-- The frozen set `B = {j : |x_j| = 1}` of an iterate (Algorithm 1, step 3). -/
noncomputable def frozen {N : ℕ} (x : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun j => |x j| = 1)

/-- The coordinate trajectory `x_j^{(1:t)} = (x_j^{(1)}, …, x_j^{(t)}) ∈ ℝ^t`. -/
def colTraj {N K : ℕ} (x : Fin K → Fin N → ℝ) (t : ℕ) (ht : t ≤ K) (j : Fin N) : RVec t :=
  WithLp.toLp 2 (fun s : Fin t => x (Fin.castLE ht s) j)

/-- The margin trajectory `u_i^{(1:t)}` with `u^{(s)} = A x^{(s)}`. -/
def rowTraj {M N K : ℕ} (A : Fin M → Fin N → ℝ) (x : Fin K → Fin N → ℝ) (t : ℕ) (ht : t ≤ K)
    (i : Fin M) : RVec t :=
  WithLp.toLp 2 (fun s : Fin t => ∑ j, A i j * x (Fin.castLE ht s) j)

/-- The empirical law `μ̂^col_{N,t} = (1/N) Σ_j δ_{x_j^{(1:t)}}` of the coordinate trajectories
(p. 4). -/
noncomputable def empColLaw {N K : ℕ} (x : Fin K → Fin N → ℝ) (t : ℕ) (ht : t ≤ K) :
    Measure (RVec t) :=
  (N : ENNReal)⁻¹ • ∑ j : Fin N, Measure.dirac (colTraj x t ht j)

/-- The empirical law `μ̂^row_{N,t} = (1/M) Σ_i δ_{u_i^{(1:t)}}` of the margin trajectories
(p. 4). For `M = 0` it is the zero measure (no coupling with a probability law exists, so its
`W₂` distance to one is `∞`). -/
noncomputable def empRowLaw {M N K : ℕ} (A : Fin M → Fin N → ℝ) (x : Fin K → Fin N → ℝ)
    (t : ℕ) (ht : t ≤ K) : Measure (RVec t) :=
  (M : ENNReal)⁻¹ • ∑ i : Fin M, Measure.dirac (rowTraj A x t ht i)

/-- The failure event of Theorem 1.1 at size `N`, for target limits `q t`, `μcol t`, `μrow t`
and tolerance `ε`: either ITERATED-LP is undefined (no run exists: some round is infeasible), or
some run (some choice of optimizers) has, for some round `1 ≤ t ≤ K`,
`W₂(μ̂^col_{N,t}, μcol t) > ε`, or `W₂(μ̂^row_{N,t}, μrow t) > ε`, or `||B_t|/N - (1 - q t)| > ε`. -/
def deviationEvent (α : ℝ) (K : ℕ) (κ : Fin K → ℝ) (q : ℕ → ℝ)
    (μcol μrow : (t : ℕ) → Measure (RVec t)) (ε : ℝ) (N : ℕ) :
    Set ((Fin (numRows α N) → Fin N → ℝ) × (Fin K → Fin N → ℝ)) :=
  {ω | (¬ ∃ x, IsRun ω.1 ω.2 κ x) ∨
    ∃ x, IsRun ω.1 ω.2 κ x ∧ ∃ t : ℕ, ∃ h1 : 1 ≤ t, ∃ ht : t ≤ K,
      ENNReal.ofReal ε < W2 (empColLaw x t ht) (μcol t) ∨
      ENNReal.ofReal ε < W2 (empRowLaw ω.1 x t ht) (μrow t) ∨
      ε < |((frozen (x ⟨t - 1, by omega⟩)).card : ℝ) / N - (1 - q t)|}

end IteratedLP.Gaussian


