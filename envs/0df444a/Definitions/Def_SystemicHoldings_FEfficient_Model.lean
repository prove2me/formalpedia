-- Prove2me | Definitions.Def_SystemicHoldings_FEfficient_Model
-- name    : SystemicHoldings_FEfficient_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:39.89804+00:00
-- url     : https://prove2.me/theorems/da3bfd7c-2f19-407a-9ac3-10564da68be9
-- title:
--   §3.1–§4.1, pp. 9–14 — feasible holdings 𝒟(q, b), G = μμᵀ + Diag(σ²), MSD(Q) = (Qv)ᵀG(Qv), f-efficiency, aggregate problem (4.3), y*, Q^{N=2}, the matrix F of (EC.1.12)
-- statement:
--   This file fixes the model of Section 4 of Awiszus, Capponi and Weber. There are $K$ assets and $N$ banks. A **holding matrix** is $Q\in\mathbb R^{K\times N}$: entry $Q_{ki}$ is the initial holding of asset $k$ by bank $i$, so column $i$ is the portfolio of bank $i$. Write $\mathbf 1_K$, $\mathbf 1_N$ for the all-ones vectors.
--
--   1. **Shock moment matrix.** For the vector $\mu\in\mathbb R^K$ of mean price shocks and the vector $\sigma\in\mathbb R^K$ of their standard deviations (Assumption 2: shocks uncorrelated, $\Sigma=\mathrm{Diag}(\sigma^2)$),
--   $$G := \mu\mu^\top + \mathrm{Diag}(\sigma^2)\in\mathbb R^{K\times K}.$$
--   2. **Feasible holdings.** For the total holdings $q\in\mathbb R^K$ of the banking sector and the bank budgets $b\in\mathbb R^N$,
--   $$\mathscr D(q,b) := \{Q\in\mathbb R^{K\times N} \mid Q\mathbf 1_N = q \text{ and } \mathbf 1_K^\top Q = b^\top\}.$$
--   3. **Mean squared deviation.** For the systemic significance vector $v\in\mathbb R^N$, $\mathrm{MSD}(Q) := (Qv)^\top G (Qv)$.
--   4. **f-efficiency (Definition 1).** $Q^*$ is *f-efficient* if $Q^*\in\mathscr D(q,b)$ and $Q^*\in\operatorname{argmin}_{Q\in\mathscr D(q,b)} \mathrm{MSD}(Q)$, i.e. $\mathrm{MSD}(Q^*)\le\mathrm{MSD}(Q)$ for every $Q\in\mathscr D(q,b)$.
--   5. **Aggregate problem (4.3).** $\mathscr D_y := \{y\in\mathbb R^K \mid \mathbf 1_K^\top y = b^\top v\}$, and $y$ *solves (4.3)* if $y\in\mathscr D_y$ and $y^\top G y\le y'^\top G y'$ for all $y'\in\mathscr D_y$.
--   6. **Lemma 4.1's vectors.** $z := G^{-1}\mathbf 1_K$ and
--   $$y^* := \frac{b^\top v}{\mathbf 1_K^\top z}\, z.$$
--   7. **Assumption 3.** There are $i,j$ with $v_i\neq v_j$, and $b^\top v\neq 0$.
--   8. **The two-bank matrix of Theorem 4.1 b).** For $q,y\in\mathbb R^K$ and $v\in\mathbb R^2$,
--   $$Q^{N=2} := \frac{1}{v_2-v_1}\big(\,v_2 q - y \;\;\; y - v_1 q\,\big)\in\mathbb R^{K\times 2},$$
--   used with $y=y^*$.
--   9. **The matrix $F$ of (EC.1.12).** $F\in\mathbb R^{(2K+N)\times KN}$ acts on $\mathrm{vec}(Q)$; its rows are the $N$ budget rows ($\mathbf 1_K^\top$ on the column of bank $i$, right-hand side $b$), the $K$ supply rows ($I_K$ blocks, right-hand side $q$) and the $K$ rows $(v_1 I_K \;\cdots\; v_N I_K)$ (right-hand side $y^*$).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** All quantities are real. Assets are `Fin K`, banks are `Fin N`; the paper's banks 1 and 2 are the indices `0` and `1`. The vector $v$ is a free parameter: the paper derives it from the primitives by (3.1), but every result of Section 4 holds for each $v$ satisfying Assumption 3, and $v$ does not depend on $Q$. f-efficiency is the argmin of Definition 1, never the characterization $Qv=y^*$. $G^{-1}$ is Mathlib's `Matrix.inv`, which is $0$ for a singular matrix; every statement mentioning it assumes $\sigma_k>0$, under which $G$ is invertible. `QN2` takes $v$ as a vector of length 2; the goal transports it along $N=2$ with `Fin.cast`. `vec(Q)` is indexed by pairs (asset, bank), so no column-stacking order is fixed; $F$ is indexed accordingly by `Fin N ⊕ Fin K ⊕ Fin K` rows.
-- source:
--   Awiszus, Capponi & Weber, Market Efficient Portfolios in a Systemic Economy, arXiv:2003.10121v3, pp. 9–14, Assumption 2, (3.2), §4.1 p. 11, Definition 1 (4.2), Assumption 3, (4.3), Lemma 4.1, Theorem 4.1 b); E-Companion p. 9 (PDF 39), (EC.1.12)

import Mathlib

namespace SystemicHoldings.FEfficient
open Matrix

/-- The shock moment matrix `G = μμᵀ + Diag(σ²)` of display (3.2), p. 10. -/
noncomputable def shockMoment {K : ℕ} (μ σ : Fin K → ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  vecMulVec μ μ + diagonal (fun k => σ k ^ 2)

/-- The set of feasible holding matrices `𝒟(q, b) = {Q ∈ ℝ^{K×N} | Q 1_N = q, 1_Kᵀ Q = bᵀ}`, p. 11.
Row `k` is asset `k`, column `i` is bank `i`. -/
def feasible {K N : ℕ} (q : Fin K → ℝ) (b : Fin N → ℝ) : Set (Matrix (Fin K) (Fin N) ℝ) :=
  {Q | Q *ᵥ (fun _ => (1 : ℝ)) = q ∧ (fun _ => (1 : ℝ)) ᵥ* Q = b}

/-- The mean squared deviation `MSD(Q) = (Qv)ᵀ G (Qv)`, displays (3.2) and (4.2). -/
noncomputable def msd {K N : ℕ} (μ σ : Fin K → ℝ) (v : Fin N → ℝ)
    (Q : Matrix (Fin K) (Fin N) ℝ) : ℝ :=
  (Q *ᵥ v) ⬝ᵥ (shockMoment μ σ *ᵥ (Q *ᵥ v))

/-- Definition 1, p. 12: `Q` is f-efficient iff `Q ∈ 𝒟(q, b)` and `Q` minimizes `MSD` over `𝒟(q, b)`. -/
def IsFEfficient {K N : ℕ} (μ σ q : Fin K → ℝ) (b v : Fin N → ℝ)
    (Q : Matrix (Fin K) (Fin N) ℝ) : Prop :=
  Q ∈ feasible q b ∧ ∀ Q' ∈ feasible q b, msd μ σ v Q ≤ msd μ σ v Q'

/-- The aggregate feasible set `𝒟_y = {y ∈ ℝ^K | 1_Kᵀ y = bᵀv}`, p. 12. -/
def aggFeasible {K N : ℕ} (b v : Fin N → ℝ) : Set (Fin K → ℝ) :=
  {y | (fun _ => (1 : ℝ)) ⬝ᵥ y = b ⬝ᵥ v}

/-- `y` solves the aggregate problem (4.3), p. 12: `y ∈ 𝒟_y` minimizes `yᵀ G y` over `𝒟_y`. -/
def SolvesAggregate {K N : ℕ} (μ σ : Fin K → ℝ) (b v : Fin N → ℝ) (y : Fin K → ℝ) : Prop :=
  y ∈ aggFeasible b v ∧ ∀ y' ∈ aggFeasible b v,
    y ⬝ᵥ (shockMoment μ σ *ᵥ y) ≤ y' ⬝ᵥ (shockMoment μ σ *ᵥ y')

/-- `z = G⁻¹ 1_K`, Lemma 4.1, p. 13. -/
noncomputable def zVec {K : ℕ} (μ σ : Fin K → ℝ) : Fin K → ℝ :=
  (shockMoment μ σ)⁻¹ *ᵥ (fun _ => (1 : ℝ))

/-- `y* = (bᵀv / 1_Kᵀ z) · z`, Lemma 4.1, p. 13. -/
noncomputable def yStar {K N : ℕ} (μ σ : Fin K → ℝ) (b v : Fin N → ℝ) : Fin K → ℝ :=
  ((b ⬝ᵥ v) / ((fun _ => (1 : ℝ)) ⬝ᵥ zVec μ σ)) • zVec μ σ

/-- Assumption 3, p. 12: some `vᵢ ≠ vⱼ`, and `bᵀv ≠ 0`. -/
def Assumption3 {N : ℕ} (b v : Fin N → ℝ) : Prop :=
  (∃ i j, v i ≠ v j) ∧ b ⬝ᵥ v ≠ 0

/-- `Q^{N=2} = (1/(v₂ − v₁)) (v₂ q − y, y − v₁ q) ∈ ℝ^{K×2}`, Theorem 4.1 b), p. 14.
Banks 1 and 2 of the paper are the `Fin 2` indices `0` and `1`. -/
noncomputable def QN2 {K : ℕ} (q y : Fin K → ℝ) (v : Fin 2 → ℝ) : Matrix (Fin K) (Fin 2) ℝ :=
  Matrix.of fun k i =>
    if i = 0 then (v 1 * q k - y k) / (v 1 - v 0)
    else (y k - v 0 * q k) / (v 1 - v 0)

/-- The matrix `F ∈ ℝ^{(2K+N) × KN}` of (EC.1.12), E-Companion p. 9, acting on `vec(Q)` indexed by
(asset `k`, bank `j`). Row block `Sum.inl i` is `1_Kᵀ` on bank `i`'s column (right-hand side `b`),
row block `Sum.inr (Sum.inl k)` sums row `k` of `Q` (right-hand side `q`), and row block
`Sum.inr (Sum.inr k)` is row `k` of `Q` weighted by `v` (right-hand side `y*`). -/
def Fmat {K N : ℕ} (v : Fin N → ℝ) : Matrix (Fin N ⊕ Fin K ⊕ Fin K) (Fin K × Fin N) ℝ :=
  Matrix.of fun r c =>
    match r with
    | Sum.inl i => if c.2 = i then 1 else 0
    | Sum.inr (Sum.inl k) => if c.1 = k then 1 else 0
    | Sum.inr (Sum.inr k) => if c.1 = k then v c.2 else 0

end SystemicHoldings.FEfficient


