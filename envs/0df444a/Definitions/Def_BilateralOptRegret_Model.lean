-- Prove2me | Definitions.Def_BilateralOptRegret_Model
-- name    : BilateralOptRegret_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:38:43.917819+00:00
-- url     : https://prove2.me/theorems/f16aa934-07c7-408f-8be9-44d50f6f025b
-- title:
--   §2 — CDF, profit, the grid $\mathcal X_K$, $\mathrm{OPT}$, $\mathrm{gap}$ and one-bit observations
-- statement:
--   Let $L$ be the law on $[0,1]^2$ of the transformed valuation $X=(S,1-B)$, where $S$ is the seller's and $B$ the buyer's valuation. An action is $x=(p,1-q)$ for a purchase price $p$ and a sale price $q$, and trade occurs exactly when $X\le x$ coordinatewise. The **CDF** is $F(x)=\mathbb P_{X\sim L}(X\le x)$ and the **expected profit** is
--   $$r(x)=(1-x_1-x_2)\,F(x).$$
--   For $K\ge 2$ the **grid** is $z_i=i/(K-1)$, $i=0,\dots,K-1$, and $\mathcal X_K=\{x_{i,j}=(z_i,z_j)\}$, with $i$ the column and $j$ the row. Further,
--   $$\mathrm{OPT}=\max_{x\in\mathcal X_K}r(x),\qquad \mathrm{gap}(x)=\mathrm{OPT}-r(x),\qquad D_j(i,i')=F(x_{i,j})-F(x_{i',j}).$$
--   An observation at $x$ is the bit $\mathbb 1\{X\le x\}$ for a fresh $X\sim L$, a Bernoulli variable of mean $F(x)$. Given estimates $\hat F$, the estimated profit is $\hat r(x)=(1-x_1-x_2)\hat F(x)$.
--
--   These objects underlie every statement of the mission. The paper's standing grid has $K=2^n+1$, so that $\ell_K=\log_2(K-1)+1=n+1$ is an integer.
--
--   **Formalization Note** The law is a `BilateralProfit.IsValLaw`: a probability measure carried by $[0,1]^2$, with no independence or density condition. Grid points are index pairs in `Fin K × Fin K`. The paper's "choose" is modelled by a selection rule `IsSel`.
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), §2.1–§2.2, pp.12–13

import Mathlib
import Definitions.Def_BilateralProfit_Model

namespace BilateralOptRegret

open MeasureTheory

/-! # The learning model in `X`-coordinates, the grid, `OPT` and `gap`

Castiglioni, Lunghi, Marchesi, *Optimal Regret for Profit Maximization in Bilateral Trade*
(manuscript, sha256 aafed174…), §2.1, pp.12–13, and §2.2, p.13.

**Formalization Note.** As on p.13 we work with `X_t = (S_t, 1 − B_t)` and `x_t = (p_t, 1 − q_t)`, so
trade means `X_t ≤ x_t` coordinatewise (`Prod.le`). A law `L` of `X_t` is a
`BilateralProfit.IsValLaw`: a probability measure carried by `[0,1]²`, with no other condition (joint
law, atoms and correlation allowed). The grid is indexed by `Fin K × Fin K`: the index `(i, j)` is
`x_{i,j} = (z_i, z_j)`, `z_i = i/(K − 1)`; `i` is the column and `j` the row. `Kof n = 2^n + 1` is the
paper's standing `K` with `K − 1` a power of two (p.13), and `ell n = n + 1` is `ℓ_K = log₂(K − 1) + 1`.
`opt` is a supremum over the finite nonempty type `Grid K` for `K ≥ 1`, hence a maximum. A
choice ("choose one such `u`", "choose `x⋆ ∈ argmax`") is a selection rule `IsSel`. -/

/-- The CDF `F(x) = P_{X∼L}(X ≤ x)` (p.13). -/
noncomputable def F (L : Measure (ℝ × ℝ)) (x : ℝ × ℝ) : ℝ := (L {y | y ≤ x}).toReal

/-- The expected profit `r(x) = (1 − x₁ − x₂) F(x)` (p.13). -/
noncomputable def r (L : Measure (ℝ × ℝ)) (x : ℝ × ℝ) : ℝ := (1 - x.1 - x.2) * F L x

/-- Grid indices `(i, j)`, `i, j ∈ {0, …, K − 1}`, of `X_K` (p.13). -/
abbrev Grid (K : ℕ) : Type := Fin K × Fin K

/-- `z_i = i/(K − 1)` (p.13). -/
noncomputable def z (K : ℕ) (i : Fin K) : ℝ := ((i : ℕ) : ℝ) / ((K : ℝ) - 1)

/-- The grid point `x_{i,j} = (z_i, z_j)` (p.13). -/
noncomputable def pt (K : ℕ) (q : Grid K) : ℝ × ℝ := (z K q.1, z K q.2)

/-- `OPT = max_{x ∈ X_K} r(x)` (p.13). -/
noncomputable def opt (L : Measure (ℝ × ℝ)) (K : ℕ) : ℝ := ⨆ q : Grid K, r L (pt K q)

/-- `gap(x) = OPT − r(x)` for `x ∈ X_K` (p.13). -/
noncomputable def gap (L : Measure (ℝ × ℝ)) (K : ℕ) (q : Grid K) : ℝ := opt L K - r L (pt K q)

/-- The same-row CDF difference `D_j(i, i′) = F(x_{i,j}) − F(x_{i′,j})` (p.13). `P_{a,b}(w)` of p.22 is
`rowDiff L K w b a`. -/
noncomputable def rowDiff (L : Measure (ℝ × ℝ)) (K : ℕ) (j i i' : Fin K) : ℝ :=
  F L (pt K (i, j)) - F L (pt K (i', j))

/-- The half-open rectangle `(z_a, z_b] × (z_{w₁}, z_{w₂}]` of (13), p.24, and of (11), p.22. -/
noncomputable def region (K : ℕ) (a b w₁ w₂ : Fin K) : Set (ℝ × ℝ) :=
  Set.Ioc (z K a) (z K b) ×ˢ Set.Ioc (z K w₁) (z K w₂)

/-- The estimated profit `r̂(x) = (1 − x₁ − x₂) F̂(x)` (p.26). -/
noncomputable def rhat {K : ℕ} (Fhat : Grid K → ℝ) (q : Grid K) : ℝ :=
  (1 - (pt K q).1 - (pt K q).2) * Fhat q

/-- A selection rule: it returns an element of every nonempty finite set. This is how the paper's
"choose" is read: each statement holds for every such rule. -/
def IsSel {α : Type} (s : Finset α → α) : Prop := ∀ t : Finset α, t.Nonempty → s t ∈ t

/-- The law of a one-bit observation with mean `p`: `1` (trade) with probability `p`, else `0`. -/
noncomputable def bitLaw (p : ℝ) : Measure ℝ :=
  ENNReal.ofReal p • Measure.dirac 1 + ENNReal.ofReal (1 - p) • Measure.dirac 0

/-- The observation at the grid action `q`: `Y = 1{X ≤ x_q}` for a fresh `X ∼ L`, so a Bernoulli of
mean `F(x_q)`, independent of everything before it (p.13). This is the argument `obs` of
`BilateralProfit.QTree.prob`; every observation of `q` has the same law. -/
noncomputable def obsLaw (L : Measure (ℝ × ℝ)) (K : ℕ) : Grid K → ℕ → Measure ℝ :=
  fun q _ => bitLaw (F L (pt K q))

/-- `K = 2^n + 1`, so `K − 1` is a power of two (p.13). -/
abbrev Kof (n : ℕ) : ℕ := 2 ^ n + 1

/-- Column and row indices `{0, …, K − 1}` for `K = 2^n + 1`. -/
abbrev Idx (n : ℕ) : Type := Fin (Kof n)

/-- Grid indices for `K = 2^n + 1`. -/
abbrev Act (n : ℕ) : Type := Grid (Kof n)

/-- `ℓ_K = log₂(K − 1) + 1 = n + 1` for `K = 2^n + 1` (p.13). -/
abbrev ell (n : ℕ) : ℕ := n + 1

end BilateralOptRegret


