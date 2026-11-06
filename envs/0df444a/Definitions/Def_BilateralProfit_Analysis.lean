-- Prove2me | Definitions.Def_BilateralProfit_Analysis
-- name    : BilateralProfit_Analysis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:06.246732+00:00
-- url     : https://prove2.me/theorems/feb1fdeb-4215-4117-8147-3aacc3eb3f69
-- title:
--   §4.2.1 — the gap $\Delta_\rho$, the information $\mathcal I_\rho$, the optimal action $a^\star$ and the trade functions $P_a$, $P_0$ of a table $\rho$ on $G_K\times\mathcal A$
-- statement:
--   Let $\rho$ be a probability distribution on $G_K\times\mathcal A$ and $(V,A)\sim\rho$ (a valuation and an action). For $a\in\mathcal A$:
--
--   1. the **expected gap** $\Delta_\rho(a)=\mathbb E_\rho[\mathrm{Profit}(V,A)-\mathrm{Profit}(V,a)]$ (eq. (9));
--   2. the **pairwise gap** $\Delta_\rho(a',a)=\mathbb E_\rho[\mathrm{Profit}(V,a')-\mathrm{Profit}(V,a)]$, which depends only on the valuation marginal of $\rho$;
--   3. the **mutual information** between $A$ and the feedback $z_a(V)$,
--   $$\mathcal I_\rho(a)=\sum_{a'\in\mathcal A}\sum_{z\in\{0,1\}}\mathbb P_\rho(A=a',z_a(V)=z)\log\frac{\mathbb P_\rho(A=a',z_a(V)=z)}{\mathbb P_\rho(A=a')\,\mathbb P_\rho(z_a(V)=z)};$$
--   4. an **optimal fixed action** $a^\star$ maximizes $\mathbb E_\rho[\mathrm{Profit}(V,a)]$ over $\mathcal A$, and $\Delta_\rho(a^\star,a)$ is its gap to $a$;
--   5. the trade functions $P_a(v)=\mathbb P_\rho(V\in[0,s]\times[b,1]\mid A=a)$ (eq. (10)) and $P_0(v)=\sum_a\mathbb P_\rho(A=a)P_a(v)=\mathbb P_\rho(V\in[0,s]\times[b,1])$ (eq. (11)), evaluated at any point $v=(s,b)$;
--   6. the parameter $\beta=K^2\log^6K$.
--
--   **Formalization Note** $\rho$ is a real function on $G_K\times\mathcal A$. $\mathbb E_\rho[\mathrm{Profit}(V,a^\star)]$ is the maximum over the finite nonempty set $\mathcal A$, so $\Delta_\rho(a^\star,\cdot)$ does not depend on which maximizer is chosen. In $\mathcal I_\rho$ a term with zero joint probability is $0$ ($0\log0=0$). The conditional $P_{a'}$ is set to $0$ when $\mathbb P_\rho(A=a')=0$; it only appears multiplied by $\mathbb P_\rho(A=a')$. Logarithms are natural.
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), §4.2.1, p.19 (PDF 21), eqs. (9), (10), (11); β: §4.1, p.17 (PDF 19)

import Mathlib
import Definitions.Def_BilateralProfit_Model

namespace BilateralProfit

/-! # Analysis objects of a table `ρ` on `G_K × 𝒜`

Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), §4.2.1, p.19 (PDF 21):
the gap `Δ_ρ(a)` (9), the pairwise gap `Δ_ρ(a′, a)`, the mutual information `ℐ_ρ(a)`, the
optimal fixed action `a⋆`, and the trade functions `P_a` (10) and `P0` (11).

**Formalization Note.** A distribution `ρ` over `G_K × 𝒜` is a function
`Grid K × Act K → ℝ`; statements assume `IsDist ρ`. `(V, A) ∼ ρ`. The value `E_ρ[Profit(V, a⋆)]`
of an optimal fixed action is the maximum `optVal` of the (finitely many) marginal expected
profits, and `Δ_ρ(a⋆, a) = optVal ρ − E_ρ[Profit(V, a)]`; it does not depend on which maximizer
`a⋆` is chosen. In `ℐ_ρ`, a term with `P_ρ(A = a′, z_a(V) = z) = 0` is `0 · log(…) = 0`, the
`0 log 0 = 0` convention; every other term has positive denominators. The conditional trade
function `P_{a′}` uses Lean's `x / 0 = 0` when `P_ρ(A = a′) = 0`; it only ever appears
multiplied by `P_ρ(A = a′)`. -/

variable {K : ℕ}

/-- The marginal `P_ρ(A = a′)`. -/
noncomputable def margA (ρ : Grid K × Act K → ℝ) (a' : Act K) : ℝ := ∑ v, ρ (v, a')

/-- `P_ρ(A = a′, z_a(V) = z)` for the bit `z ∈ {0, 1}` encoded as `Bool` (`true` = trade). -/
noncomputable def jointP (ρ : Grid K × Act K → ℝ) (a a' : Act K) (z : Bool) : ℝ := by
  classical exact ∑ v, if (Trades (pt K v) (pt K a.1) ↔ z = true) then ρ (v, a') else 0

/-- `P_ρ(z_a(V) = z)`. -/
noncomputable def zP (ρ : Grid K × Act K → ℝ) (a : Act K) (z : Bool) : ℝ :=
  ∑ a', jointP ρ a a' z

/-- The mutual information between `A` and the feedback `z_a(V)` under `ρ` (p.19):
`ℐ_ρ(a) = Σ_{a′} Σ_z P(A = a′, z_a(V) = z) log [P(A = a′, z_a(V) = z) / (P(A = a′) P(z_a(V) = z))]`
(natural logarithm). -/
noncomputable def info (ρ : Grid K × Act K → ℝ) (a : Act K) : ℝ :=
  ∑ a', ∑ z : Bool, jointP ρ a a' z * Real.log (jointP ρ a a' z / (margA ρ a' * zP ρ a z))

/-- The expected gap `Δ_ρ(a) = E_ρ[Profit(V, A) − Profit(V, a)]` (9). -/
noncomputable def gap (ρ : Grid K × Act K → ℝ) (a : Act K) : ℝ :=
  ∑ x, ρ x * (profit (pt K x.1) (pt K x.2.1) - profit (pt K x.1) (pt K a.1))

/-- `E_ρ[Profit(V, x)]` for a price pair `x ∈ ℝ²`, `V` distributed by the valuation marginal
of `ρ`. -/
noncomputable def valProfitPt (ρ : Grid K × Act K → ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑ y, ρ y * profit (pt K y.1) x

/-- `E_ρ[Profit(V, a)]` for an action `a ∈ 𝒜`. -/
noncomputable def valProfit (ρ : Grid K × Act K → ℝ) (a : Act K) : ℝ :=
  valProfitPt ρ (pt K a.1)

/-- `Δ_ρ(a′, a) = E_ρ[Profit(V, a′) − Profit(V, a)]` (p.19). -/
noncomputable def gapPair (ρ : Grid K × Act K → ℝ) (a' a : Act K) : ℝ :=
  valProfit ρ a' - valProfit ρ a

/-- `E_ρ[Profit(V, a⋆)]`, the value of an optimal fixed action `a⋆ ∈ 𝒜` under the valuation
marginal of `ρ`: the maximum over the finite nonempty set `𝒜`. -/
noncomputable def optVal (ρ : Grid K × Act K → ℝ) : ℝ := ⨆ a : Act K, valProfit ρ a

/-- `Δ_ρ(a⋆, x) = E_ρ[Profit(V, a⋆)] − E_ρ[Profit(V, x)]` for a price pair `x`. -/
noncomputable def gapStarPt (ρ : Grid K × Act K → ℝ) (x : ℝ × ℝ) : ℝ :=
  optVal ρ - valProfitPt ρ x

/-- `Δ_ρ(a⋆, a)` for an action `a ∈ 𝒜`. -/
noncomputable def gapStar (ρ : Grid K × Act K → ℝ) (a : Act K) : ℝ :=
  gapStarPt ρ (pt K a.1)

/-- The marginal trade function `P0(x) = P_ρ(V ∈ [0, s] × [b, 1])` at `x = (s, b)` (11), i.e.
the probability that the valuation `V ∼ ρ` trades at price pair `x`. -/
noncomputable def P0 (ρ : Grid K × Act K → ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑ y, ρ y * tradeBit (pt K y.1) x

/-- The conditional trade function `P_{a′}(x) = P_ρ(V ∈ [0, s] × [b, 1] | A = a′)` (10). -/
noncomputable def Pcond (ρ : Grid K × Act K → ℝ) (a' : Act K) (x : ℝ × ℝ) : ℝ :=
  (∑ v, ρ (v, a') * tradeBit (pt K v) x) / margA ρ a'

/-- `β = K² log⁶ K` (p.17), natural logarithm. -/
noncomputable def beta (K : ℕ) : ℝ := (K : ℝ) ^ 2 * Real.log K ^ 6

end BilateralProfit


