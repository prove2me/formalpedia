-- Prove2me | Definitions.Def_BilateralProfitLB_Construction
-- name    : BilateralProfitLB_Construction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-13T19:18:29.3632+00:00
-- url     : https://prove2.me/theorems/082b5f10-683b-4b1a-aaff-3b21daefb276
-- title:
--   §7 — the hard instances: baseline $\mathcal D_0$, bump $\rho$, perturbations $\mathcal D_j$, $h^j$ and the gap $\Delta$
-- statement:
--   The lower-bound construction of §7. The seller is uniform on $[0,1]$ in every instance. The **baseline** buyer has survival function
--   $$S_0(b)=\begin{cases}1-\tfrac83 b, & b\in[0,1/4],\\ \dfrac{1}{48b^2}, & b\in[1/4,1/2],\\ \dfrac{1-b}{12b}, & b\in[1/2,1],\end{cases}$$
--   and $Y_0=1/S_0$. The **bump** is $\rho(u)=16u^2(1-u)^2\,\mathbb 1\{u\in[0,1]\}$.
--
--   Fix an integer $K\ge1$ and let $w=1/(4K)$. The interval $[1/4,1/2]$ is split into $K$ consecutive intervals $I_j=(a_j,a_j+w)$, $a_j=1/4+(j-1)w$, $j=1,\dots,K$, with midpoints $q^\star_j=a_j+w/2$. For $j\in\{1,\dots,K\}$,
--   $$Y_j(b)=Y_0(b)-\tfrac12 w^2\rho\Big(\frac{b-a_j}{w}\Big),\qquad S_j(b)=\begin{cases}1/Y_j(b),& b\in I_j,\\ S_0(b),& b\notin I_j.\end{cases}$$
--   The buyer of $\mathcal D_j$ has density $f_j=-S_j'$ on $[0,1]$, and $\mathcal D_j$ is the law of an independent pair (uniform seller, this buyer); $\mathcal D_0$ uses $S_0$.
--
--   The expected profit of the prices $(q/2,q)$ under $\mathcal D_j$ is $h^j(q)=\mathbb E^j[\mathrm{Profit}(q/2,q)]$, and the suboptimality gap is
--   $$\Delta=\frac{w^2}{384\cdot 12}.$$
--
--   These are the instances on which every learning algorithm suffers regret $\Omega(T^{3/5})$ (Theorem 7.1).
--
--   **Formalization Note** $S_0$ is defined on all of $\mathbb R$ by extending each of its three formulas past its piece; only its values on $[0,1]$ matter, and the extension makes $-S_0'(0)$ and $-S_0'(1)$ the one-sided derivatives. The index $j$ is a natural number; $j=0$ (or $j>K$) gives the baseline. The intervals are open, so they are pairwise disjoint as the pieces of a partition are; since $S_j=S_0$ at both endpoints of $I_j$, the choice does not change $S_j$, and it gives the strongest form of Claim 3.4 (ii) and of the regret display. The law is built from the density, without asserting here that it is a probability measure; that is Claim 7.3. The printed "$\Delta=w^2/384\cdot12$" is read as $w^2/(384\cdot12)$, as in (76).
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), §7, p.50 (PDF 52), eqs. (74), (75); p.51 (PDF 53), ∆ and (76); h^j: §3.5, p.15 (PDF 17)

import Mathlib
import Definitions.Def_BilateralProfit_Model

namespace BilateralProfitLB

open MeasureTheory BilateralProfit

/-! # The hard instances of §7: the baseline `𝒟_0`, the bump `ρ`, the perturbations `𝒟_j`

Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), §7, p.50 (PDF 52):
the survival function `S_0` of (74), the bump `ρ(u) = 16u²(1 − u)² 1{u ∈ [0,1]}`, the partition
of `[1/4, 1/2]` into `I_1, …, I_K`, `w = 1/4K`, `Y_0 = 1/S_0`, `Y_j` of (75) and
`S_j = S_0` off `I_j`, `S_j = 1/Y_j` on `I_j`; p.51 (PDF 53): the expected profit
`h^j(q) = E^j[Profit(q/2, q)]` (§3.5, p.15) and the gap `∆ = w²/(384·12)`.

**Formalization Note.**
1. `S0` is given on all of `ℝ` by its three formulas, each extended beyond its piece
   (`b ≤ 1/4`, `1/4 < b ≤ 1/2`, `b > 1/2`); only its values on `[0, 1]` enter the laws, and the
   extension makes its derivative at `0` and `1` the one-sided derivative of the page.
2. `I K j = (a_j, a_j + w)` is open, `a_j = 1/4 + (j − 1) w`, `w = 1/(4K)`. The page partitions
   `[1/4, 1/2]` without fixing the endpoints of the pieces. The open interval makes the `I_j`
   pairwise disjoint, as pieces of a partition are; it does not change `S_j` (`S_j = S_0` at both
   endpoints of `I_j`); and it gives the strongest form of Claim 3.4 (ii) (more `q ∉ I_j`) and of
   the regret display (fewer rounds counted in `N_j`).
   The index `j` is a natural number: `j = 0` (or `j > K`) gives the baseline `𝒟_0`
   (`S K j = S0`), `1 ≤ j ≤ K` gives `𝒟_j`.
3. The buyer density of `𝒟_j` is `−S_j′` (`fB`); the law `law K j` of a valuation pair is the
   uniform seller on `[0,1]` times the buyer with density `fB K j` on `[0,1]`, independent. That
   it is a probability measure with survival function `S_j` and a regular instance is Claim 7.3,
   a theorem, not part of this definition.
4. `∆ = w²/384·12` (p.51) is read as `w²/(384·12)`, as (76) and p.52 write it. -/

/-- The bump `ρ(u) = 16u²(1 − u)² · 1{u ∈ [0, 1]}` (p.50). -/
noncomputable def rho (u : ℝ) : ℝ := by
  classical
  exact if u ∈ Set.Icc (0 : ℝ) 1 then 16 * u ^ 2 * (1 - u) ^ 2 else 0

/-- The baseline buyer survival function `S_0` of (74), p.50:
`1 − (8/3) b` on `[0, 1/4]`, `1/(48 b²)` on `[1/4, 1/2]`, `(1 − b)/(12 b)` on `[1/2, 1]`. -/
noncomputable def S0 (b : ℝ) : ℝ :=
  if b ≤ 1 / 4 then 1 - 8 / 3 * b else if b ≤ 1 / 2 then 1 / (48 * b ^ 2) else (1 - b) / (12 * b)

/-- `Y_0(b) = 1/S_0(b)` (p.50). -/
noncomputable def Y0 (b : ℝ) : ℝ := 1 / S0 b

/-- The width `w = 1/4K` of each sub-interval `I_j` (p.50). -/
noncomputable def w (K : ℕ) : ℝ := 1 / (4 * K)

/-- The left endpoint `a_j = 1/4 + (j − 1) w` of `I_j` (p.50). -/
noncomputable def a (K j : ℕ) : ℝ := 1 / 4 + ((j : ℝ) - 1) * w K

/-- The `j`-th of the `K` sub-intervals of the uniform partition of `[1/4, 1/2]` (p.50),
`I_j = (a_j, a_j + w)` (open; see the Formalization Note). -/
noncomputable def I (K j : ℕ) : Set ℝ := Set.Ioo (a K j) (a K j + w K)

/-- The midpoint `q⋆_j = a_j + w/2` of `I_j` (Claim 3.4 (ii)). -/
noncomputable def qstar (K j : ℕ) : ℝ := a K j + w K / 2

/-- `Y_j(b) = Y_0(b) − ½ w² ρ((b − a_j)/w)` of (75), p.50. -/
noncomputable def Y (K j : ℕ) (b : ℝ) : ℝ := Y0 b - 1 / 2 * w K ^ 2 * rho ((b - a K j) / w K)

/-- The buyer survival function `S_j` of `𝒟_j` (p.50): `S_j(b) = 1/Y_j(b)` for `b ∈ I_j` and
`S_j(b) = S_0(b)` otherwise, for `1 ≤ j ≤ K`; the baseline `S_0` for `j = 0` (and `j > K`). -/
noncomputable def S (K j : ℕ) (b : ℝ) : ℝ := by
  classical
  exact if 1 ≤ j ∧ j ≤ K ∧ b ∈ I K j then 1 / Y K j b else S0 b

/-- The buyer density `f_j = −S_j′` of `𝒟_j`. -/
noncomputable def fB (K j : ℕ) (b : ℝ) : ℝ := -deriv (S K j) b

/-- The valuation law `𝒟_j` (`𝒟_0` for `j = 0`): seller uniform on `[0, 1]`, independent of the
buyer, whose law has density `f_j` on `[0, 1]` (p.50). -/
noncomputable def law (K j : ℕ) : Measure (ℝ × ℝ) :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).prod
    ((volume.restrict (Set.Icc (0 : ℝ) 1)).withDensity fun b => ENNReal.ofReal (fB K j b))

/-- `h^j(q) = E^j[Profit(q/2, q)]`, the expected profit under `𝒟_j` of the seller price `q/2`
and the buyer price `q` (§3.5, p.15; p.51). -/
noncomputable def h (K j : ℕ) (q : ℝ) : ℝ := muP (law K j) (q / 2, q)

/-- The suboptimality gap `∆ = w²/(384·12)` (p.51, (76), p.52). -/
noncomputable def Delta (K : ℕ) : ℝ := w K ^ 2 / (384 * 12)

end BilateralProfitLB


