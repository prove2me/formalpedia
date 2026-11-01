-- Prove2me | Definitions.Def_TaylorInv_Quantities
-- name    : TaylorInv_Quantities
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:30:53.122784+00:00
-- url     : https://prove2.me/theorems/2f382a46-3821-45b5-a374-db3fb4f43dcb
-- title:
--   Base stocks, Taylor coefficients and costs: $s_j^l$, $r_j$, $\tilde s_j^e$, $m_j$, $p_j$, $t_j$, $\alpha$, $C_j$ and the period cost (2)
-- statement:
--   Given the features $x$ (an outcome $\omega$), write $\mu_j(x)=\gamma_j+\sum_p\beta_{jp}x_{jp}$ and let
--   $$
--   F_j(z\mid x_j)=\int_{-\infty}^{z-\mu_j(x)}f_j(e)\,de ,\qquad F_{\epsilon_j}(e)=\int_{-\infty}^{e}f_j .
--   $$
--   The **local base stock** is the critical-fractile quantile (7)
--   $$
--   s_j^l(x_j)=F_j^{-1}\Big(\frac{b_j}{b_j+h'_j}\,\Big|\,x_j\Big)=\inf\Big\{z:\ \frac{b_j}{b_j+h'_j}\le F_j(z\mid x_j)\Big\},
--   $$
--   and $F_{\epsilon_j}^{-1}(b_j/(b_j+h'_j))$ is the noise quantile. With $f_j(s_j^l\mid x_j)=f_j(s_j^l-\mu_j(x))$ the paper defines (p.12, p.OA3)
--   $$
--   r_j=\frac1{(b_j+h'_j)f_j(s_j^l\mid x_j)},\quad \tilde s_j^e=s_j^l+h_0r_j,\quad m_j=\frac{\tilde s_j^e}{r_j},\quad \underline m=\min_j m_j,
--   $$
--   $$
--   p_j=\frac1{(b_j+h'_j)u_j},\quad t_j=\frac1{(b_j+h'_j)\ell_j},\quad \alpha=\max_j\frac{u_j}{\ell_j},\quad \underline p=\min_jp_j,\ \underline t=\min_jt_j,\ \bar t=\max_jt_j,\ \underline h=\min_jh'_j .
--   $$
--   The retailer cost (4) is $C_j(z\mid x_j)=\mathbb E_{\epsilon_j}[-h_0D_j+(h'_j-h_0)(z-D_j)+(b_j+h'_j)(D_j-z)^+\mid x_j]$, the newsvendor cost is $N_j(z\mid x)=\mathbb E_{\epsilon_j}[h'_j(z-D_j)^++b_j(D_j-z)^+\mid x_j]$, and the **period cost** (2) of an order $z_0$ and an allocation $z$ is
--   $$
--   h_0\Big(z_0-\sum_{j=1}^Jz_j\Big)+\sum_{j=1}^JN_j(z_j\mid x).
--   $$
--   The feasible allocations of $z_0$ are $\{z:\ z_j\ge0,\ \sum_jz_j\le z_0\}$.
--
--   These are the quantities in which the TA policy and its analysis are written.
--
--   **Formalization Note** Minima and maxima over retailers are `⨅`/`⨆` over `Fin J` (value $0$ when $J=0$). The quantile is the lower quantile `sInf`. The period cost (2) equals (3)–(4) with the term $-h_0D_j$ kept, i.e. before the paper omits it.
-- source:
--   Huang, Shang, Yang & Zhou, Taylor Approximation of Inventory Policies for One-Warehouse, Multi-Retailer Systems with Demand Feature Information, SSRN 3993516 (Jan 29 2023), https://ssrn.com/abstract=3993516, (2)–(4), p.8; (7), p.9; p.12; (18), p.14; p.15; p.OA3; (A16), (A21), (A25), pp.OA7–OA9

import Mathlib
import Definitions.Def_TaylorInv_Model

open MeasureTheory

namespace TaylorInv

namespace Model

variable {J P : ℕ} {Ω : Type*} (M : Model J P Ω)

/-- The feature-driven mean shift `γ_j + ∑_p β_jp x_jp` of retailer `j`'s demand
(Huang, Shang, Yang & Zhou, SSRN 3993516 (Jan 29 2023), Assumption 1, p.14). -/
noncomputable def meanShift (j : Fin J) (ω : Ω) : ℝ :=
  M.γ j + ∑ p, M.β j p * M.X j p ω

/-- The CDF `F_{ϵ_j}(e) = ∫_{-∞}^e f_j` of the noise `ϵ_j` (Huang et al., SSRN 3993516, (18), p.14). -/
noncomputable def noiseCDF (j : Fin J) (e : ℝ) : ℝ :=
  ∫ x in Set.Iic e, M.f j x

/-- The conditional CDF `F_j(z | x_j) = ℙ(D_j ≤ z | x_j) = F_{ϵ_j}(z − γ_j − ∑_p β_jp x_jp)` of
demand (Huang et al., SSRN 3993516, (7), p.9, and Assumption 2, p.14). -/
noncomputable def condCDF (j : Fin J) (ω : Ω) (z : ℝ) : ℝ :=
  ∫ x in Set.Iic (z - M.meanShift j ω), M.f j x

/-- The critical fractile `b_j / (b_j + h′_j)` (Huang et al., SSRN 3993516, (7), p.9). -/
noncomputable def critFrac (j : Fin J) : ℝ :=
  M.b j / (M.b j + M.h' j)

/-- The local base-stock level `s_j^l(x_j) = F_j^{-1}(b_j/(b_j + h′_j) | x_j)` (Huang et al.,
SSRN 3993516, (7), p.9).

**Formalization Note** The inverse is the lower quantile `inf {z | c ≤ F_j(z | x_j)}`. -/
noncomputable def baseStock (j : Fin J) (ω : Ω) : ℝ :=
  sInf {z : ℝ | M.critFrac j ≤ M.condCDF j ω z}

/-- The noise quantile `F_{ϵ_j}^{-1}(b_j/(b_j + h′_j))` (Huang et al., SSRN 3993516, (18), p.14),
as the lower quantile. -/
noncomputable def noiseQuantile (j : Fin J) : ℝ :=
  sInf {e : ℝ | M.critFrac j ≤ M.noiseCDF j e}

/-- The conditional density of demand at the local base stock, `f_j(s_j^l | x_j)`
(Huang et al., SSRN 3993516, p.12); the demand density is the noise density shifted by the mean. -/
noncomputable def densAtBase (j : Fin J) (ω : Ω) : ℝ :=
  M.f j (M.baseStock j ω - M.meanShift j ω)

/-- `r_j = 1 / ((b_j + h′_j) f_j(s_j^l | x_j))` (Huang et al., SSRN 3993516, p.12). -/
noncomputable def r (j : Fin J) (ω : Ω) : ℝ :=
  1 / ((M.b j + M.h' j) * M.densAtBase j ω)

/-- The approximate echelon base stock `s̃_j^e = s_j^l + h₀ · r_j` (Huang et al., SSRN 3993516,
p.12). -/
noncomputable def sEch (j : Fin J) (ω : Ω) : ℝ :=
  M.baseStock j ω + M.h₀ * M.r j ω

/-- `m_j = s̃_j^e / r_j` (Huang et al., SSRN 3993516, p.12). -/
noncomputable def m (j : Fin J) (ω : Ω) : ℝ :=
  M.sEch j ω / M.r j ω

/-- `m̲ = min_j m_j` (Huang et al., SSRN 3993516, p.12). For `J = 0` the value is `0`. -/
noncomputable def mMin (ω : Ω) : ℝ :=
  ⨅ j, M.m j ω

/-- `p_j = 1 / ((b_j + h′_j) u_j)` (Huang et al., SSRN 3993516, p.OA3). -/
noncomputable def pc (j : Fin J) : ℝ :=
  1 / ((M.b j + M.h' j) * M.u j)

/-- `t_j = 1 / ((b_j + h′_j) ℓ_j)` (Huang et al., SSRN 3993516, p.15 and p.OA3). -/
noncomputable def tc (j : Fin J) : ℝ :=
  1 / ((M.b j + M.h' j) * M.ℓ j)

/-- `α = max_j u_j / ℓ_j` (Huang et al., SSRN 3993516, Proposition 3, p.15, and p.OA3). -/
noncomputable def α : ℝ :=
  ⨆ j, M.u j / M.ℓ j

/-- `p̲ = min_j p_j` (Huang et al., SSRN 3993516, (A16), p.OA7). -/
noncomputable def pMin : ℝ :=
  ⨅ j, M.pc j

/-- `t̲ = min_j t_j` (Huang et al., SSRN 3993516, (A25), p.OA9). -/
noncomputable def tMin : ℝ :=
  ⨅ j, M.tc j

/-- `t̄ = max_j t_j` (Huang et al., SSRN 3993516, (A21), p.OA8). -/
noncomputable def tMax : ℝ :=
  ⨆ j, M.tc j

/-- `h̲ = min_j h′_j` (Huang et al., SSRN 3993516, p.8). -/
noncomputable def hMin : ℝ :=
  ⨅ j, M.h' j

/-- The retailer cost `C_j(z | x_j)` of (4) (Huang et al., SSRN 3993516, (4), p.8):
`𝔼_{ϵ_j}[−h₀ D_j + h_j (z − D_j) + (b_j + h′_j)(D_j − z)⁺ | x_j]` with `h_j = h′_j − h₀`, the
expectation over the noise with the features fixed. -/
noncomputable def retailerCost (j : Fin J) (ω : Ω) (z : ℝ) : ℝ :=
  ∫ e, (-M.h₀ * (M.meanShift j ω + e) + (M.h' j - M.h₀) * (z - (M.meanShift j ω + e))
      + (M.b j + M.h' j) * max (M.meanShift j ω + e - z) 0) * M.f j e

/-- The retailer's expected holding and lost-sales cost given the features,
`𝔼_{ϵ_j}[h′_j (z − D_j)⁺ + b_j (D_j − z)⁺ | x_j]` (Huang et al., SSRN 3993516, the second term of
(2), p.8). -/
noncomputable def newsvendor (j : Fin J) (ω : Ω) (z : ℝ) : ℝ :=
  ∫ e, (M.h' j * max (z - (M.meanShift j ω + e)) 0
      + M.b j * max (M.meanShift j ω + e - z) 0) * M.f j e

/-- The expected period cost (2) given the features (Huang et al., SSRN 3993516, (2), p.8):
`h₀ (z₀ − ∑_j z_j) + ∑_j 𝔼_{ϵ_j}[h′_j (z_j − D_j)⁺ + b_j (D_j − z_j)⁺ | x_j]`.

**Formalization Note** This is (3)–(4) with the term `−h₀ D_j` kept, i.e. the cost before the paper
omits that term. -/
noncomputable def cost (z₀ : ℝ) (z : Fin J → ℝ) (ω : Ω) : ℝ :=
  M.h₀ * (z₀ - ∑ j, z j) + ∑ j, M.newsvendor j ω (z j)

end Model

/-- The feasible allocations of an order `z₀`: `z_j ≥ 0` and `∑_j z_j ≤ z₀`
(Huang et al., SSRN 3993516, (6), p.9). -/
def feasible {J : ℕ} (z₀ : ℝ) : Set (Fin J → ℝ) :=
  {z | (∀ j, 0 ≤ z j) ∧ ∑ j, z j ≤ z₀}

end TaylorInv


