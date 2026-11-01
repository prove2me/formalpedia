-- Prove2me | Definitions.Def_TaylorInv_Policies
-- name    : TaylorInv_Policies
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:31:37.785458+00:00
-- url     : https://prove2.me/theorems/d14243da-c832-426c-bbd4-c78fea0d5707
-- title:
--   OPT, TA and AF costs, the TA order $\tilde z_0$ and allocation $\tilde z(z_0,x)$, and the regions $\mathscr A_1,\mathscr A_2,\mathscr A_3$
-- statement:
--   **OPT.** For an order $z_0\ge0$ and features $x$, the optimal cost given $x$ is the infimum of the period cost (2) over the feasible allocations, i.e. $h_0z_0+G(z_0\mid x)$ with $G$ the second stage (6). The optimal expected cost is
--   $$
--   C_{OPT}=\inf_{z_0\ge0}\ \mathbb E_x\big[h_0z_0+G(z_0\mid x)\big] \quad\text{(5)}.
--   $$
--
--   **TA.** The Taylor allocation $\tilde z(z_0,x)$ minimizes the second-order expansion (14),
--   $$
--   \sum_{j=1}^J\Big[-h_0(z_j-s_j^l)+\frac{(b_j+h'_j)f_j(s_j^l\mid x_j)}2(z_j-s_j^l)^2\Big]
--   $$
--   (without its constant $\sum_jC_j(s_j^l\mid x_j)$) over the feasible allocations of $z_0$. The TA order is $\tilde z_0=\mathbb E_x[\sum_js_j^l(x_j)]$ (17), and $C_{TA}(x)$ is the period cost of $(\tilde z_0,\tilde z(\tilde z_0,x))$, with $C_{TA}=\mathbb E_x[C_{TA}(x)]$ (19).
--
--   **AF.** $C_{AF}(x)$ is the period cost of the order $\sum_js_j^l$ with allocation $s^l$, and $C_{AF}=\mathbb E_x[C_{AF}(x)]$.
--
--   **Regions** (p.OA6). With $S(x)=\sum_j\sum_p\beta_{jp}(x_{jp}-\mathbb Ex_{jp})$,
--   $\mathscr A_1=\{x:\ \tilde z_0\le\sum_j(\tilde s_j^e-\underline m r_j)\}$, $\mathscr A_2=\{x:\ \sum_j(\tilde s_j^e-\underline m r_j)<\tilde z_0<\sum_j\tilde s_j^e\}$, $\mathscr A_3=\{x:\ \sum_j\tilde s_j^e\le\tilde z_0\}$.
--
--   These are the policies compared in Theorem 1 and the regions of its proof.
--
--   **Formalization Note** The minimizer of (14) is chosen with `Classical.epsilon`; it is unique for $z_0\ge0$ (Proposition 2). The paper's $z_j>0$, $z_0>0$ are $z_j\ge0$, $z_0\ge0$. The paper's $C_{OPT}(x)$ is `optCostGiven z₀* x`; the definition is available at every order $z_0$. The feature sum is centred instead of assuming $\mathbb Ex_{jp}=0$.
-- source:
--   Huang, Shang, Yang & Zhou, Taylor Approximation of Inventory Policies for One-Warehouse, Multi-Retailer Systems with Demand Feature Information, SSRN 3993516 (Jan 29 2023), https://ssrn.com/abstract=3993516, (5)–(6), pp.8–9; (14), p.12; (17), p.13; (19), p.16; proof of Theorem 1, pp.OA5–OA6

import Mathlib
import Definitions.Def_TaylorInv_Quantities

open MeasureTheory

namespace TaylorInv

namespace Model

variable {J P : ℕ} {Ω : Type*} (M : Model J P Ω)

/-- The optimal cost given the features at the order `z₀`: `h₀ z₀ + G(z₀ | x)`, with `G` the
second-stage minimum (6) (Huang, Shang, Yang & Zhou, SSRN 3993516 (Jan 29 2023), (5)–(6), pp.8–9),
i.e. the infimum of the period cost (2) over the feasible allocations.

**Formalization Note** At `z₀ = z₀*` this is the paper's `C_OPT(x)` of (19), p.16. The infimum is over
the nonempty compact set `feasible z₀` when `z₀ ≥ 0`; the period cost is nonnegative there. -/
noncomputable def optCostGiven (z₀ : ℝ) (ω : Ω) : ℝ :=
  ⨅ z : {z : Fin J → ℝ // z ∈ feasible z₀}, M.cost z₀ z.1 ω

/-- The optimal expected cost `C_OPT = min_{z₀ ≥ 0} h₀ z₀ + 𝔼_x[G(z₀ | x)]` of the two-stage problem
(Huang et al., SSRN 3993516, (5), p.8, and (19), p.16).

**Formalization Note** The minimum over `z₀ > 0` is an infimum over `z₀ ≥ 0` (same value). -/
noncomputable def costOPT [MeasurableSpace Ω] (μ : Measure Ω) : ℝ :=
  ⨅ z₀ : {z₀ : ℝ // 0 ≤ z₀}, ∫ ω, M.optCostGiven z₀.1 ω ∂μ

/-- The objective of the Taylor problem (14) without its constant `∑_j C_j(s_j^l | x_j)`
(Huang et al., SSRN 3993516, (14), p.12):
`∑_j [−h₀ (z_j − s_j^l) + ((b_j + h′_j) f_j(s_j^l | x_j) / 2) (z_j − s_j^l)²]`. -/
noncomputable def taylorObj (z : Fin J → ℝ) (ω : Ω) : ℝ :=
  ∑ j, (-M.h₀ * (z j - M.baseStock j ω)
    + (M.b j + M.h' j) * M.densAtBase j ω / 2 * (z j - M.baseStock j ω) ^ 2)

/-- The Taylor-approximation allocation `z̃(z₀, x)`, the minimizer of (14) over the feasible
allocations (Huang et al., SSRN 3993516, (14), p.12).

**Formalization Note** The minimizer is chosen with `Classical.epsilon`; it exists and is unique for
`z₀ ≥ 0` (Proposition 2 gives it in closed form). The paper's `z_j > 0` is `z_j ≥ 0`. -/
noncomputable def taAlloc (z₀ : ℝ) (ω : Ω) : Fin J → ℝ :=
  Classical.epsilon fun z : Fin J → ℝ =>
    z ∈ feasible z₀ ∧ ∀ z' ∈ feasible z₀, M.taylorObj z ω ≤ M.taylorObj z' ω

/-- The TA order `z̃₀ = 𝔼_x[∑_j s_j^l(x_j)]` (Huang et al., SSRN 3993516, (17), p.13). -/
noncomputable def taOrder [MeasurableSpace Ω] (μ : Measure Ω) : ℝ :=
  ∫ ω, ∑ j, M.baseStock j ω ∂μ

/-- The TA cost given the features, `C_TA(x) = h₀ z̃₀ + ∑_j C_j(z̃_j(z̃₀, x) | x_j)`
(Huang et al., SSRN 3993516, (19), p.16), as the period cost (2). -/
noncomputable def costTAGiven [MeasurableSpace Ω] (μ : Measure Ω) (ω : Ω) : ℝ :=
  M.cost (M.taOrder μ) (M.taAlloc (M.taOrder μ) ω) ω

/-- The expected TA cost `C_TA = 𝔼_x[C_TA(x)]` (Huang et al., SSRN 3993516, (19), p.16). -/
noncomputable def costTA [MeasurableSpace Ω] (μ : Measure Ω) : ℝ :=
  ∫ ω, M.costTAGiven μ ω ∂μ

/-- The advanced-feature cost given the features, `C_AF(x) = h₀ z₀^AF + ∑_j C_j(z_j^AF | x_j)` with
`z_j^AF = s_j^l`, `z₀^AF = ∑_j s_j^l` (Huang et al., SSRN 3993516, proof of Theorem 1, p.OA5), as
the period cost (2). -/
noncomputable def costAFGiven (ω : Ω) : ℝ :=
  M.cost (∑ j, M.baseStock j ω) (fun j => M.baseStock j ω) ω

/-- The expected AF cost `C_AF = 𝔼_x[C_AF(x)]` (Huang et al., SSRN 3993516, p.OA5). -/
noncomputable def costAF [MeasurableSpace Ω] (μ : Measure Ω) : ℝ :=
  ∫ ω, M.costAFGiven ω ∂μ

/-- The centred feature sum `∑_j ∑_p β_jp (x_jp − 𝔼 x_jp)` (Huang et al., SSRN 3993516, (A11)–(A12)
and the centring of p.OA6).

**Formalization Note** The paper assumes `𝔼 x_jp = 0` without loss of generality and writes
`∑_j ∑_p β_jp x_jp`; here the means are subtracted explicitly. -/
noncomputable def centredSum [MeasurableSpace Ω] (μ : Measure Ω) (ω : Ω) : ℝ :=
  ∑ j, ∑ p, M.β j p * (M.X j p ω - ∫ ω', M.X j p ω' ∂μ)

/-- The region `𝒜₁ = {x | ∑_j (s̃_j^e − m̲ r_j) ≥ z̃₀}` (Huang et al., SSRN 3993516, p.OA6). -/
def region1 [MeasurableSpace Ω] (μ : Measure Ω) : Set Ω :=
  {ω | M.taOrder μ ≤ ∑ j, (M.sEch j ω - M.mMin ω * M.r j ω)}

/-- The region `𝒜₂ = {x | ∑_j (s̃_j^e − m̲ r_j) < z̃₀ < ∑_j s̃_j^e}` (Huang et al., SSRN 3993516,
p.OA6). -/
def region2 [MeasurableSpace Ω] (μ : Measure Ω) : Set Ω :=
  {ω | ∑ j, (M.sEch j ω - M.mMin ω * M.r j ω) < M.taOrder μ ∧ M.taOrder μ < ∑ j, M.sEch j ω}

/-- The region `𝒜₃ = {x | ∑_j s̃_j^e ≤ z̃₀}` (Huang et al., SSRN 3993516, p.OA6). -/
def region3 [MeasurableSpace Ω] (μ : Measure Ω) : Set Ω :=
  {ω | ∑ j, M.sEch j ω ≤ M.taOrder μ}

end Model

end TaylorInv


