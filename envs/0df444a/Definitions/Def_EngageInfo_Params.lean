-- Prove2me | Definitions.Def_EngageInfo_Params
-- name    : EngageInfo_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:16:51.492998+00:00
-- url     : https://prove2.me/theorems/52451416-44df-4988-b55f-d04f2bb644f0
-- title:
--   Model parameters $\theta_H>\theta_L>c\ge0$, $\bar e>k>0$ and the thresholds $\alpha_e$, $\alpha_0$, $\alpha_{\bar e}$, $\alpha_1=k/\Theta$
-- statement:
--   A monopolist seller sells one unit of a product to one customer. The product's basic value is $\theta_H$ in the high state $H$ and $\theta_L$ in the low state $L$; the seller's unit cost is $c$; engagement raises the customer's value by $\bar e$ and costs the customer $k$. The parameters satisfy
--
--   $$\theta_H>\theta_L>c\ge 0,\qquad \bar e>k>0 .$$
--
--   Write $\Theta=\theta_H-\theta_L$. For an engagement level $e$ the **price-cut threshold** of (5) is
--
--   $$\alpha_e=\frac{\theta_L+e-c}{\theta_H+e-c},$$
--
--   and $\alpha_0$, $\alpha_{\bar e}$ are its values at $e=0$ and $e=\bar e$. Further $\alpha_1=k/\Theta$ and $m=\max\{\alpha_0,\alpha_1\}$.
--
--   These are the primitives and thresholds of every statement in the mission: $\alpha_e$ governs the seller's price, and $[m,\alpha_{\bar e}]$ is the region of beliefs where the customer engages.
--
--   **Formalization Note** The assumption $\alpha_1<\alpha_{\bar e}$, which the paper adopts "hereafter" on p.10, is not part of the structure; it is a hypothesis of the statements that use it. $\bar e>0$ follows from $\bar e>k>0$.
-- source:
--   Guo, Designing Information to Engage Customers, Management Science (2025), doi:10.1287/mnsc.2022.03503, §2, pp.6–7 (θH > θL > c ≥ 0, Θ, e ∈ {0, ē}, ē > k > 0); (5) and α₀, p.9; Lemma 1 (α₁ = k/Θ), p.10

import Mathlib

namespace EngageInfo

/-- **Model parameters and the belief thresholds α_e (5), α₀, α_ē and α₁ = k/Θ.**
Guo, *Designing Information to Engage Customers*, Management Science (2025), §2, pp.6–7, and §3.1,
pp.9–10. p.6: "The seller's cost of providing and delivering the product is c ≥ 0 … trade is always
socially efficient in either state, i.e., θH > θL > c. Let Θ ≡ θH − θL". p.7: "e ∈ {0, ē}, where
ē > 0. Engagement entails a cost k > 0 … We assume that ē > k". (5), p.9:
"αe ≡ (θL + e − c)/(θH + e − c)", with α₀ ≡ (θL − c)/(θH − c) its value at e = 0 (p.9) and α_ē its
value at e = ē. Lemma 1, p.10: "α₁ ≡ k/Θ".

A `Params` records the basic values `θH > θL` of the product in the states H and L, the seller's
cost `c` with `0 ≤ c < θL`, the engagement benefit `ebar` (the paper's ē) and the engagement cost
`k` with `0 < k < ebar`.

**Formalization Note** The assumption α₁ < α_ē that p.10 adopts "hereafter" is **not** a field: it is
a separate hypothesis on the statements that use it. `ē > 0` is implied by `0 < k < ē`. The
threshold `alpha e` is defined for every real `e`; the paper uses it at `e ∈ {0, ē}`, where its
denominator `θH + e − c` is positive. `m` is the paper's `max{α₀, α₁}`. -/
structure Params where
  /-- Basic value `θ_H` in the high state. -/
  θH : ℝ
  /-- Basic value `θ_L` in the low state. -/
  θL : ℝ
  /-- The seller's unit cost `c`. -/
  c : ℝ
  /-- The engagement benefit `ē`. -/
  ebar : ℝ
  /-- The engagement cost `k`. -/
  k : ℝ
  c_nonneg : 0 ≤ c
  c_lt_θL : c < θL
  θL_lt_θH : θL < θH
  k_pos : 0 < k
  k_lt_ebar : k < ebar

namespace Params

/-- `Θ = θ_H − θ_L`, the increment in the state-dependent value (p.6). -/
def Θ (M : Params) : ℝ := M.θH - M.θL

/-- The price-cut threshold `α_e = (θ_L + e − c)/(θ_H + e − c)` of (5), p.9. -/
noncomputable def alpha (M : Params) (e : ℝ) : ℝ := (M.θL + e - M.c) / (M.θH + e - M.c)

/-- `α₀ = (θ_L − c)/(θ_H − c)`, the threshold (5) at `e = 0` (p.9). -/
noncomputable def α₀ (M : Params) : ℝ := M.alpha 0

/-- `α_ē`, the threshold (5) at `e = ē`. -/
noncomputable def αbar (M : Params) : ℝ := M.alpha M.ebar

/-- `α₁ = k/Θ` (Lemma 1, p.10). -/
noncomputable def α₁ (M : Params) : ℝ := M.k / M.Θ

/-- `m = max{α₀, α₁}`, the lower end of the engagement region of Lemma 1. -/
noncomputable def m (M : Params) : ℝ := max M.α₀ M.α₁

end Params

end EngageInfo


