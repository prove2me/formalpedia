-- Prove2me | Definitions.Def_AFIsingKS_rect
-- name    : AFIsingKS_rect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:14:28.465787+00:00
-- url     : https://prove2.me/theorems/13b4e13a-f89c-4c12-92a1-db82f89bd943
-- title:
--   The rectangles $\mathrm{rect}(\delta,\eta_0)$ and $\mathrm{rect}_+(\delta,\eta_0)$
-- statement:
--   Let $\beta_{\mathrm{lb}}=-d^{-10}$. For $\delta,\eta_0\ge0$ define the closed rectangles in the complex plane
--   $$\mathrm{rect}(\delta,\eta_0)=\{E+i\eta: E\in[\beta_{\mathrm{lb}},\beta_{\mathrm{KS}}-\delta],\ \eta\in[-\eta_0,\eta_0]\},$$
--   $$\mathrm{rect}_+(\delta,\eta_0)=\{E+i\eta: E\in[2\beta_{\mathrm{lb}},\beta_{\mathrm{KS}}-\delta],\ \eta\in[-\eta_0,\eta_0]\}.$$
--   The first is the region of zero-freeness in Theorem 3.1, the second is where the moment estimates hold.
--
--   **Formalization Note** The threshold $\delta$ is additive here. The rectangles are empty when $\beta_{\mathrm{KS}}-\delta$ falls below the left endpoint.
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), p.11, eq. (4), and p.12, eq. (8)

import Mathlib
import Definitions.Def_AFIsingKS_betaKS

open Set

namespace AFIsingKS

/-- The lower endpoint `β_lb = −d^{−10}` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 3, p.11). -/
noncomputable def betaLb (d : ℕ) : ℝ := -((d : ℝ) ^ (-10 : ℤ))

/-- The closed rectangle `rect(δ, η₀) = {E + iη : E ∈ [β_lb, β_KS − δ], η ∈ [−η₀, η₀]}`
(Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), eq. (4), p.11). It is empty when `β_KS − δ < β_lb`. -/
def rect (d : ℕ) (δ η₀ : ℝ) : Set ℂ :=
  {β | β.re ∈ Icc (betaLb d) (betaKS d - δ) ∧ β.im ∈ Icc (-η₀) η₀}

/-- The closed rectangle `rect₊(δ, η₀) = {E + iη : E ∈ [2β_lb, β_KS − δ], η ∈ [−η₀, η₀]}`
(Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), eq. (8), p.12). -/
def rectPlus (d : ℕ) (δ η₀ : ℝ) : Set ℂ :=
  {β | β.re ∈ Icc (2 * betaLb d) (betaKS d - δ) ∧ β.im ∈ Icc (-η₀) η₀}

end AFIsingKS


