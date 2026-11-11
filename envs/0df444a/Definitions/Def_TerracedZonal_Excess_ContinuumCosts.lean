-- Prove2me | Definitions.Def_TerracedZonal_Excess_ContinuumCosts
-- name    : TerracedZonal_Excess_ContinuumCosts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:03:22.231306+00:00
-- url     : https://prove2.me/theorems/eb343646-5739-4a31-b0c8-2f661bc82e07
-- title:
--   The homogeneous cost $F_\alpha$ and the per-ring trade-off $A(\theta)$, $B_\lambda(\theta)$, $f_\lambda(\theta)$
-- statement:
--   Two families of auxiliary functions of Appendix E.
--
--   **Homogeneous stretching cost (Lemma E.4).** For a terrace of $n$ rings with ideal populations $y_1,\dots,y_n>0$, an exponent $\alpha\in\mathbb R$ and a common real population $m>0$,
--
--   $$F_\alpha(m)=\sum_{k}\frac{(m-y_k)^2}{y_k^{1-\alpha}m^{\alpha}}.$$
--
--   **Per-ring trade-off (eqs. (31)–(33)).** For $N\ge1$ points, a colatitude $\theta\in(0,\pi)$ and a seam price $\lambda>0$,
--
--   $$A(\theta)=\frac{c_{\mathrm{stretch}}C_0^3\cos^2\theta}{24N^{1/2}\sin\theta},\qquad B_\lambda(\theta)=\tfrac12\lambda C_0N^{1/2}\sin\theta,$$
--
--   $$f_\lambda(\theta)=3\Big(\frac{c_{\mathrm{stretch}}\lambda^2C_0^5}{384}\cos^2\theta\sin\theta\Big)^{1/3}N^{1/6}.$$
--
--   $A(\theta)L^2$ is the stretching cost per ring of a terrace of $L$ rings at colatitude $\theta$, $B_\lambda(\theta)/L$ its share of the seam cost, and $f_\lambda(\theta)$ the minimum over $L$ of their sum.
--
--   **Formalization Note** $f_\lambda$ is defined by its closed form; its equality with $3(A B_\lambda^2/4)^{1/3}$ is part of a milestone. Powers are real powers of nonnegative bases.
-- source:
--   Kabra, Dehaen, Karlova, Hamilton, Carreira, Ovsjanikov, Barron, STOC 2027 submission #638 (October 2026), Lemma E.4 p. 28 (PDF 29); eqs. (31)–(33) p. 29 (PDF 30)

import Definitions.Def_TerracedZonal_Excess_Constants

namespace TerracedZonal.Excess

open Real

/-- The homogeneous stretching cost of Lemma E.4, p. 28 (PDF 29), for a terrace whose `n`
rings have ideal populations `y : Fin n → ℝ`, as a function of a common real population `m`:
`F_α(m) = ∑_k (m - y_k)² / (y_k^{1-α} m^α)` (real powers, used at positive `y_k`, `m`). -/
noncomputable def Fcost (α : ℝ) {n : ℕ} (y : Fin n → ℝ) (m : ℝ) : ℝ :=
  ∑ k, (m - y k) ^ 2 / (y k ^ (1 - α) * m ^ α)

/-- `A(θ) = c_stretch C₀³ cos²θ / (24 N^{1/2} sin θ)`, eq. (31), p. 29 (PDF 30). -/
noncomputable def Acoef (N : ℕ) (θ : ℝ) : ℝ :=
  cStretch * C0 ^ 3 * Real.cos θ ^ 2 / (24 * (N : ℝ) ^ (1 / 2 : ℝ) * Real.sin θ)

/-- `B_λ(θ) = λ y(θ) = ½ λ C₀ N^{1/2} sin θ`, eq. (32), p. 29 (PDF 30). -/
noncomputable def Bcoef (lam : ℝ) (N : ℕ) (θ : ℝ) : ℝ :=
  (1 / 2) * lam * C0 * (N : ℝ) ^ (1 / 2 : ℝ) * Real.sin θ

/-- The minimal per-ring cost after (33), p. 29 (PDF 30), in its closed form
`f_λ(θ) = 3 (c_stretch λ² C₀⁵ / 384)^{1/3} (cos²θ sin θ)^{1/3} N^{1/6}`. -/
noncomputable def fLam (lam : ℝ) (N : ℕ) (θ : ℝ) : ℝ :=
  3 * (cStretch * lam ^ 2 * C0 ^ 5 / 384) ^ (1 / 3 : ℝ)
    * (Real.cos θ ^ 2 * Real.sin θ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 6 : ℝ)

end TerracedZonal.Excess


