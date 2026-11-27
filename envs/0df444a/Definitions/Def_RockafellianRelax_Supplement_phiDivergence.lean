-- Prove2me | Definitions.Def_RockafellianRelax_Supplement_phiDivergence
-- name    : RockafellianRelax_Supplement_phiDivergence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:13:21.475477+00:00
-- url     : https://prove2.me/theorems/913a484d-2661-44f7-97cb-d4b1e78c82af
-- title:
--   $\Phi$-divergence $d_\Phi(q|\bar q)$ with the conventions at $\bar q_i = 0$
-- statement:
--   For $\Phi : \mathbb R \to \overline{\mathbb R}$ and $q,\bar q \in \mathbb R^s$ (used with both in the probability simplex), the **$\Phi$-divergence** is
--
--   $$
--   d_\Phi(q|\bar q) = \sum_{i=1}^s T_i,\qquad
--   T_i = \begin{cases}\bar q_i\,\Phi(q_i/\bar q_i), & \bar q_i > 0,\\ 0, & \bar q_i = 0 = q_i,\\ q_i \lim_{\alpha\to\infty}\Phi(\alpha)/\alpha, & \bar q_i = 0 \ne q_i .\end{cases}
--   $$
--
--   The last two cases are the paper's conventions $0\cdot\Phi(0/0) = 0$ and $0\cdot\Phi(\beta/0) = \beta\lim_{\alpha\to\infty}\Phi(\alpha)/\alpha$.
--
--   It is the penalty in the approximating functions (4.7).
--
--   **Formalization Note** The limit is written as an upper limit in `EReal`; it equals the limit for every admissible $\Phi$, where the limit exists in $(0,\infty]$ by convexity. The second and third cases are the branch $\bar q_i \le 0$, used only at $\bar q_i = 0$.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, §4.2, Refinement A, p.14 (Φ-divergence and conventions)

import Mathlib

namespace RockafellianRelax.Supplement

/-- **Φ-divergence `d_Φ(q|q̄)`.** Royset, Chen & Eckstrand, arXiv:2204.04762v4, §4.2, Refinement A, p.14: "d_Φ(q|q̄) = ∑_{i=1}^s q̄_i Φ(q_i/q̄_i)
… we adopt the usual conventions: 0 · Φ(0/0) = 0, and, for β ∈ (0, ∞), 0 · Φ(β/0) =
β lim_{α→∞} Φ(α)/α."

**Formalization Note.** The arguments are `q` then `qbar`, as in `d_Φ(q|q̄)`. The two conventions at
`q̄ᵢ = 0` are written out, as real division by zero would give `0`. The limit is written as the
`limsup` in `EReal` as `α → ∞`: it equals the limit, in `(0, ∞]`, for every admissible `Φ`, where
the limit exists by convexity. The definition is used only at `q, q̄ ∈ ∆`. -/
noncomputable def phiDivergence {s : ℕ} (Φ : ℝ → EReal) (q qbar : Fin s → ℝ) : EReal :=
  ∑ i, if 0 < qbar i then (qbar i : EReal) * Φ (q i / qbar i)
    else if q i = 0 then 0
    else (q i : EReal) * Filter.limsup (fun α : ℝ => ((α⁻¹ : ℝ) : EReal) * Φ α) Filter.atTop

end RockafellianRelax.Supplement


