-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_rFn
-- name    : KallMayerSLP_Multistage_rFn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:18:15.379867+00:00
-- url     : https://prove2.me/theorems/d917567e-4f3f-4307-9ee9-2d1e43fc2cef
-- title:
--   Stage value $r_t$ of (3.15)
-- statement:
--   For $t=T,\dots,1$,
--   $$
--   r_t(z_{t-1};\widehat\zeta_t):=\min_{x_t}\{c_t^{\mathsf T}x_t+\Phi_{t+1}(z_t;\widehat\zeta_t)\}\quad\text{s.t.}\quad A_{tt}x_t=b_t(\widehat\zeta_t)-\sum_{\tau=1}^{t-1}A_{t\tau}x_\tau,\quad x_t\ge0.
--   $$
--   At $t=1$ this is the book's $r_1$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (3.15), p.263 (PDF 272)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_Phi

namespace KallMayerSLP.Multistage

open MeasureTheory

/-- The stage value `r_t(z_{t-1}; ζ̂_t) := min_{x_t} {c_tᵀ x_t + Φ_{t+1}(z_t; ζ̂_t)}` s.t.
`A_tt x_t = b_t(ζ̂_t) − Σ_{τ=1}^{t-1} A_{tτ} x_τ`, `x_t ≥ 0` of the recursion (3.15) (Kall & Mayer,
*Stochastic Linear Programming* (2005), Chapter 3, (3.15), p.263, PDF 272), and at `t = 1` the
book's `r_1`, p.263.

**Formalization Note.** `μ t` is the law `ℙ_{ξ_t}`, `z` holds `z_{t-1}`, and `w` holds `ζ̂_t` in
its coordinates `s ≤ t`. See `stageMin` and `Phi` for the `EReal` conventions. -/
noncomputable def rFn (D : MSLP) (μ : ∀ t, Measure (Fin (D.r t) → ℝ)) (t : ℕ)
    (z : ∀ τ, Fin (D.n τ) → ℝ) (w : ∀ s, Fin (D.r s) → ℝ) : EReal :=
  stageMin D t (D.b t (toHist t w)) (fun z' => Phi D μ (t + 1) z' w) z

end KallMayerSLP.Multistage


