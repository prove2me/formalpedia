-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_qFn
-- name    : KallMayerSLP_Multistage_qFn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:21:20.330328+00:00
-- url     : https://prove2.me/theorems/199b5374-3bd6-4a90-9e53-cebc61f582d4
-- title:
--   Aggregated stage value $q_t$ of (3.17)
-- statement:
--   For a node $n$ of stage $t$, with $\widehat\zeta^n=(\widehat\zeta_{t-1},\bar\xi^n_t)$,
--   $$
--   q_t(z_{t-1};\widehat\zeta_{t-1},\bar\xi^n_t):=\min_{x_t}\{c_t^{\mathsf T}x_t+\Psi_{t+1}(z_t;\widehat\zeta_{t-1},\bar\xi^n_t)\}
--   $$
--   subject to $A_{tt}x_t=b_t(\widehat\zeta_{t-1},\bar\xi^n_t)-\sum_{\tau=1}^{t-1}A_{t\tau}x_\tau$, $x_t\ge0$. At the root this is the book's $q_1$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (3.17), p.264 (PDF 273)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_Psi

namespace KallMayerSLP.Multistage

open MeasureTheory

/-- The aggregated stage value `q_t(z_{t-1}; ζ̂_{t-1}, ξ̄^n_t)` at a node `n` of stage `t`, (3.17)
(Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, (3.17), p.264, PDF 273):
`min_{x_t} {c_tᵀ x_t + Ψ_{t+1}(z_t; ζ̂_{t-1}, ξ̄^n_t)}` s.t.
`A_tt x_t = b_t(ζ̂_{t-1}, ξ̄^n_t) − Σ_{τ=1}^{t-1} A_{tτ} x_τ`, `x_t ≥ 0`, and at the root the book's
`q_1`. The pair `(ζ̂_{t-1}, ξ̄^n_t)` is `ζ̂^n`. -/
noncomputable def qFn {D : MSLP} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)} (𝒯 : ScenarioTree D Ξ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ξ : ∀ t, Ω → Fin (D.r t) → ℝ)
    (t : ℕ) (n : 𝒯.Node t) (z : ∀ τ, Fin (D.n τ) → ℝ) : EReal :=
  stageMin D t (D.b t (zetaHat 𝒯 P ξ n)) (Psi 𝒯 P ξ t n) z

end KallMayerSLP.Multistage


