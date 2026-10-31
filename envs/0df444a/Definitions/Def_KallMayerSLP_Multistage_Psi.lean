-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_Psi
-- name    : KallMayerSLP_Multistage_Psi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:19:54.126908+00:00
-- url     : https://prove2.me/theorems/c0b0764c-49cb-458d-9605-bad6386ff73a
-- title:
--   Aggregated cost-to-go $\Psi_{t+1}$ of (3.17)
-- statement:
--   For a node $h$ of stage $t$, with realization $\widehat\zeta^h$, this is the aggregated cost-to-go: $\Psi_{T+1}\equiv0$, and for $t<T$
--   $$
--   \Psi_{t+1}(z_t;\widehat\zeta^h)=\sum_{\nu\in C_h}\mathbb P_{\xi_{t+1}}(\Xi^{t+1}_\nu)\,q_{t+1}\big(z_t;\widehat\zeta^h,\bar\xi^\nu_{t+1}\big).
--   $$
--
--   **Formalization Note** The Lean index is the stage of the node $h$, one less than the book's index of $\Psi$, because the book's $\Psi_t$ is a function of a node of stage $t-1$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (3.17), p.264 (PDF 273)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_psiAux

namespace KallMayerSLP.Multistage

open MeasureTheory

/-- The aggregated cost-to-go of the recursion (3.17) (Kall & Mayer, *Stochastic Linear Programming*
(2005), Chapter 3, (3.17), p.264, PDF 273): `Psi 𝒯 P ξ t h` is the book's
`Ψ_{t+1}(z_t; ζ̂_t)` at the node `h` of stage `t`, whose realization is `ζ̂_t = ζ̂^h`. So
`Ψ_{T+1} ≡ 0`, and for `t < T`
`Ψ_{t+1}(z_t; ζ̂^h) = Σ_{ν∈C_h} ℙ_{ξ_{t+1}}(Ξ^{t+1}_ν) q_{t+1}(z_t; ζ̂^h, ξ̄^ν_{t+1})`.

**Formalization Note.** The index is the stage of the node `h`, one less than the book's index of
`Ψ`, because the book's `Ψ_t` is a function of a node of stage `t - 1`. -/
noncomputable def Psi {D : MSLP} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)} (𝒯 : ScenarioTree D Ξ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ξ : ∀ t, Ω → Fin (D.r t) → ℝ)
    (t : ℕ) (h : 𝒯.Node t) (z : ∀ τ, Fin (D.n τ) → ℝ) : EReal :=
  psiAux 𝒯 P ξ (D.T - t) t h z

end KallMayerSLP.Multistage


