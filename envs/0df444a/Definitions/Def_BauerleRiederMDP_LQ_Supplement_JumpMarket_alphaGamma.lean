-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_alphaGamma
-- name    : BauerleRiederMDP_LQ_Supplement_JumpMarket_alphaGamma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:20:28.986271+00:00
-- url     : https://prove2.me/theorems/65e72f6a-8e6f-47ef-bcad-4ea5dde043e3
-- title:
--   The constant $\alpha _\gamma $
-- statement:
--   **The constant $\alpha _\gamma $** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Proposition 9.3.2 b), eq. (9.14), p.284, PDF 294): $\alpha _\gamma  = \lambda (1 + ȳ)/(\gamma  + \lambda  - \bar{\mu}) \cdot  (1 - e^{-T(\gamma +\lambda -\bar{\mu})})$, where $\bar{\mu} := \max {\mu _1, \dots , \mu _d, \rho }$ and $ȳ := \max {\mathbb E Y_1, \dots , \mathbb E Y_d, 0}$; $\alpha _b \le  \alpha _\gamma $ for the bounding function `b = bfun γ`.
--
--   **Formalization Note.** $\bar{\mu}$ is `muBar`; $ȳ$ is a finite maximum (`Finset.sup'` over $Fin d$ joined with $0$); $\mathbb E Y_k$ is a Bochner integral of an integrable function ($\mathbb E \|Y\| < \infty $).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Proposition 9.3.2 b), eq. (9.14), p.284, PDF 294

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_muBar

open MeasureTheory

namespace BauerleRiederMDP.LQ.Supplement

/-- **The constant `α_γ`** (Bäuerle & Rieder, *Markov Decision Processes with Applications to
Finance* (2011), Proposition 9.3.2 b), eq. (9.14), p.284, PDF 294):
`α_γ = λ(1 + ȳ)/(γ + λ − μ̄) · (1 − e^{−T(γ+λ−μ̄)})`, where `μ̄ := max{μ_1, …, μ_d, ρ}` and
`ȳ := max{𝔼Y_1, …, 𝔼Y_d, 0}`; `α_b ≤ α_γ` for the bounding function `b = bfun γ`.

**Formalization Note.** `μ̄` is `muBar`; `ȳ` is a finite maximum (`Finset.sup'` over `Fin d` joined with `0`); `𝔼Y_k` is a Bochner integral of an integrable function (`𝔼‖Y‖ < ∞`). -/
noncomputable def JumpMarket.alphaGamma {d : ℕ} (Mk : JumpMarket d) (γ : ℝ) : ℝ :=
  let μbar : ℝ := Mk.muBar
  let ybar : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun k : Option (Fin d) =>
    k.elim 0 fun j => ∫ y, y j ∂Mk.QY)
  Mk.lam * (1 + ybar) / (γ + Mk.lam - μbar) * (1 - Real.exp (-Mk.T * (γ + Mk.lam - μbar)))

end BauerleRiederMDP.LQ.Supplement


