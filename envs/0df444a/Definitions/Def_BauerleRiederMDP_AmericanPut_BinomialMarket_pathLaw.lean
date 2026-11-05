-- Prove2me | Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_pathLaw
-- name    : BauerleRiederMDP_AmericanPut_BinomialMarket_pathLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:21.754804+00:00
-- url     : https://prove2.me/theorems/ef60dedb-31dc-4c2c-9426-729cb8a6e22b
-- title:
--   Risk-neutral law $\mathbb Q$ of the up/down moves
-- statement:
--   Under $\mathbb Q$ the moves of the stock are independent, each up with probability $q$ and down with probability $1-q$. Equivalently the stock price is a Markov chain with kernel
--   $$Q^X(B\mid x)=q\,\delta_{xu}(B)+(1-q)\,\delta_{xd}(B).$$
--
--   **Formalization Note** The sample space is the set of sequences $\omega\in\{\mathrm{true},\mathrm{false}\}^{\mathbb N}$, with $\omega_k=\mathrm{true}$ meaning that the $(k+1)$-st move is up. $\mathbb Q$ is the infinite product of the two-point law $q\,\delta_{\mathrm{true}}+(1-q)\,\delta_{\mathrm{false}}$ (Mathlib's `Measure.infinitePi`); it is a probability measure because $q\in(0,1)$.
-- source:
--   N. Bäuerle and U. Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, §3.1, p.60, PDF 74 and §11.1, pp.331–332, PDF 339–340

import Mathlib
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_q

open MeasureTheory

namespace BauerleRiederMDP.AmericanPut

/-- The **risk-neutral law `ℚ` of the up/down moves** (Bäuerle & Rieder, Markov Decision Processes with
Applications to Finance (2011), §3.1, p.60, PDF 74 and §11.1, pp.331–332, PDF 339–340): under `ℚ` the relative
price changes `R̃₁, R̃₂, …` are i.i.d. with `ℚ(R̃ₙ = u) = q` and `ℚ(R̃ₙ = d) = 1 − q`, `q` from (11.1).
Equivalently the stock price is a Markov chain with kernel `Q^X(B|x) = q δ_{xu}(B) + (1 − q) δ_{xd}(B)`
(p.332).

**Formalization Note.** The sample space is `ℕ → Bool`; the coordinate `ω k = true` means that the
`(k+1)`-st move is up (`R̃_{k+1} = u`), `false` that it is down. `ℚ` is Mathlib's infinite product
`Measure.infinitePi` of the two-point law `q δ_true + (1 − q) δ_false`, which is a probability measure because
`q ∈ (0, 1)`. -/
noncomputable def BinomialMarket.pathLaw (M : BinomialMarket) : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ =>
    ENNReal.ofReal M.q • Measure.dirac true + ENNReal.ofReal (1 - M.q) • Measure.dirac false)

end BauerleRiederMDP.AmericanPut


