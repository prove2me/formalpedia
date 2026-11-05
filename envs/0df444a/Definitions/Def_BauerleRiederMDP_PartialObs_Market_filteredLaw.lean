-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_Market_filteredLaw
-- name    : BauerleRiederMDP_PartialObs_Market_filteredLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:03:03.881331+00:00
-- url     : https://prove2.me/theorems/8888909c-2d36-4653-9f10-0b4908e51857
-- title:
--   Law of the returns in the filtered Markov Decision Model
-- statement:
--   In the filtered Markov Decision Model of the terminal wealth problem the state is $(x,\rho)\in E_X\times\mathbb P(E_Y)$. The next relative risk $z$ is drawn from the predictive law
--   $$
--   \int Q^R(\cdot\mid y)\,\rho(dy)
--   $$
--   (it does not depend on the wealth or the action), and the belief moves to $\Phi(\rho,z)$. Started at belief $\rho$, the return path $(z_1,\dots,z_n)$ of this model therefore has the law $\widehat P^\rho_n$ defined recursively by: $z_{k+1}$ is drawn from $\int Q^R(\cdot\mid y)\,\mu_k(dy)$, where $\mu_k$ is the filter started at $\rho$ along $(z_1,\dots,z_k)$.
--
--   Under a Markov policy of the filtered model the state process is a function of this path and of the initial wealth. That $\widehat P^{Q_0}_n$ equals the market law of the returns is the content of Theorem 5.2.1 and Theorem 5.3.2; it is not built into this definition.
-- source:
--   Bäuerle & Rieder (2011), Definition 5.3.1, p.157 (PDF 170); §6.1, p.177 (PDF 190)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_Market_filter

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **The law of the return path in the filtered Markov Decision Model.**
Bäuerle & Rieder (2011), Definition 5.3.1, p.157 (PDF 170), for the model of §6.1: in the filtered
model with state `(x, ρ) ∈ E_X × IP(E_Y)` the next relative risk `z` is drawn from the
predictive law `∫ Q^R(·|y) ρ(dy)` (the `z`-marginal of `Q'(·|x, ρ, a)`; it does not depend on
`(x, a)`), and the belief moves to `Φ(ρ, z)`.

`M.filteredLaw ρ n` is the law of `(z_1, …, z_n)` in this model started at belief `ρ`: `z_{k+1}`
is drawn from `∫ Q^R(·|y) μ_k(dy)`, where `μ_k = M.filter ρ k (z_1, …, z_k)`. The state process
of the filtered model under a Markov policy is a function of this path and of the initial
wealth (`markovWealth`).

**Formalization Note.** The path is 0-indexed (`r k = z_{k+1}`); `Measure.bind` against the
Markov kernel `Q^R` is `∫ Q^R(·|y) ρ(dy)`. -/
noncomputable def Market.filteredLaw {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d)
    (ρ : ProbabilityMeasure EY) : (n : ℕ) → Measure (Fin n → Fin d → ℝ)
  | 0 => Measure.dirac (fun k : Fin 0 => k.elim0)
  | n + 1 => (Market.filteredLaw M ρ n).bind (fun r =>
      (((M.filter ρ n r : ProbabilityMeasure EY) : Measure EY).bind M.QR).map (Fin.snoc r))

end BauerleRiederMDP.PartialObs


