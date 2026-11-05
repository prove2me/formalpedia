-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_twValue
-- name    : BauerleRiederMDP_PartialObs_twValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:04:11.986589+00:00
-- url     : https://prove2.me/theorems/7eeb9bbd-d8d0-460a-98bd-ad5b3cc0c740
-- title:
--   The maximal value of the terminal wealth problem (6.2)
-- statement:
--   The partially observable terminal wealth problem is
--   $$
--   \begin{cases}\mathbb E_x U(X^\varphi_N)\to\max\\ \varphi \text{ is a portfolio strategy and } X^\varphi_N\in\operatorname{dom}U \text{ a.s.}\end{cases}\tag{6.2}
--   $$
--   where admissible strategies may depend only on the observable stock prices. Its maximal value is
--   $$
--   \sup_{\varphi\ \text{admissible}}\ \mathbb E\,U(X^\varphi_N)\in[-\infty,\infty],
--   $$
--   the expectation being taken under the market law of the returns with $Y_0\sim Q_0$ and the supremum over all admissible (history-dependent) strategies.
--
--   **Formalization Note** Extended-real values; the expectation is $\int U^+ - \int U^-$.
-- source:
--   Bäuerle & Rieder (2011), §6.1, (6.2), p.176 (PDF 189)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_twAdmissible
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_eint

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **The maximal value of the partially observable terminal wealth problem (6.2).**
Bäuerle & Rieder (2011), §6.1, p.176 (PDF 189):
`IE_x U(X^φ_N) → max`, `φ` is a portfolio strategy and `X^φ_N ∈ dom U` IP-a.s.  (6.2)
with `F_n = F^S_n`, "i.e. the admissible portfolio strategies depend only on the observable stock
prices".

`twValue M i domU U N x` is the supremum of `IE U(X^φ_N)` (computed under the market law with
`Y_0 ~ Q_0`) over all admissible strategies (`twAdmissible`), which are arbitrary measurable
functions of the observed history: no Markov or filter structure is imposed on the competitors.

**Formalization Note.** Values are in `EReal`; the expectation is `eint` (positive minus negative
part), so a strategy with `IE U(X^φ_N) = −∞` contributes `−∞`. -/
noncomputable def twValue {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d) (i : ℝ)
    (domU : Set ℝ) (U : ℝ → ℝ) (N : ℕ) (x : ℝ) : EReal :=
  ⨆ φ ∈ {φ : (n : ℕ) → (Fin n → Fin d → ℝ) → Fin d → ℝ | twAdmissible M i domU N x φ},
    BauerleRiederMDP.RegimeSwitching.eint (M.returnLaw M.Q0 N) (fun r => ((U (wealth (fun _ => i) x φ N r) : ℝ) : EReal))

end BauerleRiederMDP.PartialObs


