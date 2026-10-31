-- Prove2me | Definitions.Def_KallMayerSLP_ValueOfInfo_WS
-- name    : KallMayerSLP_ValueOfInfo_WS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:14:02.307958+00:00
-- url     : https://prove2.me/theorems/a8dfd3dd-b505-448b-b2c5-cb7dd079d37f
-- title:
--   Wait-and-see value $WS=\mathbb E_\xi[\gamma(\xi)]$ (2.68)
-- statement:
--   The expected optimal value when the decision maker may wait for the outcome of $\xi$ before deciding:
--
--   $$
--   WS=\mathbb E_\xi[\gamma(\xi)].
--   $$
--
--   **Formalization Note** The expectation is the extended-real expectation `eExp` under the law $\mu$ of $\xi$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, eq. (2.68), p.244 (PDF 253)

import Mathlib
import Definitions.Def_KallMayerSLP_ValueOfInfo_gamma
import Definitions.Def_KallMayerSLP_ValueOfInfo_eExp

open MeasureTheory

namespace KallMayerSLP.ValueOfInfo

/-- **The wait-and-see value `WS`, (2.68).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, eq. (2.68), p.244 (PDF 253):
`WS := 𝔼_ξ[γ(ξ)]`.

**Formalization Note.** `μ` is the law `ℙ_ξ`; the expectation is `eExp` (`+∞` when `𝔼[γ⁺] = +∞`). -/
noncomputable def WS {r n₁ m₁ n₂ m₂ : ℕ} (P : TwoStageSLP r n₁ m₁ n₂ m₂)
    (μ : Measure (Fin r → ℝ)) : EReal :=
  eExp μ (gamma P)

end KallMayerSLP.ValueOfInfo


