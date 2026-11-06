-- Prove2me | Definitions.Def_RiskDistMDP_DPP_polSeqOp
-- name    : RiskDistMDP_DPP_polSeqOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:57.419909+00:00
-- url     : https://prove2.me/theorems/0d69370f-e52c-4ae4-bdf2-7bd7baa7987d
-- title:
--   Policy operator on sequences $\mathfrak H^{\mathfrak p}\mathfrak v=(H^{\mathfrak p}_tv_{t+1})_{t\in\mathbb N}$
-- statement:
--   For $\mathfrak p\in\Pi$ and a sequence $\mathfrak v=(v_t)_{t\in\mathbb N}$,
--   $$\mathfrak H^{\mathfrak p}\mathfrak v:=\big(H^{\mathfrak p}_tv_{t+1}\big)_{t\in\mathbb N}.$$
--   Its fixed point is the infinite-horizon value of $\mathfrak p$ (Proposition 5.2).
--
--   **Formalization Note** Real-valued via `.toReal`; Proposition 5.2 states that the values are finite.
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, p. 22

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_H

set_option autoImplicit false

open MeasureTheory

namespace RiskDistMDP.DPP

/-- The operator `ℌ^𝔭 𝔳 := (H^𝔭_t v_{t+1})_{t∈ℕ}` on sequences `𝔳 = (v_t)_{t∈ℕ}`
(arXiv:2203.09612v4, p.22).

**Formalization Note** Real-valued through `.toReal` of `H^𝔭_t`; Proposition 5.2
(`proposition_5_2`) states that these values are finite. Index `0` is unused. -/
noncomputable def polSeqOp {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] (R : RiskMDP 𝕏 𝔸)
    (𝔭 : ℕ → 𝕏 → ProbabilityMeasure 𝔸) (v : ℕ → 𝕏 → ℝ) (t : ℕ) (x : 𝕏) : ℝ :=
  (H R 𝔭 t (v (t + 1)) x).toReal

end RiskDistMDP.DPP


