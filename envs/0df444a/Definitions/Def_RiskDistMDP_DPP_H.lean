-- Prove2me | Definitions.Def_RiskDistMDP_DPP_H
-- name    : RiskDistMDP_DPP_H
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:56:18.347419+00:00
-- url     : https://prove2.me/theorems/5b56b73b-d939-4a15-bc9b-a7ce2c701272
-- title:
--   Policy operator $H^{\mathfrak p}_t v(x)=G^{\pi_t(x)}_t v(x)$ (3.4)
-- statement:
--   For $t\in\mathbb N$ and a Markovian policy $\mathfrak p=(\pi_t)$,
--   $$H^{\mathfrak p}_tv(x):=G^{\pi_t(x)}_tv(x).$$
--   Compositions $H^{\mathfrak p}_t\circ\cdots\circ H^{\mathfrak p}_TO$ evaluate the DRM of a Markovian policy (Lemma 3.3).
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, (3.4), p. 15

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_G

set_option autoImplicit false

open MeasureTheory

namespace RiskDistMDP.DPP

/-- The policy operator `H^𝔭_t v(x) := G^{π_t(x)}_t v(x)` of arXiv:2203.09612v4, (3.4), p.15, for
`t ∈ ℕ` and a Markovian policy `𝔭 = (π_t)`. -/
noncomputable def H {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] (R : RiskMDP 𝕏 𝔸)
    (𝔭 : ℕ → 𝕏 → ProbabilityMeasure 𝔸) (t : ℕ) (v : 𝕏 → ℝ) (x : 𝕏) : EReal :=
  G R t (𝔭 t x) v x

end RiskDistMDP.DPP


