-- Prove2me | Definitions.Def_FoundationsRL_E2DStructured_decSup
-- name    : FoundationsRL_E2DStructured_decSup
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:25:22.238993+00:00
-- url     : https://prove2.me/theorems/a7076cf7-15b3-42df-b4a2-bfde7cd1b97f
-- title:
--   The DEC over unconstrained reference models
-- statement:
--   The Decision-Estimation Coefficient over unconstrained reference models is
--   $$\sup_{\hat f:\Pi\to\mathbb R}\mathrm{dec}_\gamma(\mathcal F,\hat f).$$
--   This is the quantity that controls the regret of E2D for arbitrary $\Pi$ and $\mathcal F$, and it is the left side of Proposition 24.
--
--   **Formalization Note** The supremum ranges over measurable $\hat f$, the functions for which the expectations in the DEC are defined.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §4.2, p. 66; Proposition 24, p. 80

import Mathlib
import Definitions.Def_FoundationsRL_E2DStructured_dec

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- The DEC over unconstrained reference models, `sup_{f̂:Π→ℝ} dec_γ(F, f̂)`
(Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.2, p. 66, last display of the proof of Proposition 13; p. 80, Proposition 24).

**Formalization Note.** The supremum ranges over measurable `f̂`: the expectations in (4.15) are
meaningful only for those. -/
noncomputable def decSup {D : Type*} [MeasurableSpace D] (γ : ℝ) (F : Set (D → ℝ)) : EReal :=
  ⨆ (fhat : D → ℝ) (_ : Measurable fhat), dec γ F fhat

end FoundationsRL.E2DStructured


