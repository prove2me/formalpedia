-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_logObj
-- name    : BauerleRiederMDP_LQ_Supplement_logObj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:41:49.37546+00:00
-- url     : https://prove2.me/theorems/1680db08-3b17-536e-8da1-b0e76e3c4f66
-- title:
--   The one-period objective of (6.6)
-- statement:
--   **The one-period objective of (6.6)** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), eq. (6.6), p.182, PDF 195): $\int  \int  \log (1 + \alpha  \cdot  z) Q^R(dz|y) \rho (dy)$ for a belief $\rho $ and a fraction vector $\alpha $.
--
--   **Formalization Note.** Both integrals are the published extended-real `eint` (positive minus negative part, Lebesgue integrals).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (6.6), p.182, PDF 195

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_Market
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_eint

open MeasureTheory
open BauerleRiederMDP.PartialObs (Market)
open BauerleRiederMDP.RegimeSwitching (eint)

namespace BauerleRiederMDP.LQ.Supplement

/-- **The one-period objective of (6.6)** (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), eq. (6.6), p.182, PDF 195):
`∫ ∫ log(1 + α · z) Q^R(dz|y) ρ(dy)` for a belief `ρ` and a fraction vector `α`.

**Formalization Note.** Both integrals are the published extended-real `eint` (positive minus
negative part, Lebesgue integrals). -/
noncomputable def logObj {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d)
    (ρ : ProbabilityMeasure EY) (α : Fin d → ℝ) : EReal :=
  eint (ρ : Measure EY) fun y => eint (M.QR y) fun z => ((Real.log (1 + α ⬝ᵥ z) : ℝ) : EReal)

end BauerleRiederMDP.LQ.Supplement


