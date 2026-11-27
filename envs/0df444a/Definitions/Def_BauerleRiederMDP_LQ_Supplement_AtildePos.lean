-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_AtildePos
-- name    : BauerleRiederMDP_LQ_Supplement_AtildePos
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:55:35.92167+00:00
-- url     : https://prove2.me/theorems/a7732470-c5a2-5534-b935-37a277d06664
-- title:
--   The admissible fractions $\tilde A $ for logarithmic utility
-- statement:
--   **The admissible fractions $\tilde A $ for logarithmic utility** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §6.1 "Logarithmic Utility", p.181, PDF 194): `Ã := {α ∈ ℝ^d | 1 + α · R(y) > 0 ℙ-a.s.}`.
--
--   **Formalization Note.** As the published `PartialObs.Atilde` (the $\ge  0$ set of the power case): the intersection over $y \in  E_Y$, which under (FM)(ii) is each of the sets.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §6.1 "Logarithmic Utility", p.181, PDF 194

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_Market

open MeasureTheory
open BauerleRiederMDP.PartialObs (Market)

namespace BauerleRiederMDP.LQ.Supplement

/-- **The admissible fractions `Ã` for logarithmic utility** (Bäuerle & Rieder, *Markov Decision
Processes with Applications to Finance* (2011), §6.1 "Logarithmic Utility", p.181, PDF 194):
`Ã := {α ∈ ℝ^d | 1 + α · R(y) > 0 ℙ-a.s.}`.

**Formalization Note.** As the published `PartialObs.Atilde` (the `≥ 0` set of the power case):
the intersection over `y ∈ E_Y`, which under (FM)(ii) is each of the sets. -/
def AtildePos {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d) : Set (Fin d → ℝ) :=
  {α | ∀ y, ∀ᵐ z ∂M.QR y, 0 < 1 + α ⬝ᵥ z}

end BauerleRiederMDP.LQ.Supplement


