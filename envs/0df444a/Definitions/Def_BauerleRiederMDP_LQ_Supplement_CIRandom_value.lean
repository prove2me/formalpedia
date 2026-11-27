-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom_value
-- name    : BauerleRiederMDP_LQ_Supplement_CIRandom_value
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:07:50.535542+00:00
-- url     : https://prove2.me/theorems/6944af31-090f-4206-a522-684ba71df548
-- title:
--   The maximal value of problem (9.1)
-- statement:
--   **The maximal value of problem (9.1)** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), eq. (9.1), p.268, PDF 278): the supremum of the objective over all admissible consumption-investment strategies, initial wealth $x$.
--
--   **Formalization Note.** A supremum in $[0, \infty ]$; the strategy $c ≡ 0$, $\varphi  ≡ 0$ is admissible for $x \ge  0$, so the supremum is over a nonempty set there.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (9.1), p.268, PDF 278

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom_IsStrategy
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom_objective

open scoped ENNReal

namespace BauerleRiederMDP.LQ.Supplement

/-- **The maximal value of problem (9.1)** (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), eq. (9.1), p.268, PDF 278): the supremum of the objective over all
admissible consumption-investment strategies, initial wealth `x`.

**Formalization Note.** A supremum in `[0, ∞]`; the strategy `c ≡ 0`, `φ ≡ 0` is admissible for
`x ≥ 0`, so the supremum is over a nonempty set there. -/
noncomputable def CIRandom.value {d : ℕ} (C : CIRandom d) (x : ℝ) : ℝ≥0∞ :=
  ⨆ (c : (n : ℕ) → (Fin n → Fin d → ℝ) → ℝ) (φ : (n : ℕ) → (Fin n → Fin d → ℝ) → Fin d → ℝ)
    (_ : C.IsStrategy x c φ), C.objective x c φ

end BauerleRiederMDP.LQ.Supplement


