-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_D
-- name    : BauerleRiederMDP_LQ_Supplement_TWMarket_D
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:33:34.652026+00:00
-- url     : https://prove2.me/theorems/ca8a5c34-4ba4-5136-869d-0333956bcb85
-- title:
--   The admissible investments
-- statement:
--   **The admissible investments** $D_n(x)$ (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), eq. (4.4), p.80, PDF 94, and the HARA form on p.88, PDF 102): for a family $E_n$ of state sets, `D_n(x) := {a ∈ ℝ^d | (1 + i_{n+1})(x + a · R_{n+1}) ∈ E_{n+1} ℙ-a.s.}`. With $E_n = dom U$ for all $n$ this is (4.4); with $E_n = \{x | x S^0_N/S^0_n + b \ge  0\}$ it is the admissible set of the HARA problem (p.88).
--
--   **Formalization Note.** The state sets are a parameter $Es : \mathbb N  \to  Set \mathbb R $, so one definition covers both forms.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (4.4), p.80, PDF 94, and the HARA form on p.88, PDF 102

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket

open MeasureTheory

namespace BauerleRiederMDP.LQ.Supplement

/-- **The admissible investments** `D_n(x)` (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), eq. (4.4), p.80, PDF 94, and the HARA form on p.88, PDF 102): for a
family `E_n` of state sets,
`D_n(x) := {a ∈ ℝ^d | (1 + i_{n+1})(x + a · R_{n+1}) ∈ E_{n+1} ℙ-a.s.}`.
With `E_n = dom U` for all `n` this is (4.4); with `E_n = {x | x S^0_N/S^0_n + b ≥ 0}` it is the
admissible set of the HARA problem (p.88).

**Formalization Note.** The state sets are a parameter `Es : ℕ → Set ℝ`, so one definition covers
both forms. -/
def TWMarket.D {d : ℕ} (Mk : TWMarket d) (Es : ℕ → Set ℝ) (n : ℕ) (x : ℝ) : Set (Fin d → ℝ) :=
  {a | ∀ᵐ z ∂(Mk.ν (n + 1) : Measure (Fin d → ℝ)), (1 + Mk.i (n + 1)) * (x + a ⬝ᵥ z) ∈ Es (n + 1)}

end BauerleRiederMDP.LQ.Supplement


