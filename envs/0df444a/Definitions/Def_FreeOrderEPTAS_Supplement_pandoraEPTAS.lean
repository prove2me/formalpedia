-- Prove2me | Definitions.Def_FreeOrderEPTAS_Supplement_pandoraEPTAS
-- name    : FreeOrderEPTAS_Supplement_pandoraEPTAS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:40:12.05959+00:00
-- url     : https://prove2.me/theorems/092595ed-8aff-5be2-a37f-f9fe89a9bd2a
-- title:
--   The EPTAS of Theorem 1.4 as a program
-- statement:
--   The algorithm of Theorem 1.4: the reduction of Theorem 6.1 run with the published Free-Order Prophets program `freeOrder` at accuracy $\varepsilon$ (the algorithm of Theorem 3.1) as its subroutine, with an LP solver and a dependent-rounding procedure.
--
--   **Formalization Note** All work of `freeOrder` is counted. Each of its oracle queries is a query of the $Y$-oracle, which `freeOrder` charges as one oracle call; its true cost (one $X$-oracle query and at most 5 operations) is accounted for in Theorem 1.4.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, Theorem 1.4, p.5 (with Theorem 6.1, p.31, and Theorem 3.1, p.17)

import Mathlib
import Definitions.Def_FreeOrderEPTAS_Supplement_pandoraReduce
import Definitions.Def_FreeOrderEPTAS_freeOrder

namespace FreeOrderEPTAS.Supplement

variable {n : ℕ}

/-- The algorithm of Theorem 1.4 (arXiv:2007.13121v3, p.5): the reduction of Theorem 6.1 with the
published Free-Order Prophets program `freeOrder ε` (Theorem 3.1) as its subroutine, run on the
oracle of `Y`, with the LP solver `lp` and the rounding `rnd`.

**Formalization Note.** The work of `freeOrder` is counted in full. Each of its oracle queries is a
query of `yOracle`, which `freeOrder` charges as one oracle call; its true cost is one query of the
`X`-oracle and at most 5 operations (`callY`), which Theorem 1.4 accounts for. -/
noncomputable def pandoraEPTAS (ε : ℝ) (o : Fin n → ℝ → ℝ) (κ : Fin n → WithTop ℝ)
    (c : Fin n → ℝ) (lp : LPSolver) (rnd : Rounding) : Prog (PBCPolicy n) :=
  pandoraReduce (fun oY => freeOrder ε oY lp rnd) o κ c

end FreeOrderEPTAS.Supplement


