-- Prove2me | Definitions.Def_GeomRescale_init
-- name    : GeomRescale_init
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:16:20.98482+00:00
-- url     : https://prove2.me/theorems/66891869-a88c-4120-8c2b-aa63de357817
-- title:
--   The initial state of Algorithm 2
-- statement:
--   Line 1 of Algorithm 2 sets $Q := I_n$, $R := I_n$ and $\Gamma := \emptyset$. All counters are $0$, and $f$ has not been evaluated.
--
--   **Formalization Note** $\mu$ and $W$ hold placeholder values until the step for lines 2–3.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 2, line 1, p.10

import Mathlib
import Definitions.Def_GeomRescale_St

namespace GeomRescale

/-- The initial state: line 1 of Algorithm 2 (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 2, p.10), `Q := I_n`, `R := I_n`,
`Γ := ∅`. Nothing has been evaluated and the counters are `0`. The values of `μ`, `W` are
placeholders until the step `Step.start`, which is lines 2–3. -/
def init (n : ℕ) : St n where
  vn := { μ := 0, W := ∅, data := [], y := 0, evals := 0, ops := 0 }
  Q := 1
  R := 1
  Γ := []
  i := 0
  mode := Mode.start

end GeomRescale


