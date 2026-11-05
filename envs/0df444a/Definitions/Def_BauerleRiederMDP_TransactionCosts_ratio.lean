-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_ratio
-- name    : BauerleRiederMDP_TransactionCosts_ratio
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:19.376019+00:00
-- url     : https://prove2.me/theorems/ff80fdff-7461-4e0f-a13c-3ea675336733
-- title:
--   Stock-to-bond ratio $x_1/x_0\in[0,\infty]$
-- statement:
--   The stock-to-bond ratio of a state $x=(x_0,x_1)\in E$ is $x_1/x_0\in[0,\infty]$, with $x_1/0=\infty$ for $x_1>0$. It decides which of the sell, no-transaction and buy regions contains $x$ in (4.26) and (4.32).
--
--   **Formalization Note** Computed in $[0,\infty]$ (`ℝ≥0∞`). At $x=(0,0)$ the book's ratio is undefined and the value is $0/0=0$; statements either exclude $x=0$ or check that their value there is the only admissible stock amount $0$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.5, (4.26), p.109 (PDF 123); (4.32), p.113 (PDF 127)

import Mathlib

open scoped ENNReal

namespace BauerleRiederMDP.TransactionCosts

/-- The stock-to-bond ratio `x₁/x₀ ∈ [0, ∞]` of a state `x = (x₀, x₁) ∈ E` (Bäuerle & Rieder
2011, §4.5, (4.26), p.109, PDF 123, and (4.32), p.113, PDF 127).

**Formalization Note.** Computed in `ℝ≥0∞`: `x₁/0 = ∞` for `x₁ > 0`, as the book's regions
`x₁/x₀ > q₊` read it at `x₀ = 0`. At `x = (0, 0)`, where the book's ratio is undefined, the
`ℝ≥0∞` value is `0/0 = 0`; the statements exclude `x = 0` from the region conditions or check that
their value there is the only admissible action `0`. -/
noncomputable def ratio (x : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal x.2 / ENNReal.ofReal x.1

end BauerleRiederMDP.TransactionCosts


