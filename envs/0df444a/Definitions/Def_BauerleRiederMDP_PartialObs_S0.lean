-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_S0
-- name    : BauerleRiederMDP_PartialObs_S0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:00:33.072331+00:00
-- url     : https://prove2.me/theorems/1cdaccec-7524-45de-9463-9ca0a7ef61bc
-- title:
--   The bond price $S^0_n=\prod_{k=1}^n(1+i_k)$
-- statement:
--   The riskless bond has price $S^0_0\equiv1$ and $S^0_{n+1}:=S^0_n(1+i_{n+1})$, where $i_{n+1}$ is the deterministic interest rate of the period $[n,n+1)$. Hence
--   $$
--   S^0_n=\prod_{k=1}^n(1+i_k),
--   $$
--   and $S^0_n=(1+i)^n$ for a constant rate.
-- source:
--   Bäuerle & Rieder (2011), §3.1, p.61 (PDF 75)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **The bond price `S^0_n`.**
Bäuerle & Rieder (2011), §3.1, p.61 (PDF 75): `S^0_0 ≡ 1`, `S^0_{n+1} := S^0_n (1 + i_{n+1})`, where
`i_{n+1}` is the interest rate of the period `[n, n+1)`; so `S^0_n = ∏_{k=1}^n (1 + i_k)`, and
`S^0_n = (1 + i)^n` for a constant rate. -/
noncomputable def S0 (i : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 + i (k + 1))

end BauerleRiederMDP.PartialObs


