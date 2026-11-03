-- Prove2me | Definitions.Def_WeightedCongestionBR_rhoBar
-- name    : WeightedCongestionBR_rhoBar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:54.494206+00:00
-- url     : https://prove2.me/theorems/0fb4e404-1096-48d2-a2c3-872fc17fed04
-- title:
--   Approximation factor $\bar\rho(d)$ of Algorithm 1
-- statement:
--   The factor that the proof of Theorem 6 obtains for the output of Algorithm 1:
--
--   $$
--   \bar\rho(d)=p\,\frac{1+3p^{-1}}{1-2p^{-1}} ,
--   $$
--
--   with $p$ from (9). The paper writes it as $d^{d+o(d)}$; for $d=1$, $\bar\rho(1)=160\cdot163/158\approx165.1$.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, proof of Theorem 6, p.21

import Mathlib
import Definitions.Def_WeightedCongestionBR_pConst
set_option autoImplicit false
open scoped NNReal

namespace WeightedCongestionBR

/-- The approximation factor of Algorithm 1, `ρ̄(d) := p (1 + 3p⁻¹)/(1 − 2p⁻¹)`, read off the proof of
Theorem 6 (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, p.21), where the paper writes it as `d^{d+o(d)}`. For `d = 1`,
`ρ̄(1) = 160 · 163/158`. -/
noncomputable def rhoBar (d : ℕ) : ℝ :=
  pConst d * (1 + 3 / pConst d) / (1 - 2 / pConst d)

end WeightedCongestionBR


