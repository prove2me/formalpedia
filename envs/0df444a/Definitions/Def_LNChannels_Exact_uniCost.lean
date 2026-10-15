-- Prove2me | Definitions.Def_LNChannels_Exact_uniCost
-- name    : LNChannels_Exact_uniCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:20.739976+00:00
-- url     : https://prove2.me/theorems/9bab8937-862d-4390-a069-e9553cccbddc
-- title:
--   (1), p. 6 — the unidirectional cost formula at a real channel size
-- statement:
--   For a payment rate $\lambda$, discount rate $r$, reset cost $B$ and a real channel size $m$, set
--
--   $$u(m)=m+B\left(\left(\frac{r+\lambda}{\lambda}\right)^{m}-1\right)^{-1}.$$
--
--   At a natural size $m=l_2$ this is the right-hand side of (1), the cost of a unidirectional channel. The paper minimizes this expression over real sizes $m>0$ (by differentiating in $m$) to obtain the minimal cost (2).
--
--   **Formalization Note** The power is the real power `Real.rpow`, so $m$ ranges over the reals. This is the closed-form expression only, used to state the minimization (2); the cost of a unidirectional channel itself is defined by its equations (`IsUniCostFn`), and its equality with (1) at natural sizes is a separate theorem.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 6 (PDF p. 7), Theorem 1 (i), equation (1); real-size reading from the proof of Theorem 2(i), p. 11 (PDF p. 12)

import Mathlib

set_option autoImplicit false

namespace LNChannels.Exact

/-- The right-hand side of (1), p. 6, at a real channel size `m`, for payment rate `lam`:
`m + B (((r + λ)/λ)^m − 1)⁻¹`, with a real-exponent (`Real.rpow`) power. -/
noncomputable def uniCost (lam r B m : ℝ) : ℝ := m + B * (((r + lam) / lam) ^ m - 1)⁻¹

end LNChannels.Exact


