-- Prove2me | Definitions.Def_LNChannels_SmallRate_uniOptimalSize
-- name    : LNChannels_SmallRate_uniOptimalSize
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T11:00:07.138161+00:00
-- url     : https://prove2.me/theorems/a93d7567-b619-4c66-a23b-6195dc2fb769
-- title:
--   Optimal unidirectional channel size
-- statement:
--   Set $k=B\log(1+r/\lambda)$. The channel size displayed after equation (2) is
--
--   $$l_2^*=\frac{B}{k}\log\!\left(\frac{k+\sqrt{k(k+4)}+2}{2}\right).$$
--
--   Theorem 3(i)'s size milestone checks both its optimality and its small-rate expansion. **Formalization Note** The later theorem assumes $B,\lambda,r>0$, so $k>0$.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 6 (PDF 7), sentence following equation (2)

import Mathlib

set_option autoImplicit false

namespace LNChannels.SmallRate

/-- The channel size displayed after equation (2), with k = B log (1 + r/λ). -/
noncomputable def uniOptimalSize (lam r B : ℝ) : ℝ :=
  let k := B * Real.log (1 + r / lam)
  B / k * Real.log ((k + Real.sqrt (k * (k + 4)) + 2) / 2)

end LNChannels.SmallRate


