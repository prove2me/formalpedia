-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxLengthMCFP0
-- name    : DiscreteConvex_NetworkFlowsB_AuxLengthMCFP0
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:31.124992+00:00
-- url     : https://prove2.me/theorems/580bf684-970e-4712-a426-587795670c88
-- title:
--   AuxLengthMCFP0
-- statement:
--   The arc-length function $\ell_\xi$ of Eq. (9.34).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.252, Eq. (9.34).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.252, Eq. (9.34)

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The arc-length function `ℓξ` of Eq. (9.34). -/
def AuxLengthMCFP0 (gamma : A → ℝ) : A ⊕ A → WithTop ℝ
  | .inl a => (gamma a : WithTop ℝ)
  | .inr a => ((-gamma a : ℝ) : WithTop ℝ)

-- ===== MSFP2 (linear arc cost, M-convex boundary cost) =====

end DiscreteConvex.NetworkFlowsB


