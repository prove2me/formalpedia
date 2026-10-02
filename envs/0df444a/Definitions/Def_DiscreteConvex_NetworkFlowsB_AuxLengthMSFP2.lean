-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxLengthMSFP2
-- name    : DiscreteConvex_NetworkFlowsB_AuxLengthMSFP2
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:25:36.158646+00:00
-- url     : https://prove2.me/theorems/97751fdd-55c8-45fe-af22-48d5e405105c
-- title:
--   AuxLengthMSFP2
-- statement:
--   The arc-length function $\ell_\xi$ of Eq. (9.71).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.263, Eq. (9.71).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.263, Eq. (9.71)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Boundary
import Definitions.Def_DiscreteConvex_NetworkFlowsB_DirDeriv

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The arc-length function `ℓξ` of Eq. (9.71). -/
noncomputable def AuxLengthMSFP2 (tail head : A → V) (gamma : A → ℝ) (f : (V → ℝ) → WithTop ℝ) (xi : A → ℝ) :
    A ⊕ A ⊕ (V × V) → WithTop ℝ
  | .inl a => (gamma a : WithTop ℝ)
  | .inr (.inl a) => ((-gamma a : ℝ) : WithTop ℝ)
  | .inr (.inr (u, v)) =>
      DirDeriv f (Boundary tail head xi)
        (fun w => -(if w = u then (1:ℝ) else 0) + (if w = v then (1:ℝ) else 0))

-- ===== Integer versions (MSFP3, MSFP2 for integer flows) =====

end DiscreteConvex.NetworkFlowsB


