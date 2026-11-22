-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieOp
-- name    : Formalism_SharpRestriction_Divisibility_HookProducts_RBTieOp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:25:44.302815+00:00
-- url     : https://prove2.me/theorems/1565addf-dd91-4a64-b9a7-e479da44ef1a
-- title:
--   RBTie Op
-- statement:
--   Definitions and structural lemmas for RBTie Op, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieOp.lean

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField Module
noncomputable section
namespace Formalism.MainNotions.DIV.HookProducts.RBTie
section Op
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {VN VR : Type} [AddCommGroup VN] [Module K VN] [AddCommGroup VR] [Module K VR]
  {ιN ιR : Type} [Fintype ιN] [DecidableEq ιN] [Fintype ιR] [DecidableEq ιR] {d n : ℕ}
end Op
end Formalism.MainNotions.DIV.HookProducts.RBTie


