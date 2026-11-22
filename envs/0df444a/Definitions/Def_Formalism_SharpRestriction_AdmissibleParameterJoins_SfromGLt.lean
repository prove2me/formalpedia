-- Prove2me | Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLt
-- name    : Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:48:59.107034+00:00
-- url     : https://prove2.me/theorems/f0f283a6-c7b1-4f07-8c83-95e4c81f1ef2
-- title:
--   Sfrom GLt
-- statement:
--   Definitions and structural lemmas for Sfrom GLt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.J
open Ideal NumberField IsDedekindDomain
section Split
variable (K : Type) [Field K] [NumberField K] (p : ℕ)
variable (L : Type) [Field L] [NumberField L] [Algebra K L]
end Split
end Formalism.MainNotions.J
end


