-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:24:54.472965+00:00
-- url     : https://prove2.me/theorems/932c460b-c4ce-44e9-b43b-168fa945c8a1
-- title:
--   Card Filter Res Char Le
-- statement:
--   Definitions and structural lemmas for Card Filter Res Char Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardFilterResCharLe.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
variable {K : Type} [Field K] [NumberField K]
def resChar (P : Ideal (𝓞 K)) : ℕ := Ideal.absNorm (P.under ℤ)
end Formalism.HermitianLattices.Ext.L3.IdealNormInequalities


