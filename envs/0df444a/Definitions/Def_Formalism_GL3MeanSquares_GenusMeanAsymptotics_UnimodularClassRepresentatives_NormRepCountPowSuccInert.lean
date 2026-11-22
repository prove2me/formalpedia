-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:30:47.665035+00:00
-- url     : https://prove2.me/theorems/b4a4f6b2-ef6c-4d6c-bfc7-83ca72bab82b
-- title:
--   Norm Rep Count Pow Succ Inert
-- statement:
--   Definitions and structural lemmas for Norm Rep Count Pow Succ Inert, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountPowSuccInert.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
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
namespace Formalism.HermitianLattices.Ext.L3.NormLifting
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def conjQ (J : Ideal (𝓞 K)) (hJ : ∀ a ∈ J, conjO K a ∈ J) : (𝓞 K ⧸ J) →+* (𝓞 K ⧸ J) :=
  Ideal.quotientMap J (conjO K) (fun a ha => hJ a ha)
end Formalism.HermitianLattices.Ext.L3.NormLifting
namespace Formalism.HermitianLattices.Ext.L3
open NormLifting
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Formalism.HermitianLattices.Ext.L3


