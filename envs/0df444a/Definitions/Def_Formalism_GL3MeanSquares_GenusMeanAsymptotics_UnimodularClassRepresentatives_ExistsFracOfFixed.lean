-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:50:10.744774+00:00
-- url     : https://prove2.me/theorems/b8abaab5-8e24-44a8-bf98-3aba3103d7e7
-- title:
--   Exists Frac Of Fixed
-- statement:
--   Definitions and structural lemmas for Exists Frac Of Fixed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsFracOfFixed.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
def toK (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] (t : 𝓞 F) : K :=
  algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t)
end Formalism.HermitianLattices.Ext.L3.U0


