-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:39:20.650986+00:00
-- url     : https://prove2.me/theorems/0f77a09c-77cd-4ca5-b04e-c9c7ada6d4c2
-- title:
--   Algebra Map Int Cast Smul
-- statement:
--   Definitions and structural lemmas for Algebra Map Int Cast Smul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapIntCastSmul.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
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
namespace Formalism.HermitianLattices.Ext.L3.LocF
variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
section Gen
variable {W : Type} [AddCommGroup W] [Module (𝓞 K) W]
end Gen
section Lat
variable [StarRing K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
end Lat
end Formalism.HermitianLattices.Ext.L3.LocF


