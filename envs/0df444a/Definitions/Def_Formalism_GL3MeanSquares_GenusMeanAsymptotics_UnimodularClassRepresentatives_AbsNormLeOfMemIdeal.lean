-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormLeOfMemIdeal
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormLeOfMemIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:03.691515+00:00
-- url     : https://prove2.me/theorems/530cd187-90f1-4c24-b389-1538461fb37b
-- title:
--   Abs Norm Le Of Mem Ideal
-- statement:
--   Definitions and structural lemmas for Abs Norm Le Of Mem Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AbsNormLeOfMemIdeal.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormEqProdOfMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.BoxCube
open BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
end Formalism.HermitianLattices.Ext.L3.BoxCube


