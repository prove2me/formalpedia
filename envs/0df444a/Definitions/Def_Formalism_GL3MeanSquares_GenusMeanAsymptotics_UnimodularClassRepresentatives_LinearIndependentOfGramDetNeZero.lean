-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:39:00.949403+00:00
-- url     : https://prove2.me/theorems/c939de29-df9a-4936-ad09-27436c8decfd
-- title:
--   Linear Independent Of Gram Det Ne Zero
-- statement:
--   Definitions and structural lemmas for Linear Independent Of Gram Det Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LinearIndependentOfGramDetNeZero.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthUnitFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GmapLocEqOfFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.LocF
open Formalism.HermitianLattices.Ext.L3.WA
section Units
variable {K : Type*} [Field K] {S : Subring K}
end Units
section Ring
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Ring
section Gram
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ}
end Gram
section Cramer
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ}
end Cramer
end Formalism.HermitianLattices.Ext.L3.LocF


