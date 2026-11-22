-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapConjO
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapConjO
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:39:50.855111+00:00
-- url     : https://prove2.me/theorems/af616acd-b1f2-4c95-8db1-5bab7dc9a336
-- title:
--   Algebra Map Conj O
-- statement:
--   Definitions and structural lemmas for Algebra Map Conj O, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapConjO.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
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
namespace Formalism.HermitianLattices.Ext.L3.BallB
section Gram
variable {K V ι : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [Fintype ι]
  [DecidableEq ι]
end Gram
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
def gdet (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis (Fin (finrank K V)) K V) : K :=
  (Matrix.of fun i j => h (b i) (b j)).det
end Formalism.HermitianLattices.Ext.L3.BallB


