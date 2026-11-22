-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomScale
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomScale
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:36:47.264496+00:00
-- url     : https://prove2.me/theorems/5eee5c65-d4fc-4131-bcd4-42feb6b9ee55
-- title:
--   Exists Isom Scale
-- statement:
--   Definitions and structural lemmas for Exists Isom Scale, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomScale.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
def cutW (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V) (X : V) : Submodule K V :=
  W ⊓ LinearMap.ker (h X)
def cutM (h : V →ₗ⋆[K] V →ₗ[K] K) (M : AddSubgroup V) (X : V) : AddSubgroup V :=
  M ⊓ (LinearMap.ker (h X)).toAddSubgroup
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}
end Formalism.HermitianLattices.Ext.L3.U0


