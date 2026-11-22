-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:25:47.733802+00:00
-- url     : https://prove2.me/theorems/681f3ac8-096c-439b-96ca-5ab561c71eed
-- title:
--   Exists Isom Frame
-- statement:
--   Definitions and structural lemmas for Exists Isom Frame, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomFrame.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormOneOfPair
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
structure IsSelfDualMod (S : Subring K) (h : V →ₗ⋆[K] V →ₗ[K] K) (M : AddSubgroup V) : Prop where
  smul_mem : ∀ a ∈ S, ∀ m ∈ M, a • m ∈ M
  int : ∀ x ∈ M, ∀ y ∈ M, h x y ∈ S
  dual : ∀ x : V, (∀ m ∈ M, h m x ∈ S) → x ∈ M
  span : ∀ x : V, ∃ t : K, t ≠ 0 ∧ t • x ∈ M
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V}
end Formalism.HermitianLattices.Ext.L3.WA


