-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:11.553803+00:00
-- url     : https://prove2.me/theorems/96934868-2345-4936-bb25-4b1e4414e5f4
-- title:
--   Exists Primitive Norm
-- statement:
--   Definitions and structural lemmas for Exists Primitive Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsPrimitiveNorm.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
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
structure IsLatIn (S : Subring K) (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V)
    (M : AddSubgroup V) : Prop where
  le : ∀ m ∈ M, m ∈ W
  smul_mem : ∀ a ∈ S, ∀ m ∈ M, a • m ∈ M
  int : ∀ x ∈ M, ∀ y ∈ M, h x y ∈ S
  span : ∀ x ∈ W, ∃ t : K, t ≠ 0 ∧ t • x ∈ M
structure IsSD (S : Subring K) (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V)
    (M : AddSubgroup V) : Prop extends IsLatIn S h W M where
  dual : ∀ x ∈ W, (∀ m ∈ M, h m x ∈ S) → x ∈ M
structure IsASD (S : Subring K) (π : K) (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V)
    (M : AddSubgroup V) (z : V) : Prop extends IsLatIn S h W M where
  z_mem : z ∈ M
  z_norm : IsUnitIn S (h z z * π⁻¹)
  z_rad : ∀ m ∈ M, Dv S π (h z m)
  dual : ∀ x ∈ W, h z x = 0 → (∀ m ∈ M, h m x ∈ S) → x ∈ M
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}
end Formalism.HermitianLattices.Ext.L3.U0


