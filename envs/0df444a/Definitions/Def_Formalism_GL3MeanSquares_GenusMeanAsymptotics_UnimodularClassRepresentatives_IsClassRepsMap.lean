-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsClassRepsMap
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsClassRepsMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:39:27.18368+00:00
-- url     : https://prove2.me/theorems/294210d9-79b8-41ca-a6c7-a81f8463fa8f
-- title:
--   Is Class Reps Map
-- statement:
--   Definitions and structural lemmas for Is Class Reps Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsClassRepsMap.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.RankOne
open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
section Transfer
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
  (Φ : Submodule (𝓞 K) V ≃ Submodule (𝓞 K) V') (τ : (V ≃ₗ[K] V) ≃ (V' ≃ₗ[K] V'))
  (hτ : ∀ g, τ g ∈ isom h' ↔ g ∈ isom h)
  (hg : ∀ g M, Φ (gmap g M) = gmap (τ g) (Φ M))
  (hloc : ∀ p : Ideal (𝓞 K), p.IsMaximal → ∀ M, Φ (loc (K := K) p M) = loc (K := K) p (Φ M))
  (hlat : ∀ M, Submodule.IsLattice K (Φ M) ↔ Submodule.IsLattice K M)
include hτ hg hloc hlat
end Transfer
def mapE (φ : V ≃ₗ[K] V') : Submodule (𝓞 K) V ≃ Submodule (𝓞 K) V' :=
  (Submodule.orderIsoMapComap (φ.restrictScalars (𝓞 K))).toEquiv
def conjE (φ : V ≃ₗ[K] V') : (V ≃ₗ[K] V) ≃ (V' ≃ₗ[K] V') where
  toFun g := (φ.symm.trans g).trans φ
  invFun g := (φ.trans g).trans φ.symm
  left_inv g := by ext x; simp
  right_inv g := by ext x; simp
end Formalism.HermitianLattices.Ext.L3.RankOne


