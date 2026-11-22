-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:07.172116+00:00
-- url     : https://prove2.me/theorems/533858e3-cdab-4f79-a623-a73c9f65c14c
-- title:
--   Finite Dimensional Of Ortho
-- statement:
--   Definitions and structural lemmas for Finite Dimensional Of Ortho, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FiniteDimensionalOfOrtho.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
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
namespace Formalism.HermitianLattices.Ext.L3
def stdForm (K : Type) [Field K] [StarRing K] (n : ℕ) :
    (Fin n → K) →ₗ⋆[K] (Fin n → K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => ∑ i, star (x i) * y i)
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_assoc, starRingEnd_apply])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_left_comm])
def stdLat (K : Type) [Field K] (n : ℕ) : Submodule (𝓞 K) (Fin n → K) :=
  Submodule.span (𝓞 K) (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → K))
section Ortho
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace StandardSymmetricSums
end StandardSymmetricSums
open StandardSymmetricSums
end Ortho
end Formalism.HermitianLattices.Ext.L3


