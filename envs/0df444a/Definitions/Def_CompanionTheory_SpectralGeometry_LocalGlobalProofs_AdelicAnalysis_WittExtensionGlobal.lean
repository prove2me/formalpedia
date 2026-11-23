-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WittExtensionGlobal
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WittExtensionGlobal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:22.739486+00:00
-- url     : https://prove2.me/theorems/508a6fce-73cc-4517-a6fb-e099a634332c
-- title:
--   Witt Extension Global
-- statement:
--   Definitions and structural lemmas for Witt Extension Global, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.WittE
section Form
variable {E V : Type} [Field E] [AddCommGroup V] [Module E V] {σ : E →+* E}
def IsIsom (B : V →ₛₗ[σ] V →ₗ[E] E) (γ : V →ₗ[E] V) : Prop :=
  ∀ z w, B (γ z) (γ w) = B z w
def lin {n : ℕ} (X : Fin n → V) (c : Fin n → E) : V := ∑ a, c a • X a
end Form
section Induct
variable {E V : Type} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  {σ : E →+* E}
end Induct
section Concrete
variable {E : Type} [Field E]
def formB (s : E →+* E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    (Fin M → E) →ₛₗ[s] (Fin M → E) →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ s (RingHom.id E) (fun x y => hform s J x y)
    (fun x x' y => by
      simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc])
    (fun x y y' => by
      simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
end Concrete
end GlobalTheory.CompanionTheory.SW.WittE


