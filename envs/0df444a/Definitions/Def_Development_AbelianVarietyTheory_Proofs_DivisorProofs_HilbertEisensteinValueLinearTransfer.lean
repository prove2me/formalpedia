-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinValueLinearTransfer
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinValueLinearTransfer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:11.91186+00:00
-- url     : https://prove2.me/theorems/f8303b2c-e195-4473-ba67-5b89ddf432b1
-- title:
--   Hilbert Eisenstein Value Linear Transfer
-- statement:
--   Definitions and structural lemmas for Hilbert Eisenstein Value Linear Transfer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinValueLinearTransfer.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinSummandUnitSmul
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
namespace GlobalTheory.HilbFam
variable {F : Type} [Field F] [NumberField F]
set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
variable {F : Type} [Field F] [NumberField F] in
theorem _root_.GlobalTheory.HilbFam.transf_units_smul (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) (ε : (𝓞 F)ˣ) (x : Fin 2 → F) :
    T (ε • x) = ε • T x := by
  change T.toLinearMap ((ε : 𝓞 F) • x) = (ε : 𝓞 F) • T.toLinearMap x
  exact LinearMap.map_smul_of_tower T.toLinearMap _ _
noncomputable def transfQuot (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) :
    Quotient (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F)) ≃ Quotient (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F)) :=
  Quotient.congr T.toEquiv (by
    intro x y
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨ε, rfl⟩
      exact ⟨ε, (transf_units_smul T ε y).symm⟩
    · rintro ⟨ε, h⟩
      refine ⟨ε, T.injective ?_⟩
      rw [transf_units_smul]
      exact h)
end GlobalTheory.HilbFam


