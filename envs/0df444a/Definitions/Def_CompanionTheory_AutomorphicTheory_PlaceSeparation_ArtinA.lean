-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_PlaceSeparation_ArtinA
-- name    : CompanionTheory_AutomorphicTheory_PlaceSeparation_ArtinA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:54.952564+00:00
-- url     : https://prove2.me/theorems/9c87a03a-4e54-4aa3-aaeb-118b38137eee
-- title:
--   Artin A
-- statement:
--   Definitions and structural lemmas for Artin A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/PlaceSeparation/ArtinA.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise
namespace CompanionTheory.FamInh
variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra L Ω]
  [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsAlgClosure L Ω]
variable [IsGalois K L]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)}
def intAut (L : Type) [Field L] [NumberField L] [Algebra L Ω] (σ : G K Ω) : IntCl L Ω ≃+* IntCl L Ω where
  toFun b := ⟨σ b, ((isIntegral_int_of_isIntegral b.2).map (σ.toAlgHom.restrictScalars ℤ)).tower_top⟩
  invFun b := ⟨σ.symm b, ((isIntegral_int_of_isIntegral b.2).map (σ.symm.toAlgHom.restrictScalars ℤ)).tower_top⟩
  left_inv b := Subtype.ext (σ.symm_apply_apply _)
  right_inv b := Subtype.ext (σ.apply_symm_apply _)
  map_mul' a b := Subtype.ext (map_mul σ _ _)
  map_add' a b := Subtype.ext (map_add σ _ _)
end CompanionTheory.FamInh
end


