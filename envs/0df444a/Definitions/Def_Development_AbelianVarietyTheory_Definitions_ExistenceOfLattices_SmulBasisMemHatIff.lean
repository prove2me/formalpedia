-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_SmulBasisMemHatIff
-- name    : Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_SmulBasisMemHatIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:24.926271+00:00
-- url     : https://prove2.me/theorems/fa54d982-328a-4af6-b5af-916619b8d3a6
-- title:
--   Smul Basis Mem Hat Iff
-- statement:
--   Definitions and structural lemmas for Smul Basis Mem Hat Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/SmulBasisMemHatIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AdLat.Model
open NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
def ext {n : ℕ} (φ : (Fin n → E) →ₗ[F] F) : (Fin n → RA F E) →+ FiniteAdeleRing (𝓞 F) F where
  toFun z := ∑ i, TensorProduct.rid F _
    (LinearMap.lTensor (FiniteAdeleRing (𝓞 F) F) (φ ∘ₗ LinearMap.single F (fun _ => E) i) (z i))
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]
def freeLat {n : ℕ} {ι : Type} (b : Module.Basis ι F (Fin n → E)) : Set (Fin n → E) :=
  {x | ∀ j, b.coord j x ∈ (algebraMap (𝓞 F) F).range}
end GlobalTheory.AdLat.Model


