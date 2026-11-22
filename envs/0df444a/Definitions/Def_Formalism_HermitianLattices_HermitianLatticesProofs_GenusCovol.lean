-- Prove2me | Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
-- name    : Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:21:51.160943+00:00
-- url     : https://prove2.me/theorems/831673b3-6685-404b-a691-5be1f5f707de
-- title:
--   Genus Covol
-- statement:
--   Definitions and structural lemmas for Genus Covol, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovol.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_hsmul_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_hsmul_right
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_sigma_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
namespace Formalism.HermitianLatticesTheory
section PartS
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
end PartS
section PartT
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
theorem star_algebraMap_ringOfIntegers_mem_range (r : 𝓞 K) : star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
  ⟨⟨star (algebraMap (𝓞 K) K r), r.isIntegral_coe.map (starRingEnd K).toIntAlgHom⟩, rfl⟩
theorem genusCovol_hinj : Function.Injective (algebraMap (𝓞 K) K) :=
  FaithfulSMul.algebraMap_injective _ _
def genusCovol_tdual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) V where
  carrier := {y | ∀ x ∈ L, ∃ z : ℤ, Algebra.trace ℚ K (h x y) = z}
  add_mem' := by
    intro a b ha hb x hx
    obtain ⟨z1, h1⟩ := ha x hx
    obtain ⟨z2, h2⟩ := hb x hx
    exact ⟨z1 + z2, by rw [map_add, map_add, h1, h2]; push_cast; ring⟩
  zero_mem' := fun x _ => ⟨0, by simp⟩
  smul_mem' := by
    intro r y hy x hx
    obtain ⟨z, hz⟩ := hy (locBasic_sigma genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range r • x)
      (L.smul_mem _ hx)
    refine ⟨z, ?_⟩
    rw [← hz]
    congr 1
    rw [genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range, genusBasic_hsmul_right,
      locBasic_sigma_spec, locBasic_sigma_spec, star_star]
end PartT
section PartE
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end PartE
section PartF
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end PartF
end Formalism.HermitianLatticesTheory


