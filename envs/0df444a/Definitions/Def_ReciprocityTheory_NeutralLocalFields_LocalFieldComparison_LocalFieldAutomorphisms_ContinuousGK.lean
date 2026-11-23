-- Prove2me | Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ContinuousGK
-- name    : ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ContinuousGK
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:41.060169+00:00
-- url     : https://prove2.me/theorems/ba54c89e-1a9e-46ec-a945-6bfecefb8212
-- title:
--   Continuous GK
-- statement:
--   Definitions and structural lemmas for Continuous GK, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ContinuousGK.lean

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ValuationIntCastLtOneIff
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_MemRangeOfAevalRatEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Pointwise
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
theorem exists_res (ι : Ω →+* PadicAlgCl p) (σ : GK F ι) : ∃ τ : Ω ≃ₐ[F] Ω, ∀ x, ι (τ x) = σ (ι x) := by
  letI : Algebra Ω (PadicAlgCl p) := ι.toAlgebra
  letI : Algebra F (PadicAlgCl p) := (ι.comp (algebraMap F Ω)).toAlgebra
  haveI : IsScalarTower F Ω (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Normal F Ω := IsAlgClosure.normal F Ω
  let χ : PadicAlgCl p ≃ₐ[F] PadicAlgCl p := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun c =>
    σ.commutes ⟨ι (algebraMap F Ω c), IntermediateField.subset_adjoin _ _ ⟨c, rfl⟩⟩
  exact ⟨χ.restrictNormal Ω, fun x => χ.restrictNormal_commutes Ω x⟩
def res (ι : Ω →+* PadicAlgCl p) : GK F ι →* (Ω ≃ₐ[F] Ω) where
  toFun σ := Classical.choose (exists_res ι σ)
  map_one' := by
    ext x
    apply ι.injective
    rw [Classical.choose_spec (exists_res ι 1) x]
    rfl
  map_mul' σ τ := by
    ext x
    apply ι.injective
    rw [Classical.choose_spec (exists_res ι (σ * τ)) x, AlgEquiv.mul_apply, AlgEquiv.mul_apply,
      Classical.choose_spec (exists_res ι σ), Classical.choose_spec (exists_res ι τ)]
end ReciprocityTheory.Neutral.Cmp


