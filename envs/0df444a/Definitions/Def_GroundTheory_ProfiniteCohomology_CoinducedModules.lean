-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules
-- name    : GroundTheory_ProfiniteCohomology_CoinducedModules
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T15:48:45.6804+00:00
-- url     : https://prove2.me/theorems/25f65fb0-b97a-49dc-9730-43c4e6cc95b7
-- title:
--   Coinduced Modules
-- statement:
--   Definitions and structural lemmas for Coinduced Modules, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CoinducedModules.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_isLocallyConstant_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open CategoryTheory Filter Topology
universe u
section Translation
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
theorem eventually_forall_mul_eq {Y : Type*} (f : LocallyConstant G Y) :
    ∀ᶠ g in 𝓝 (1 : G), ∀ x : G, f (x * g) = f x := by
  have key := isCompact_univ.eventually_forall_of_forall_eventually (x₀ := (1 : G))
    (P := fun g x => f (x * g) = f x) (K := Set.univ) ?_
  · exact key.mono fun g hg x => hg x (Set.mem_univ x)
  intro y _
  have h1 := (f.isLocallyConstant.comp_continuous
    (continuous_snd.mul continuous_fst : Continuous fun z : G × G => z.2 * z.1)).eventually_eq
      ((1 : G), y)
  have h2 := (f.isLocallyConstant.comp_continuous
    (continuous_snd : Continuous fun z : G × G => z.2)).eventually_eq ((1 : G), y)
  filter_upwards [h1, h2] with z hz1 hz2
  change f (z.2 * z.1) = f (y * 1) at hz1
  change f z.2 = f y at hz2
  rw [hz1, hz2, mul_one]
end Translation
variable (k G : Type u) [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : Type u) [AddCommGroup X] [Module k X]
noncomputable def discreteCoindRep : Representation k G (LocallyConstant G X) where
  toFun g := LocallyConstant.comapₗ k (ContinuousMap.mulRight g)
  map_one' := by
    ext f x
    simp
  map_mul' g h := by
    ext f x
    simp [mul_assoc]
@[simp]
theorem discreteCoindRep_apply (g : G) (f : LocallyConstant G X) (x : G) :
    discreteCoindRep k G X g f x = f (x * g) :=
  rfl
noncomputable abbrev discreteCoind : Rep.{u} k G :=
  Rep.of (discreteCoindRep k G X)
instance isDiscreteRep_discreteCoind [CompactSpace G] : IsDiscreteRep (discreteCoind k G X) :=
  ⟨fun f => Subgroup.isOpen_of_mem_nhds (g := 1) _ <|
    Filter.mem_of_superset (eventually_forall_mul_eq f) fun g (hg : ∀ x, f (x * g) = f x) =>
      LocallyConstant.ext fun x => hg x⟩
noncomputable def coindEval : LocallyConstant G X →ₗ[k] X where
  toFun f := f 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
omit [IsTopologicalGroup G] in
@[simp]
theorem coindEval_apply (f : LocallyConstant G X) : coindEval k G X f = f 1 :=
  rfl
noncomputable def invariantsDiscreteCoindEquiv :
    (discreteCoindRep k G X).invariants ≃ₗ[k] X where
  toFun f := (f : LocallyConstant G X) 1
  invFun x := ⟨LocallyConstant.const G x, fun _ => rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := Subtype.ext <| LocallyConstant.ext fun x => by
    have h := congrArg (fun φ : LocallyConstant G X => φ 1) (f.2 x)
    simp only [discreteCoindRep_apply, one_mul] at h
    simp [h]
  right_inv _ := rfl
@[simp]
theorem invariantsDiscreteCoindEquiv_apply (f : (discreteCoindRep k G X).invariants) :
    invariantsDiscreteCoindEquiv k G X f = (f : LocallyConstant G X) 1 :=
  rfl
@[simp]
theorem invariantsDiscreteCoindEquiv_symm_apply (x : X) :
    ((invariantsDiscreteCoindEquiv k G X).symm x : LocallyConstant G X) =
      LocallyConstant.const G x :=
  rfl
section Embedding
variable {k G}
noncomputable def coindEmbedding (A : Rep.{u} k G) [IsDiscreteRep A] : A ⟶ discreteCoind k G A :=
  Rep.ofHom
    { toFun := fun a => ⟨fun g => A.ρ g a, isLocallyConstant_apply A a⟩
      map_add' := fun a b => LocallyConstant.ext fun g => map_add (A.ρ g) a b
      map_smul' := fun r a => LocallyConstant.ext fun g => map_smul (A.ρ g) r a
      isIntertwining' := fun h => LinearMap.ext fun a => LocallyConstant.ext fun x => by
        change A.ρ x (A.ρ h a) = A.ρ (x * h) a
        rw [map_mul, Module.End.mul_apply] }
@[simp]
theorem coindEmbedding_hom_apply (A : Rep.{u} k G) [IsDiscreteRep A] (a : A) (g : G) :
    ((coindEmbedding A).hom a : LocallyConstant G A) g = A.ρ g a :=
  rfl
@[simp]
theorem coindEval_coindEmbedding (A : Rep.{u} k G) [IsDiscreteRep A] (a : A) :
    coindEval k G A ((coindEmbedding A).hom a) = a := by
  change A.ρ 1 a = a
  rw [map_one, Module.End.one_apply]
theorem coindEmbedding_injective (A : Rep.{u} k G) [IsDiscreteRep A] :
    Function.Injective (coindEmbedding A).hom :=
  Function.LeftInverse.injective (g := coindEval k G A) (coindEval_coindEmbedding A)
instance (A : Rep.{u} k G) [IsDiscreteRep A] : Mono (coindEmbedding A) :=
  (Rep.mono_iff_injective _).2 (coindEmbedding_injective A)
noncomputable def coindEmbeddingRange (A : Rep.{u} k G) [IsDiscreteRep A] :
    Submodule k (LocallyConstant G A) :=
  LinearMap.range (coindEmbedding A).hom.toLinearMap
theorem coindEmbeddingRange_le_comap (A : Rep.{u} k G) [IsDiscreteRep A] (g : G) :
    coindEmbeddingRange A ≤ (coindEmbeddingRange A).comap ((discreteCoind k G A).ρ g) := by
  rintro _ ⟨a, rfl⟩
  exact ⟨A.ρ g a, Rep.hom_comm_apply (coindEmbedding A) g a⟩
noncomputable abbrev coindCokernel (A : Rep.{u} k G) [IsDiscreteRep A] : Rep.{u} k G :=
  (discreteCoind k G A).quotient (coindEmbeddingRange A) (coindEmbeddingRange_le_comap A)
noncomputable abbrev coindCokernelπ (A : Rep.{u} k G) [IsDiscreteRep A] :
    discreteCoind k G A ⟶ coindCokernel A :=
  Rep.mkQ (discreteCoind k G A) (coindEmbeddingRange A) (coindEmbeddingRange_le_comap A)
instance isDiscreteRep_coindCokernel [CompactSpace G] (A : Rep.{u} k G) [IsDiscreteRep A] :
    IsDiscreteRep (coindCokernel A) :=
  isDiscreteRep_quotient (discreteCoind k G A) _ _
theorem coindEmbedding_comp_coindCokernelπ (A : Rep.{u} k G) [IsDiscreteRep A] :
    coindEmbedding A ≫ coindCokernelπ A = 0 := by
  ext a
  exact (Submodule.Quotient.mk_eq_zero _).2 ⟨a, rfl⟩
noncomputable def coindShortComplex (A : Rep.{u} k G) [IsDiscreteRep A] :
    ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (coindEmbedding A) (coindCokernelπ A) (coindEmbedding_comp_coindCokernelπ A)
noncomputable def coindCokernelSection (A : Rep.{u} k G) [IsDiscreteRep A] :
    (LocallyConstant G A ⧸ coindEmbeddingRange A) →ₗ[k] LocallyConstant G A :=
  (coindEmbeddingRange A).liftQ
    (LinearMap.id - (coindEmbedding A).hom.toLinearMap ∘ₗ coindEval k G A) <| by
      rintro _ ⟨a, rfl⟩
      rw [LinearMap.mem_ker]
      change (coindEmbedding A).hom a -
        (coindEmbedding A).hom (coindEval k G A ((coindEmbedding A).hom a)) = 0
      rw [coindEval_coindEmbedding, sub_self]
end Embedding
end GroundTheory.ProfCoh


