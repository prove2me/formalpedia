-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
-- name    : GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T14:49:40.079869+00:00
-- url     : https://prove2.me/theorems/edd88cde-7441-40cb-824a-fdbac73801cc
-- title:
--   Is Discrete Rep Iff Forall Exists Open Normal Subgroup
-- statement:
--   Definitions and structural lemmas for Is Discrete Rep Iff Forall Exists Open Normal Subgroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/DiscreteModules/IsDiscreteRepIffForallExistsOpenNormalSubgroup.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_iff
import Theorems.Thm_GroundTheory_ProfCoh_isOpen_stabilizer
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
open CategoryTheory Limits Topology
universe w u v
variable {k : Type u} {G : Type v} [CommRing k] [Group G]
section Stabilizer
variable {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
theorem stabilizer_zero : stabilizer ρ 0 = ⊤ := by
  ext g
  simp
theorem inf_le_stabilizer_add (a b : V) :
    stabilizer ρ a ⊓ stabilizer ρ b ≤ stabilizer ρ (a + b) := by
  intro g hg
  rw [Subgroup.mem_inf] at hg
  simp only [mem_stabilizer] at *
  rw [map_add, hg.1, hg.2]
theorem stabilizer_le_stabilizer_smul (r : k) (a : V) :
    stabilizer ρ a ≤ stabilizer ρ (r • a) := by
  intro g hg
  simp only [mem_stabilizer] at *
  rw [map_smul, hg]
theorem coe_stabilizer_apply (g : G) (a : V) :
    (stabilizer ρ (ρ g a) : Set G) = (fun h => g⁻¹ * h * g) ⁻¹' (stabilizer ρ a : Set G) := by
  ext h
  simp only [SetLike.mem_coe, Set.mem_preimage, mem_stabilizer, map_mul, Module.End.mul_apply]
  constructor
  · intro H
    rw [H, Representation.inv_self_apply]
  · intro H
    have := congrArg (ρ g) H
    rwa [Representation.self_inv_apply] at this
theorem stabilizer_eq_top_of_isTrivial [ρ.IsTrivial] (a : V) : stabilizer ρ a = ⊤ := by
  ext g
  simp
end Stabilizer
theorem stabilizer_le_stabilizer_hom {A B : Rep.{w} k G} (f : A ⟶ B) (a : A) :
    stabilizer A.ρ a ≤ stabilizer B.ρ (f.hom a) := by
  intro g hg
  simp only [mem_stabilizer] at *
  rw [← Rep.hom_comm_apply, hg]
theorem stabilizer_hom_of_injective {A B : Rep.{w} k G} (f : A ⟶ B)
    (hf : Function.Injective f.hom) (a : A) :
    stabilizer B.ρ (f.hom a) = stabilizer A.ρ a := by
  ext g
  simp only [mem_stabilizer]
  rw [← Rep.hom_comm_apply]
  exact hf.eq_iff
variable [TopologicalSpace G]
section Criteria
instance isDiscreteRep_of_discreteTopology [DiscreteTopology G] (A : Rep.{w} k G) :
    IsDiscreteRep A :=
  ⟨fun _ => isOpen_discrete _⟩
instance isDiscreteRep_of_isTrivial (A : Rep.{w} k G) [A.ρ.IsTrivial] : IsDiscreteRep A :=
  ⟨fun a => by rw [stabilizer_eq_top_of_isTrivial]; exact isOpen_univ⟩
theorem IsDiscreteRep.of_subsingleton (A : Rep.{w} k G) [Subsingleton A] : IsDiscreteRep A :=
  ⟨fun a => by rw [Subsingleton.elim a 0, stabilizer_zero]; exact isOpen_univ⟩
variable [IsTopologicalGroup G]
omit [IsTopologicalGroup G] in

theorem IsDiscreteRep.of_injective {A B : Rep.{w} k G} (f : A ⟶ B)
    (hf : Function.Injective f.hom) [IsDiscreteRep B] : IsDiscreteRep A :=
  ⟨fun a => by
    rw [← stabilizer_hom_of_injective f hf a]; exact GroundTheory.ProfCoh.isOpen_stabilizer B _⟩
theorem IsDiscreteRep.of_surjective {A B : Rep.{w} k G} (f : A ⟶ B)
    (hf : Function.Surjective f.hom) [IsDiscreteRep A] : IsDiscreteRep B :=
  ⟨fun b => by
    obtain ⟨a, rfl⟩ := hf b
    exact Subgroup.isOpen_mono (stabilizer_le_stabilizer_hom f a)
      (GroundTheory.ProfCoh.isOpen_stabilizer A a)⟩
theorem IsDiscreteRep.of_iso {A B : Rep.{w} k G} (e : A ≅ B) [IsDiscreteRep A] :
    IsDiscreteRep B :=
  IsDiscreteRep.of_surjective e.hom fun b => ⟨e.inv.hom b, Rep.hom_inv_apply (e := e) (x := b)⟩
end Criteria
variable [IsTopologicalGroup G]
section Smooth
def smoothSubmodule (A : Rep.{w} k G) : Submodule k A where
  carrier := {a | IsOpen (stabilizer A.ρ a : Set G)}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, stabilizer_zero, Subgroup.coe_top]
    exact isOpen_univ
  add_mem' {a b} ha hb := by
    refine Subgroup.isOpen_mono (inf_le_stabilizer_add A.ρ a b) ?_
    rw [Subgroup.coe_inf]
    exact ha.inter hb
  smul_mem' r a ha := Subgroup.isOpen_mono (stabilizer_le_stabilizer_smul A.ρ r a) ha
theorem mem_smoothSubmodule (A : Rep.{w} k G) (a : A) :
    a ∈ smoothSubmodule A ↔ IsOpen (stabilizer A.ρ a : Set G) :=
  Iff.rfl
theorem apply_mem_smoothSubmodule (A : Rep.{w} k G) (g : G) {a : A}
    (ha : a ∈ smoothSubmodule A) : A.ρ g a ∈ smoothSubmodule A := by
  rw [mem_smoothSubmodule, coe_stabilizer_apply]
  exact ha.preimage ((continuous_const.mul continuous_id).mul continuous_const)
theorem smoothSubmodule_le_comap (A : Rep.{w} k G) (g : G) :
    smoothSubmodule A ≤ (smoothSubmodule A).comap (A.ρ g) :=
  fun _ ha => apply_mem_smoothSubmodule A g ha
theorem hom_mem_smoothSubmodule {A B : Rep.{w} k G} (f : A ⟶ B) {a : A}
    (ha : a ∈ smoothSubmodule A) : f.hom a ∈ smoothSubmodule B :=
  Subgroup.isOpen_mono (stabilizer_le_stabilizer_hom f a) ha
theorem isDiscreteRep_iff_smoothSubmodule_eq_top (A : Rep.{w} k G) :
    IsDiscreteRep A ↔ smoothSubmodule A = ⊤ := by
  rw [isDiscreteRep_iff, Submodule.eq_top_iff']
  rfl
theorem mem_smoothSubmodule_of_isDiscreteRep (A : Rep.{w} k G) [IsDiscreteRep A] (a : A) :
    a ∈ smoothSubmodule A :=
  isOpen_stabilizer A a
abbrev smoothSubrep (A : Rep.{w} k G) : Rep.{w} k G :=
  A.subrepresentation (smoothSubmodule A) (smoothSubmodule_le_comap A)
end Smooth
section Closure
instance isDiscreteRep_subrepresentation (A : Rep.{w} k G) [IsDiscreteRep A] (W : Submodule k A)
    (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) : IsDiscreteRep (A.subrepresentation W le_comap) :=
  IsDiscreteRep.of_injective (Rep.subtype A W le_comap) fun _ _ h => Subtype.ext h
instance isDiscreteRep_quotient (A : Rep.{w} k G) [IsDiscreteRep A] (W : Submodule k A)
    (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) : IsDiscreteRep (A.quotient W le_comap) :=
  IsDiscreteRep.of_surjective (Rep.mkQ A W le_comap) (Submodule.mkQ_surjective W)
instance isDiscreteRep_smoothSubrep (A : Rep.{w} k G) : IsDiscreteRep (smoothSubrep A) :=
  ⟨fun a => by
    rw [← stabilizer_hom_of_injective (Rep.subtype A (smoothSubmodule A)
      (smoothSubmodule_le_comap A)) (fun _ _ h => Subtype.ext h) a]
    exact a.2⟩
instance isDiscreteRep_biprod (A B : Rep.{w} k G) [IsDiscreteRep A] [IsDiscreteRep B] :
    IsDiscreteRep (A ⊞ B) := by
  rw [isDiscreteRep_iff_smoothSubmodule_eq_top, Submodule.eq_top_iff']
  intro x
  have hx : x = (biprod.inl : A ⟶ A ⊞ B).hom ((biprod.fst : A ⊞ B ⟶ A).hom x) +
      (biprod.inr : B ⟶ A ⊞ B).hom ((biprod.snd : A ⊞ B ⟶ B).hom x) :=
    calc x = (𝟙 (A ⊞ B) : A ⊞ B ⟶ A ⊞ B).hom x := rfl
      _ = (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr : A ⊞ B ⟶ A ⊞ B).hom x := by
        rw [biprod.total]
      _ = _ := by
        rw [Rep.add_hom, Representation.IntertwiningMap.coe_add, Pi.add_apply]
        rfl
  rw [hx]
  exact Submodule.add_mem _
    (hom_mem_smoothSubmodule biprod.inl (mem_smoothSubmodule_of_isDiscreteRep A _))
    (hom_mem_smoothSubmodule biprod.inr (mem_smoothSubmodule_of_isDiscreteRep B _))
instance isDiscreteRep_biproduct {J : Type} [Fintype J] (f : J → Rep.{w} k G) [HasBiproduct f]
    [∀ j, IsDiscreteRep (f j)] : IsDiscreteRep (⨁ f) := by
  rw [isDiscreteRep_iff_smoothSubmodule_eq_top, Submodule.eq_top_iff']
  intro x
  have hx : x = ∑ j, (biproduct.ι f j).hom ((biproduct.π f j).hom x) :=
    calc x = (𝟙 (⨁ f) : ⨁ f ⟶ ⨁ f).hom x := rfl
      _ = (∑ j, biproduct.π f j ≫ biproduct.ι f j : ⨁ f ⟶ ⨁ f).hom x := by
        rw [biproduct.total (f := f)]
      _ = _ := by
        rw [Rep.sum_hom, Representation.IntertwiningMap.sum_apply]
        rfl
  rw [hx]
  exact Submodule.sum_mem _ fun j _ =>
    hom_mem_smoothSubmodule (biproduct.ι f j) (mem_smoothSubmodule_of_isDiscreteRep (f j) _)
instance isDiscreteRep_directSum {ι : Type w} (A : ι → Rep.{w} k G) [∀ i, IsDiscreteRep (A i)] :
    IsDiscreteRep (Rep.of (Representation.directSum fun i => (A i).ρ)) := by
  classical
  refine ⟨fun x => ?_⟩
  change x ∈ smoothSubmodule (Rep.of (Representation.directSum fun i => (A i).ρ))
  rw [← DirectSum.sum_support_of x]
  refine Submodule.sum_mem _ fun i _ => ?_
  refine Subgroup.isOpen_mono (H₁ := stabilizer (A i).ρ (x i)) ?_ (isOpen_stabilizer (A i) (x i))
  intro g hg
  simp only [mem_stabilizer] at *
  change DirectSum.lmap (fun j => (A j).ρ g) (DirectSum.of _ i (x i)) = DirectSum.of _ i (x i)
  rw [DirectSum.lmap_of, hg]
instance isDiscreteRep_prod (A B : Rep.{w} k G) [IsDiscreteRep A] [IsDiscreteRep B] :
    IsDiscreteRep (Rep.of (A.ρ.prod B.ρ)) :=
  ⟨fun x => by
    refine Subgroup.isOpen_mono (H₁ := stabilizer A.ρ x.1 ⊓ stabilizer B.ρ x.2) ?_ ?_
    · intro g hg
      rw [Subgroup.mem_inf] at hg
      simp only [mem_stabilizer] at *
      exact Prod.ext hg.1 hg.2
    · rw [Subgroup.coe_inf]
      exact (isOpen_stabilizer A x.1).inter (isOpen_stabilizer B x.2)⟩
end Closure
section Subcategory
instance : (isDiscreteRep.{w} k G).IsClosedUnderSubobjects where
  prop_of_mono f _ hY := by
    have : IsDiscreteRep _ := hY
    exact IsDiscreteRep.of_injective f ((Rep.mono_iff_injective f).1 ‹_›)
instance : (isDiscreteRep.{w} k G).IsClosedUnderQuotients where
  prop_of_epi f _ hX := by
    have : IsDiscreteRep _ := hX
    exact IsDiscreteRep.of_surjective f ((Rep.epi_iff_surjective f).1 ‹_›)
instance : (isDiscreteRep.{w} k G).ContainsZero where
  exists_zero := ⟨Rep.trivial k G PUnit, (Rep.isZero_iff k G _).2 inferInstance,
    IsDiscreteRep.of_subsingleton _⟩
instance : (isDiscreteRep.{w} k G).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := ⟨by
    rintro X ⟨p⟩
    have := Fintype.ofFinite J
    have : HasFiniteBiproducts (Rep.{w} k G) := HasFiniteBiproducts.of_hasFiniteProducts
    have h : ∀ j, IsDiscreteRep ((p.diag.obj ∘ Discrete.mk) j) := fun j => p.prop_diag_obj _
    have e : X ≅ ⨁ (p.diag.obj ∘ Discrete.mk) :=
      IsLimit.conePointsIsoOfNatIso p.isLimit (biproduct.isLimit _) Discrete.natIsoFunctor
    exact IsDiscreteRep.of_iso e.symm⟩
noncomputable instance : Abelian (DiscreteRep.{w} k G) := inferInstance
end Subcategory
section LocallyConstant
end LocallyConstant
section Invariants
theorem isDiscreteRep_quotientToInvariants (A : Rep.{w} k G) (U : Subgroup G) [U.Normal]
    (hU : IsOpen (U : Set G)) : IsDiscreteRep (A.quotientToInvariants U) := by
  have := QuotientGroup.discreteTopology hU
  infer_instance
instance isDiscreteRep_quotientToInvariants_openNormalSubgroup (A : Rep.{w} k G)
    (U : OpenNormalSubgroup G) : IsDiscreteRep (A.quotientToInvariants U.toSubgroup) :=
  isDiscreteRep_quotientToInvariants A U.toSubgroup U.isOpen
end Invariants
end GroundTheory.ProfCoh


