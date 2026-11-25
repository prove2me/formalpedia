-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.subsingleton_etale_cohomology_succ_of_isSepClosed_point
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T16:29:16.644472+00:00
-- url     : https://prove2.me/submissions/2a66be6b-b5c7-4df8-93c2-98789f0162f7

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_14

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

theorem solution
    {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)] [IsSepClosed (X.residueField x0)]
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (n : ℕ) :
    Subsingleton (Abelian.Ext.{u}
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).obj (ModuleCat.of Λ Λ)) F (n + 1)) := by
  classical
  open RamanujanPetersson.EtSheaves in
  have hgal : Subsingleton (Gal x0) := by
    constructor
    intro σ τ
    apply AlgEquiv.ext
    intro y
    obtain ⟨c, rfl⟩ := IsSepClosed.algebraMap_surjective (k := X.residueField x0)
      (K := SeparableClosure (X.residueField x0)) y
    rw [AlgEquiv.commutes, AlgEquiv.commutes]
  open RamanujanPetersson.EtSheaves in
  have hproj : Projective (unitSh Λ X) := by
    refine ⟨fun {F G} f e _ => ?_⟩
    let s := (geomPtAt x0).stalkF Λ
    let c := constStalkIso Λ (geomPtAt x0) (ModuleCat.of Λ Λ)
    let g0 : stalk Λ (unitSh Λ X) x0 := c.inv.hom (1 : Λ)
    have hepi : Epi (s.map e) := inferInstance
    obtain ⟨m', hm'⟩ := (ModuleCat.epi_iff_surjective (s.map e)).1 hepi ((s.map f).hom g0)
    let ℓ : stalk Λ (unitSh Λ X) x0 →ₗ[Λ] stalk Λ F x0 :=
      (LinearMap.toSpanSingleton Λ _ m').comp c.hom.hom
    have hℓ : ∀ σ : Gal x0, ℓ ∘ₗ galRep Λ (unitSh Λ X) x0 σ = galRep Λ F x0 σ ∘ₗ ℓ := by
      intro σ
      rw [Subsingleton.elim σ 1, map_one, map_one]
      exact LinearMap.ext fun v => by simp
    have key : ∀ r : Λ, c.hom.hom (c.inv.hom r) = r := fun r => by
      change (c.inv ≫ c.hom).hom r = r
      rw [Iso.inv_hom_id]
      rfl
    have key2 : ∀ v, c.inv.hom (c.hom.hom v) = v := fun v => by
      change (c.hom ≫ c.inv).hom v = v
      rw [Iso.hom_inv_id]
      rfl
    refine ⟨(specField_homEquiv x0 Λ (unitSh Λ X) F).symm ⟨ℓ, hℓ⟩, ?_⟩
    apply (specField_homEquiv x0 Λ (unitSh Λ X) G).injective
    apply Subtype.ext
    rw [specField_homEquiv_apply, specField_homEquiv_apply, Functor.map_comp, ModuleCat.hom_comp]
    have h1 : (s.map ((specField_homEquiv x0 Λ (unitSh Λ X) F).symm ⟨ℓ, hℓ⟩)).hom = ℓ := by
      rw [← specField_homEquiv_apply, Equiv.apply_symm_apply]
    rw [h1]
    apply LinearMap.ext
    intro v
    rw [← key2 v]
    have hv : c.inv.hom (c.hom.hom v) = c.hom.hom v • g0 := by
      rw [← map_smul, smul_eq_mul, mul_one]
    have hg0 : ℓ g0 = m' := by
      change LinearMap.toSpanSingleton Λ _ m' (c.hom.hom (c.inv.hom 1)) = m'
      rw [key, LinearMap.toSpanSingleton_apply, one_smul]
    rw [LinearMap.comp_apply, hv, map_smul, map_smul, map_smul, hg0]
    exact congrArg _ hm'
  exact subsingleton_of_forall_eq 0 fun e => Abelian.Ext.eq_zero_of_projective e
