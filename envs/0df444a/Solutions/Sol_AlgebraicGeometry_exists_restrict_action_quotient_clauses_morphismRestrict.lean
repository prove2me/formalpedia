-- Prove2me | solution 1 for AlgebraicGeometry.exists_restrict_action_quotient_clauses_morphismRestrict
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/02d705f8-8267-5fc5-9767-1905dba1659c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_restrict_action_quotient_clauses_morphismRestrict

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

namespace QuotOpenRestrictAux

theorem appLE_injective {M X : Scheme.{u}} (f : M ⟶ X) (V : X.Opens) {A : M.Opens}
    (e : A = f ⁻¹ᵁ V) (h : A ≤ f ⁻¹ᵁ V) (hinj : Function.Injective (f.app V)) :
    Function.Injective (f.appLE V A h) := by
  subst e
  rw [Scheme.Hom.appLE_eq_app]
  exact hinj

theorem range_appLE_eq {M X : Scheme.{u}} (f : M ⟶ X) (V : X.Opens) {A : M.Opens}
    (e : A = f ⁻¹ᵁ V) (h : A ≤ f ⁻¹ᵁ V) (G : Type u)
    (α : G → (Γ(M, f ⁻¹ᵁ V) ⟶ Γ(M, f ⁻¹ᵁ V))) (β : G → (Γ(M, A) ⟶ Γ(M, A)))
    (hαβ : ∀ g, α g ≫ M.presheaf.map (homOfLE h).op = M.presheaf.map (homOfLE h).op ≫ β g)
    (hr : Set.range (f.app V) = {s | ∀ g, α g s = s}) :
    Set.range (f.appLE V A h) = {s | ∀ g, β g s = s} := by
  subst e
  have h1 : M.presheaf.map (homOfLE h).op = 𝟙 _ := by
    rw [Subsingleton.elim (homOfLE h) (𝟙 _), op_id, M.presheaf.map_id]
  have h2 : ∀ g, α g = β g := fun g => by simpa [h1] using hαβ g
  rw [Scheme.Hom.appLE_eq_app, hr]
  ext s
  simp only [Set.mem_setOf_eq, h2]

end QuotOpenRestrictAux

theorem solution
    {M X : Scheme.{u}} (G : Type u) [Group G] [Finite G] (ρ : G →* Aut M)
    (π : M ⟶ X) [IsFinite π] (hπ : ∀ g : G, (ρ g).hom ≫ π = π)
    (hsurj : Function.Surjective π.base)
    (horbit : ∀ x x' : M, π.base x = π.base x' ↔ ∃ g : G, (ρ g).hom.base x = x')
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s})
    (U : X.Opens) :
    ∃ ρ' : G →* Aut ((π ⁻¹ᵁ U : M.Opens) : Scheme.{u}),
      (∀ g : G, (ρ' g).hom ≫ (π ⁻¹ᵁ U).ι = (π ⁻¹ᵁ U).ι ≫ (ρ g).hom) ∧
      (∃ hπ' : ∀ g : G, (ρ' g).hom ≫ (π ∣_ U) = π ∣_ U,
        IsFinite (π ∣_ U) ∧
        Function.Surjective (π ∣_ U).base ∧
        (∀ u u' : ((π ⁻¹ᵁ U : M.Opens) : Scheme.{u}), (π ∣_ U).base u = (π ∣_ U).base u' ↔ ∃ g : G, (ρ' g).hom.base u = u') ∧
        (∀ V : (U : Scheme.{u}).Opens, Function.Injective ((π ∣_ U).app V)) ∧
        (∀ V : (U : Scheme.{u}).Opens, Set.range ((π ∣_ U).app V) =
          {s | ∀ g : G, (ρ' g).hom.appLE ((π ∣_ U) ⁻¹ᵁ V) ((π ∣_ U) ⁻¹ᵁ V)
            (by rw [← Scheme.Hom.comp_preimage, hπ' g]) s = s})) := by

  have hW : ∀ g : G, (π ⁻¹ᵁ U) ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ U) := fun g =>
    le_of_eq (by rw [← Scheme.Hom.comp_preimage, hπ g])

  let r : G → (((π ⁻¹ᵁ U : M.Opens) : Scheme.{u}) ⟶ ((π ⁻¹ᵁ U : M.Opens) : Scheme.{u})) :=
    fun g => (ρ g).hom.resLE (π ⁻¹ᵁ U) (π ⁻¹ᵁ U) (hW g)
  have r_ι : ∀ g, r g ≫ (π ⁻¹ᵁ U).ι = (π ⁻¹ᵁ U).ι ≫ (ρ g).hom := fun g =>
    Scheme.Hom.resLE_comp_ι _ _
  have r_one : r 1 = 𝟙 _ := by
    rw [← cancel_mono (π ⁻¹ᵁ U).ι, r_ι, map_one, Category.id_comp]
    exact Category.comp_id _
  have r_mul : ∀ g h : G, r (g * h) = r h ≫ r g := by
    intro g h
    rw [← cancel_mono (π ⁻¹ᵁ U).ι]
    simp only [Category.assoc, r_ι, map_mul, Aut.Aut_mul_def, Iso.trans_hom]
    rw [← Category.assoc (r h), r_ι, Category.assoc]
  let ρ₁ : G → Aut ((π ⁻¹ᵁ U : M.Opens) : Scheme.{u}) := fun g =>
    { hom := r g
      inv := r g⁻¹
      hom_inv_id := by rw [← r_mul, inv_mul_cancel, r_one]
      inv_hom_id := by rw [← r_mul, mul_inv_cancel, r_one] }
  let ρ' : G →* Aut ((π ⁻¹ᵁ U : M.Opens) : Scheme.{u}) :=
    { toFun := ρ₁
      map_one' := Iso.ext r_one
      map_mul' := fun g h => Iso.ext (by
        change r (g * h) = (ρ₁ g * ρ₁ h).hom
        rw [Aut.Aut_mul_def, Iso.trans_hom]
        exact r_mul g h) }
  have ρ'_hom : ∀ g, (ρ' g).hom = r g := fun _ => rfl
  have hπ' : ∀ g : G, (ρ' g).hom ≫ (π ∣_ U) = π ∣_ U := fun g => by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ρ'_hom, ← Category.assoc, r_ι,
      Category.assoc, hπ]
  refine ⟨ρ', fun g => r_ι g, hπ', inferInstance, ?_, ?_, ?_, ?_⟩
  ·
    have : Surjective π := ⟨hsurj⟩
    exact (MorphismProperty.of_isPullback (P := @Surjective)
      (isPullback_morphismRestrict π U).flip this).surj
  ·
    intro u u'
    constructor
    · intro h
      have h1 : π.base u.1 = π.base u'.1 := by
        have := congrArg Subtype.val h
        rwa [morphismRestrict_base_coe, morphismRestrict_base_coe] at this
      obtain ⟨g, hg⟩ := (horbit u.1 u'.1).mp h1
      refine ⟨g, Subtype.ext ?_⟩
      rw [ρ'_hom]
      change ((ρ g).hom.resLE (π ⁻¹ᵁ U) (π ⁻¹ᵁ U) (hW g) u).1 = u'.1
      rw [Scheme.Hom.coe_resLE_apply]
      exact hg
    · rintro ⟨g, rfl⟩
      have := congrArg (fun k => k.base u) (hπ' g)
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
      exact this.symm
  ·
    intro V
    rw [morphismRestrict_app']
    exact QuotOpenRestrictAux.appLE_injective π (U.ι ''ᵁ V) (image_morphismRestrict_preimage π U V) _
      (hsec _)
  ·
    intro V
    rw [morphismRestrict_app']
    have hβ : ∀ (g : G) (h'),
        (ρ' g).hom.appLE ((π ∣_ U) ⁻¹ᵁ V) ((π ∣_ U) ⁻¹ᵁ V) h' =
          (ρ g).hom.appLE ((π ⁻¹ᵁ U).ι ''ᵁ ((π ∣_ U) ⁻¹ᵁ V)) ((π ⁻¹ᵁ U).ι ''ᵁ ((π ∣_ U) ⁻¹ᵁ V))
            ((Scheme.Hom.le_resLE_preimage_iff _ (hW g) _ _).mp h') := by
      intro g h'
      exact Scheme.Hom.resLE_appLE (ρ g).hom (hW g) _ _ h'
    simp_rw [hβ]
    refine QuotOpenRestrictAux.range_appLE_eq π (U.ι ''ᵁ V) (image_morphismRestrict_preimage π U V) _ G
      (fun g => (ρ g).hom.appLE (π ⁻¹ᵁ (U.ι ''ᵁ V)) (π ⁻¹ᵁ (U.ι ''ᵁ V))
        (by rw [← Scheme.Hom.comp_preimage, hπ g]))
      (fun g => (ρ g).hom.appLE _ _ _) (fun g => ?_) (hinv _)
    simp only [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

end S_AlgebraicGeometry_exists_restrict_action_quotient_clauses_morphismRestrict
end P2MW
export P2MW.S_AlgebraicGeometry_exists_restrict_action_quotient_clauses_morphismRestrict (solution)
