-- Prove2me | solution 1 for AlgebraicGeometry.stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/22712b86-2339-5220-91d0-44333dae54a5

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_map_germ_ker_ideal_eq_ker_stalkMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective.AlgebraicGeometry"

universe u

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective Scheme.toSpecΓ_naturality_assoc Scheme.Hom Scheme.Hom.app SurjectiveOnStalks.stalkMap_surjective Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Scheme.Hom.comp_appTop IsClosedImmersion.spec_of_surjective IsClosedImmersion Scheme.Hom.comp_app exists_isAffineOpen_mem_and_subset SurjectiveOnStalks toSpecΓ_SpecMap_ΓSpecIso_inv IsAffineOpen Scheme.Hom.ker_apply Scheme.ΓSpecIso Scheme.Hom.map_germ_ker_ideal_eq_ker_stalkMap" namespace IsAffineOpen p2m_export "AlgebraicGeometry.IsAffineOpen" "fromSpec_preimage_self fromSpec_app_self fromSpec fromSpec_toSpecΓ_assoc" end AlgebraicGeometry.IsAffineOpen
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.IsAffineOpen" in

theorem AlgebraicGeometry.IsAffineOpen.fromSpec_comp_eq_specMap_of_hom_spec
    {O : Type u} [CommRing O] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of O)) {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp
      ((f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom))) := by
  simp only [CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp]
  rw [← hU.fromSpec_toSpecΓ_assoc, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem solution
    {O κ : Type u} [CommRing O] [CommRing κ] (q : O →+* κ) (hq : Function.Surjective q)
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of O)) (g : Y ⟶ X) (t : Y ⟶ Spec (CommRingCat.of κ))
    (H : IsPullback g t f (Spec.map (CommRingCat.ofHom q))) (y : Y) :
    Function.Surjective (g.stalkMap y).hom ∧
      RingHom.ker (g.stalkMap y).hom =
        Ideal.map ((X.presheaf.germ ⊤ (g.base y) trivial).hom.comp
          ((f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom)) (RingHom.ker q) := by
  classical
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom q)) := IsClosedImmersion.spec_of_surjective _ hq
  haveI : IsClosedImmersion g := MorphismProperty.of_isPullback H.flip inferInstance
  refine ⟨SurjectiveOnStalks.stalkMap_surjective g y, ?_⟩

  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := g.base y) (U := ⊤) trivial
  have h272 := AlgebraicGeometry.Scheme.Hom.map_germ_ker_ideal_eq_ker_stalkMap g y ⟨U, hU⟩ hxU
  rw [← h272, Scheme.Hom.ker_apply]

  set φU : O →+* Γ(X, U) := (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp
    ((f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom) with hφU

  have hKJ : RingHom.ker (g.app U).hom = Ideal.map φU (RingHom.ker q) := by
    apply le_antisymm
    ·
      intro a ha
      rw [RingHom.mem_ker] at ha
      set J : Ideal Γ(X, U) := Ideal.map φU (RingHom.ker q) with hJ

      let πJ : Γ(X, U) →+* Γ(X, U) ⧸ J := Ideal.Quotient.mk J
      let ψ₀ : O ⧸ RingHom.ker q →+* Γ(X, U) ⧸ J :=
        Ideal.Quotient.lift (RingHom.ker q) (πJ.comp φU) (fun b hb => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem φU hb))
      let e : O ⧸ RingHom.ker q ≃+* κ := RingHom.quotientKerEquivOfSurjective hq
      let ψ : κ →+* Γ(X, U) ⧸ J := ψ₀.comp e.symm.toRingHom
      have hψ : ψ.comp q = πJ.comp φU := by
        ext b
        have heb : e.symm (q b) = Ideal.Quotient.mk (RingHom.ker q) b := by
          apply e.injective
          rw [RingEquiv.apply_symm_apply]
          rfl
        show ψ₀ (e.symm (q b)) = πJ (φU b)
        rw [heb]
        rfl

      let h : Spec (CommRingCat.of (Γ(X, U) ⧸ J)) ⟶ X := Spec.map (CommRingCat.ofHom πJ) ≫ hU.fromSpec
      have hcomm : h ≫ f = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom q) := by
        show (Spec.map (CommRingCat.ofHom πJ) ≫ hU.fromSpec) ≫ f = _
        rw [Category.assoc, AlgebraicGeometry.IsAffineOpen.fromSpec_comp_eq_specMap_of_hom_spec f hU, ← Spec.map_comp, ← Spec.map_comp,
          ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← hφU, hψ]
      let l := H.lift h (Spec.map (CommRingCat.ofHom ψ)) hcomm
      have hl : l ≫ g = h := H.lift_fst h (Spec.map (CommRingCat.ofHom ψ)) hcomm

      have hha : (h.app U).hom a = 0 := by
        rw [← hl, Scheme.Hom.comp_app]
        show (l.app _).hom ((g.app U).hom a) = 0
        rw [ha, map_zero]

      obtain ⟨ε, hε⟩ : ∃ ε : hU.fromSpec ⁻¹ᵁ U ⟶ ⊤, hU.fromSpec.app U = (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map ε.op :=
        ⟨_, hU.fromSpec_app_self⟩
      have hnat2 := (Spec.map (CommRingCat.ofHom πJ)).naturality ε.op
      have hread : (h.app U).hom a =
          ((Spec (CommRingCat.of (Γ(X, U) ⧸ J))).presheaf.map ((TopologicalSpace.Opens.map (Spec.map (CommRingCat.ofHom πJ)).base).map ε.op.unop).op).hom
            ((Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ J))).inv.hom (πJ a)) := by
        show ((Spec.map (CommRingCat.ofHom πJ) ≫ hU.fromSpec).app U).hom a = _
        rw [Scheme.Hom.comp_app, hε]
        simp only [CommRingCat.hom_comp, RingHom.comp_apply]
        have h4 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso Γ(X, U)).inv.hom a)) hnat2
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h4
        erw [h4]
        congr 1
        have h5 := congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom πJ))
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h5
        exact h5.symm

      have htop : (Spec.map (CommRingCat.ofHom πJ)) ⁻¹ᵁ (hU.fromSpec ⁻¹ᵁ U) = ⊤ := by
        rw [hU.fromSpec_preimage_self]; rfl
      let m : (Spec.map (CommRingCat.ofHom πJ)) ⁻¹ᵁ (hU.fromSpec ⁻¹ᵁ U) ⟶ (⊤ : (Spec (CommRingCat.of (Γ(X, U) ⧸ J))).Opens) :=
        (TopologicalSpace.Opens.map (Spec.map (CommRingCat.ofHom πJ)).base).map ε.op.unop
      let m' : (⊤ : (Spec (CommRingCat.of (Γ(X, U) ⧸ J))).Opens) ⟶ (Spec.map (CommRingCat.ofHom πJ)) ⁻¹ᵁ (hU.fromSpec ⁻¹ᵁ U) :=
        eqToHom htop.symm
      have hmm : m' ≫ m = 𝟙 _ := Subsingleton.elim _ _
      have hinj : ∀ z, ((Spec (CommRingCat.of (Γ(X, U) ⧸ J))).presheaf.map m.op).hom z = 0 → z = 0 := by
        intro z hz
        have h3 : ((Spec (CommRingCat.of (Γ(X, U) ⧸ J))).presheaf.map m'.op).hom
            (((Spec (CommRingCat.of (Γ(X, U) ⧸ J))).presheaf.map m.op).hom z) = z := by
          rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, hmm, op_id, CategoryTheory.Functor.map_id, CommRingCat.id_apply]
        rw [← h3, hz, map_zero]
      have hz : (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ J))).inv.hom (πJ a) = 0 :=
        hinj _ (hread ▸ hha)
      have hπ : πJ a = 0 := by
        apply (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ J))).commRingCatIsoToRingEquiv.symm.injective
        rw [map_zero]
        exact hz
      exact Ideal.Quotient.eq_zero_iff_mem.mp hπ
    ·
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker, hφU, RingHom.comp_apply, RingHom.comp_apply]
      have hnat := g.naturality (homOfLE (le_top : U ≤ ⊤)).op
      have h1 : (g.app U).hom ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom ((f.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a))) =
          (Y.presheaf.map ((TopologicalSpace.Opens.map g.base).map (homOfLE (le_top : U ≤ ⊤)).op.unop).op).hom
            ((g.appTop).hom ((f.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a))) := by
        rw [← CommRingCat.comp_apply, hnat, CommRingCat.comp_apply]
        rfl
      rw [h1, ← CommRingCat.comp_apply _ g.appTop, ← Scheme.Hom.comp_appTop, H.w, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        ← CommRingCat.comp_apply _ (Spec.map (CommRingCat.ofHom q)).appTop, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
      have hqa : q a = 0 := RingHom.mem_ker.mp ha
      have hqa' : (ConcreteCategory.hom (CommRingCat.ofHom q)) a = 0 := hqa
      rw [hqa', map_zero, map_zero]
      exact map_zero _
  have hcomp : (X.presheaf.germ U (g.base y) hxU).hom.comp φU =
      (X.presheaf.germ ⊤ (g.base y) trivial).hom.comp ((f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom) := by
    ext a
    simp only [hφU, RingHom.comp_apply]
    exact TopCat.Presheaf.germ_res_apply X.presheaf _ _ _ _
  rw [show (Scheme.Hom.app g U) = g.app U from rfl, hKJ, Ideal.map_map, hcomp]

end S_AlgebraicGeometry_stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective
end P2MW
export P2MW.S_AlgebraicGeometry_stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective (solution)
