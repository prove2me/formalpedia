-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.germ_app_eq_of_germ_eq_of_comp_eq_comp_of_fromSpecStalk_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/e4cfdd4d-152e-5be8-8d6d-769e7d7a7d8d

import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicGeometry_exists_ringHom_functionField_germ_eq_of_base_genericPoint_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_germ_app_eq_of_germ_eq_of_comp_eq_comp_of_fromSpecStalk_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve Opposite

theorem rdt_germ_app_eq_of_fromSpecStalk_comp_eq {X : Scheme.{u}} [IsIntegral X] (h : X ⟶ X)
    (E : X.presheaf.stalk (genericPoint X) ⟶ X.presheaf.stalk (genericPoint X))
    (hh : X.fromSpecStalk (genericPoint X) ≫ h = Spec.map E ≫ X.fromSpecStalk (genericPoint X))
    (U : X.Opens) (hU : genericPoint X ∈ U) (hU' : genericPoint X ∈ h ⁻¹ᵁ U) (sec : X.presheaf.obj (op U)) :
    (X.presheaf.germ (h ⁻¹ᵁ U) (genericPoint X) hU').hom ((h.app U).hom sec) =
      E.hom ((X.presheaf.germ U (genericPoint X) hU).hom sec) := by

  have hsub : ∀ p q : ↥(Spec (X.presheaf.stalk (genericPoint X))), p = q := by
    intro p q
    haveI : Unique (PrimeSpectrum X.functionField) := inferInstance
    exact Subsingleton.elim (α := PrimeSpectrum X.functionField) p q

  have hx : h.base (genericPoint X) = genericPoint X := by
    have h1 := congrArg (fun g => g.base (IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X)))) hh
    simp only [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint] at h1
    rw [h1, hsub ((Spec.map E) (IsLocalRing.closedPoint _)) (IsLocalRing.closedPoint _)]
    exact Scheme.fromSpecStalk_closedPoint

  have hins : Inseparable (genericPoint X) (h.base (genericPoint X)) := Inseparable.of_eq hx.symm
  set φ : X.presheaf.stalk (genericPoint X) ⟶ X.presheaf.stalk (genericPoint X) :=
    (X.presheaf.stalkCongr hins).hom ≫ h.stalkMap (genericPoint X) with hφ
  have hφE : φ = E := by
    have key : Spec.map φ ≫ X.fromSpecStalk (genericPoint X) = Spec.map E ≫ X.fromSpecStalk (genericPoint X) := by
      rw [← hh, hφ, Spec.map_comp, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk h]
      congr 1

      exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk hins.ge
    exact Spec.map_injective ((cancel_mono (X.fromSpecStalk (genericPoint X))).1 key)

  have hU'' : h.base (genericPoint X) ∈ U := hU'
  have e1 : (X.presheaf.germ (h ⁻¹ᵁ U) (genericPoint X) hU').hom ((h.app U).hom sec) =
      (h.stalkMap (genericPoint X)).hom ((X.presheaf.germ U (h.base (genericPoint X)) hU'').hom sec) :=
    (Scheme.Hom.germ_stalkMap_apply h U (genericPoint X) hU'' sec).symm
  have e2 : (X.presheaf.germ U (h.base (genericPoint X)) hU'').hom sec =
      ((X.presheaf.stalkCongr hins).hom).hom ((X.presheaf.germ U (genericPoint X) hU).hom sec) := by
    change _ = ((X.presheaf.germ U (genericPoint X) hU) ≫ X.presheaf.stalkSpecializes hins.ge).hom sec
    rw [TopCat.Presheaf.germ_stalkSpecializes]
  rw [e1, e2, ← CommRingCat.comp_apply, ← hφ, hφE]

theorem solution
    {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L] (M : CurveModel K L)
    {Y : Scheme.{u}} [IsIntegral Y] (φ : Y ⟶ M.C) (hφ : φ.base (genericPoint Y) = genericPoint M.C)
    (j : L →+* Y.functionField)
    (hpin : ∀ (x : L) (U : M.C.Opens) (hU : genericPoint M.C ∈ U) (hU' : genericPoint Y ∈ φ ⁻¹ᵁ U)
        (sec : M.C.presheaf.obj (op U)),
        (M.C.presheaf.germ U (genericPoint M.C) hU).hom sec = M.ffEquiv x →
        (Y.presheaf.germ (φ ⁻¹ᵁ U) (genericPoint Y) hU').hom ((φ.app U).hom sec) = j x)
    (V : L ≃ₐ[K] L) (h : M.C ⟶ M.C)
    (hh : M.C.fromSpecStalk (genericPoint M.C) ≫ h =
      Spec.map (CommRingCat.ofHom
        (M.ffEquiv.toRingHom.comp ((V : L →ₐ[K] L).toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
        M.C.fromSpecStalk (genericPoint M.C))
    (a : Y ⟶ Y) (ha₀ : a.base (genericPoint Y) = genericPoint Y) (ha : a ≫ φ = φ ≫ h) :
    ∀ (x : L) (U : Y.Opens) (hU : genericPoint Y ∈ U) (hU' : genericPoint Y ∈ a ⁻¹ᵁ U)
      (sec : Y.presheaf.obj (op U)),
      (Y.presheaf.germ U (genericPoint Y) hU).hom sec = j x →
      (Y.presheaf.germ (a ⁻¹ᵁ U) (genericPoint Y) hU').hom ((a.app U).hom sec) = j (V x) := by

  intro x U hU hU' sec hsec
  classical

  have hgerm := rdt_germ_app_eq_of_fromSpecStalk_comp_eq h
    (CommRingCat.ofHom (M.ffEquiv.toRingHom.comp ((V : L →ₐ[K] L).toRingHom.comp M.ffEquiv.symm.toRingHom))) hh

  have hηM : h.base (genericPoint M.C) = genericPoint M.C := by
    have h1 := congrArg (fun g => g.base (IsLocalRing.closedPoint (M.C.presheaf.stalk (genericPoint M.C)))) hh
    simp only [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint] at h1
    haveI : Unique (PrimeSpectrum M.C.functionField) := inferInstance
    rw [h1, Subsingleton.elim (α := PrimeSpectrum M.C.functionField)
      ((Spec.map (CommRingCat.ofHom (M.ffEquiv.toRingHom.comp ((V : L →ₐ[K] L).toRingHom.comp M.ffEquiv.symm.toRingHom))))
        (IsLocalRing.closedPoint _)) (IsLocalRing.closedPoint _)]
    exact Scheme.fromSpecStalk_closedPoint

  obtain ⟨δ, hδ⟩ := AlgebraicGeometry.exists_ringHom_functionField_germ_eq_of_base_genericPoint_eq a ha₀

  obtain ⟨W, hW, secW, hsecW⟩ := TopCat.Presheaf.exists_germ_eq M.C.presheaf (M.ffEquiv x)
  have hWφ : genericPoint Y ∈ φ ⁻¹ᵁ W := (Scheme.Hom.mem_preimage _).2 (by rw [hφ]; exact hW)
  have hjx := hpin x W hW hWφ secW hsecW
  have hWh : genericPoint M.C ∈ h ⁻¹ᵁ W := (Scheme.Hom.mem_preimage _).2 (by rw [hηM]; exact hW)
  have hA : (M.C.presheaf.germ (h ⁻¹ᵁ W) (genericPoint M.C) hWh).hom ((h.app W).hom secW) = M.ffEquiv (V x) := by
    rw [hgerm W hW hWh secW, hsecW]
    show M.ffEquiv ((V : L →ₐ[K] L) (M.ffEquiv.symm (M.ffEquiv x))) = M.ffEquiv (V x)
    rw [RingEquiv.symm_apply_apply]
    rfl
  have hWφh : genericPoint Y ∈ φ ⁻¹ᵁ (h ⁻¹ᵁ W) := (Scheme.Hom.mem_preimage _).2 (by rw [hφ]; exact hWh)
  have hjVx := hpin (V x) (h ⁻¹ᵁ W) hWh hWφh ((h.app W).hom secW) hA
  have hWa : genericPoint Y ∈ a ⁻¹ᵁ (φ ⁻¹ᵁ W) := (Scheme.Hom.mem_preimage _).2 (by rw [ha₀]; exact hWφ)
  rw [← hδ U hU hU' sec, hsec, ← hjx, hδ _ hWφ hWa, ← hjVx]
  have key : ∀ (ψ ψ' : Y ⟶ M.C) (e : ψ = ψ') (h1 : genericPoint Y ∈ ψ ⁻¹ᵁ W) (h2 : genericPoint Y ∈ ψ' ⁻¹ᵁ W),
      (Y.presheaf.germ (ψ ⁻¹ᵁ W) (genericPoint Y) h1).hom ((ψ.app W).hom secW) =
      (Y.presheaf.germ (ψ' ⁻¹ᵁ W) (genericPoint Y) h2).hom ((ψ'.app W).hom secW) := by
    rintro ψ ψ' rfl h1 h2; rfl
  exact key (a ≫ φ) (φ ≫ h) ha hWa hWφh

end S_AlgebraicCurve_CurveModel_germ_app_eq_of_germ_eq_of_comp_eq_comp_of_fromSpecStalk_comp_eq
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_germ_app_eq_of_germ_eq_of_comp_eq_comp_of_fromSpecStalk_comp_eq (solution)
