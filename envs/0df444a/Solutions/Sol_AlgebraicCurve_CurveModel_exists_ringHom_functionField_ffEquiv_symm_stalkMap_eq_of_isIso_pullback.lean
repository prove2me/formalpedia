-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.exists_ringHom_functionField_ffEquiv_symm_stalkMap_eq_of_isIso_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/e64780df-2517-51b4-9453-09a1304d3321

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicGeometry_genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_exists_ringHom_functionField_ffEquiv_symm_stalkMap_eq_of_isIso_pullback

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K))
    {L : Type v} [Field L] [Algebra K L] (M : AlgebraicCurve.CurveModel K L)
    {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of R))
    (e₀ : M.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M.toBase) :
    ∃ Θ : X.functionField →+* L,
      (∀ (P : X) (hgenP : (e₀ ≫ pullback.fst c _).base (genericPoint M.C) ⤳ P) (z : X.presheaf.stalk P),
        M.ffEquiv.symm ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) (genericPoint M.C)).hom
          ((X.presheaf.stalkSpecializes hgenP).hom z)) = Θ (algebraMap (X.presheaf.stalk P) X.functionField z)) ∧
      (∀ (x : M.C) (w : X.presheaf.stalk ((e₀ ≫ pullback.fst c _).base x)),
        M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x) M.C.functionField
          ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) x).hom w)) =
          Θ (algebraMap (X.presheaf.stalk ((e₀ ≫ pullback.fst c _).base x)) X.functionField w)) ∧
      (∀ (P : X) (r : R), Θ (algebraMap (X.presheaf.stalk P) X.functionField
          ((X.presheaf.germ ⊤ P trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))) =
        algebraMap K L (algebraMap R K r)) ∧
      (IsIso (Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) (genericPoint M.C)) → Function.Bijective Θ) := by
  set f := e₀ ≫ pullback.fst c _ with hfdef

  have HGEN : f.base (genericPoint M.C) = genericPoint X := by
    have hgp : IsGenericPoint (f.base (genericPoint M.C)) Set.univ := by
      rw [isGenericPoint_iff_specializes]
      intro z
      simp only [Set.mem_univ, iff_true]
      rw [specializes_iff_forall_open]
      intro U hU hzU
      exact AlgebraicGeometry.genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap
        hinj c e₀ ⟨U, hU⟩ ⟨z, hzU⟩
    exact (hgp.inseparable (genericPoint_spec X)).eq
  have hξX : f.base (genericPoint M.C) ⤳ genericPoint X := HGEN ▸ specializes_rfl
  set Θ : X.functionField →+* L := M.ffEquiv.symm.toRingHom.comp ((Scheme.Hom.stalkMap f (genericPoint M.C)).hom.comp
      (X.presheaf.stalkSpecializes hξX).hom) with hΘ
  have h1 : ∀ (P : X) (hgenP : f.base (genericPoint M.C) ⤳ P) (z : X.presheaf.stalk P),
      M.ffEquiv.symm ((Scheme.Hom.stalkMap f (genericPoint M.C)).hom ((X.presheaf.stalkSpecializes hgenP).hom z)) =
        Θ (algebraMap (X.presheaf.stalk P) X.functionField z) := by
    intro P hgenP z
    simp only [hΘ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    congr 2
    rw [RingHom.algebraMap_toAlgebra]
    erw [← CommRingCat.comp_apply (X.presheaf.stalkSpecializes _) (X.presheaf.stalkSpecializes hξX),
      TopCat.Presheaf.stalkSpecializes_comp]
  refine ⟨Θ, h1, ?_, ?_, ?_⟩
  ·
    intro x w
    rw [← h1 (f.base x) ((genericPoint_specializes x).map f.continuous) w]
    congr 1
    rw [RingHom.algebraMap_toAlgebra]
    erw [← Scheme.Hom.stalkSpecializes_stalkMap_apply f (genericPoint M.C) x (genericPoint_specializes x)]
  ·
    intro P r
    have hfc : f ≫ c = M.toBase ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
      rw [hfdef, Category.assoc, pullback.condition, ← Category.assoc, he₀]
    simp only [hΘ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [RingHom.algebraMap_toAlgebra]
    erw [← CommRingCat.comp_apply (X.presheaf.stalkSpecializes _) (X.presheaf.stalkSpecializes hξX), TopCat.Presheaf.stalkSpecializes_comp]
    erw [← CommRingCat.comp_apply (X.presheaf.germ ⊤ P trivial) (X.presheaf.stalkSpecializes _),
      TopCat.Presheaf.germ_stalkSpecializes]
    erw [Scheme.Hom.germ_stalkMap_apply f ⊤ (genericPoint M.C) trivial]
    have h3 : f.appTop.hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
        M.toBase.appTop.hom ((Spec.map (CommRingCat.ofHom (algebraMap R K))).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
      change (c.appTop ≫ f.appTop).hom _ = ((Spec.map (CommRingCat.ofHom (algebraMap R K))).appTop ≫ M.toBase.appTop).hom _
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hfc]
    have h4 : (Spec.map (CommRingCat.ofHom (algebraMap R K))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (algebraMap R K r) := by
      have h := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K)))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
      rw [← h]
    erw [h3, h4]
    apply M.ffEquiv.injective
    rw [RingEquiv.apply_symm_apply, M.ffEquiv_algebraMap]
    rfl
  ·
    intro hbir
    have hsp : IsIso (X.presheaf.stalkSpecializes hξX) := by
      have : X.presheaf.stalkSpecializes hξX =
          (X.presheaf.stalkCongr (Inseparable.of_eq HGEN.symm)).hom := rfl
      rw [this]; infer_instance
    have hb1 : Function.Bijective (X.presheaf.stalkSpecializes hξX).hom :=
      ConcreteCategory.bijective_of_isIso (X.presheaf.stalkSpecializes hξX)
    have hb2 : Function.Bijective (Scheme.Hom.stalkMap f (genericPoint M.C)).hom :=
      ConcreteCategory.bijective_of_isIso (Scheme.Hom.stalkMap f (genericPoint M.C))
    simp only [hΘ]
    exact M.ffEquiv.symm.bijective.comp (hb2.comp hb1)

end S_AlgebraicCurve_CurveModel_exists_ringHom_functionField_ffEquiv_symm_stalkMap_eq_of_isIso_pullback
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_exists_ringHom_functionField_ffEquiv_symm_stalkMap_eq_of_isIso_pullback (solution)
