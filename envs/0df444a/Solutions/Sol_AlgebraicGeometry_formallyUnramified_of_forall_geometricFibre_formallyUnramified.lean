-- Prove2me | solution 1 for AlgebraicGeometry.formallyUnramified_of_forall_geometricFibre_formallyUnramified
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/585a9205-b60b-554d-963e-40a22edf7650

import Mathlib
import Theorems.Thm_Algebra_FormallyUnramified_of_forall_isAlgClosed_formallyUnramified_tensorProduct_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_formallyUnramified_of_forall_geometricFibre_formallyUnramified

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace Alpha1Sol

lemma appLE_congr_hom {X₁ X₂ : Scheme.{u}} {f g : X₁ ⟶ X₂} (hfg : f = g) (U : X₂.Opens) (V : X₁.Opens)
    (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (hfg ▸ e) := by
  subst hfg; rfl

lemma ringHom_ext_tmul {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [Algebra R A] [Algebra R B]
    {f g : A ⊗[R] B →+* C} (h : ∀ a b, f (a ⊗ₜ b) = g (a ⊗ₜ b)) : f = g := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b => exact h a b
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem fibre_step
    {S : Type u} [CommRing S] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of S)) (q : Y ⟶ Spec (CommRingCat.of S)) (φ : X ⟶ Y) (hφ : φ ≫ q = p)
    (U : Y.affineOpens) (V : X.affineOpens) (e : (V : X.Opens) ≤ φ ⁻¹ᵁ (U : Y.Opens))
    (k : Type u) [Field k] [Algebra S k]
    (X' Y' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of k)) (q' : Y' ⟶ Spec (CommRingCat.of k))
    (φ' : X' ⟶ Y') (iX : X' ⟶ X) (iY : Y' ⟶ Y)
    (hX : IsPullback iX p' p (Spec.map (CommRingCat.ofHom (algebraMap S k))))
    (hY : IsPullback iY q' q (Spec.map (CommRingCat.ofHom (algebraMap S k))))
    (hq' : φ' ≫ q' = p') (hcomm : iX ≫ φ = φ' ≫ iY) [FormallyUnramified φ'] :
    letI : Algebra S (Y.presheaf.obj (Opposite.op U.1)) :=
      ((q.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom).toAlgebra
    letI : Algebra S (X.presheaf.obj (Opposite.op V.1)) :=
      ((p.appLE ⊤ V.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom).toAlgebra
    letI : Algebra (Y.presheaf.obj (Opposite.op U.1)) (X.presheaf.obj (Opposite.op V.1)) := (φ.appLE U V e).hom.toAlgebra
    ∀ [IsScalarTower S (Y.presheaf.obj (Opposite.op U.1)) (X.presheaf.obj (Opposite.op V.1))],
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S (Y.presheaf.obj (Opposite.op U.1)) (X.presheaf.obj (Opposite.op V.1))) (AlgHom.id S k)).toRingHom.FormallyUnramified := by
  letI : Algebra S (Y.presheaf.obj (Opposite.op U.1)) :=
    ((q.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom).toAlgebra
  letI : Algebra S (X.presheaf.obj (Opposite.op V.1)) :=
    ((p.appLE ⊤ V.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom).toAlgebra
  letI : Algebra (Y.presheaf.obj (Opposite.op U.1)) (X.presheaf.obj (Opposite.op V.1)) := (φ.appLE U V e).hom.toAlgebra
  intro _
  let sk : CommRingCat.of S ⟶ CommRingCat.of k := CommRingCat.ofHom (algebraMap S k)

  haveI : IsAffineHom iX := MorphismProperty.IsStableUnderBaseChange.of_isPullback hX.flip inferInstance
  haveI : IsAffineHom iY := MorphismProperty.IsStableUnderBaseChange.of_isPullback hY.flip inferInstance
  have hV' : IsAffineOpen (iX ⁻¹ᵁ V.1) := V.2.preimage iX
  have hU' : IsAffineOpen (iY ⁻¹ᵁ U.1) := U.2.preimage iY
  have hV'eq : iX ⁻¹ᵁ V.1 = iX ⁻¹ᵁ V.1 ⊓ p' ⁻¹ᵁ ⊤ := by simp
  have hU'eq : iY ⁻¹ᵁ U.1 = iY ⁻¹ᵁ U.1 ⊓ q' ⁻¹ᵁ ⊤ := by simp
  have e' : iX ⁻¹ᵁ V.1 ≤ φ' ⁻¹ᵁ (iY ⁻¹ᵁ U.1) := by
    intro x hx
    show (φ' ≫ iY).base x ∈ (U.1 : Set Y)
    rw [← hcomm]
    exact e hx

  have hfu : (φ'.appLE (iY ⁻¹ᵁ U.1) (iX ⁻¹ᵁ V.1) e').hom.FormallyUnramified :=
    HasRingHomProperty.appLE (P := @FormallyUnramified) φ' inferInstance ⟨_, hU'⟩ ⟨_, hV'⟩ e'

  have sqX := (isIso_pushoutSection_iff hX (US := ⊤) (UT := ⊤) le_top (le_top : V.1 ≤ p ⁻¹ᵁ ⊤) hV'eq).mp
    (isIso_pushoutSection_of_isAffineOpen hX le_top le_top hV'eq (isAffineOpen_top _) (isAffineOpen_top _) V.2)
  have sqY := (isIso_pushoutSection_iff hY (US := ⊤) (UT := ⊤) le_top (le_top : U.1 ≤ q ⁻¹ᵁ ⊤) hU'eq).mp
    (isIso_pushoutSection_of_isAffineOpen hY le_top le_top hU'eq (isAffineOpen_top _) (isAffineOpen_top _) U.2)

  letI : Algebra (X.presheaf.obj (Opposite.op V.1)) (X'.presheaf.obj (Opposite.op (iX ⁻¹ᵁ V.1))) := (iX.appLE V.1 (iX ⁻¹ᵁ V.1) le_rfl).hom.toAlgebra
  letI : Algebra (Y.presheaf.obj (Opposite.op U.1)) (Y'.presheaf.obj (Opposite.op (iY ⁻¹ᵁ U.1))) := (iY.appLE U.1 (iY ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  letI : Algebra k (X'.presheaf.obj (Opposite.op (iX ⁻¹ᵁ V.1))) :=
    ((p'.appLE ⊤ (iX ⁻¹ᵁ V.1) le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra
  letI : Algebra k (Y'.presheaf.obj (Opposite.op (iY ⁻¹ᵁ U.1))) :=
    ((q'.appLE ⊤ (iY ⁻¹ᵁ U.1) le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra

  have hsk : (Spec.map sk).appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of S)).hom ≫ sk := by
    rw [show (Spec.map sk).appLE ⊤ ⊤ le_top = (Spec.map sk).app ⊤ from (Scheme.Hom.app_eq_appLE (Spec.map sk)).symm]
    exact Scheme.ΓSpecIso_naturality sk

  have sqX' : IsPushout (CommRingCat.ofHom (algebraMap S (X.presheaf.obj (Opposite.op V.1)))) (CommRingCat.ofHom (algebraMap S k))
      (CommRingCat.ofHom (algebraMap (X.presheaf.obj (Opposite.op V.1)) (X'.presheaf.obj (Opposite.op (iX ⁻¹ᵁ V.1))))) (CommRingCat.ofHom (algebraMap k (X'.presheaf.obj (Opposite.op (iX ⁻¹ᵁ V.1))))) := by
    refine sqX.of_iso (Scheme.ΓSpecIso (CommRingCat.of S)) (Iso.refl _) (Scheme.ΓSpecIso (CommRingCat.of k)) (Iso.refl _)
      ?_ hsk ?_ ?_ <;>
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_comp,
      CommRingCat.ofHom_hom, Iso.hom_inv_id_assoc]
  have sqY' : IsPushout (CommRingCat.ofHom (algebraMap S (Y.presheaf.obj (Opposite.op U.1)))) (CommRingCat.ofHom (algebraMap S k))
      (CommRingCat.ofHom (algebraMap (Y.presheaf.obj (Opposite.op U.1)) (Y'.presheaf.obj (Opposite.op (iY ⁻¹ᵁ U.1))))) (CommRingCat.ofHom (algebraMap k (Y'.presheaf.obj (Opposite.op (iY ⁻¹ᵁ U.1))))) := by
    refine sqY.of_iso (Scheme.ΓSpecIso (CommRingCat.of S)) (Iso.refl _) (Scheme.ΓSpecIso (CommRingCat.of k)) (Iso.refl _)
      ?_ hsk ?_ ?_ <;>
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_comp,
      CommRingCat.ofHom_hom, Iso.hom_inv_id_assoc]

  letI : Algebra S (X'.presheaf.obj (Opposite.op (iX ⁻¹ᵁ V.1))) := ((algebraMap (X.presheaf.obj (Opposite.op V.1)) (X'.presheaf.obj (Opposite.op (iX ⁻¹ᵁ V.1)))).comp (algebraMap S (X.presheaf.obj (Opposite.op V.1)))).toAlgebra
  letI : Algebra S (Y'.presheaf.obj (Opposite.op (iY ⁻¹ᵁ U.1))) := ((algebraMap (Y.presheaf.obj (Opposite.op U.1)) (Y'.presheaf.obj (Opposite.op (iY ⁻¹ᵁ U.1)))).comp (algebraMap S (Y.presheaf.obj (Opposite.op U.1)))).toAlgebra
  haveI : IsScalarTower S (X.presheaf.obj (Opposite.op V.1)) (X'.presheaf.obj (Opposite.op (iX ⁻¹ᵁ V.1))) := IsScalarTower.of_algebraMap_eq (R := S) (S := (X.presheaf.obj (Opposite.op V.1))) (A := (X'.presheaf.obj (Opposite.op (iX ⁻¹ᵁ V.1)))) (fun _ => rfl)
  haveI : IsScalarTower S (Y.presheaf.obj (Opposite.op U.1)) (Y'.presheaf.obj (Opposite.op (iY ⁻¹ᵁ U.1))) := IsScalarTower.of_algebraMap_eq (R := S) (S := (Y.presheaf.obj (Opposite.op U.1))) (A := (Y'.presheaf.obj (Opposite.op (iY ⁻¹ᵁ U.1)))) (fun _ => rfl)
  haveI : IsScalarTower S k (X'.presheaf.obj (Opposite.op (iX ⁻¹ᵁ V.1))) := IsScalarTower.of_algebraMap_eq (R := S) (S := k) (A := (X'.presheaf.obj (Opposite.op (iX ⁻¹ᵁ V.1)))) (fun s => by
    have := congrArg (fun t => CommRingCat.Hom.hom t s) sqX'.w
    simp at this
    exact this)
  haveI : IsScalarTower S k (Y'.presheaf.obj (Opposite.op (iY ⁻¹ᵁ U.1))) := IsScalarTower.of_algebraMap_eq (R := S) (S := k) (A := (Y'.presheaf.obj (Opposite.op (iY ⁻¹ᵁ U.1)))) (fun s => by
    have := congrArg (fun t => CommRingCat.Hom.hom t s) sqY'.w
    simp at this
    exact this)
  haveI hPB : Algebra.IsPushout S (X.presheaf.obj (Opposite.op V.1)) k (X'.presheaf.obj (Opposite.op (iX ⁻¹ᵁ V.1))) := CommRingCat.isPushout_iff_isPushout.mp sqX'
  haveI hPA : Algebra.IsPushout S (Y.presheaf.obj (Opposite.op U.1)) k (Y'.presheaf.obj (Opposite.op (iY ⁻¹ᵁ U.1))) := CommRingCat.isPushout_iff_isPushout.mp sqY'
  let eB := Algebra.IsPushout.equiv S (X.presheaf.obj (Opposite.op V.1)) k (X'.presheaf.obj (Opposite.op (iX ⁻¹ᵁ V.1)))
  let eA := Algebra.IsPushout.equiv S (Y.presheaf.obj (Opposite.op U.1)) k (Y'.presheaf.obj (Opposite.op (iY ⁻¹ᵁ U.1)))

  have F1 : ∀ a : (Y.presheaf.obj (Opposite.op U.1)), (φ'.appLE (iY ⁻¹ᵁ U.1) (iX ⁻¹ᵁ V.1) e').hom ((iY.appLE U.1 (iY ⁻¹ᵁ U.1) le_rfl).hom a) =
      (iX.appLE V.1 (iX ⁻¹ᵁ V.1) le_rfl).hom ((φ.appLE U V e).hom a) := by
    intro a
    have h1 := Scheme.Hom.appLE_comp_appLE φ' iY U.1 (iY ⁻¹ᵁ U.1) (iX ⁻¹ᵁ V.1) le_rfl e'
    have h2 := Scheme.Hom.appLE_comp_appLE iX φ U.1 V.1 (iX ⁻¹ᵁ V.1) e le_rfl
    rw [appLE_congr_hom hcomm] at h2
    have := congrArg (fun t => CommRingCat.Hom.hom t a) (h1.trans h2.symm)
    simpa using this
  have F2 : ∀ y, (φ'.appLE (iY ⁻¹ᵁ U.1) (iX ⁻¹ᵁ V.1) e').hom ((q'.appLE ⊤ (iY ⁻¹ᵁ U.1) le_top).hom y) =
      (p'.appLE ⊤ (iX ⁻¹ᵁ V.1) le_top).hom y := by
    intro y
    have h1 := Scheme.Hom.appLE_comp_appLE φ' q' ⊤ (iY ⁻¹ᵁ U.1) (iX ⁻¹ᵁ V.1) le_top e'
    rw [appLE_congr_hom hq'] at h1
    have := congrArg (fun t => CommRingCat.Hom.hom t y) h1
    simpa using this

  have key : (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S (Y.presheaf.obj (Opposite.op U.1)) (X.presheaf.obj (Opposite.op V.1))) (AlgHom.id S k)).toRingHom =
      eB.symm.toRingEquiv.toRingHom.comp ((φ'.appLE (iY ⁻¹ᵁ U.1) (iX ⁻¹ᵁ V.1) e').hom.comp eA.toRingEquiv.toRingHom) := by
    apply ringHom_ext_tmul
    intro a x
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]
    rw [eq_comm, AlgEquiv.symm_apply_eq]
    rw [Algebra.IsPushout.equiv_tmul, Algebra.IsPushout.equiv_tmul, map_mul]
    show _ = (iX.appLE V.1 (iX ⁻¹ᵁ V.1) le_rfl).hom ((φ.appLE U V e).hom a) *
      ((p'.appLE ⊤ (iX ⁻¹ᵁ V.1) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom x))
    rw [← F1, ← F2]
    rfl
  rw [key]
  exact RingHom.FormallyUnramified.respectsIso.1 _ eB.symm.toRingEquiv
    (RingHom.FormallyUnramified.respectsIso.2 _ eA.toRingEquiv hfu)

end Alpha1Sol

theorem solution
    {S : Type u} [CommRing S] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of S)) [LocallyOfFiniteType p]
    (q : Y ⟶ Spec (CommRingCat.of S))
    (φ : X ⟶ Y) (hφ : φ ≫ q = p)
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k),
      ∃ (X' Y' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of k)) (q' : Y' ⟶ Spec (CommRingCat.of k))
        (φ' : X' ⟶ Y') (iX : X' ⟶ X) (iY : Y' ⟶ Y),
        IsPullback iX p' p (Spec.map (CommRingCat.ofHom sk)) ∧
        IsPullback iY q' q (Spec.map (CommRingCat.ofHom sk)) ∧
        φ' ≫ q' = p' ∧ iX ≫ φ = φ' ≫ iY ∧ FormallyUnramified φ') :
    FormallyUnramified φ := by
  rw [HasRingHomProperty.iff_appLE (P := @FormallyUnramified)]
  intro U V e
  letI iA : Algebra S (Y.presheaf.obj (Opposite.op U.1)) :=
    ((q.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom).toAlgebra
  letI iB : Algebra S (X.presheaf.obj (Opposite.op V.1)) :=
    ((p.appLE ⊤ V.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom).toAlgebra
  letI iAB : Algebra (Y.presheaf.obj (Opposite.op U.1)) (X.presheaf.obj (Opposite.op V.1)) := (φ.appLE U V e).hom.toAlgebra
  haveI : IsScalarTower S (Y.presheaf.obj (Opposite.op U.1)) (X.presheaf.obj (Opposite.op V.1)) :=
    IsScalarTower.of_algebraMap_eq (R := S) (S := Y.presheaf.obj (Opposite.op U.1)) (A := X.presheaf.obj (Opposite.op V.1))
      (fun s => by
        simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
        show (p.appLE ⊤ V.1 le_top).hom _ = (q.appLE ⊤ U.1 le_top ≫ φ.appLE U V e).hom _
        rw [Scheme.Hom.appLE_comp_appLE, Alpha1Sol.appLE_congr_hom hφ])
  haveI : Algebra.FiniteType S (X.presheaf.obj (Opposite.op V.1)) := by
    have h1 : (p.appLE ⊤ V.1 le_top).hom.FiniteType :=
      HasRingHomProperty.appLE (P := @LocallyOfFiniteType) p inferInstance ⟨⊤, isAffineOpen_top _⟩ V le_top
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of S)).symm.commRingCatIsoToRingEquiv.surjective
    exact h1.comp h2
  refine @Algebra.FormallyUnramified.of_forall_isAlgClosed_formallyUnramified_tensorProduct_map S _ _ _ _ _ iA iB iAB _ _ ?_
  intro k _ _ _
  obtain ⟨X', Y', p', q', φ', iX, iY, hX, hY, hq', hcomm, hfu⟩ := hfib k (algebraMap S k)
  exact Alpha1Sol.fibre_step p q φ hφ U V e k X' Y' p' q' φ' iX iY hX hY hq' hcomm

end S_AlgebraicGeometry_formallyUnramified_of_forall_geometricFibre_formallyUnramified
end P2MW
export P2MW.S_AlgebraicGeometry_formallyUnramified_of_forall_geometricFibre_formallyUnramified (solution)
