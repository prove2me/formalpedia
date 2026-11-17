-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.nonempty_parallelogram_iso_of_isSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:48.376394+00:00
-- url     : https://prove2.me/submissions/81ba3d79-da48-4c20-8d9f-90ff2610113a

import Mathlib
import Definitions.Def_AlgebraicGeometry_SymmetricFiniteFrame
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_mul_mul_tensor_iso_monoidalV2
import Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_isAlgClosed_of_isProper_of_connectedSpace
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_field
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field_monoidalV2
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Polarisation

private theorem cls_tensor {C : Type*} [Category C] [MonoidalCategory C] (X Y : C) :
    toSkeleton (X ⊗ Y) = toSkeleton X * toSkeleton Y := Skeleton.toSkeleton_tensorObj X Y

private theorem cls_unit {C : Type*} [Category C] [MonoidalCategory C] :
    toSkeleton (𝟙_ C) = (1 : Skeleton C) := Skeleton.one_eq.symm

private theorem cls_pull_comp {X Y Z : Scheme.{0}} (g : X ⟶ Y) (h : Y ⟶ Z) (M : Z.Modules) :
    toSkeleton ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj M)) =
      toSkeleton ((Scheme.Modules.pullback (g ≫ h)).obj M) :=
  toSkeleton_eq_toSkeleton_iff.mpr ⟨(Scheme.Modules.pullbackComp g h).app M⟩

private theorem cls_pull_pow {X Y : Scheme.{0}} (g : X ⟶ Y) (M : Y.Modules) (n : ℕ) :
    toSkeleton ((Scheme.Modules.pullback g).obj (M.tensorPow n)) =
      toSkeleton ((Scheme.Modules.pullback g).obj M) ^ n := by
  induction n with
  | zero =>
    rw [Scheme.Modules.tensorPow_zero, pow_zero]
    exact (toSkeleton_eq_toSkeleton_iff.mpr ⟨Scheme.Modules.pullbackTensorUnitObjIso g⟩).trans cls_unit
  | succ n ih =>
    rw [Scheme.Modules.tensorPow_succ]
    rw [toSkeleton_eq_toSkeleton_iff.mpr ⟨Scheme.Modules.pullbackTensorObjIso g (M.tensorPow n) M⟩,
      cls_tensor, ih, pow_succ]

private theorem connectedSpace_of_bundle {k : Type} [Field k] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of k)} (hA : AbelianSchemePropertyBundle k f) : ConnectedSpace A := by
  obtain ⟨s⟩ := (inferInstance : Nonempty ↥(Spec (CommRingCat.of k)))
  have hs : f.base ⁻¹' {s} = Set.univ := Set.eq_univ_of_forall fun y => Subsingleton.elim _ _
  have h := hA.connectedFibres s
  rw [hs] at h
  exact connectedSpace_iff_univ.mpr h

/-- The cube identity evaluated at the two projections and the inverse second projection. -/
theorem _root_.solution (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}}
    (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle k f) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hsym : Polarisation.IsSymmetric f L 𝓛) :
    Nonempty (((Scheme.Modules.pullback (Polarisation.addMor f L)).obj 𝓛 ⊗
        (Scheme.Modules.pullback (Polarisation.subMor f L)).obj 𝓛) ≅
      ((Scheme.Modules.pullback (pullback.fst f f)).obj (𝓛.tensorPow 2) ⊗
        (Scheme.Modules.pullback (pullback.snd f f)).obj (𝓛.tensorPow 2))) := by
  letI : GrpObj (Over.mk f) := L.grpObjOverMk
  haveI : IsCommMonObj (Over.mk f) := L.isCommMonObj_grpObjOverMk_iff_mul_comm.mpr (fun t x y => hc t x y)
  haveI : IsProper f := hA.proper
  haveI : ConnectedSpace A := connectedSpace_of_bundle hA
  have hgc := AlgebraicGeometry.geometricallyConnected_of_isAlgClosed_of_isProper_of_connectedSpace k f
  let Y := Over.mk (pullback.fst f f ≫ f)
  let p : Y ⟶ Over.mk f := Over.homMk (pullback.fst f f) rfl
  let q : Y ⟶ Over.mk f := Over.homMk (pullback.snd f f) pullback.condition.symm
  have hmul : (p * q).left = addMor f L := by
    exact congrArg Subtype.val (L.overHomEquivSchemeHomOver_mul Y p q)
  have hinv : (q⁻¹).left = q.left ≫ negMor f L := by
    have hqi : q⁻¹ = q ≫ (𝟙 (Over.mk f))⁻¹ := by
      rw [GrpObj.comp_inv, Category.comp_id]
    rw [hqi, Over.comp_left]
    congr 1
  let r : Y ⟶ Y := Over.homMk
    (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ negMor f L)
      (by rw [Category.assoc, negMor_over]; exact pullback.condition))
    (by
      change _ ≫ (pullback.fst f f ≫ f) = _
      rw [← Category.assoc, pullback.lift_fst]
      rfl)
  have hrp : r ≫ p = p := by
    ext
    exact pullback.lift_fst _ _ _
  have hrq : r ≫ q = q⁻¹ := by
    ext
    simp only [Over.comp_left]
    change (r.left ≫ pullback.snd f f) = (q⁻¹).left
    rw [hinv]
    exact pullback.lift_snd _ _ _
  have hsub : (p * q⁻¹).left = subMor f L := by
    have hr : r ≫ (p * q) = p * q⁻¹ := by
      rw [MonObj.comp_mul, hrp, hrq]
    rw [← hr, Over.comp_left, hmul]
    rfl
  obtain ⟨e⟩ := Scheme.Modules.nonempty_pullback_mul_mul_tensor_iso_monoidalV2 k f hA.smooth hA.proper hgc 𝓛 h𝓛 p q q⁻¹
  apply toSkeleton_eq_toSkeleton_iff.mp
  have he := toSkeleton_eq_toSkeleton_iff.mpr ⟨e⟩
  simp only [cls_tensor] at he ⊢
  simp only [mul_inv_cancel_right, mul_inv_cancel] at he
  obtain ⟨es⟩ := (locIsoOnBase_iff_nonempty_iso_of_field f _ _).mp hsym
  have hs : toSkeleton ((Scheme.Modules.pullback (q⁻¹).left).obj 𝓛) =
      toSkeleton ((Scheme.Modules.pullback q.left).obj 𝓛) := by
    rw [hinv, ← cls_pull_comp]
    exact toSkeleton_eq_toSkeleton_iff.mpr ⟨(Scheme.Modules.pullback q.left).mapIso es⟩
  have hone : (1 : Y ⟶ Over.mk f).left = Y.hom ≫ (η : 𝟙_ _ ⟶ Over.mk f).left := by
    rw [Hom.one_def, Over.comp_left]
    rfl
  have hz : toSkeleton ((Scheme.Modules.pullback (1 : Y ⟶ Over.mk f).left).obj 𝓛) = 1 := by
    rw [hone, ← cls_pull_comp]
    obtain ⟨ez⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field_monoidalV2 k
      ((Scheme.Modules.pullback (η : 𝟙_ _ ⟶ Over.mk f).left).obj 𝓛) (h𝓛.pullback _)
    exact (toSkeleton_eq_toSkeleton_iff.mpr ⟨(Scheme.Modules.pullback Y.hom).mapIso ez ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso Y.hom⟩).trans cls_unit
  rw [hs, hz, hmul, hsub, mul_one] at he
  rw [cls_pull_pow, cls_pull_pow]
  change toSkeleton ((Scheme.Modules.pullback (addMor f L)).obj 𝓛) *
      toSkeleton ((Scheme.Modules.pullback (subMor f L)).obj 𝓛) =
    toSkeleton ((Scheme.Modules.pullback p.left).obj 𝓛) ^ 2 *
      toSkeleton ((Scheme.Modules.pullback q.left).obj 𝓛) ^ 2
  exact he.symm.trans (by simp only [pow_two]; ac_rfl)

end AlgebraicGeometry.Polarisation
