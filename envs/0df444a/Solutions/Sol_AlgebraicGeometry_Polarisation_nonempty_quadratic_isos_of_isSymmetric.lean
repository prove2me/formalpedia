-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.nonempty_quadratic_isos_of_isSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:49.037784+00:00
-- url     : https://prove2.me/submissions/d3efeaa3-472c-4f66-881b-11331467a727

import Mathlib
import Definitions.Def_AlgebraicGeometry_SymmetricFiniteFrame
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_parallelogram_iso_of_isSymmetric
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_mul_mul_tensor_iso_monoidalV2
import Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_isAlgClosed_of_isProper_of_connectedSpace
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_field
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_schemeNsmul_iso_tensorPow_sq_of_isSymmetric_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_baseChange_negMor_comp_fst
import Theorems.Thm_AlgebraicGeometry_Polarisation_baseChange_addMor_subMor_comp_map
import Theorems.Thm_CategoryTheory_isPullback_selfProduct_baseChange
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_nonempty_pullback_iso_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_prodStr_commRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_baseChange_schemeNsmul_comp_fst_and_eq_pullback_map
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.Polarisation

private theorem class_comp {X Y Z : Scheme.{0}} (g : X ⟶ Y) (h : Y ⟶ Z) (M : Z.Modules) :
    toSkeleton ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj M)) =
      toSkeleton ((Scheme.Modules.pullback (g ≫ h)).obj M) :=
  toSkeleton_eq_toSkeleton_iff.mpr ⟨(Scheme.Modules.pullbackComp g h).app M⟩

private theorem class_map {X Y : Scheme.{0}} (g : X ⟶ Y) {M N : Y.Modules}
    (h : toSkeleton M = toSkeleton N) :
    toSkeleton ((Scheme.Modules.pullback g).obj M) = toSkeleton ((Scheme.Modules.pullback g).obj N) :=
  toSkeleton_eq_toSkeleton_iff.mpr ⟨(Scheme.Modules.pullback g).mapIso (Skeleton.isoOfEq h)⟩

private theorem class_tensor {X : Scheme.{0}} (M N : X.Modules) :
    toSkeleton (M ⊗ N) = toSkeleton M * toSkeleton N := Skeleton.toSkeleton_tensorObj M N

private theorem class_pull_tensor {X Y : Scheme.{0}} (g : X ⟶ Y) (M N : Y.Modules) :
    toSkeleton ((Scheme.Modules.pullback g).obj (M ⊗ N)) =
      toSkeleton ((Scheme.Modules.pullback g).obj M) * toSkeleton ((Scheme.Modules.pullback g).obj N) :=
  (toSkeleton_eq_toSkeleton_iff.mpr ⟨Scheme.Modules.pullbackTensorObjIso g M N⟩).trans (class_tensor _ _)

private theorem class_pow {X : Scheme.{0}} (M : X.Modules) (n : ℕ) :
    toSkeleton (M.tensorPow n) = toSkeleton M ^ n := by
  induction n with
  | zero => exact Skeleton.one_eq.symm
  | succ n ih => rw [Scheme.Modules.tensorPow_succ, class_tensor, ih, pow_succ]

private theorem class_pull_pow {X Y : Scheme.{0}} (g : X ⟶ Y) (M : Y.Modules) (n : ℕ) :
    toSkeleton ((Scheme.Modules.pullback g).obj (M.tensorPow n)) =
      toSkeleton ((Scheme.Modules.pullback g).obj M) ^ n := by
  induction n with
  | zero =>
    exact (toSkeleton_eq_toSkeleton_iff.mpr ⟨Scheme.Modules.pullbackTensorUnitObjIso g⟩).trans Skeleton.one_eq.symm
  | succ n ih => rw [Scheme.Modules.tensorPow_succ, class_pull_tensor, ih, pow_succ]

private theorem invertible_pow {X : Scheme.{0}} {M : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (n : ℕ) : Scheme.Modules.IsInvertible (M.tensorPow n) := by
  induction n with
  | zero => exact Scheme.Modules.isInvertible_unit X
  | succ n ih => exact ih.tensor_monoidalV2 hM

private theorem class_square {X X' Y Y' : Scheme.{0}} (g : X' ⟶ X) (a : X ⟶ Y)
    (a' : X' ⟶ Y') (h : Y' ⟶ Y) (comm : a' ≫ h = g ≫ a) (M : Y.Modules) :
    toSkeleton ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback a).obj M)) =
      toSkeleton ((Scheme.Modules.pullback a').obj ((Scheme.Modules.pullback h).obj M)) := by
  calc
    _ = toSkeleton ((Scheme.Modules.pullback (g ≫ a)).obj M) := class_comp _ _ _
    _ = toSkeleton ((Scheme.Modules.pullback (a' ≫ h)).obj M) := by rw [comm]
    _ = _ := (class_comp _ _ _).symm

/-- The quadratic bundle identities over a field follow by reflection from its algebraic closure. -/
theorem _root_.solution (k : Type) [Field k] {A : Scheme.{0}}
    (f : A ⟶ Spec (CommRingCat.of k)) (G : RelativeGroupLaw k f) (hc : G.IsCommutative)
    (hA : AbelianSchemePropertyBundle k f) (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hsym : IsSymmetric f G M) :
    Nonempty ((Scheme.Modules.pullback (G.schemeNsmul 2)).obj M ≅ M.tensorPow 4) ∧
    Nonempty (((Scheme.Modules.pullback (addMor f G)).obj M ⊗
        (Scheme.Modules.pullback (subMor f G)).obj M) ≅
      ((Scheme.Modules.pullback (pullback.fst f f)).obj (M.tensorPow 2) ⊗
        (Scheme.Modules.pullback (pullback.snd f f)).obj (M.tensorPow 2))) := by
  let k' := AlgebraicClosure k
  let φ : k →+* k' := algebraMap k k'
  let b := Spec.map (CommRingCat.ofHom φ)
  let g := pullback.fst f b
  let f' := pullback.snd f b
  let G' := G.baseChange b
  let M' := (Scheme.Modules.pullback g).obj M
  have hA' : AbelianSchemePropertyBundle k' f' := hA.of_isPullback (IsPullback.of_hasPullback f b)
  have hc' : G'.IsCommutative := RelativeGroupLaw.IsCommutative.baseChange b hc
  have hM' : Scheme.Modules.IsInvertible M' := hM.pullback g
  have hs : toSkeleton ((Scheme.Modules.pullback (negMor f G)).obj M) = toSkeleton M :=
    toSkeleton_eq_toSkeleton_iff.mpr ((locIsoOnBase_iff_nonempty_iso_of_field f _ _).mp hsym)
  have hs' : IsSymmetric f' G' M' := by
    apply (locIsoOnBase_iff_nonempty_iso_of_field f' _ _).mpr
    apply toSkeleton_eq_toSkeleton_iff.mp
    exact (class_square g (negMor f G) (negMor f' G') g
      (baseChange_negMor_comp_fst G b) M).symm.trans (class_map g hs)
  have hd' := nonempty_pullback_schemeNsmul_iso_tensorPow_sq_of_isSymmetric_monoidalV2
    k' f' G' hc' hA' M' hM' hs' 2
  have hpar' := nonempty_parallelogram_iso_of_isSymmetric k' f' G' hc' hA' M' hM' hs'
  constructor
  · apply Scheme.Modules.IsInvertible.nonempty_iso_of_nonempty_pullback_iso_of_isPullback
      k f hA _ _ (hM.pullback _) (invertible_pow hM 4) k' φ f' g (IsPullback.of_hasPullback f b)
    apply toSkeleton_eq_toSkeleton_iff.mp
    calc
      _ = toSkeleton ((Scheme.Modules.pullback (G'.schemeNsmul 2)).obj M') :=
        class_square g (G.schemeNsmul 2) (G'.schemeNsmul 2) g
          (RelativeGroupLaw.baseChange_schemeNsmul_comp_fst_and_eq_pullback_map b G 2).1 M
      _ = toSkeleton (M'.tensorPow 4) := toSkeleton_eq_toSkeleton_iff.mpr hd'
      _ = _ := by rw [class_pow, class_pull_pow]
  · let π := pullback.map f' f' f f g g b pullback.condition.symm pullback.condition.symm
    have hπ : IsPullback π (pullback.fst f' f' ≫ f') (pullback.fst f f ≫ f) b :=
      CategoryTheory.isPullback_selfProduct_baseChange f b
    have hmaps := baseChange_addMor_subMor_comp_map G b
    have hp : pullback.fst f' f' ≫ g = π ≫ pullback.fst f f := by
      simp only [π, pullback.map, pullback.lift_fst, pullback.lift_snd]
    have hq : pullback.snd f' f' ≫ g = π ≫ pullback.snd f f := by
      simp only [π, pullback.map, pullback.lift_fst, pullback.lift_snd]
    apply Scheme.Modules.IsInvertible.nonempty_iso_of_nonempty_pullback_iso_of_isPullback
      k (pullback.fst f f ≫ f) (hA.prodStr_commRing hA) _ _
      ((hM.pullback _).tensor_monoidalV2 (hM.pullback _))
      (((invertible_pow hM 2).pullback _).tensor_monoidalV2 ((invertible_pow hM 2).pullback _))
      k' φ (pullback.fst f' f' ≫ f') π hπ
    apply toSkeleton_eq_toSkeleton_iff.mp
    rw [class_pull_tensor, class_pull_tensor]
    calc
      _ = toSkeleton ((Scheme.Modules.pullback (addMor f' G')).obj M') *
          toSkeleton ((Scheme.Modules.pullback (subMor f' G')).obj M') :=
        congrArg₂ (· * ·) (class_square π _ _ g hmaps.1 M) (class_square π _ _ g hmaps.2 M)
      _ = toSkeleton ((Scheme.Modules.pullback (pullback.fst f' f')).obj (M'.tensorPow 2)) *
          toSkeleton ((Scheme.Modules.pullback (pullback.snd f' f')).obj (M'.tensorPow 2)) := by
        simpa only [class_tensor] using toSkeleton_eq_toSkeleton_iff.mpr hpar'
      _ = _ := by
        congr 1
        · calc
            _ = toSkeleton ((Scheme.Modules.pullback (pullback.fst f' f')).obj
                ((Scheme.Modules.pullback g).obj (M.tensorPow 2))) :=
              class_map _ (by rw [class_pow, class_pull_pow])
            _ = _ := (class_square π (pullback.fst f f) (pullback.fst f' f') g hp (M.tensorPow 2)).symm
        · calc
            _ = toSkeleton ((Scheme.Modules.pullback (pullback.snd f' f')).obj
                ((Scheme.Modules.pullback g).obj (M.tensorPow 2))) :=
              class_map _ (by rw [class_pow, class_pull_pow])
            _ = _ := (class_square π (pullback.snd f f) (pullback.snd f' f') g hq (M.tensorPow 2)).symm

end AlgebraicGeometry.Polarisation
