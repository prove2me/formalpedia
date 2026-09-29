-- Prove2me | solution 1 for AlgebraicGeometry.bijective_appTop_of_forall_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/b75b3adf-6369-5bfb-9b81-21d81c34aae5

import Mathlib
import Theorems.Thm_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_bijective_appTop_of_forall_isMaximal

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace P2LocAux

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (q : X ⟶ Spec R) [CompactSpace X] [QuasiSeparatedSpace X]

noncomputable def φ : (R : Type u) →+* (Γ(X, ⊤) : Type u) := ((Scheme.ΓSpecIso R).inv ≫ q.appTop).hom

variable (P : Ideal R) [P.IsMaximal]

abbrev A : Type u := Localization.AtPrime P
noncomputable abbrev ι : Spec (CommRingCat.of (A P)) ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R (A P)))
noncomputable abbrev ΓP : Type u := (Γ(pullback q (ι P), ⊤) : Type u)

noncomputable def ψ : A P →+* ΓP q P :=
  ((Scheme.ΓSpecIso (CommRingCat.of (A P))).inv ≫ (pullback.snd q (ι P)).appTop).hom

noncomputable def γ : (Γ(X, ⊤) : Type u) →+* ΓP q P := (pullback.fst q (ι P)).appTop.hom

theorem hw (r : R) : ψ q P (algebraMap R (A P) r) = γ q P (φ q r) := by
  have w := (AlgebraicGeometry.isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat (k := (R : Type u)) q (A P)).w
  have := congrArg (fun f => (CommRingCat.Hom.hom f) r) w
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  exact this

end P2LocAux

open P2LocAux in
theorem solution
    {X : Scheme.{u}} {R : CommRingCat.{u}} (q : X ⟶ Spec R) [CompactSpace X] [QuasiSeparatedSpace X]
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      Function.Bijective (pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime P))))).appTop) :
    Function.Bijective q.appTop := by
  classical

  suffices hφ : Function.Bijective (P2LocAux.φ q) by
    haveI : IsIso ((Scheme.ΓSpecIso R).inv ≫ q.appTop) := (ConcreteCategory.isIso_iff_bijective _).mpr hφ
    haveI : IsIso q.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso R).inv q.appTop
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

  letI algRΓ : Algebra R Γ(X, ⊤) := (P2LocAux.φ q).toAlgebra

  let algA : ∀ (P : Ideal R) [P.IsMaximal], Algebra (P2LocAux.A P) (P2LocAux.ΓP q P) :=
    fun P _ => (P2LocAux.ψ q P).toAlgebra
  let algΓ : ∀ (P : Ideal R) [P.IsMaximal], Algebra Γ(X, ⊤) (P2LocAux.ΓP q P) :=
    fun P _ => (P2LocAux.γ q P).toAlgebra
  let algR : ∀ (P : Ideal R) [P.IsMaximal], Algebra R (P2LocAux.ΓP q P) :=
    fun P _ => ((P2LocAux.γ q P).comp (P2LocAux.φ q)).toAlgebra
  have towRA : ∀ (P : Ideal R) [P.IsMaximal],
      @IsScalarTower R (P2LocAux.A P) (P2LocAux.ΓP q P) _ (algA P).toSMul (algR P).toSMul := by
    intro P _
    letI := algA P; letI := algR P
    exact IsScalarTower.of_algebraMap_eq (fun r => (P2LocAux.hw q P r).symm)
  have towRΓ : ∀ (P : Ideal R) [P.IsMaximal],
      @IsScalarTower R Γ(X, ⊤) (P2LocAux.ΓP q P) _ (algΓ P).toSMul (algR P).toSMul := by
    intro P _
    letI := algΓ P; letI := algR P
    exact IsScalarTower.of_algebraMap_eq (fun r => rfl)

  have hpush : ∀ (P : Ideal R) [P.IsMaximal],
      @Algebra.IsPushout R (P2LocAux.A P) _ _ _ Γ(X, ⊤) (P2LocAux.ΓP q P) _ _ _ (algA P) (algΓ P) (algR P)
        (towRΓ P) (towRA P) := by
    intro P _
    letI := algA P; letI := algΓ P; letI := algR P; haveI := towRA P; haveI := towRΓ P
    apply CommRingCat.isPushout_iff_isPushout.mp
    have e1 : CommRingCat.ofHom (algebraMap (↑R) ↑Γ(X, ⊤)) = (Scheme.ΓSpecIso R).inv ≫ q.appTop := CommRingCat.ofHom_hom _
    have e2 : CommRingCat.ofHom (algebraMap (P2LocAux.A P) (P2LocAux.ΓP q P)) =
        (Scheme.ΓSpecIso (CommRingCat.of (P2LocAux.A P))).inv ≫ (pullback.snd q (P2LocAux.ι P)).appTop :=
      CommRingCat.ofHom_hom _
    have e3 : CommRingCat.ofHom (algebraMap ↑Γ(X, ⊤) (P2LocAux.ΓP q P)) = (pullback.fst q (P2LocAux.ι P)).appTop :=
      CommRingCat.ofHom_hom _
    rw [e1, e2, e3]
    exact AlgebraicGeometry.isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat (k := (R : Type u)) q (P2LocAux.A P)

  let F : (R : Type u) →ₗ[R] Γ(X, ⊤) := Algebra.linearMap R Γ(X, ⊤)
  let g : ∀ (P : Ideal R) [P.IsMaximal], @LinearMap R R _ _ (RingHom.id R) Γ(X, ⊤) (P2LocAux.ΓP q P) _ _ _ (algR P).toModule :=
    fun P _ => by
      letI := algΓ P; letI := algR P; haveI := towRΓ P
      exact (IsScalarTower.toAlgHom R Γ(X, ⊤) (P2LocAux.ΓP q P)).toLinearMap
  have hloc : ∀ (P : Ideal R) [P.IsMaximal],
      @IsLocalizedModule.AtPrime (↑R) (↑Γ(X, ⊤)) (P2LocAux.ΓP q P) _ P _ _ _ _ (algR P).toModule (g P) := by
    intro P _
    letI := algA P; letI := algΓ P; letI := algR P; haveI := towRA P; haveI := towRΓ P; haveI := hpush P
    exact (isLocalizedModule_iff_isBaseChange P.primeCompl (P2LocAux.A P) (g P)).mpr Algebra.IsPushout.out
  refine @bijective_of_isLocalized_maximal R R Γ(X, ⊤) _ _ _ _ _
    (fun P _ => P2LocAux.A P) (fun P _ => inferInstance) (fun P _ => inferInstance)
    (fun P _ => Algebra.linearMap R (P2LocAux.A P)) (fun P _ => inferInstance)
    (fun P _ => P2LocAux.ΓP q P) (fun P _ => inferInstance) (fun P _ => (algR P).toModule)
    g hloc F ?_
  intro P _
  letI := algA P; letI := algΓ P; letI := algR P; haveI := towRA P; haveI := towRΓ P; haveI := hloc P

  let ψlin : P2LocAux.A P →ₗ[R] P2LocAux.ΓP q P := (IsScalarTower.toAlgHom R (P2LocAux.A P) (P2LocAux.ΓP q P)).toLinearMap
  have hmap : IsLocalizedModule.map P.primeCompl (Algebra.linearMap R (P2LocAux.A P)) (g P) F = ψlin := by
    apply IsLocalizedModule.linearMap_ext P.primeCompl (Algebra.linearMap R (P2LocAux.A P)) (g P)
    rw [IsLocalizedModule.map_comp]
    apply LinearMap.ext; intro r
    show P2LocAux.γ q P (P2LocAux.φ q r) = P2LocAux.ψ q P (algebraMap R (P2LocAux.A P) r)
    exact (P2LocAux.hw q P r).symm
  rw [hmap]

  show Function.Bijective (P2LocAux.ψ q P)
  haveI : IsIso (pullback.snd q (P2LocAux.ι P)).appTop := (ConcreteCategory.isIso_iff_bijective _).mpr (h P)
  exact (ConcreteCategory.isIso_iff_bijective
    ((Scheme.ΓSpecIso (CommRingCat.of (P2LocAux.A P))).inv ≫ (pullback.snd q (P2LocAux.ι P)).appTop)).mp inferInstance

end S_AlgebraicGeometry_bijective_appTop_of_forall_isMaximal
end P2MW
export P2MW.S_AlgebraicGeometry_bijective_appTop_of_forall_isMaximal (solution)
