-- Prove2me | solution 1 for AlgebraicGeometry.FramedPolarisedAbelianScheme.nonempty_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/3ef7a0c1-425e-5cd0-94d1-5e641d0ac061

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_nonempty_of_subsingleton

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace EmptyFramedAux

open AlgebraicGeometry

variable (S : Type) [CommRing S] [Subsingleton S]

scoped instance isEmpty_spec : IsEmpty ↥(Spec (CommRingCat.of S)) := inferInstanceAs (IsEmpty (PrimeSpectrum S))

theorem isEmpty_of_over {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) : IsEmpty ↥T :=
  Function.isEmpty t.base

theorem false_of_ringHom_field {k : Type} [Field k] (sk : S →+* k) : False := by
  have h : (1 : k) = 0 := by rw [← map_one sk, Subsingleton.elim (1 : S) 0, map_zero]
  exact one_ne_zero h

scoped instance subsingleton_pts {A T : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (t : T ⟶ Spec (CommRingCat.of S)) :
    Subsingleton (SchemeHomOver t f) := by
  haveI := isEmpty_of_over S t
  exact ⟨fun x y => Subtype.ext ((isInitialOfIsEmpty (X := T)).hom_ext _ _)⟩

noncomputable def pt {A T : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (t : T ⟶ Spec (CommRingCat.of S)) :
    SchemeHomOver t f :=
  haveI := isEmpty_of_over S t
  ⟨(isInitialOfIsEmpty (X := T)).to A, (isInitialOfIsEmpty (X := T)).hom_ext _ _⟩

noncomputable def law {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) : RelativeGroupLaw S f where
  mul t x _ := x
  one t := pt S f t
  inv t x := x
  mul_assoc _ _ _ _ := rfl
  one_mul t x := Subsingleton.elim _ _
  mul_one _ _ := rfl
  inv_mul_cancel t x := Subsingleton.elim _ _
  mul_natural _ _ _ _ _ _ := Subsingleton.elim _ _

end EmptyFramedAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_nonempty_of_subsingleton.EmptyFramedAux"

open EmptyFramedAux in
theorem solution
    (g N n : ℕ) (S : Type) [CommRing S] [Subsingleton S] :
    Nonempty (FramedPolarisedAbelianScheme g N n S) := by
  classical
  haveI hS : IsEmpty ↥(Spec (CommRingCat.of S)) := EmptyFramedAux.isEmpty_spec S
  let A : Scheme.{0} := ∅
  let f : A ⟶ Spec (CommRingCat.of S) := Scheme.emptyTo _
  haveI : IsIso f := isIso_of_isEmpty f
  let L : RelativeGroupLaw S f := EmptyFramedAux.law S f
  have hbundle : AbelianSchemePropertyBundle S f :=
    { smooth := inferInstance
      proper := inferInstance
      connectedFibres := fun s => (IsEmpty.false s).elim
      hasGroupLaw := ⟨L⟩ }
  let pol : A.Modules := SheafOfModules.unit A.ringCatSheaf
  have hΓ : ∀ V : A.Opens, Subsingleton Γ(pol, V) := fun V => by
    change Subsingleton ((∅ : Scheme.{0}).presheaf.obj (Opposite.op V))
    infer_instance
  let 𝔓 : pol.ProjPresentation f N :=
    { σ := (fun _ => 0)
      toProj := Scheme.emptyTo _
      toProj_π := Scheme.empty_ext _ _
      frame := by
        intro i V hV
        haveI := hΓ V
        exact ⟨fun a b _ => Subsingleton.elim _ _, fun m => ⟨0, Subsingleton.elim _ _⟩⟩
      app_ratio_smul := by
        intro i j
        exact (hΓ _).elim _ _ }
  let 𝔓₀ : pol.ProjPresentation f 0 :=
    { σ := (fun _ => 0)
      toProj := Scheme.emptyTo _
      toProj_π := Scheme.empty_ext _ _
      frame := by
        intro i V hV
        haveI := hΓ V
        exact ⟨fun a b _ => Subsingleton.elim _ _, fun m => ⟨0, Subsingleton.elim _ _⟩⟩
      app_ratio_smul := by
        intro i j
        exact (hΓ _).elim _ _ }
  have hpres : Scheme.Modules.ClosedImmersionBySections pol f := ⟨0, 𝔓₀, inferInstance⟩
  have hbasis : Scheme.Modules.IsSectionBasis f pol 𝔓.σ := by
    haveI := hΓ ⊤
    refine ⟨fun a b _ => Subsingleton.elim _ _, fun m => ⟨fun _ => 0, Subsingleton.elim _ _⟩⟩
  let u : FramedPolarisedAbelianScheme g N n S :=
    { A := A
      f := f
      L := L
      comm := fun t x y => Subsingleton.elim _ _
      bundle := hbundle
      dim_fibre := fun s => (IsEmpty.false s).elim
      P := fun _ => EmptyFramedAux.pt S f _
      P_torsion := fun _ => Subsingleton.elim _ _
      P_indep := fun k _ _ sk => (EmptyFramedAux.false_of_ringHom_field S sk).elim
      P_span := fun k _ _ sk => (EmptyFramedAux.false_of_ringHom_field S sk).elim
      pol := pol
      pol_isInvertible := Scheme.Modules.isInvertible_unit A
      pol_veryAmple := hpres
      pol_finrank := fun k _ _ sk => (EmptyFramedAux.false_of_ringHom_field S sk).elim
      frame := 𝔓
      frame_isClosedImmersion := inferInstance
      frame_basis := hbasis }
  exact ⟨u⟩

end S_AlgebraicGeometry_FramedPolarisedAbelianScheme_nonempty_of_subsingleton
end P2MW
export P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_nonempty_of_subsingleton (solution)
