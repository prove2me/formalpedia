-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit_of_commRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/7b7656e6-2bbb-50d9-8192-c574df8d326c

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit_of_commRing

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem solution
    (k : Type) [CommRing k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f) :
    L.IsInStabilizer 𝓛 t x ↔
      LocIsoOnBase (pullback.snd f t) ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) (𝟙_ ((pullback f t).Modules)) := by

  have Q := LocIsoOnBase.equivalence (S := R) (pullback.snd f t)
  have ofIso : ∀ {M M' : (pullback f t).Modules}, (M ≅ M') → LocIsoOnBase (pullback.snd f t) M M' :=
    fun e _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩
  have hdual := Scheme.Modules.IsInvertible.dual_monoidalV2 h𝓛
  obtain ⟨e𝓛⟩ := hdual.2

  have hψ : sliceAt f x ≫ (pullback.fst f f ≫ f) = pullback.snd f t ≫ t := by
    rw [← Category.assoc, sliceAt, pullback.lift_fst]; exact pullback.condition
  have key : sliceAt f x ≫ addMor f L = L.mulRight t x := by
    have nat := L.mul_natural (pullback.fst f f ≫ f) (pullback.snd f t ≫ t) (sliceAt f x) hψ
      ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩
    have hP : schemeHomOverComp (sliceAt f x) hψ ⟨pullback.fst f f, rfl⟩ = L.fstPoint t :=
      Subtype.ext (by rw [schemeHomOverComp_coe, RelativeGroupLaw.fstPoint_coe]; unfold sliceAt; exact pullback.lift_fst _ _ _)
    have hQ : schemeHomOverComp (sliceAt f x) hψ ⟨pullback.snd f f, pullback.condition.symm⟩ = L.sndPoint t x :=
      Subtype.ext (by rw [schemeHomOverComp_coe, RelativeGroupLaw.sndPoint_coe]; unfold sliceAt; exact pullback.lift_snd _ _ _)
    rw [hP, hQ] at nat
    have h1 := congrArg Subtype.val nat
    simpa [schemeHomOverComp, addMor, RelativeGroupLaw.mulRight] using h1
  have hp1 : sliceAt f x ≫ pullback.fst f f = pullback.fst f t := by unfold sliceAt; exact pullback.lift_fst _ _ _
  have hp2 : sliceAt f x ≫ pullback.snd f f = pullback.snd f t ≫ x.1 := by unfold sliceAt; exact pullback.lift_snd _ _ _

  let P0 : (pullback f t).Modules := (Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛
  let PR : (pullback f t).Modules := (Scheme.Modules.pullback (L.mulRight t x)).obj 𝓛
  let D0 : (pullback f t).Modules := (Scheme.Modules.pullback (pullback.fst f t)).obj (Scheme.Modules.dual 𝓛)
  let Nx : (pullback f t).Modules := (Scheme.Modules.pullback (pullback.snd f t ≫ x.1)).obj (Scheme.Modules.dual 𝓛)
  let W : (pullback f t).Modules := D0 ⊗ Nx

  have cmp : ∀ (g : pullback f f ⟶ A) (g' : pullback f t ⟶ A) (hg : sliceAt f x ≫ g = g') (M : A.Modules),
      (Scheme.Modules.pullback (sliceAt f x)).obj ((Scheme.Modules.pullback g).obj M) ≅ (Scheme.Modules.pullback g').obj M :=
    fun g g' hg M => (Scheme.Modules.pullbackComp (sliceAt f x) g).app M ≪≫ (Scheme.Modules.pullbackCongr hg).app M
  have E0 : (Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛) ≅ PR ⊗ W := by
    unfold mumfordBundle
    exact Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      (cmp _ _ key 𝓛 ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (cmp _ _ hp1 _ ⊗ᵢ cmp _ _ hp2 _)))

  have hNinv : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback x.1).obj (Scheme.Modules.dual 𝓛)) :=
    Scheme.Modules.IsInvertible.pullback _ hdual.1
  have hN : LocIsoOnBase (pullback.snd f t) Nx (𝟙_ _) := by
    intro s
    obtain ⟨U, hsU, ⟨eU⟩⟩ := hNinv.1 s
    refine ⟨U, hsU, ⟨?_⟩⟩
    have hfact : (pullback.snd f t ⁻¹ᵁ U).ι ≫ (pullback.snd f t ≫ x.1) = ((pullback.snd f t ∣_ U) ≫ U.ι) ≫ x.1 := by
      rw [← Category.assoc, ← morphismRestrict_ι]
    exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr hfact).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫ ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
      (Scheme.Modules.pullback (pullback.snd f t ∣_ U)).mapIso eU ≪≫
      Scheme.Modules.pullbackUnitIso _ ≪≫ (Scheme.Modules.pullbackTensorUnitObjIso _).symm

  have eP0D0 : P0 ⊗ D0 ≅ 𝟙_ _ :=
    (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫ (Scheme.Modules.pullback _).mapIso e𝓛 ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso _
  have hF : LocIsoOnBase (pullback.snd f t) (P0 ⊗ W) (𝟙_ _) :=
    Q.trans (ofIso ((α_ _ _ _).symm ≪≫ (eP0D0 ⊗ᵢ Iso.refl Nx) ≪≫ λ_ Nx)) hN

  have hWinv : Scheme.Modules.IsInvertible W :=
    Scheme.Modules.IsInvertible.tensor_monoidalV2 (Scheme.Modules.IsInvertible.pullback _ hdual.1)
      (Scheme.Modules.IsInvertible.pullback _ hdual.1)
  obtain ⟨eW⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 hWinv).2
  have cancel : ∀ P : (pullback f t).Modules, LocIsoOnBase (pullback.snd f t) (P ⊗ W) (𝟙_ _) →
      LocIsoOnBase (pullback.snd f t) P (Scheme.Modules.dual W) := fun P hPW =>
    Q.trans (ofIso ((ρ_ P).symm ≪≫ (Iso.refl P ⊗ᵢ eW.symm) ≪≫ (α_ _ _ _).symm))
      (Q.trans (LocIsoOnBase.tensor hPW (Q.refl _)) (ofIso (λ_ _)))
  constructor
  · intro hst

    have h1 : LocIsoOnBase (pullback.snd f t) (PR ⊗ W) (P0 ⊗ W) := LocIsoOnBase.tensor hst (Q.refl _)
    exact Q.trans (ofIso E0) (Q.trans h1 hF)
  · intro hsl
    have h1 : LocIsoOnBase (pullback.snd f t) (PR ⊗ W) (𝟙_ _) := Q.trans (ofIso E0.symm) hsl
    exact Q.trans (cancel PR h1) (Q.symm (cancel P0 hF))

end S_AlgebraicGeometry_Polarisation_isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit_of_commRing
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit_of_commRing (solution)
