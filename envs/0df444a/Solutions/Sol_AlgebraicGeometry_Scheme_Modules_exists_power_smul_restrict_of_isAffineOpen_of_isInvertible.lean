-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_power_smul_restrict_of_isAffineOpen_of_isInvertible
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-13T19:45:34.253151+00:00
-- url     : https://prove2.me/submissions/b69f1927-57f9-475d-8979-c701896560bd

import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Mathlib.AlgebraicGeometry.Modules.Tilde

universe u

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.DenominatorClearing

def unitPresentation {X : Scheme.{u}} (U : X.Opens) :
    (SheafOfModules.unit.{u} (X.ringCatSheaf.over U)).Presentation := by
  let e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit.{u+1} ≅
      SheafOfModules.unit (X.ringCatSheaf.over U) :=
    coproductUniqueIso _
  refine SheafOfModules.presentationOfIsCokernelFree
    (0 : SheafOfModules.free PEmpty.{u+1} ⟶ SheafOfModules.free PUnit.{u+1})
    e.hom (by simp) ?_
  refine Cofork.IsColimit.mk _ (fun s => e.inv ≫ s.π) (fun s => by simp) ?_
  intro s m hm
  simpa using congrArg (fun k => e.inv ≫ k) hm

theorem quasicoherent_of_invertible {X : Scheme.{u}} (M : X.Modules)
    (hM : Scheme.Modules.IsInvertible M) : M.IsQuasicoherent := by
  choose U hx e using hM.exists_trivialization
  let iso (x : X) : M.over (U x) ≅ SheafOfModules.unit (X.ringCatSheaf.over (U x)) :=
    (Scheme.Modules.overEquiv (U x)).fullyFaithfulFunctor.preimageIso
      ((Scheme.Modules.overFunctorEquiv (U x)).app M ≪≫
       (Scheme.Modules.restrictFunctorIsoPullback (U x).ι).app M ≪≫
       (e x).some ≪≫ ((U x).sheafOfModulesEquivOverUnit X.ringCatSheaf).symm)
  let data : M.QuasicoherentData :=
    { I := X
      X := U
      coversTop := by
        rw [Opens.coversTop_iff]
        apply top_unique
        intro x _
        exact (le_iSup U x) (hx x)
      presentation := fun x => (unitPresentation (U x)).ofIsIso (iso x).inv }
  exact data.isQuasicoherent

end AlgebraicGeometry.Scheme.DenominatorClearing

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.DenominatorClearing

lemma fromSpec_coeff {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (V : (Spec Γ(X, U)).Opens) :
    (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map V.leTop.op ≫
      (hU.fromSpec.appIso V).inv =
    X.presheaf.map (homOfLE (show hU.fromSpec ''ᵁ V ≤ U from
      (hU.fromSpec.image_mono le_top).trans (by simp))).op := by
  have hV : V ≤ hU.fromSpec ⁻¹ᵁ U := by simp
  have h : hU.fromSpec.appLE U V hV =
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map V.leTop.op := by
    simp only [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    rfl
  simpa only [h, Category.assoc] using hU.fromSpec.appLE_appIso_inv hV

def affineSectionsIso {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) (V : (Spec Γ(X, U)).Opens) (W : X.Opens)
    (h : hU.fromSpec ''ᵁ V = W) : Γ(M.restrict hU.fromSpec, V) ≅ Γ(M, W) :=
  M.restrictAppIso hU.fromSpec V ≪≫ M.presheaf.mapIso (eqToIso h.symm).op

lemma affineSectionsIso_smul {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) (V : (Spec Γ(X, U)).Opens) (W : X.Opens)
    (h : hU.fromSpec ''ᵁ V = W) (hWU : W ≤ U)
    (r : Γ(X, U)) (s : Γ(M.restrict hU.fromSpec, V)) :
    (affineSectionsIso M hU V W h).hom (r • s) =
      X.presheaf.map (homOfLE hWU).op r • (affineSectionsIso M hU V W h).hom s := by
  have hs := congr($(M.smul_restrictAppIso_hom hU.fromSpec V
    ((Spec Γ(X, U)).presheaf.map V.leTop.op ((Scheme.ΓSpecIso Γ(X, U)).inv r))) s)
  have hc := congr($(fromSpec_coeff hU V) r)
  simp only [ConcreteCategory.comp_apply] at hc
  change (M.restrictAppIso hU.fromSpec V).hom (r • s) =
    (hU.fromSpec.appIso V).inv
      ((Spec Γ(X, U)).presheaf.map V.leTop.op ((Scheme.ΓSpecIso Γ(X, U)).inv r)) •
        (M.restrictAppIso hU.fromSpec V).hom s at hs
  rw [hc] at hs
  change M.presheaf.map (eqToHom h.symm).op ((M.restrictAppIso hU.fromSpec V).hom (r • s)) = _
  rw [hs, M.map_smul]
  simp only [← X.presheaf.map_comp_apply]
  rfl

lemma affineSectionsIso_map {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) {V₀ V₁ : (Spec Γ(X, U)).Opens} {W₀ W₁ : X.Opens}
    (h₀ : hU.fromSpec ''ᵁ V₀ = W₀) (h₁ : hU.fromSpec ''ᵁ V₁ = W₁)
    (hV : V₁ ≤ V₀) (hW : W₁ ≤ W₀) (s : Γ(M.restrict hU.fromSpec, V₀)) :
    (affineSectionsIso M hU V₁ W₁ h₁).hom
      ((M.restrict hU.fromSpec).presheaf.map (homOfLE hV).op s) =
    M.presheaf.map (homOfLE hW).op ((affineSectionsIso M hU V₀ W₀ h₀).hom s) := by
  have hs := congr($(M.map_restrictAppIso_hom hU.fromSpec (homOfLE hV).op) s)
  simp only [ConcreteCategory.comp_apply] at hs
  change M.presheaf.map (eqToHom h₁.symm).op
    ((M.restrictAppIso hU.fromSpec V₁).hom
      ((M.restrict hU.fromSpec).presheaf.map (homOfLE hV).op s)) = _
  rw [hs]
  change M.presheaf.map _ (M.presheaf.map _ _) = M.presheaf.map _ (M.presheaf.map _ _)
  simp only [← M.presheaf.map_comp_apply]
  rfl

theorem clear_of_quasicoherent {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) (f : Γ(X, U))
    (s : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, U)),
      M.presheaf.map (homOfLE (X.basicOpen_le f)).op t =
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ n • s := by
  let N := M.restrict hU.fromSpec
  have htop : hU.fromSpec ''ᵁ ⊤ = U := by simp
  let e₀ := affineSectionsIso M hU ⊤ U htop
  let e₁ := affineSectionsIso M hU (PrimeSpectrum.basicOpen f) (X.basicOpen f)
    (hU.fromSpec_image_basicOpen f)
  haveI : IsLocalizedModule.Away f
      ((modulesSpecToSheaf.obj N).obj.map (PrimeSpectrum.basicOpen f).leTop.op).hom :=
    (isIso_fromTildeΓ_iff_isLocalizing N).mp inferInstance f
  obtain ⟨n, t, ht⟩ := IsLocalizedModule.Away.surj
    ((modulesSpecToSheaf.obj N).obj.map (PrimeSpectrum.basicOpen f).leTop.op).hom f (e₁.inv s)
  refine ⟨n, e₀.hom t, ?_⟩
  have h := congr(e₁.hom $ht.symm)
  change e₁.hom ((M.restrict hU.fromSpec).presheaf.map
    (homOfLE (show PrimeSpectrum.basicOpen f ≤ ⊤ from le_top)).op t) =
      e₁.hom (f ^ n • e₁.inv s) at h
  rw [affineSectionsIso_map M hU htop (hU.fromSpec_image_basicOpen f) le_top
    (X.basicOpen_le f)] at h
  rw [affineSectionsIso_smul M hU _ _ (hU.fromSpec_image_basicOpen f)
    (X.basicOpen_le f), map_pow, Iso.inv_hom_id_apply] at h
  exact h

end AlgebraicGeometry.Scheme.DenominatorClearing

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Opposite

theorem solution
    {X : Scheme.{u}} (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (U : X.Opens) (hU : IsAffineOpen U) (f : Γ(X, U))
    (s : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, U)),
      M.presheaf.map (homOfLE (X.basicOpen_le f)).op t =
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ n • s := by
  letI := Scheme.DenominatorClearing.quasicoherent_of_invertible M hM
  exact Scheme.DenominatorClearing.clear_of_quasicoherent M U hU f s
