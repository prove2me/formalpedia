-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_representsRelSubPic_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/9a9bd7e3-7a9e-54d7-a629-442b85095074

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_baseChange

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian AlgebraicGeometry.RelPicard.BaseChange

namespace RepBCSketch

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

noncomputable def pullbackAlongComp {T T' T'' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} {t'' : T'' ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) (φ : SchemeHomOver t' t) (ψ : SchemeHomOver t'' t') :
    ((M.pullbackAlong φ).pullbackAlong ψ).L ≅ (M.pullbackAlong (postComp φ ψ)).L :=
  (Scheme.Modules.pullbackComp (baseChangeSnd c ψ) (baseChangeSnd c φ)).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c φ ψ)).app M.L

noncomputable def pullbackAlongCongr {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t) {φ ψ : SchemeHomOver t' t}
    (e : φ.1 = ψ.1) : (M.pullbackAlong φ).L ≅ (M.pullbackAlong ψ).L :=
  eqToIso (by cases φ; cases ψ; cases e; rfl)

noncomputable def unitPullbackAlong {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    ((RigidifiedLineBundle.unit (c := c) (ε := ε) t).pullbackAlong ψ).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) t').L :=
  Scheme.Modules.pullbackUnitIso (baseChangeSnd c ψ)

variable (R' : Type u) [CommRing R'] [Algebra R R']

noncomputable def isoOfToRIso {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R')}
    (X M : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε) t)
    (i : (toR c ε R' X).L ≅ (toR c ε R' M).L) : X.L ≅ M.L :=
  (ofR_toR_iso c ε R' X).symm ≪≫ (Scheme.Modules.pullback (κ c R' t).hom).mapIso i ≪≫ ofR_toR_iso c ε R' M

theorem mem_iff {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
    (M : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε) t) :
    (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)).P t M ↔
      (algEquivZeroCut c ε).P (t ≫ specMap R R') (toR c ε R' M) := by
  rw [← restrict_algEquivZeroCut]
  rfl

end RepBCSketch

open RepBCSketch in
theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    ∃ h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
        (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'),
      Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
        (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L) := by
  classical

  let ψ₀ : SchemeHomOver ((D.baseChange R').toBase ≫ specMap R R') D.toBase :=
    ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩
  let P' : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε) (D.baseChange R').toBase :=
    ofR c ε R' (h.poincare.pullbackAlong ψ₀)

  have chain : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R')}
      (γ : SchemeHomOver t (D.baseChange R').toBase),
      (toR c ε R' (P'.pullbackAlong γ)).L ≅ (h.poincare.pullbackAlong (postComp ψ₀ (overR R' γ))).L :=
    fun γ => (toR_pullbackAlong_iso c ε R' γ P').symm ≪≫
      (Scheme.Modules.pullback (baseChangeSnd c (overR R' γ))).mapIso (toR_ofR_iso c ε R' _) ≪≫
      pullbackAlongComp h.poincare ψ₀ (overR R' γ)
  refine ⟨{ poincare := P', poincare_mem := ?_, univ := ?_, zero := ?_ }, ⟨Iso.refl _⟩⟩
  ·
    have hmem : (algEquivZeroCut c ε).P _ (h.poincare.pullbackAlong ψ₀) :=
      (algEquivZeroCut c ε).pullback_mem _ _ ψ₀ _ h.poincare_mem
    exact (mem_iff R' _ P').2 ((algEquivZeroCut c ε).congr _ _ _ ⟨(toR_ofR_iso c ε R' _).symm⟩ hmem)
  ·
    intro T t M hM
    have hN : (algEquivZeroCut c ε).P (t ≫ specMap R R') (toR c ε R' M) := (mem_iff R' t M).1 hM
    obtain ⟨g, ⟨eg⟩, guniq⟩ := h.univ (t ≫ specMap R R') (toR c ε R' M) hN
    let g' : SchemeHomOver t (D.baseChange R').toBase := ⟨pullback.lift g.1 t g.2, pullback.lift_snd _ _ _⟩
    have hg' : (postComp ψ₀ (overR R' g')).1 = g.1 := pullback.lift_fst _ _ _
    refine ⟨g', ⟨?_⟩, ?_⟩
    · exact isoOfToRIso R' _ _ (chain g' ≪≫ pullbackAlongCongr h.poincare hg' ≪≫ eg)
    · rintro γ ⟨eγ⟩
      let i := chain γ
      have hG : postComp ψ₀ (overR R' γ) = g :=
        guniq _ ⟨i.symm ≪≫ (Scheme.Modules.pullback (κ c R' t).inv).mapIso eγ⟩
      apply Subtype.ext
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        exact congrArg Subtype.val hG
      · rw [pullback.lift_snd]
        exact γ.2
  ·
    let z' : SchemeHomOver (𝟙 _) (D.baseChange R').toBase :=
      ⟨(D.baseChange R').zeroSection, (D.baseChange R').zeroSection_toBase⟩
    let s : SchemeHomOver (𝟙 (Spec (CommRingCat.of R')) ≫ specMap R R') (𝟙 (Spec (CommRingCat.of R))) :=
      ⟨specMap R R', by rw [Category.comp_id, Category.id_comp]⟩
    have hz : (postComp ψ₀ (overR R' z')).1 = (postComp ⟨D.zeroSection, D.zeroSection_toBase⟩ s).1 :=
      pullback.lift_fst _ _ _
    obtain ⟨e0⟩ := h.zero
    exact ⟨isoOfToRIso R' _ _ (chain z' ≪≫ pullbackAlongCongr h.poincare hz ≪≫
      (pullbackAlongComp h.poincare ⟨D.zeroSection, D.zeroSection_toBase⟩ s).symm ≪≫
      (Scheme.Modules.pullback (baseChangeSnd c s)).mapIso e0 ≪≫
      unitPullbackAlong s ≪≫ (toR_unit_iso c ε R' (𝟙 _)).symm)⟩

end S_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_baseChange
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_baseChange (solution)
