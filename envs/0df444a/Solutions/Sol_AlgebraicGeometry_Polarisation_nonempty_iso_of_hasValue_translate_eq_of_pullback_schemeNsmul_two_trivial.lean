-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.nonempty_iso_of_hasValue_translate_eq_of_pullback_schemeNsmul_two_trivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/4bf20bba-8735-5b96-8518-76eb0c150b14

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_TorsionCharacter
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_translate_comp_schemeNsmul_of_mem_torsionSubset
import Theorems.Thm_AlgebraicGeometry_DescentCharacter_hasValue_trans
import Theorems.Thm_AlgebraicGeometry_DescentCharacter_hasValue_symm_of_mul_eq_one
import Theorems.Thm_AlgebraicGeometry_DescentCharacter_existsUnique_iso_mapIso_eq_of_hasValue_one
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_action_isIso_shear_of_existsUnique_isTorsionPoint_of_commRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isTorsionPoint_fst_schemeKer_and_existsUnique_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_nonempty_iso_of_hasValue_translate_eq_of_pullback_schemeNsmul_two_trivial

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard AlgebraicGeometry.DescentCharacter"

universe u

namespace C6HV

variable {X Y Y' : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))

theorem isBaseScalar_conj {M M' : X.Modules} (e : M' ≅ M) {σ : M ⟶ M} {c : R}
    (h : IsBaseScalar f σ c) : IsBaseScalar f (e.hom ≫ σ ≫ e.inv) c := by
  intro U s
  have h1 : (e.hom ≫ σ ≫ e.inv).app U s = e.inv.app U (σ.app U (e.hom.app U s)) := by
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  have h2 : e.inv.app U (e.hom.app U s) = s := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id,
      Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]
  rw [h1, h U, Scheme.Modules.Hom.app_smul, h2]

theorem pullbackCongr_hom_app {q₁ q₂ : X ⟶ Y} (e : q₁ = q₂) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr e).hom.app M = eqToHom (by rw [e]) := by
  subst e
  simp [Scheme.Modules.pullbackCongr]

theorem pullbackCongr_inv_app {q₁ q₂ : X ⟶ Y} (e : q₁ = q₂) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr e).inv.app M = eqToHom (by rw [e]) := by
  subst e
  simp [Scheme.Modules.pullbackCongr]

theorem pullbackComp_hom_app_eqToHom {r₁ r₂ : X ⟶ Y'} (e : r₁ = r₂) (s : Y' ⟶ Y) (M : Y.Modules) :
    (Scheme.Modules.pullbackComp r₁ s).hom.app M ≫
        eqToHom (show (Scheme.Modules.pullback (r₁ ≫ s)).obj M = (Scheme.Modules.pullback (r₂ ≫ s)).obj M by rw [e]) =
      eqToHom (show (Scheme.Modules.pullback r₁).obj ((Scheme.Modules.pullback s).obj M) = (Scheme.Modules.pullback r₂).obj ((Scheme.Modules.pullback s).obj M) by rw [e]) ≫
        (Scheme.Modules.pullbackComp r₂ s).hom.app M := by
  subst e
  simp

theorem mapIso_pullbackComp_trans_transportIso {T : X ⟶ X} {r : X ⟶ Y'} (s : Y' ⟶ Y)
    (hr : T ≫ r = r) (h : T ≫ r ≫ s = r ≫ s) (M : Y.Modules) :
    (Scheme.Modules.pullback T).mapIso ((Scheme.Modules.pullbackComp r s).app M) ≪≫ transportIso h M =
      transportIso hr ((Scheme.Modules.pullback s).obj M) ≪≫ (Scheme.Modules.pullbackComp r s).app M := by
  apply Iso.ext
  have A := congrArg (fun α => NatTrans.app α M) (Scheme.Modules.pseudofunctor_associativity T r s)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.comp_obj, Category.id_comp, eqToHom_app] at A

  have A1 := (Iso.inv_comp_eq ((Scheme.Modules.pullbackComp T (r ≫ s)).app M)).mp A
  have A2 := (Iso.inv_comp_eq
    ((Scheme.Modules.pullback T).mapIso ((Scheme.Modules.pullbackComp r s).app M))).mp A1

  simp only [Functor.mapIso_hom, Iso.app_hom] at A2
  have B := pullbackComp_hom_app_eqToHom hr s M
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, transportIso, pullbackCongr_hom_app,
    Category.assoc]
  erw [← B, reassoc_of% A2]
  simp only [Category.assoc, eqToHom_trans]
  try rfl

theorem hasValue_rebase {T : X ⟶ X} {r : X ⟶ Y'} {s : Y' ⟶ Y} (hr : T ≫ r = r) (h : T ≫ r ≫ s = r ≫ s)
    {N M : Y.Modules}
    (β : (Scheme.Modules.pullback r).obj ((Scheme.Modules.pullback s).obj N) ≅
      (Scheme.Modules.pullback r).obj ((Scheme.Modules.pullback s).obj M))
    (c : R) (hβ : HasValue f hr β c) :
    HasValue f h (((Scheme.Modules.pullbackComp r s).app N).symm ≪≫ β ≪≫ (Scheme.Modules.pullbackComp r s).app M) c := by
  have KMh := congrArg Iso.hom (mapIso_pullbackComp_trans_transportIso s hr h M)
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at KMh
  have KNi := congrArg Iso.inv (mapIso_pullbackComp_trans_transportIso s hr h N)
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv] at KNi
  unfold HasValue at hβ ⊢
  have hd : (discrepancy h (((Scheme.Modules.pullbackComp r s).app N).symm ≪≫ β ≪≫
        (Scheme.Modules.pullbackComp r s).app M)).hom =
      (Scheme.Modules.pullbackComp r s).inv.app M ≫ (discrepancy hr β).hom ≫
        (Scheme.Modules.pullbackComp r s).hom.app M := by
    simp only [discrepancy, translateIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc]
    dsimp only [Functor.comp_obj] at KNi KMh ⊢
    have hC := Iso.hom_inv_id_app (Scheme.Modules.pullbackComp r s) N
    dsimp only [Functor.comp_obj] at hC
    rw [reassoc_of% KNi, reassoc_of% hC, KMh]
    try simp only [Category.assoc]
  rw [hd]
  exact isBaseScalar_conj f ((Scheme.Modules.pullbackComp r s).app M).symm hβ

theorem hasValue_of_hasValue_conj_pullbackComp {T : X ⟶ X} {r : X ⟶ Y'} {s : Y' ⟶ Y} (hr : T ≫ r = r)
    (h : T ≫ r ≫ s = r ≫ s) {N M : Y.Modules}
    (B' : (Scheme.Modules.pullback (r ≫ s)).obj N ≅ (Scheme.Modules.pullback (r ≫ s)).obj M) (c : R)
    (hβ : HasValue f hr ((Scheme.Modules.pullbackComp r s).app N ≪≫ B' ≪≫
      ((Scheme.Modules.pullbackComp r s).app M).symm) c) :
    HasValue f h B' c := by
  have h1 := hasValue_rebase f hr h _ c hβ
  dsimp only [Functor.comp_obj] at h1 ⊢
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id, Iso.trans_refl] at h1
  exact h1

theorem hasValue_congr_q {T : X ⟶ X} {q₁ q₂ : X ⟶ Y} (e : q₁ = q₂) (h₁ : T ≫ q₁ = q₁) (h₂ : T ≫ q₂ = q₂)
    {N M : Y.Modules}
    (B : (Scheme.Modules.pullback q₂).obj N ≅ (Scheme.Modules.pullback q₂).obj M) (c : R)
    (hB : HasValue f h₁ ((Scheme.Modules.pullbackCongr e).app N ≪≫ B ≪≫ ((Scheme.Modules.pullbackCongr e).app M).symm) c) :
    HasValue f h₂ B c := by
  subst e
  have : (Scheme.Modules.pullbackCongr (rfl : q₁ = q₁)).app N ≪≫ B ≪≫
      ((Scheme.Modules.pullbackCongr (rfl : q₁ = q₁)).app M).symm = B := by
    apply Iso.ext
    simp [Scheme.Modules.pullbackCongr]
  rw [this] at hB
  exact hB

end C6HV

namespace C6Aux

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

theorem baseChange_nsmul {R' : Type u} [CommRing R'] (σ : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (n : ℕ)
    (y : SchemeHomOver t' (RelativeGroupLaw.baseChangeStr σ f)) :
    (L.baseChange σ).nsmul t' n y =
      RelativeGroupLaw.baseChangePointOfBase σ (L.nsmul (t' ≫ σ) n (RelativeGroupLaw.baseChangePointToBase σ y)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, ih, RelativeGroupLaw.baseChange_mul,
      RelativeGroupLaw.baseChangePointToBase_ofBase]

theorem isTorsionPoint_baseChange_iff {R' : Type u} [CommRing R']
    (σ : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S)) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (n : ℕ) (y : SchemeHomOver t' (RelativeGroupLaw.baseChangeStr σ f)) :
    (L.baseChange σ).IsTorsionPoint t' n y ↔
      L.IsTorsionPoint (t' ≫ σ) n (RelativeGroupLaw.baseChangePointToBase σ y) := by
  rw [RelativeGroupLaw.isTorsionPoint_def, RelativeGroupLaw.isTorsionPoint_def, baseChange_nsmul,
    RelativeGroupLaw.baseChange_one]
  constructor
  · intro h
    have h' := congrArg (RelativeGroupLaw.baseChangePointToBase σ) h
    rwa [RelativeGroupLaw.baseChangePointToBase_ofBase, RelativeGroupLaw.baseChangePointToBase_ofBase] at h'
  · intro h
    rw [h]

theorem mem_torsionSubset_ofBase {R' : Type u} [CommRing R']
    (σ : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S)) (n : ℕ)
    (x : SchemeHomOver σ f) (hx : L.IsTorsionPoint σ n x) :
    RelativeGroupLaw.baseChangePointOfBase σ (t' := 𝟙 (Spec (CommRingCat.of R')))
        ⟨x.1, by rw [Category.id_comp]; exact x.2⟩ ∈
      (L.baseChange σ).torsionSubset (𝟙 (Spec (CommRingCat.of R'))) n := by
  rw [RelativeGroupLaw.mem_torsionSubset, RelativeGroupLaw.isTorsionPoint_def, baseChange_nsmul,
    RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointToBase_ofBase]
  congr 1

theorem translate_comp_schemeNsmul (hc : L.IsCommutative) {R' : Type u} [CommRing R']
    (σ : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S)) (n : ℕ)
    (x : SchemeHomOver σ f) (hx : L.IsTorsionPoint σ n x) :
    (L.baseChange σ).translate
        (RelativeGroupLaw.baseChangePointOfBase σ (t' := 𝟙 (Spec (CommRingCat.of R')))
          ⟨x.1, by rw [Category.id_comp]; exact x.2⟩) ≫ (L.baseChange σ).schemeNsmul n =
      (L.baseChange σ).schemeNsmul n :=
  RelativeGroupLaw.translate_comp_schemeNsmul_of_mem_torsionSubset _ (hc.baseChange σ) n _
    (mem_torsionSubset_ofBase L σ n x hx)

theorem baseChangeSnd_comp_fst {R R' : Type u} [CommRing R] [CommRing R']
    {ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)} {ι' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S)}
    (ψ : SchemeHomOver ι' ι) : baseChangeSnd f ψ ≫ pullback.fst f ι = pullback.fst f ι' := by
  unfold baseChangeSnd; rw [pullback.lift_fst, Category.comp_id]

theorem baseChangeSnd_comp_snd {R R' : Type u} [CommRing R] [CommRing R']
    {ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)} {ι' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S)}
    (ψ : SchemeHomOver ι' ι) : baseChangeSnd f ψ ≫ pullback.snd f ι = pullback.snd f ι' ≫ ψ.1 := by
  unfold baseChangeSnd; rw [pullback.lift_snd]

theorem schemeNsmul_comp_baseChangeSnd {R R' : Type u} [CommRing R] [CommRing R']
    {ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)} {ι' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S)}
    (ψ : SchemeHomOver ι' ι) (n : ℕ) :
    (L.baseChange ι').schemeNsmul n ≫ baseChangeSnd f ψ = baseChangeSnd f ψ ≫ (L.baseChange ι).schemeNsmul n := by
  have w := (RelativeGroupLaw.isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange ι L n).1.w
  have w' := (RelativeGroupLaw.isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange ι' L n).1.w
  have hfst := baseChangeSnd_comp_fst (f := f) ψ
  have hsnd := baseChangeSnd_comp_snd (f := f) ψ
  apply pullback.hom_ext
  · rw [Category.assoc, hfst, Category.assoc, ← w, ← Category.assoc, hfst, w']
  · rw [Category.assoc, hsnd, Category.assoc, (L.baseChange ι).schemeNsmul_over, ← Category.assoc,
      (L.baseChange ι').schemeNsmul_over, hsnd]

theorem ker2_pullbackAlong {R R' : Type u} [CommRing R] [CommRing R']
    {ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)} {ι' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S)}
    (ψ : SchemeHomOver ι' ι) (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι)
    (h : Nonempty ((Scheme.Modules.pullback ((L.baseChange ι).schemeNsmul 2)).obj N.L ≅ 𝟙_ _)) :
    Nonempty ((Scheme.Modules.pullback ((L.baseChange ι').schemeNsmul 2)).obj (N.pullbackAlong ψ).L ≅ 𝟙_ _) := by
  obtain ⟨e⟩ := h
  exact ⟨(Scheme.Modules.pullbackComp ((L.baseChange ι').schemeNsmul 2) (baseChangeSnd f ψ)).app N.L ≪≫
    (Scheme.Modules.pullbackCongr (schemeNsmul_comp_baseChangeSnd L ψ 2)).app N.L ≪≫
    ((Scheme.Modules.pullbackComp (baseChangeSnd f ψ) ((L.baseChange ι).schemeNsmul 2)).app N.L).symm ≪≫
    (Scheme.Modules.pullback (baseChangeSnd f ψ)).mapIso e ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso (baseChangeSnd f ψ)⟩

theorem nonempty_beta {R : Type u} [CommRing R] {ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)}
    (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι)
    (h : Nonempty ((Scheme.Modules.pullback ((L.baseChange ι).schemeNsmul 2)).obj N.L ≅ 𝟙_ _))
    (T : Type u) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R)) :
    Nonempty ((Scheme.Modules.pullback ((L.baseChange (κ ≫ ι)).schemeNsmul 2)).obj
        (N.pullbackAlong (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)).L ≅
      (Scheme.Modules.pullback ((L.baseChange (κ ≫ ι)).schemeNsmul 2)).obj (𝟙_ _)) := by
  obtain ⟨e⟩ := ker2_pullbackAlong L (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι) N h
  exact ⟨e ≪≫ (Scheme.Modules.pullbackTensorUnitObjIso _).symm⟩

theorem mul_val_congr {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of S)} (e : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst e
  obtain rfl : P = P' := Subtype.ext hP
  obtain rfl : Q = Q' := Subtype.ext hQ
  rfl

theorem isPullback_translate_sq (hc : L.IsCommutative) {R : Type u} [CommRing R]
    (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) {T : Type u} [CommRing T]
    (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver (κ ≫ ι) f)
    (hxu : (L.baseChange ι).IsTorsionPoint κ 2 (RelativeGroupLaw.baseChangePointOfBase ι x) ∧
      ∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of R))
        (z : SchemeHomOver t (RelativeGroupLaw.baseChangeStr ι f)), (L.baseChange ι).IsTorsionPoint t 2 z →
        ∃! g : T' ⟶ Spec (CommRingCat.of T), g ≫ (RelativeGroupLaw.baseChangePointOfBase ι x).1 = z.1) :
    IsPullback (baseChangeSnd f (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι))
      ((L.baseChange (κ ≫ ι)).translate
          (RelativeGroupLaw.baseChangePointOfBase (κ ≫ ι) (t' := 𝟙 (Spec (CommRingCat.of T)))
            ⟨x.1, by rw [Category.id_comp]; exact x.2⟩) ≫
        baseChangeSnd f (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι))
      ((L.baseChange ι).schemeNsmul 2) ((L.baseChange ι).schemeNsmul 2) := by

  obtain ⟨act, -, hpts, hsh, hiso⟩ :=
    RelativeGroupLaw.exists_action_isIso_shear_of_existsUnique_isTorsionPoint_of_commRing R
      (RelativeGroupLaw.baseChangeStr ι f) (L.baseChange ι) (hc.baseChange ι) 2 κ
      (RelativeGroupLaw.baseChangePointOfBase ι x) hxu.1 hxu.2
  haveI := hiso
  have hP0 : IsPullback (pullback.fst (RelativeGroupLaw.baseChangeStr ι f) κ) act
      ((L.baseChange ι).schemeNsmul 2) ((L.baseChange ι).schemeNsmul 2) :=
    IsPullback.of_iso_pullback ⟨hsh⟩
      (asIso (pullback.lift (f := (L.baseChange ι).schemeNsmul 2) (g := (L.baseChange ι).schemeNsmul 2)
        (pullback.fst (RelativeGroupLaw.baseChangeStr ι f) κ) act hsh))
      (by rw [asIso_hom, pullback.lift_fst]) (by rw [asIso_hom, pullback.lift_snd])

  let e := pullbackLeftPullbackSndIso f ι κ
  have hgf := baseChangeSnd_comp_fst (f := f) (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)
  have hgs := baseChangeSnd_comp_snd (f := f) (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)
  have h1 : e.inv ≫ pullback.fst (RelativeGroupLaw.baseChangeStr ι f) κ =
      baseChangeSnd f (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hgf]; exact pullbackLeftPullbackSndIso_inv_fst f ι κ
    · rw [Category.assoc, hgs]; exact pullbackLeftPullbackSndIso_inv_fst_snd f ι κ
  have h2 : e.inv ≫ pullback.snd (RelativeGroupLaw.baseChangeStr ι f) κ = pullback.snd f (κ ≫ ι) :=
    pullbackLeftPullbackSndIso_inv_snd_snd f ι κ
  have hx0 : baseChangeSnd f (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι) ≫ RelativeGroupLaw.baseChangeStr ι f =
      pullback.snd f (κ ≫ ι) ≫ κ := hgs
  have heinv : e.inv = pullback.lift (baseChangeSnd f (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι))
      (pullback.snd f (κ ≫ ι)) hx0 := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]; exact h1
    · rw [pullback.lift_snd]; exact h2
  refine hP0.of_iso' e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id]; exact h1
  · rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id, heinv,
      hpts (pullback.snd f (κ ≫ ι) ≫ κ) ⟨baseChangeSnd f (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι), hx0⟩
        (pullback.snd f (κ ≫ ι)) hx0]

    apply pullback.hom_ext
    · rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
      conv_rhs => rw [Category.assoc, hgf]; unfold RelativeGroupLaw.translate
      conv_rhs => rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
      apply mul_val_congr L (Category.assoc _ _ _)
      · rw [RelativeGroupLaw.baseChangePointToBase_coe, RelativeGroupLaw.baseChangePointToBase_coe, hgf]
        exact (Category.id_comp _).symm
      · simp only [RelativeGroupLaw.baseChangePointToBase_coe, RelativeGroupLaw.baseChangePointOfBase_coe,
          Category.assoc, pullback.lift_fst]
    · rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_snd]
      conv_rhs => rw [Category.assoc, hgs]; unfold RelativeGroupLaw.translate
      conv_rhs => rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe,
        ← Category.assoc, pullback.lift_snd]

end C6Aux

open C6HV C6Aux

theorem solution
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (hker : IsFinite (L.schemeKerStr 2) ∧ Flat (L.schemeKerStr 2) ∧ LocallyOfFinitePresentation (L.schemeKerStr 2))
    (h2fl : IsAffineHom (L.schemeNsmul 2) ∧ Flat (L.schemeNsmul 2) ∧ Surjective (L.schemeNsmul 2)) :
    let Adm : ∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)),
        RigidifiedLineBundle f (L.one (𝟙 _)) ι → Prop :=
      fun R _ ι N =>
        Nonempty ((Scheme.Modules.pullback ((L.baseChange ι).schemeNsmul 2)).obj N.L ≅ 𝟙_ _)
    let IsCharOf : ∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)),
        RigidifiedLineBundle f (L.one (𝟙 _)) ι → L.TorsionCharacter 2 ι → Prop :=
      fun R _ ι N χ =>
        ∀ (T : Type) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
          (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x)
          (hTq : (L.baseChange (κ ≫ ι)).translate
              (RelativeGroupLaw.baseChangePointOfBase (κ ≫ ι) (t' := 𝟙 (Spec (CommRingCat.of T)))
                ⟨x.1, by rw [Category.id_comp]; exact x.2⟩) ≫ (L.baseChange (κ ≫ ι)).schemeNsmul 2 =
            (L.baseChange (κ ≫ ι)).schemeNsmul 2)
          (β : (Scheme.Modules.pullback ((L.baseChange (κ ≫ ι)).schemeNsmul 2)).obj
                (N.pullbackAlong (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)).L ≅
              (Scheme.Modules.pullback ((L.baseChange (κ ≫ ι)).schemeNsmul 2)).obj (𝟙_ _)),
          HasValue (pullback.snd f (κ ≫ ι)) hTq β ((χ.val T κ x hx : Tˣ) : T)
    ∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
      (N N' : RigidifiedLineBundle f (L.one (𝟙 _)) ι) (χ : L.TorsionCharacter 2 ι),
      Adm R ι N → Adm R ι N' → IsCharOf R ι N χ → IsCharOf R ι N' χ → Nonempty (N.L ≅ N'.L) := by
  intro Adm IsCharOf R _ ι N N' χ hN hN' hχ hχ'

  have h472 := RelativeGroupLaw.isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange ι L 2
  haveI hqa : IsAffineHom ((L.baseChange ι).schemeNsmul 2) := h472.2 _ inferInstance h2fl.1
  haveI hqf : Flat ((L.baseChange ι).schemeNsmul 2) := h472.2 _ inferInstance h2fl.2.1
  haveI hqs : Surjective ((L.baseChange ι).schemeNsmul 2) := h472.2 _ inferInstance h2fl.2.2

  obtain ⟨hu0, hu0t, huniv0⟩ :=
    RelativeGroupLaw.isTorsionPoint_fst_schemeKer_and_existsUnique_comp_eq (L.baseChange ι) 2
  haveI : IsAffineHom ((L.baseChange ι).schemeKerStr 2) := MorphismProperty.pullback_snd _ _ hqa
  haveI : IsAffine ((L.baseChange ι).schemeKer 2) := isAffine_of_isAffineHom ((L.baseChange ι).schemeKerStr 2)
  let K : Scheme := (L.baseChange ι).schemeKer 2
  let T : Type := Γ(K, ⊤)
  let eK : Spec (CommRingCat.of T) ≅ K := K.isoSpec.symm
  let κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R) := eK.hom ≫ (L.baseChange ι).schemeKerStr 2
  let xR : SchemeHomOver κ (RelativeGroupLaw.baseChangeStr ι f) :=
    schemeHomOverComp eK.hom rfl
      ⟨pullback.fst ((L.baseChange ι).schemeNsmul 2) ((L.baseChange ι).one (𝟙 _)).1, hu0⟩
  have hxR : (L.baseChange ι).IsTorsionPoint κ 2 xR :=
    (L.baseChange ι).isTorsionPoint_schemeHomOverComp _ _ eK.hom rfl 2 hu0t
  have hxRu : ∀ {T' : Scheme} (t : T' ⟶ Spec (CommRingCat.of R))
      (z : SchemeHomOver t (RelativeGroupLaw.baseChangeStr ι f)), (L.baseChange ι).IsTorsionPoint t 2 z →
      ∃! g : T' ⟶ Spec (CommRingCat.of T), g ≫ xR.1 = z.1 := by
    intro T' t z hz
    obtain ⟨g₀, hg₀, hg₀u⟩ := huniv0 t z hz
    refine ⟨g₀ ≫ eK.inv, ?_, fun g hg => ?_⟩
    · show (g₀ ≫ eK.inv) ≫ eK.hom ≫ _ = z.1
      rw [Category.assoc, eK.inv_hom_id_assoc]; exact hg₀
    · have hg' : (g ≫ eK.hom) ≫ pullback.fst ((L.baseChange ι).schemeNsmul 2) ((L.baseChange ι).one (𝟙 _)).1 =
          z.1 := by rw [Category.assoc]; exact hg
      rw [← hg₀u _ hg', Category.assoc, eK.hom_inv_id, Category.comp_id]
  let x : SchemeHomOver (κ ≫ ι) f := RelativeGroupLaw.baseChangePointToBase ι xR
  have hxo : RelativeGroupLaw.baseChangePointOfBase ι x = xR := RelativeGroupLaw.baseChangePointOfBase_toBase ι xR
  have hx : L.IsTorsionPoint (κ ≫ ι) 2 x := (isTorsionPoint_baseChange_iff L ι κ 2 xR).mp hxR
  have hTq := translate_comp_schemeNsmul L hc (κ ≫ ι) 2 x hx

  have hP := isPullback_translate_sq L hc ι κ x (by rw [hxo]; exact ⟨hxR, hxRu⟩)

  let q := (L.baseChange ι).schemeNsmul 2
  let qT := (L.baseChange (κ ≫ ι)).schemeNsmul 2
  let gX := baseChangeSnd f (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)
  let Tx := (L.baseChange (κ ≫ ι)).translate
    (RelativeGroupLaw.baseChangePointOfBase (κ ≫ ι) (t' := 𝟙 (Spec (CommRingCat.of T)))
      ⟨x.1, by rw [Category.id_comp]; exact x.2⟩)
  have hcomm : qT ≫ gX = gX ≫ q := schemeNsmul_comp_baseChangeSnd L ⟨κ, rfl⟩ 2
  have h' : Tx ≫ qT ≫ gX = qT ≫ gX := by rw [← Category.assoc, hTq]
  have h'' : Tx ≫ gX ≫ q = gX ≫ q := by rw [← hcomm]; exact h'

  let β : (Scheme.Modules.pullback q).obj N.L ≅ (Scheme.Modules.pullback q).obj N'.L := hN.some ≪≫ hN'.some.symm
  let B : (Scheme.Modules.pullback (gX ≫ q)).obj N.L ≅ (Scheme.Modules.pullback (gX ≫ q)).obj N'.L :=
    ((Scheme.Modules.pullbackComp gX q).app N.L).symm ≪≫ (Scheme.Modules.pullback gX).mapIso β ≪≫
      (Scheme.Modules.pullbackComp gX q).app N'.L
  let B₁ : (Scheme.Modules.pullback (qT ≫ gX)).obj N.L ≅ (Scheme.Modules.pullback (qT ≫ gX)).obj N'.L :=
    (Scheme.Modules.pullbackCongr hcomm).app N.L ≪≫ B ≪≫ ((Scheme.Modules.pullbackCongr hcomm).app N'.L).symm
  let β' : (Scheme.Modules.pullback qT).obj ((Scheme.Modules.pullback gX).obj N.L) ≅
      (Scheme.Modules.pullback qT).obj ((Scheme.Modules.pullback gX).obj N'.L) :=
    (Scheme.Modules.pullbackComp qT gX).app N.L ≪≫ B₁ ≪≫ ((Scheme.Modules.pullbackComp qT gX).app N'.L).symm

  obtain ⟨β'T₀⟩ := nonempty_beta L N' hN' T κ
  let β'T : (Scheme.Modules.pullback qT).obj ((Scheme.Modules.pullback gX).obj N'.L) ≅
      (Scheme.Modules.pullback qT).obj (𝟙_ _) := β'T₀
  have h1 : HasValue (pullback.snd f (κ ≫ ι)) hTq (β' ≪≫ β'T) ((χ.val T κ x hx : Tˣ) : T) :=
    hχ T κ x hx hTq (β' ≪≫ β'T)
  have h2 : HasValue (pullback.snd f (κ ≫ ι)) hTq β'T ((χ.val T κ x hx : Tˣ) : T) :=
    hχ' T κ x hx hTq β'T
  have h3 := hasValue_symm_of_mul_eq_one (pullback.snd f (κ ≫ ι)) hTq β'T _
    (((χ.val T κ x hx)⁻¹ : Tˣ) : T) h2 (Units.inv_mul _)
  have h4 := hasValue_trans (pullback.snd f (κ ≫ ι)) hTq (β' ≪≫ β'T) β'T.symm _ _ h1 h3
  rw [Units.mul_inv, Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] at h4

  have h6 := hasValue_of_hasValue_conj_pullbackComp (pullback.snd f (κ ≫ ι)) hTq h' B₁ 1 h4
  have h7 := hasValue_congr_q (pullback.snd f (κ ≫ ι)) hcomm h' h'' B 1 h6

  obtain ⟨α, -⟩ := existsUnique_iso_mapIso_eq_of_hasValue_one (pullback.snd f (κ ≫ ι)) q gX (Tx ≫ gX) hP
    Tx rfl h'' N.isInvertible N'.isInvertible β h7
  exact ⟨α⟩

end S_AlgebraicGeometry_Polarisation_nonempty_iso_of_hasValue_translate_eq_of_pullback_schemeNsmul_two_trivial
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_nonempty_iso_of_hasValue_translate_eq_of_pullback_schemeNsmul_two_trivial (solution)
