-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.lisse_smallEtale_equiv_unramified_genericFibre
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-15T08:31:37.254194+00:00
-- url     : https://prove2.me/submissions/9fdd8fbf-7e3d-415e-bcc1-6767c0332bf0

import Mathlib
import Definitions.Def_RPLib_S4_EtShEssSurj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

namespace EssSurjSol

open RamanujanPetersson RamanujanPetersson.EtSheaves RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin
  GalCover.grp GalCover.fG GalCover.act GalCover.gal genAlg genAlgSep genTower

universe u

theorem unram_iff (A K : Type) [CommRing A] [Field K] [Algebra A K]
    (L : IntermediateField K (AlgebraicClosure K)) :
    IsUnramifiedSub A K L ↔ ∀ P : Ideal (integralClosure A L), P.IsPrime → ∀ σ : L ≃ₐ[K] L,
      (∀ b : integralClosure A L, ∃ c ∈ P, (c : L) = σ b - b) → σ = 1 := by
  refine forall_congr' fun P => forall_congr' fun _ => ?_
  rw [Subgroup.eq_bot_iff_forall]
  refine forall_congr' fun σ => imp_congr_left ?_
  rw [AddSubgroup.mem_inertia]
  refine forall_congr' fun b => ⟨fun h => ⟨_, h, rfl⟩, fun ⟨c, hc, he⟩ => ?_⟩
  have : c = σ • b - b := Subtype.ext he
  rwa [← this]

/-- Local constancy over `U`, slice form vs. the lib's pullback form. -/
theorem nonempty_iso_iff {Λ : Type u} [CommRing Λ] {X : Scheme.{u}} (F : EtSh Λ X) (U : X.Etale)
    (M : ModuleCat.{u} Λ) :
    Nonempty ((pull U.hom Λ).obj F ≅ constSh Λ U.left M) ↔
      Nonempty ((Over.forget U).op ⋙ F.obj ≅ (Over.forget U).op ⋙ (constSh Λ X M).obj) := by
  let eM : (res U.hom Λ).obj (constSh Λ X M) ≅ constSh Λ U.left M :=
    ((pullIsoRes U.hom Λ).app _).symm ≪≫ pullConst Λ U.hom M
  let eF : (pull U.hom Λ).obj F ≅ (res U.hom Λ).obj F := (pullIsoRes U.hom Λ).app F
  let E := (overOf U).asEquivalence.op.congrLeft (E := ModuleCat.{u} Λ)
  constructor
  · rintro ⟨e⟩
    let e2 : (res U.hom Λ).obj F ≅ (res U.hom Λ).obj (constSh Λ X M) := eF.symm ≪≫ e ≪≫ eM.symm
    let e3 : E.inverse.obj ((Over.forget U).op ⋙ F.obj) ≅
        E.inverse.obj ((Over.forget U).op ⋙ (constSh Λ X M).obj) :=
      (sheafToPresheaf _ _).mapIso e2
    exact ⟨E.fullyFaithfulInverse.preimageIso e3⟩
  · rintro ⟨e⟩
    let e3 : (sheafToPresheaf _ _).obj ((res U.hom Λ).obj F) ≅
        (sheafToPresheaf _ _).obj ((res U.hom Λ).obj (constSh Λ X M)) :=
      Functor.isoWhiskerLeft (overOf U).op e
    let e4 : (res U.hom Λ).obj F ≅ (res U.hom Λ).obj (constSh Λ X M) :=
      (fullyFaithfulSheafToPresheaf _ _).preimageIso e3
    exact ⟨eF ≪≫ e4 ≪≫ eM⟩

theorem isLisse_iff {Λ : Type u} [CommRing Λ] {X : Scheme.{u}} (F : EtSh Λ X) :
    IsLisse Λ F ↔ ∀ x : X, ∃ (U : X.Etale) (v : U.left), U.hom v = x ∧
      ∃ M : ModuleCat.{u} Λ, Module.Finite Λ M ∧
        Nonempty ((Over.forget U).op ⋙ F.obj ≅
          (Over.forget U).op ⋙ ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).obj M).obj) := by
  refine forall_congr' fun x => exists_congr fun U => exists_congr fun v => and_congr_right fun _ =>
    exists_congr fun M => and_congr_right fun _ => nonempty_iso_iff F U M

section Gen

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

/-- The generic geometric point is `Spec` of `A → K → κ(η) → κ(η)^sep`. -/
theorem pt_eq :
    Spec.map (CommRingCat.ofHom ((algebraMap (genField A) (SeparableClosure (genField A))).comp
      ((fracIso A K : K →+* genField A).comp (algebraMap A K)))) =
    Spec.map (CommRingCat.ofHom (algebraMap (genField A) (SeparableClosure (genField A)))) ≫
      (Spec (CommRingCat.of A)).fromSpecResidueField (genPt A) := by
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
  refine congrArg (algebraMap (genField A) (SeparableClosure (genField A))) ?_
  show (Scheme.Spec.residueFieldIso (CommRingCat.of A) (genPt A)).inv.hom
      ((IsLocalization.algEquiv (nonZeroDivisors A) K (⊥ : Ideal A).ResidueField) (algebraMap A K a)) = _
  rw [AlgEquiv.commutes]
  rfl

end Gen

end EssSurjSol

set_option maxHeartbeats 1000000 in
open RamanujanPetersson RamanujanPetersson.EtSheaves RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec EssSurjSol in
attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin
  GalCover.grp GalCover.fG GalCover.act GalCover.gal genAlg genAlgSep genTower in
theorem EssSurjSol.main
    (A K : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] (Λ : Type) [CommRing Λ]
    (η : Spec (.of A)) (hη : IsGenericPoint η ⊤)
    (pt : Spec (.of (SeparableClosure ((Spec (.of A)).residueField η))) ⟶ Spec (.of A))
    (hpt : pt = Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of A)).residueField η)
        (SeparableClosure ((Spec (.of A)).residueField η)))) ≫ (Spec (.of A)).fromSpecResidueField η)
    (IsLisse : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat Λ) → Prop)
    (hIsLisse : ∀ F, IsLisse F ↔ ∀ x : Spec (.of A),
      ∃ (U : (Spec (.of A)).Etale) (v : U.left), U.hom v = x ∧
        ∃ M : ModuleCat Λ, Module.Finite Λ M ∧
          Nonempty ((Over.forget U).op ⋙ F.obj ≅
            (Over.forget U).op ⋙ ((constantSheaf (Spec (.of A)).smallEtaleTopology (ModuleCat Λ)).obj M).obj))
    (Unr : Subgroup (SeparableClosure ((Spec (.of A)).residueField η) ≃ₐ[(Spec (.of A)).residueField η]
      SeparableClosure ((Spec (.of A)).residueField η)) → Prop)
    (hUnr : ∀ H, Unr H ↔ ∃ L : IntermediateField K (AlgebraicClosure K),
      FiniteDimensional K L ∧ IsGalois K L ∧
      (∀ P : Ideal (integralClosure A L), P.IsPrime → ∀ σ : L ≃ₐ[K] L,
        (∀ b : integralClosure A L, ∃ c ∈ P, (c : L) = σ b - b) → σ = 1) ∧
      ∃ ι : L →+* SeparableClosure ((Spec (.of A)).residueField η),
        Spec.map (CommRingCat.ofHom (ι.comp (algebraMap A L))) = pt ∧
        ∀ σ, (∀ x : L, σ (ι x) = ι x) → σ ∈ H) :
    ∃ ρ : ∀ F : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat Λ),
        Representation Λ (SeparableClosure ((Spec (.of A)).residueField η) ≃ₐ[(Spec (.of A)).residueField η]
          SeparableClosure ((Spec (.of A)).residueField η)) (((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).obj F),
      (∀ ρ', ρ' = ρ ↔ ∀ F (σ : SeparableClosure ((Spec (.of A)).residueField η) ≃ₐ[(Spec (.of A)).residueField η]
          SeparableClosure ((Spec (.of A)).residueField η)) (U : (Spec (.of A)).Etale) (a b : Over.mk pt ⟶ (Scheme.Etale.forget _).obj U),
        b.left = Spec.map (CommRingCat.ofHom (σ : _ →+* _)) ≫ a.left →
        ∀ z, ρ' F σ ((Scheme.pointSmallEtale pt).toPresheafFiber U a F.obj z) =
          (Scheme.pointSmallEtale pt).toPresheafFiber U b F.obj z) ∧
      (∀ F G, IsLisse G →
        ∀ f : ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).obj F →ₗ[Λ] ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).obj G,
        (∀ σ v, f (ρ F σ v) = ρ G σ (f v)) →
        ∃ φ : F ⟶ G, (((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).map φ).hom = f) ∧
      (∀ F G, IsLisse F → IsLisse G → ∀ φ ψ : F ⟶ G,
        ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).map φ = ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).map ψ → φ = ψ) ∧
      (∀ F G, IsLisse F → IsLisse G →
        ∀ e : ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).obj F ≃ₗ[Λ] ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).obj G,
        (∀ σ v, e (ρ F σ v) = ρ G σ (e v)) → Nonempty (F ≅ G)) ∧
      (∀ F, IsLisse F →
        Module.Finite Λ (((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).obj F) ∧ Unr (ρ F).ker) ∧
      (∀ (V : Type) [AddCommGroup V] [Module Λ V], Module.Finite Λ V →
        ∀ ρV : Representation Λ (SeparableClosure ((Spec (.of A)).residueField η) ≃ₐ[(Spec (.of A)).residueField η]
          SeparableClosure ((Spec (.of A)).residueField η)) V, Unr ρV.ker →
        ∃ F, IsLisse F ∧ ∃ e : ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).obj F ≃ₗ[Λ] V,
          ∀ σ w, e (ρ F σ w) = ρV σ (e w)) := by
  have hη' : η = genPt A := by
    rw [genPt_eq]; exact hη.eq (genericPoint_spec _)
  subst hη'
  have hp : Spec.map (CommRingCat.ofHom (algebraMap (genField A) (SeparableClosure (genField A)))) ≫
      (Spec (CommRingCat.of A)).fromSpecResidueField (genPt A) = (geomPtAt (genPt A)).pt := rfl
  rw [hp] at hpt
  subst hpt
  have hL : ∀ F, IsLisse F ↔ EtSheaves.IsLisse Λ F := fun F => (hIsLisse F).trans (EssSurjSol.isLisse_iff F).symm
  -- ring-hom form of the point
  have hptA : ∀ (L : IntermediateField K (AlgebraicClosure K)) (ι : L →+* SeparableClosure (genField A)),
      Spec.map (CommRingCat.ofHom (ι.comp (algebraMap A L))) =
        Spec.map (CommRingCat.ofHom (algebraMap (genField A) (SeparableClosure (genField A)))) ≫
          (Spec (CommRingCat.of A)).fromSpecResidueField (genPt A) ↔
      ι.comp (algebraMap A L) = (algebraMap K (SeparableClosure (genField A))).comp (algebraMap A K) := by
    intro L ι
    rw [← pt_eq A K]
    constructor
    · intro h
      have := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
      exact this
    · intro h
      congr 2
  -- the embedding of `L ∈ unramSet` through `K_U`
  let jL : ∀ (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K),
      L →ₐ[K] SeparableClosure (genField A) := fun L hL =>
    (emb A K (SeparableClosure (genField A))).comp (IntermediateField.inclusion (le_maxUnram A K L hL))
  have hjL : ∀ (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K) (σ : Gal (genPt A))
      (y : L), σ (jL L hL y) = jL L hL y ↔
        genToPi1 A K σ (IntermediateField.inclusion (le_maxUnram A K L hL) y) =
          IntermediateField.inclusion (le_maxUnram A K L hL) y := by
    intro L hL σ y
    rw [← (genEmb A K).injective.eq_iff, genEmb_genToPi1]
    rfl
  -- an `A`-compatible `ι` has the same image as `jL`
  have hrange : ∀ (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K)
      (ι : L →+* SeparableClosure (genField A)),
      ι.comp (algebraMap A L) = (algebraMap K (SeparableClosure (genField A))).comp (algebraMap A K) →
      ∀ x : L, ∃ y : L, jL L hL y = ι x := by
    intro L hL ι hι x
    haveI := hL.2.1
    have hK : ι.comp (algebraMap K L) = algebraMap K (SeparableClosure (genField A)) := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors A)
      rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hι]
    let ιK : L →ₐ[K] SeparableClosure (genField A) :=
      { ι with commutes' := fun k => congrArg (fun f : K →+* _ => f k) hK }
    obtain ⟨y, hy⟩ := mem_fieldRange_of_normal ιK (jL L hL) x
    exact ⟨y, hy⟩
  refine ⟨fun F => galRep Λ F (genPt A), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ρ'
    constructor
    · rintro rfl F σ U a b hab z
      have hb : b = (galAct (genPt A) σ).app U a := Over.OverMorphism.ext hab
      rw [hb]
      exact Trans.galRep_germ (genPt A) Λ F σ U a z
    · intro h
      funext F
      refine MonoidHom.ext fun σ => LinearMap.ext fun v => ?_
      obtain ⟨U, a, z, rfl⟩ := (geomPtAt (genPt A)).point.toPresheafFiber_jointly_surjective (P := F.obj) v
      exact (h F σ U a ((galAct (genPt A) σ).app U a) rfl z).trans
        (Trans.galRep_germ (genPt A) Λ F σ U a z).symm
  · intro F G hG f hf
    exact EssSurj.full A ((hL G).1 hG) f hf
  · intro F G hF hG φ ψ h
    exact stalk_faithful ((hL F).1 hF) ((hL G).1 hG).isLocConst (geomPtAt (genPt A)) h
  · intro F G hF hG e he
    exact EssSurj.nonempty_iso_of_stalk A ((hL F).1 hF) ((hL G).1 hG) e.toModuleIso he
  · intro F hF
    have hF' := (hL F).1 hF
    refine ⟨hF'.finite_stalkF _, (hUnr _).2 ?_⟩
    obtain ⟨L, hL', hker⟩ := exists_resL_ker_le A K _ (EssSurj.isOpen_ker_fibRep A K F hF')
    refine ⟨L, hL'.1, hL'.2.1, (unram_iff A K L).1 hL'.2.2, (jL L hL').toRingHom, ?_, ?_⟩
    · refine (hptA L _).2 (RingHom.ext fun a => ?_)
      change genEmb A K (IntermediateField.inclusion (le_maxUnram A K L hL') (algebraMap A L a)) = _
      have : IntermediateField.inclusion (le_maxUnram A K L hL') (algebraMap A L a) =
          algebraMap K (maxUnram A K) (algebraMap A K a) := Subtype.ext (by
        change ((algebraMap A L a : L) : AlgebraicClosure K) = algebraMap K (AlgebraicClosure K) (algebraMap A K a)
        rw [← IsScalarTower.algebraMap_apply]; rfl)
      rw [this, genEmb_algebraMap]
      rfl
    · intro σ hσ
      rw [MonoidHom.mem_ker]
      show galRep Λ F (genPt A) σ = 1
      rw [← EssSurj.fibRep_genToPi1 A K F hF']
      have h1 : resL A K L hL' (genToPi1 A K σ) = 1 :=
        resL_eq_one_of_fix A K L hL' _ fun y => (hjL L hL' σ y).1 (hσ y)
      exact MonoidHom.mem_ker.1 (hker (MonoidHom.mem_ker.2 h1))
  · intro V _ _ hV ρV hρV
    obtain ⟨L, hfin, hgal, hun, ι, hι, hfix⟩ := (hUnr _).1 hρV
    have hL' : L ∈ unramSet A K := ⟨hfin, hgal, (unram_iff A K L).2 hun⟩
    have hι' := (hptA L ι).1 hι
    have key : ∀ σ : Gal (genPt A), (∀ y : L, σ (jL L hL' y) = jL L hL' y) → ρV σ = 1 := by
      intro σ hσ
      refine MonoidHom.mem_ker.1 (hfix σ fun x => ?_)
      obtain ⟨y, hy⟩ := hrange L hL' ι hι' x
      rw [← hy]; exact hσ y
    have hk : (genToPi1 A K).ker ≤ ρV.toHomUnits.ker := fun σ hσ => MonoidHom.mem_ker.2 (Units.ext (by
      refine (key σ fun y => (hjL L hL' σ y).2 ?_).trans rfl
      rw [MonoidHom.mem_ker.1 hσ]; rfl))
    let ρ' : Representation Λ (Pi1 A K) V :=
      (Units.coeHom (Module.End Λ V)).comp
        ((genToPi1 A K).liftOfSurjective (genToPi1_surjective A K) ⟨ρV.toHomUnits, hk⟩)
    have hρ' : ∀ σ, ρ' (genToPi1 A K σ) = ρV σ := fun σ =>
      congrArg Units.val ((genToPi1 A K).liftOfRightInverse_comp_apply
        (Function.surjInv (genToPi1_surjective A K)) (Function.rightInverse_surjInv (genToPi1_surjective A K))
        ⟨ρV.toHomUnits, hk⟩ σ)
    have hopen : IsOpen (ρ'.ker : Set (Pi1 A K)) := by
      refine Subgroup.isOpen_mono (fun τ hτ => ?_) (isOpen_ker_resL A K L hL')
      obtain ⟨σ, rfl⟩ := genToPi1_surjective A K τ
      rw [MonoidHom.mem_ker, hρ']
      refine key σ fun y => (hjL L hL' σ y).2 ?_
      have := resL_spec A K L hL' (genToPi1 A K σ) y
      rw [MonoidHom.mem_ker.1 hτ] at this
      exact this.symm
    obtain ⟨L2, hL2, ρ2, -, hlis, e, he⟩ := exists_lisse_of_rep A K Λ ρ' hopen
    refine ⟨FV (coverOf A K L2 hL2) Λ ρ2, (hL _).2 hlis, e.toLinearEquiv, fun σ w => ?_⟩
    show e.hom.hom (galRep Λ _ (genPt A) σ w) = ρV σ (e.hom.hom w)
    rw [he σ w, hρ']

-- The statement below is the platform statement verbatim, elaborated under default options.
set_option backward.isDefEq.respectTransparency.types true in
theorem solution
    (A K : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] (Λ : Type) [CommRing Λ]
    (η : Spec (.of A)) (hη : IsGenericPoint η ⊤)
    (pt : Spec (.of (SeparableClosure ((Spec (.of A)).residueField η))) ⟶ Spec (.of A))
    (hpt : pt = Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of A)).residueField η)
        (SeparableClosure ((Spec (.of A)).residueField η)))) ≫ (Spec (.of A)).fromSpecResidueField η)
    (IsLisse : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat Λ) → Prop)
    (hIsLisse : ∀ F, IsLisse F ↔ ∀ x : Spec (.of A),
      ∃ (U : (Spec (.of A)).Etale) (v : U.left), U.hom v = x ∧
        ∃ M : ModuleCat Λ, Module.Finite Λ M ∧
          Nonempty ((Over.forget U).op ⋙ F.obj ≅
            (Over.forget U).op ⋙ ((constantSheaf (Spec (.of A)).smallEtaleTopology (ModuleCat Λ)).obj M).obj))
    (Unr : Subgroup (SeparableClosure ((Spec (.of A)).residueField η) ≃ₐ[(Spec (.of A)).residueField η]
      SeparableClosure ((Spec (.of A)).residueField η)) → Prop)
    (hUnr : ∀ H, Unr H ↔ ∃ L : IntermediateField K (AlgebraicClosure K),
      FiniteDimensional K L ∧ IsGalois K L ∧
      (∀ P : Ideal (integralClosure A L), P.IsPrime → ∀ σ : L ≃ₐ[K] L,
        (∀ b : integralClosure A L, ∃ c ∈ P, (c : L) = σ b - b) → σ = 1) ∧
      ∃ ι : L →+* SeparableClosure ((Spec (.of A)).residueField η),
        Spec.map (CommRingCat.ofHom (ι.comp (algebraMap A L))) = pt ∧
        ∀ σ, (∀ x : L, σ (ι x) = ι x) → σ ∈ H) :
    ∃ ρ : ∀ F : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat Λ),
        Representation Λ (SeparableClosure ((Spec (.of A)).residueField η) ≃ₐ[(Spec (.of A)).residueField η]
          SeparableClosure ((Spec (.of A)).residueField η)) (((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).obj F),
      (∀ ρ', ρ' = ρ ↔ ∀ F (σ : SeparableClosure ((Spec (.of A)).residueField η) ≃ₐ[(Spec (.of A)).residueField η]
          SeparableClosure ((Spec (.of A)).residueField η)) (U : (Spec (.of A)).Etale) (a b : Over.mk pt ⟶ (Scheme.Etale.forget _).obj U),
        b.left = Spec.map (CommRingCat.ofHom (σ : _ →+* _)) ≫ a.left →
        ∀ z, ρ' F σ ((Scheme.pointSmallEtale pt).toPresheafFiber U a F.obj z) =
          (Scheme.pointSmallEtale pt).toPresheafFiber U b F.obj z) ∧
      (∀ F G, IsLisse G →
        ∀ f : ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).obj F →ₗ[Λ] ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).obj G,
        (∀ σ v, f (ρ F σ v) = ρ G σ (f v)) →
        ∃ φ : F ⟶ G, (((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).map φ).hom = f) ∧
      (∀ F G, IsLisse F → IsLisse G → ∀ φ ψ : F ⟶ G,
        ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).map φ = ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).map ψ → φ = ψ) ∧
      (∀ F G, IsLisse F → IsLisse G →
        ∀ e : ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).obj F ≃ₗ[Λ] ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).obj G,
        (∀ σ v, e (ρ F σ v) = ρ G σ (e v)) → Nonempty (F ≅ G)) ∧
      (∀ F, IsLisse F →
        Module.Finite Λ (((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).obj F) ∧ Unr (ρ F).ker) ∧
      (∀ (V : Type) [AddCommGroup V] [Module Λ V], Module.Finite Λ V →
        ∀ ρV : Representation Λ (SeparableClosure ((Spec (.of A)).residueField η) ≃ₐ[(Spec (.of A)).residueField η]
          SeparableClosure ((Spec (.of A)).residueField η)) V, Unr ρV.ker →
        ∃ F, IsLisse F ∧ ∃ e : ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).obj F ≃ₗ[Λ] V,
          ∀ σ w, e (ρ F σ w) = ρV σ (e w)) := by
  exact EssSurjSol.main A K Λ η hη pt hpt IsLisse hIsLisse Unr hUnr
