-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T15:36:15.667442+00:00
-- url     : https://prove2.me/theorems/fc32bb74-53e7-4fbb-a074-262e2d4e8f75
-- title:
--   Comparison Mem Cech Hodge Filtration
-- statement:
--   Definitions and structural lemmas for Comparison Mem Cech Hodge Filtration, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ComparisonMemCechHodgeFiltration.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsNilDPOfCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_StructureHomApply
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_of_algHom
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_oneFormMap_eq_kaehlerDifferential_map
import Theorems.Thm_GlobalTheory_CechDR_coneMap_bijective
import Theorems.Thm_GlobalTheory_CechDR_dOne_connForm
import Theorems.Thm_GlobalTheory_CechDR_dOne_smul_D
import Theorems.Thm_GlobalTheory_CechDR_pullHyp1_ofForm
import Theorems.Thm_GlobalTheory_Cris_connForm_map
import Theorems.Thm_GlobalTheory_Cris_crystallineConnectionForm_coboundaryZero
import Theorems.Thm_GlobalTheory_Cris_ev_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
namespace GlobalTheory.CechDR
open CatCoh Cris
universe v u v' u'
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
section Points
attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler
variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X}
theorem connForm_add {B : Type} [CommRing B] [Algebra R B] (f g : Z1 (O (dp0 R) s)) (x : Sp B ⟶ X)
    (hx : x ≫ s = spMap (algebraMap R B)) :
    connForm (f + g) x hx = connForm f x hx + connForm g x hx :=
  (congrArg (TrivSqZeroExt.snd (R := B))
    (add_sub_add_comm (α := TrivSqZeroExt B Ω[B⁄R]) _ _ _ _)).trans (TrivSqZeroExt.snd_add _ _)
theorem connForm_smul {B : Type} [CommRing B] [Algebra R B] (r : R) (f : Z1 (O (dp0 R) s))
    (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B)) :
    connForm (r • f) x hx = r • connForm f x hx :=
  (congrArg (TrivSqZeroExt.snd (R := B))
    (smul_sub r (_ : TrivSqZeroExt B Ω[B⁄R]) _).symm).trans (TrivSqZeroExt.snd_smul _ _)
theorem connForm_algHom {B B' : Type} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
    (α : B →ₐ[R] B') (f : Z1 (O (dp0 R) s)) (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B))
    (x' : Sp B' ⟶ X) (hx' : x' ≫ s = spMap (algebraMap R B')) (e : spMap (α : B →+* B') ≫ x = x') :
    connForm f x' hx' = (SemiHom.of_algHom α).m1 (connForm f x hx) +
      D R B' (ev f (Thick.trivHom (hx := hx) (T := Thick.triv B' x' hx') α e)) := by
  letI : Algebra B B' := (α : B →+* B').toAlgebra
  haveI : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq fun r ↦ (α.commutes r).symm
  rw [SemiHom.oneFormMap_eq_kaehlerDifferential_map _ fun _ ↦ rfl]
  exact eq_add_of_sub_eq' (connForm_map f x hx x' hx' e)
section Semi
variable {B B' : Type} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R' B'] {α : B →+* B'}
  (h : IsMor (dp0 R) s (dp0 R') s' σ φ) (ha : SemiHom σ α)
  {x : Sp B ⟶ X} (hx : x ≫ s = spMap (algebraMap R B))
  {x' : Sp B' ⟶ X'} (hx' : x' ≫ s' = spMap (algebraMap R' B')) (e : spMap α ≫ x = x' ≫ φ)
def semiTriv : Thick.triv B x hx ⟶ h.obj (Thick.triv B' x' hx') :=
  Thick.trivHom { α with commutes' := ha.map_algebraMap } e
def semiDiag : TrivSqZeroExt B Ω[B⁄R] →+* TrivSqZeroExt B' Ω[B'⁄R'] where
  toFun c := TrivSqZeroExt.inl (α c.fst) + TrivSqZeroExt.inr (ha.m1 c.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp
theorem fst_semiDiag (c : TrivSqZeroExt B Ω[B⁄R]) : (semiDiag ha c).fst = α c.fst := add_zero _
theorem snd_semiDiag (c : TrivSqZeroExt B Ω[B⁄R]) : (semiDiag ha c).snd = ha.m1 c.snd := zero_add _
def semiDiagHom : (diagExt R B).thick x hx ⟶ h.obj ((diagExt R' B').thick x' hx') where
  φ := { semiDiag ha with
    commutes' := fun r ↦ by
      change semiDiag ha (algebraMap R _ r) = algebraMap R' _ (σ r)
      ext
      · rw [fst_semiDiag]; simp [TrivSqZeroExt.algebraMap_eq_inl', ha.map_algebraMap]
      · rw [snd_semiDiag]; simp [TrivSqZeroExt.algebraMap_eq_inl'] }
  φ₀ := α
  comm c := (fst_semiDiag ha c).symm
  dp := isDPMorphism_sqDP (diagExt R B).sq (diagExt R' B').sq _ fun a ha' ↦ by
    have h0 : a.fst = 0 := ha'
    change (semiDiag ha a).fst = 0
    rw [fst_semiDiag, h0, map_zero]
  pt := e
end Semi
variable {C : Type u} [Category.{v} C] {F : C ⥤ CommAlgCat.{0} R}
  (x : ∀ T : C, Sp (F.obj T) ⟶ X) (hx : ∀ T, x T ≫ s = spMap (algebraMap R (F.obj T)))
  (hc : ∀ ⦃T T' : C⦄ (a : T ⟶ T'), spMap (mp F a : F.obj T →+* F.obj T') ≫ x T = x T')
def ptFunctor : C ⥤ (IsTriv s).FullSubcategory where
  obj T := ⟨Thick.triv (F.obj T) (x T) (hx T), rfl⟩
  map {T T'} a := ⟨Thick.trivHom (T := Thick.triv (F.obj T') (x T') (hx T')) (mp F a) (hc a)⟩
  map_id T := ObjectProperty.hom_ext _ (Thick.hom_ext (mp_id F T))
  map_comp a b := ObjectProperty.hom_ext _ (Thick.hom_ext (mp_comp F a b))
def ptCoef : CoefMap (RingHom.id R) ((IsTriv s).ι ⋙ O (dp0 R) s) F where
  G := ptFunctor x hx hc
  α T := RingHom.id (F.obj T)
  naturality _ _ := rfl
  smul _ _ _ := rfl
def ptZZ : Z1 (O (dp0 R) s) →ₗ[R] cechDeRhamTotalCocyclesOne F where
  toFun f := ⟨(fun _ _ a ↦ ev f ((ptFunctor x hx hc).map a).hom, fun T ↦ connForm f (x T) (hx T)),
    mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨fun T T' T'' a b ↦ by
      change ev f ((ptFunctor x hx hc).map (a ≫ b)).hom = _
      rw [Functor.map_comp]
      exact ev_comp f _ _,
      fun T T' a ↦ connForm_algHom (mp F a) f _ _ _ _ (hc a), fun T ↦ dOne_connForm f _ _⟩⟩
  map_add' f g := Subtype.ext (Tot1.ext (fun _ _ _ ↦ rfl) fun T ↦ connForm_add f g _ _)
  map_smul' r f := Subtype.ext (Tot1.ext (fun _ _ _ ↦ rfl) fun T ↦ connForm_smul r f _ _)
def ptCmp : FirstDeRham s →ₗ[R] Hyp1 F :=
  Submodule.mapQ _ _ (ptZZ x hx hc) (by
    rintro _ ⟨g, rfl⟩
    exact ⟨fun T ↦ g (Thick.triv (F.obj T) (x T) (hx T)),
      Subtype.ext (Tot1.ext (fun _ _ _ ↦ rfl) fun T ↦ (crystallineConnectionForm_coboundaryZero g _ _).symm)⟩)
end Points
def Sec (_s : X ⟶ Sp R) (U : X.Opens) : Type := GlobalTheory.SectionsCommRing.Sections _s U
def secMap (s : X ⟶ Sp R) (U : X.Opens) : CommRingCat.of R ⟶ Γ(X, U) :=
  CommRingCat.ofHom (GlobalTheory.SectionsCommRing.structureHom s U)
instance (s : X ⟶ Sp R) (U : X.Opens) : CommRing (Sec s U) := inferInstanceAs (CommRing Γ(X, U))
instance (s : X ⟶ Sp R) (U : X.Opens) : Algebra R (Sec s U) :=
  RingHom.toAlgebra (S := Sec s U) (secMap s U).hom
def Sec.res (s : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) : Sec s U →ₐ[R] Sec s V :=
  GlobalTheory.SectionsCommRing.Sections.restrict s h
theorem Sec.res_res (s : X ⟶ Sp R) {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (c : Sec s U) :
    Sec.res s (h'.trans h) c = Sec.res s h' (Sec.res s h c) :=
  congrArg (fun q ↦ q.hom c) (X.presheaf.map_comp (homOfLE h).op (homOfLE h').op)
abbrev AffOp (X : Scheme.{0}) : Type := (X.affineOpens)ᵒᵖ
@[reducible] def OAff (s : X ⟶ Sp R) : AffOp X ⥤ CommAlgCat.{0} R where
  obj U := CommAlgCat.of R (Sec s U.unop.1)
  map a := CommAlgCat.ofHom (Sec.res s (leOfHom a.unop))
  map_id U := CommAlgCat.hom_ext (AlgHom.ext fun b ↦
    congrArg (fun q ↦ q.hom b) (X.presheaf.map_id (op U.unop.1)))
  map_comp a b := CommAlgCat.hom_ext (AlgHom.ext fun c ↦
    Sec.res_res s (leOfHom a.unop) (leOfHom b.unop) c)
abbrev OmU (s : X ⟶ Sp R) (U : X.Opens) (j : ℕ) : Type := Om R (Sec s U) j
abbrev HH1 (s : X ⟶ Sp R) : Type := Hyp1 (OAff s)
abbrev HH2 (s : X ⟶ Sp R) : Type := Hyp2 (OAff s)
abbrev cupHH (s : X ⟶ Sp R) : HH1 s →ₗ[R] HH1 s →ₗ[R] HH2 s := cupHyp (OAff s)
abbrev HO1 (s : X ⟶ Sp R) : Type := CatCoh.H1 (OAff s)
abbrev toHO1 (s : X ⟶ Sp R) : HH1 s →ₗ[R] HO1 s := toO (OAff s)
abbrev CechHodgeFiltration (s : X ⟶ Sp R) : Submodule R (HH1 s) := Fil1 (OAff s)
abbrev GlobForm (s : X ⟶ Sp R) : Submodule R (A0 (OAff s)) := Glob1 (OAff s)
abbrev ClosedForm (s : X ⟶ Sp R) : Submodule R (GlobForm s) := Closed1 (OAff s)
abbrev clForm (s : X ⟶ Sp R) : ClosedForm s →ₗ[R] HH1 s := ofForm (OAff s)
def affPt (s : X ⟶ Sp R) (U : X.affineOpens) : Sp (Sec s U.1) ⟶ X := U.2.fromSpec
theorem affPt_w (s : X ⟶ Sp R) (U : X.affineOpens) :
    affPt s U ≫ s = spMap (algebraMap R (Sec s U.1)) := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top _) U.2 le_top
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at this
  exact this.symm
theorem affPt_res (s : X ⟶ Sp R) {U V : X.affineOpens} (h : V.1 ≤ U.1) :
    spMap (Sec.res s h : Sec s U.1 →+* Sec s V.1) ≫ affPt s U = affPt s V :=
  IsAffineOpen.map_fromSpec U.2 V.2 (homOfLE h).op
def cmpZZ (s : X ⟶ Sp R) : Z1 (O (dp0 R) s) →ₗ[R] cechDeRhamTotalCocyclesOne (OAff s) :=
  ptZZ (F := OAff s) (fun U ↦ affPt s U.unop) (fun U ↦ affPt_w s U.unop)
    fun _ _ a ↦ affPt_res s (leOfHom a.unop)
def cmp1 (s : X ⟶ Sp R) : FirstDeRham s →ₗ[R] HH1 s :=
  ptCmp (F := OAff s) (fun U ↦ affPt s U.unop) (fun U ↦ affPt_w s U.unop)
    fun _ _ a ↦ affPt_res s (leOfHom a.unop)
def cmpO (s : X ⟶ Sp R) : FirstCohomStructureSheaf s →ₗ[R] HO1 s :=
  (ptCoef (F := OAff s) (fun U ↦ affPt s U.unop) (fun U ↦ affPt_w s U.unop)
    fun _ _ a ↦ affPt_res s (leOfHom a.unop)).pull1
def cmpForm (s : X ⟶ Sp R) : Form s →ₗ[R] ClosedForm s where
  toFun f := ⟨⟨(cmpZZ s f.1).1.2, fun U V a ↦ by
    rw [cechDeRhamTotalCocyclesOne.conn _ a, show (cmpZZ s f.1).1.1 U V a = 0 from f.2 _ rfl rfl, map_zero, add_zero]⟩,
    cechDeRhamTotalCocyclesOne.closed (cmpZZ s f.1)⟩
  map_add' f g := Subtype.ext (Subtype.ext (funext fun _ ↦ connForm_add f.1 g.1 _ _))
  map_smul' r f := Subtype.ext (Subtype.ext (funext fun _ ↦ connForm_smul r f.1 _ _))
theorem cmpForm_apply (s : X ⟶ Sp R) (f : Form s) (U : AffOp X) :
    (cmpForm s f).1.1 U = connForm f.1 (affPt s U.unop) (affPt_w s U.unop) := rfl
theorem comparison_formClass (s : X ⟶ Sp R) (f : Form s) : cmp1 s (Form.cl s f) = clForm s (cmpForm s f) :=
  congrArg (Hyp1.mk _) (Subtype.ext (Tot1.ext (fun _ _ _ ↦ f.2 _ rfl rfl) fun _ ↦ rfl))
section Pull
abbrev Pair (φ : X' ⟶ X) : Type :=
  {p : X'.affineOpens × X.affineOpens // p.1.1 ≤ φ ⁻¹ᵁ p.2.1}
theorem Pair.le_fst {φ : X' ⟶ X} {p q : Pair φ} (h : p ≤ q) : p.1.1 ≤ q.1.1 :=
  (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).1
theorem Pair.le_snd {φ : X' ⟶ X} {p q : Pair φ} (h : p ≤ q) : p.1.2 ≤ q.1.2 :=
  (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).2
def pairFst (φ : X' ⟶ X) : (Pair φ)ᵒᵖ ⥤ AffOp X' :=
  (Monotone.functor (f := fun p : Pair φ ↦ p.1.1) fun _ _ h ↦ Pair.le_fst h).op
def pairSnd (φ : X' ⟶ X) : (Pair φ)ᵒᵖ ⥤ AffOp X :=
  (Monotone.functor (f := fun p : Pair φ ↦ p.1.2) fun _ _ h ↦ Pair.le_snd h).op
abbrev OPair (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : (Pair φ)ᵒᵖ ⥤ CommAlgCat.{0} R' := pairFst φ ⋙ OAff s'
def pairRes (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : CoefMap (RingHom.id R') (OAff s') (OPair φ s') :=
  CoefMap.restrict _ _
variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X}
def secPull (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (p : Pair φ) : Sec s p.1.2.1 →+* Sec s' p.1.1.1 :=
  (φ.appLE _ _ p.2).hom
theorem secPull_affPt (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (p : Pair φ) :
    spMap (secPull s s' p) ≫ affPt s p.1.2 = affPt s' p.1.1 ≫ φ :=
  IsAffineOpen.SpecMap_appLE_fromSpec φ p.1.2.2 p.1.1.2 p.2
theorem semiHom_secPull (h : φ ≫ s = s' ≫ spMap σ) (p : Pair φ) : SemiHom σ (secPull s s' p) := by
  have e : spMap ((secPull s s' p).comp (algebraMap R _)) = spMap ((algebraMap R' _).comp σ) := by
    rw [spMap_comp, spMap_comp, ← affPt_w, ← affPt_w, ← Category.assoc, secPull_affPt,
      Category.assoc, h, Category.assoc]
  intro r b
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  exact congrArg (· * _) (congrArg (fun q ↦ q.hom r) (Spec.map_injective e))
def pairPull (h : φ ≫ s = s' ≫ spMap σ) : CoefMap σ (OAff s) (OPair φ s') where
  G := pairSnd φ
  α p := secPull s s' p.unop
  naturality {p q} a b :=
    (congrArg (fun t ↦ t.hom b) (φ.map_appLE q.unop.2 (homOfLE (Pair.le_snd (leOfHom a.unop))).op)).trans
      (congrArg (fun t ↦ t.hom b) (φ.appLE_map p.unop.2 (homOfLE (Pair.le_fst (leOfHom a.unop))).op)).symm
  smul p := semiHom_secPull h p.unop
variable (h : φ ≫ s = s' ≫ spMap σ)
def IsPull1 (c : HH1 s) (c' : HH1 s') : Prop := pullHyp1 (pairPull h) c = pullHyp1 (pairRes φ s') c'
def IsPull2 (c : HH2 s) (c' : HH2 s') : Prop := pullHyp2 (pairPull h) c = pullHyp2 (pairRes φ s') c'
def IsPullO (c : HO1 s) (c' : HO1 s') : Prop := (pairPull h).pull1 c = (pairRes φ s').pull1 c'
def IsPullForm (ω : GlobForm s) (ω' : GlobForm s') : Prop :=
  pullGlob1 (pairPull h) ω = pullGlob1 (pairRes φ s') ω'
variable {h}
theorem IsPullForm.cl {ω : ClosedForm s} {ω' : ClosedForm s'} (e : IsPullForm h ω.1 ω'.1) :
    IsPull1 h (clForm s ω) (clForm s' ω') := by
  unfold IsPull1
  rw [pullHyp1_ofForm, pullHyp1_ofForm]
  exact congrArg _ (Subtype.ext e)
def pairIdTrans (X : Scheme.{0}) : pairSnd (𝟙 X) ⟶ pairFst (𝟙 X) where
  app p := (homOfLE (show p.unop.1.1 ≤ p.unop.1.2 from p.unop.2)).op
end Pull
section Affine
variable (R) (B : Type) [CommRing B] [Algebra R B]
abbrev algStr : Sp B ⟶ Sp R := spMap (algebraMap R B)
theorem affPt_eq (U : (Sp B).affineOpens) :
    affPt (algStr R B) U = Spec.map (secMap (𝟙 (Sp B)) U.1) :=
  (Category.comp_id _).symm.trans (affPt_w (𝟙 (Sp B)) U)
def toSec (U : (Sp B).affineOpens) : B →ₐ[R] Sec (algStr R B) U.1 :=
  { (secMap (𝟙 (Sp B)) U.1).hom with
    commutes' := fun r ↦ by
      have e : Spec.map (CommRingCat.ofHom (algebraMap R B) ≫ secMap (𝟙 (Sp B)) U.1) =
          spMap (algebraMap R (Sec (algStr R B) U.1)) := (Spec.map_comp _ _).trans
        ((congrArg (· ≫ algStr R B) (affPt_eq R B U)).symm.trans (affPt_w _ U))
      exact congrArg (fun q ↦ q.hom r) (Spec.map_injective e) }
theorem res_toSec ⦃U V : AffOp (Sp B)⦄ (a : U ⟶ V) (b : B) :
    mp (OAff (algStr R B)) a (toSec R B U.unop b) = toSec R B V.unop b :=
  (Sec.res (𝟙 (Sp B)) (leOfHom a.unop)).commutes b
def affEquiv : AlgebraFirstDeRham R B ≃ₗ[R] HH1 (algStr R B) :=
  LinearEquiv.ofBijective (coneMap (F := OAff (algStr R B)) (fun U ↦ toSec R B U.unop) (res_toSec R B))
    (coneMap_bijective _ _ (T₀ := op ⟨⊤, isAffineOpen_top _⟩)
      (Limits.IsInitial.ofUniqueHom (fun U ↦ (homOfLE (show U.unop ≤ ⟨⊤, isAffineOpen_top _⟩ from
        le_top (a := U.unop.1))).op) fun _ _ ↦ rfl)
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv))
theorem affEquiv_mk (ω : LinearMap.ker (dOne R B)) : affEquiv R B (Submodule.Quotient.mk ω) =
    clForm _ (coneForm (F := OAff (algStr R B)) (fun U ↦ toSec R B U.unop) (res_toSec R B) ω) := rfl
open Polynomial
theorem dOne_line (ω : Ω[R[X]⁄R]) : dOne R R[X] ω = 0 := by
  induction ω using ind1 with
  | h b c =>
    rw [dOne_smul_D, polynomial_D_apply R b, polynomial_D_apply R c]
    simp
  | h0 => simp
  | ha x y hx hy => rw [map_add, hx, hy, add_zero]
def lineEquiv : (Ω[R[X]⁄R] ⧸ LinearMap.range (D R R[X]).toLinearMap) ≃ₗ[R] HH1 (lineStr R) :=
  (Submodule.Quotient.equiv (exact1 R R[X]) _
    (LinearEquiv.ofTop _ (eq_top_iff.2 fun ω _ ↦ dOne_line R ω)) (by
      ext ω
      exact ⟨fun ⟨x, hx, e⟩ ↦ e ▸ hx, fun hω ↦ ⟨⟨ω, dOne_line R ω⟩, hω, rfl⟩⟩)).symm.trans
    (affEquiv R R[X])
theorem lineEquiv_mk (ω : Ω[R[X]⁄R]) : lineEquiv R (Submodule.Quotient.mk ω) =
    affEquiv R R[X] (Submodule.Quotient.mk ⟨ω, dOne_line R ω⟩) := rfl
attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler in
variable {R B} in

theorem connForm_tdt (x : Sp B ⟶ Sp R[X]) (hx : x ≫ lineStr R = spMap (algebraMap R B)) :
    connForm (tdt R).1 x hx =
      (Spec.preimage x).hom Polynomial.X • D R B ((Spec.preimage x).hom Polynomial.X) := by
  have c0 : coordLift (Thick.triv B x hx) = (Spec.preimage x).hom Polynomial.X :=
    π_coordLift (Thick.triv B x hx)
  have c1 : (coordLift ((diagExt R B).thick x hx)).fst = (Spec.preimage x).hom Polynomial.X :=
    π_coordLift ((diagExt R B).thick x hx)
  change TrivSqZeroExt.snd (R := B) ((TrivSqZeroExt.inl (coordLift (Thick.triv B x hx)) *
    (_ - TrivSqZeroExt.inl (coordLift (Thick.triv B x hx))) + (divided₂ (diagExt R B).sq).dpow 2 _) -
    (diagSec R B (coordLift (Thick.triv B x hx)) * (_ - diagSec R B (coordLift (Thick.triv B x hx))) +
      (divided₂ (diagExt R B).sq).dpow 2 _)) = _
  rw [squareZeroDividedPowers_dpow _ le_rfl, squareZeroDividedPowers_dpow _ le_rfl, c0]
  have key : ∀ (c : TrivSqZeroExt B Ω[B⁄R]) (b : B), c.fst = b →
      TrivSqZeroExt.snd ((TrivSqZeroExt.inl b * (c - TrivSqZeroExt.inl b) + 0) -
        (diagSec R B b * (c - diagSec R B b) + 0)) = b • D R B b := by
    intro c b h
    simp [h, smul_sub]
  exact key _ _ c1
theorem comparison_tdt_line : cmp1 (lineStr R) (Form.cl _ (tdt R)) =
    lineEquiv R (Submodule.Quotient.mk ((Polynomial.X : R[X]) • D R R[X] Polynomial.X)) := by
  rw [comparison_formClass, lineEquiv_mk, affEquiv_mk]
  refine congrArg _ (Subtype.ext (Subtype.ext (funext fun U ↦ ?_)))
  rw [cmpForm_apply, connForm_tdt, coneForm_apply, SemiHom.oneFormMap_smul_semilinear, SemiHom.m1_D]
  have : Spec.preimage (affPt (lineStr R) U.unop) = secMap (𝟙 (Sp R[X])) U.unop.1 := by
    rw [affPt_eq]; exact Spec.preimage_map _
  rw [this]; rfl
example (r : R) (h : r * 2 = 1) : cmp1 (lineStr R) (Form.cl _ (tdt R)) = 0 := by
  rw [comparison_tdt_line, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
  refine ⟨r • (Polynomial.X * Polynomial.X), ?_⟩
  rw [map_smul, Derivation.coeFn_coe, Derivation.leibniz, ← two_smul R, smul_smul, h, one_smul]
end Affine
end GlobalTheory.CechDR


