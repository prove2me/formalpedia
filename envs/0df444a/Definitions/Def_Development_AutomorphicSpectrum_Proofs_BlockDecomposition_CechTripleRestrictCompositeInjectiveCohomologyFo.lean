-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechTripleRestrictCompositeInjectiveCohomologyFo
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechTripleRestrictCompositeInjectiveCohomologyFo
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:55.264773+00:00
-- url     : https://prove2.me/theorems/e2c5008b-43a3-4484-986c-0e061e3e5afc
-- title:
--   Cech Triple Restrict Composite Injective Cohomology Fo
-- statement:
--   Definitions and structural lemmas for Cech Triple Restrict Composite Injective Cohomology Fo, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechTripleRestrictCompositeInjectiveCohomologyFo.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Glue_mono
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Sep_mono
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Van1_mono
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Van2_mono
import Theorems.Thm_GlobalTheory_CatCoh_Desc_VandermondeTwoBasis_CovBy_mono
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_smul
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge Limits
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.CompanionTheory.HopfSys
variable {R : Type} [CommRing R]
def secA {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ : X' ⟶ X}
    (h : φ ≫ s = s' ≫ spMap (RingHom.id R)) (p : Pair φ) : Sec s p.1.2.1 →ₐ[R] Sec s' p.1.1.1 :=
  { secPull s s' p with commutes' := (semiHom_secPull h p).map_algebraMap }
theorem kunneth_open (A B : Over (Sp R)) (U : A.left.affineOpens) (V : B.left.affineOpens) :
    ∃ hV : IsAffineOpen ((fst A B).left ⁻¹ᵁ U.1 ⊓ (snd A B).left ⁻¹ᵁ V.1),
      Function.Bijective (Algebra.TensorProduct.lift
        (secA (wOver (fst A B)) ⟨(⟨_, hV⟩, U), inf_le_left⟩)
        (secA (wOver (snd A B)) ⟨(⟨_, hV⟩, V), inf_le_right⟩) (fun _ _ ↦ Commute.all _ _)) := by
  let Sa := Sec A.hom U.1
  let Sb := Sec B.hom V.1
  let iU := affPt A.hom U
  let iV := affPt B.hom V
  have eU : iU ≫ A.hom = spMap (algebraMap R Sa) := affPt_w _ _
  have eV : iV ≫ B.hom = spMap (algebraMap R Sb) := affPt_w _ _
  let ma : pullback (spMap (algebraMap R Sa)) (spMap (algebraMap R Sb)) ⟶ pullback A.hom B.hom :=
    pullback.map _ _ _ _ iU iV (𝟙 _) (by rw [Category.comp_id, eU]) (by rw [Category.comp_id, eV])
  haveI hma : IsOpenImmersion ma :=
    MorphismProperty.pullback_map (P := @IsOpenImmersion) (f := spMap (algebraMap R Sa)) (g := spMap (algebraMap R Sb))
      (IsAffineOpen.isOpenImmersion_fromSpec U.2) (IsAffineOpen.isOpenImmersion_fromSpec V.2) eU.symm eV.symm
  let j : Spec (CommRingCat.of (Sa ⊗[R] Sb)) ⟶ pullback A.hom B.hom := (pullbackSpecIso R Sa Sb).inv ≫ ma
  have hj : j.opensRange = (fst A B).left ⁻¹ᵁ U.1 ⊓ (snd A B).left ⁻¹ᵁ V.1 := by
    apply TopologicalSpace.Opens.ext
    have e1 : Set.range j = Set.range ma := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨(pullbackSpecIso R Sa Sb).inv y, (Scheme.Hom.comp_apply _ _ y).symm⟩
      · rintro ⟨y, rfl⟩
        refine ⟨(pullbackSpecIso R Sa Sb).hom y, ?_⟩
        simp [j, ← Scheme.Hom.comp_apply]
    have e2 := Scheme.Pullback.range_map (spMap (algebraMap R Sa)) (spMap (algebraMap R Sb)) A.hom B.hom iU iV (𝟙 _)
      (by rw [Category.comp_id, eU]) (by rw [Category.comp_id, eV])
    simp only [Scheme.Hom.coe_opensRange, e1]
    refine e2.trans ?_
    rw [show Set.range iU = (U.1 : Set A.left) from U.2.range_fromSpec, show Set.range iV = (V.1 : Set B.left) from V.2.range_fromSpec]
    rfl
  have hV : IsAffineOpen ((fst A B).left ⁻¹ᵁ U.1 ⊓ (snd A B).left ⁻¹ᵁ V.1) := hj ▸ isAffineOpen_opensRange j
  refine ⟨hV, ?_⟩
  let κ : Sa ⊗[R] Sb →ₐ[R] Sec (A ⊗ B).hom ((fst A B).left ⁻¹ᵁ U.1 ⊓ (snd A B).left ⁻¹ᵁ V.1) := Algebra.TensorProduct.lift
        (secA (wOver (fst A B)) ⟨(⟨_, hV⟩, U), inf_le_left⟩)
        (secA (wOver (snd A B)) ⟨(⟨_, hV⟩, V), inf_le_right⟩) (fun _ _ ↦ Commute.all _ _)
  have hk : spMap κ.toRingHom ≫ j = hV.fromSpec := by
    apply pullback.hom_ext
    · have s1 := secPull_affPt (φ := (fst A B).left) A.hom (A ⊗ B).hom ⟨(⟨_, hV⟩, U), inf_le_left⟩
      have l : κ.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom = secPull A.hom (A ⊗ B).hom ⟨(⟨_, hV⟩, U), inf_le_left⟩ :=
        RingHom.ext fun x ↦ by
          change κ (x ⊗ₜ 1) = _
          rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]; rfl
      have m1 : ma ≫ pullback.fst A.hom B.hom = pullback.fst _ _ ≫ iU := pullback.lift_fst _ _ _
      rw [Category.assoc, Category.assoc, m1, ← Category.assoc (pullbackSpecIso R Sa Sb).inv, pullbackSpecIso_inv_fst]
      have m2 : spMap κ.toRingHom ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) =
          spMap (secPull A.hom (A ⊗ B).hom ⟨(⟨_, hV⟩, U), inf_le_left⟩) := by
        rw [← l, spMap_comp]
      rw [← Category.assoc, m2]
      exact s1
    · have s1 := secPull_affPt (φ := (snd A B).left) B.hom (A ⊗ B).hom ⟨(⟨_, hV⟩, V), inf_le_right⟩
      have l : κ.toRingHom.comp (Algebra.TensorProduct.includeRight : Sb →ₐ[R] Sa ⊗[R] Sb).toRingHom = secPull B.hom (A ⊗ B).hom ⟨(⟨_, hV⟩, V), inf_le_right⟩ :=
        RingHom.ext fun x ↦ by
          change κ (1 ⊗ₜ x) = _
          rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]; rfl
      have m1 : ma ≫ pullback.snd A.hom B.hom = pullback.snd _ _ ≫ iV := pullback.lift_snd _ _ _
      rw [Category.assoc, Category.assoc, m1, ← Category.assoc (pullbackSpecIso R Sa Sb).inv, pullbackSpecIso_inv_snd]
      have m2 : spMap κ.toRingHom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : Sb →ₐ[R] Sa ⊗[R] Sb).toRingHom) =
          spMap (secPull B.hom (A ⊗ B).hom ⟨(⟨_, hV⟩, V), inf_le_right⟩) := by
        rw [← l, spMap_comp]
      rw [← Category.assoc]
      exact (congrArg (· ≫ iV) m2).trans s1
  haveI hj1 : IsOpenImmersion j := inferInstance
  haveI h2 : IsOpenImmersion (spMap κ.toRingHom ≫ j) := hk ▸ IsAffineOpen.isOpenImmersion_fromSpec hV
  haveI h3 : IsOpenImmersion (spMap κ.toRingHom) := IsOpenImmersion.of_comp _ j
  have hs : Function.Surjective (spMap κ.toRingHom) := by
    intro t
    have ht : j t ∈ Set.range hV.fromSpec := by
      rw [hV.range_fromSpec, ← hj]; exact ⟨t, rfl⟩
    obtain ⟨y, hy⟩ := ht
    refine ⟨y, j.injective ?_⟩
    rw [← hy, ← hk]; rfl
  haveI : Epi (spMap κ.toRingHom).base := (TopCat.epi_iff_surjective _).2 hs
  haveI hi : IsIso (spMap κ.toRingHom) := IsOpenImmersion.isIso (spMap κ.toRingHom)
  haveI : IsIso (CommRingCat.ofHom κ.toRingHom) := by
    let g := Spec.preimage (inv (Spec.map (CommRingCat.ofHom κ.toRingHom)))
    refine ⟨g, Spec.map_injective ?_, Spec.map_injective ?_⟩ <;> simp [g]
  exact ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom κ.toRingHom)
end GlobalTheory.CompanionTheory.HopfSys
namespace GlobalTheory.CompanionTheory.HopfSys
section Comp
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {φ : X' ⟶ X} {ψ : X'' ⟶ X'}
end Comp
section Over
variable {R : Type} [CommRing R]
variable (A : Over (Sp R)) [GrpObj A]
end Over
end GlobalTheory.CompanionTheory.HopfSys
namespace GlobalTheory.CompanionTheory.HopfSys
section Lift
variable {R : Type} [CommRing R] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ : X' ⟶ X}
  {C D : Type} [Category.{0} C] [Category.{0} D]
def pairFn (φ : X' ⟶ X) (u : C ⥤ AffOp X) (t : D ⥤ C) (fb : D ⥤ AffOp X')
    (hle : ∀ d, (fb.obj d).unop.1 ≤ φ ⁻¹ᵁ (u.obj (t.obj d)).unop.1) : D ⥤ (Pair φ)ᵒᵖ where
  obj d := op ⟨((fb.obj d).unop, (u.obj (t.obj d)).unop), hle d⟩
  map {d d'} a := (homOfLE (show (⟨((fb.obj d').unop, (u.obj (t.obj d')).unop), hle d'⟩ : Pair φ) ≤
    ⟨((fb.obj d).unop, (u.obj (t.obj d)).unop), hle d⟩ from
    Prod.le_def.2 ⟨leOfHom (fb.map a).unop, leOfHom (u.map (t.map a)).unop⟩)).op
  map_id _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  map_comp _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
def liftAlong (h : φ ≫ s = s' ≫ spMap (RingHom.id R)) (u : C ⥤ AffOp X) (t : D ⥤ C) (fb : D ⥤ AffOp X')
    (hle : ∀ d, (fb.obj d).unop.1 ≤ φ ⁻¹ᵁ (u.obj (t.obj d)).unop.1) :
    CoefMap (RingHom.id R) (u ⋙ OAff s) (fb ⋙ OAff s') where
  G := t
  α d := (pairPull h).α ((pairFn φ u t fb hle).obj d)
  naturality a b := (pairPull h).naturality ((pairFn φ u t fb hle).map a) b
  smul d := (pairPull h).smul ((pairFn φ u t fb hle).obj d)
end Lift
end GlobalTheory.CompanionTheory.HopfSys
namespace GlobalTheory.CompanionTheory.HopfSys
section Aff
theorem aff_inf_preimage {X Y T : Scheme.{0}} (s : Y ⟶ T) [IsSeparated s] [IsAffine T] (f : X ⟶ Y) {V : X.Opens}
    (hV : IsAffineOpen V) {U : Y.Opens} (hU : IsAffineOpen U) : IsAffineOpen (V ⊓ f ⁻¹ᵁ U) := by
  haveI : IsAffine V := hV
  haveI : IsAffineHom (V.ι ≫ f) := by
    haveI : IsAffineHom ((V.ι ≫ f) ≫ s) := inferInstance
    exact IsAffineHom.of_comp _ s
  have := (hU.preimage (V.ι ≫ f)).image_of_isOpenImmersion V.ι
  rwa [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] at this
end Aff
end GlobalTheory.CompanionTheory.HopfSys
namespace GlobalTheory.CompanionTheory.HopfSys
section Main
variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {P : Type} [SemilatticeInf P] (S : Sys A.left P)
def Vop (a b : P) : (A ⊗ A).left.Opens := (fst A A).left ⁻¹ᵁ (S.u a).1 ⊓ (snd A A).left ⁻¹ᵁ (S.u b).1
def Wop (a b c : P) : (A ⊗ A).left.Opens := Vop A S a b ⊓ μ[A].left ⁻¹ᵁ (S.u c).1
theorem Vop_aff (a b : P) : IsAffineOpen (Vop A S a b) := (kunneth_open A A (S.u a) (S.u b)).choose
theorem Wop_aff [IsSeparated A.hom] (a b c : P) : IsAffineOpen (Wop A S a b c) :=
  aff_inf_preimage A.hom _ (Vop_aff A S a b) (S.u c).2
theorem Wop_mono {a a' b b' c c' : P} (ha : a' ≤ a) (hb : b' ≤ b) (hc : c' ≤ c) :
    Wop A S a' b' c' ≤ Wop A S a b c := fun _ hx ↦
  ⟨⟨S.mono ha hx.1.1, S.mono hb hx.1.2⟩, S.mono hc hx.2⟩
variable [IsSeparated A.hom]
def wFn : (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ ⥤ AffOp (A ⊗ A).left where
  obj T := op ⟨Wop A S T.1.1.unop T.1.2.unop T.2.unop, Wop_aff A S _ _ _⟩
  map {T T'} f := (homOfLE (show (⟨Wop A S T'.1.1.unop T'.1.2.unop T'.2.unop, Wop_aff A S _ _ _⟩ :
      (A ⊗ A).left.affineOpens) ≤ ⟨Wop A S T.1.1.unop T.1.2.unop T.2.unop, Wop_aff A S _ _ _⟩ from
    Wop_mono A S (leOfHom f.1.1.unop) (leOfHom f.1.2.unop) (leOfHom f.2.unop))).op
  map_id _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  map_comp _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
abbrev GG : (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ ⥤ CommAlgCat.{0} R := wFn A S ⋙ OAff (A ⊗ A).hom
def pMap : CoefMap (RingHom.id R) (OSys A.hom S) (GG A S) :=
  liftAlong (wOver (fst A A)) S.fn (CategoryTheory.Prod.fst _ _ ⋙ CategoryTheory.Prod.fst _ _) (wFn A S)
    fun _ _ hx ↦ hx.1.1
def qMap : CoefMap (RingHom.id R) (OSys A.hom S) (GG A S) :=
  liftAlong (wOver (snd A A)) S.fn (CategoryTheory.Prod.fst _ _ ⋙ CategoryTheory.Prod.snd _ _) (wFn A S)
    fun _ _ hx ↦ hx.1.2
def mMap : CoefMap (RingHom.id R) (OSys A.hom S) (GG A S) :=
  liftAlong (wOver μ[A]) S.fn (CategoryTheory.Prod.snd _ _) (wFn A S) fun _ _ hx ↦ hx.2
end Main
section
variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
  {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}
def toAlg (m : CoefMap (RingHom.id R) F G) (T : D) : F.obj (m.G.obj T) →ₐ[R] G.obj T :=
  { m.α T with
    commutes' := fun r ↦ by
      change m.α T _ = _
      rw [Algebra.algebraMap_eq_smul_one, m.smul, map_one, ← Algebra.algebraMap_eq_smul_one]
      rfl }
end
section Main2
variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {P : Type} [SemilatticeInf P] (S : Sys A.left P)
  [IsSeparated A.hom]
def pA (T : (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ) : (OSys A.hom S).obj T.1.1 →ₐ[R] (GG A S).obj T := toAlg (pMap A S) T
def qA (T : (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ) : (OSys A.hom S).obj T.1.2 →ₐ[R] (GG A S).obj T := toAlg (qMap A S) T
def pjAlg (T : (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ) : (box (OSys A.hom S)).obj T.1 →ₐ[R] (GG A S).obj T :=
  Algebra.TensorProduct.lift (pA A S T) (qA A S T) fun _ _ ↦ Commute.all _ _
theorem pjAlg_tmul (T : (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ) (x : (OSys A.hom S).obj T.1.1) (y : (OSys A.hom S).obj T.1.2) :
    pjAlg A S T (x ⊗ₜ[R] y) = pA A S T x * qA A S T y :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _
def pj : Proj (box (OSys A.hom S)) (GG A S) where
  α T := pjAlg A S T
  naturality {T T'} φ b := by
    have e : (pjAlg A S T').comp (mp (box (OSys A.hom S)) φ.1) = (mp (GG A S) φ).comp (pjAlg A S T) :=
      Algebra.TensorProduct.ext' fun x y ↦ by
        change pjAlg A S T' (mp (OSys A.hom S) φ.1.1 x ⊗ₜ[R] mp (OSys A.hom S) φ.1.2 y) =
          mp (GG A S) φ (pjAlg A S T (x ⊗ₜ[R] y))
        rw [pjAlg_tmul, pjAlg_tmul, map_mul]
        exact congrArg₂ (· * ·) ((pMap A S).naturality φ x) ((qMap A S).naturality φ y)
    exact congrArg (fun t ↦ t b) e
end Main2
end GlobalTheory.CompanionTheory.HopfSys
namespace GlobalTheory.CompanionTheory.HopfSys
section Main3
variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {P : Type} [SemilatticeInf P] (S : Sys A.left P)
def kap (a b : P) : Sec A.hom (S.u a).1 ⊗[R] Sec A.hom (S.u b).1 →ₐ[R] Sec (A ⊗ A).hom (Vop A S a b) :=
  Algebra.TensorProduct.lift (secA (wOver (fst A A)) ⟨(⟨_, Vop_aff A S a b⟩, S.u a), inf_le_left⟩)
    (secA (wOver (snd A A)) ⟨(⟨_, Vop_aff A S a b⟩, S.u b), inf_le_right⟩) fun _ _ ↦ Commute.all _ _
variable [IsSeparated A.hom]
end Main3
end GlobalTheory.CompanionTheory.HopfSys
namespace GlobalTheory.CompanionTheory.HopfSys
section AutomorphyRankFourMain
variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {P : Type} [SemilatticeInf P] (S : Sys A.left P)
  [IsSeparated A.hom]
end AutomorphyRankFourMain
end GlobalTheory.CompanionTheory.HopfSys
namespace GlobalTheory.CompanionTheory.HopfSys
section Main5
variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {P : Type} [SemilatticeInf P] (S : Sys A.left P)
  [IsSeparated A.hom]
abbrev iota : A ⟶ A ⊗ A := lift (1 : A ⟶ A) (𝟙 A)
def tK (a₀ : P) : Pᵒᵖ ⥤ (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ where
  obj b := ((op a₀, b), b)
  map f := ((𝟙 _, f), f)
theorem iota_fst : (iota A).left ≫ (fst A A).left = A.hom ≫ η[A].left :=
  congrArg (fun f ↦ f.left) (lift_fst (1 : A ⟶ A) (𝟙 A))
theorem iota_snd : (iota A).left ≫ (snd A A).left = 𝟙 _ :=
  congrArg (fun f ↦ f.left) (lift_snd (1 : A ⟶ A) (𝟙 A))
theorem iota_mul : (iota A).left ≫ μ[A].left = 𝟙 _ :=
  congrArg (fun f ↦ f.left) ((Hom.mul_def (1 : A ⟶ A) (𝟙 A)).symm.trans (_root_.one_mul (𝟙 A)))
variable {A S}
theorem kle {a₀ : P} (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) (b : Pᵒᵖ) :
    (S.fn.obj b).unop.1 ≤ (iota A).left ⁻¹ᵁ ((wFn A S).obj ((tK a₀).obj b)).unop.1 := by
  intro x hx
  have h1 : (fst A A).left ((iota A).left x) ∈ (S.u a₀).1 := by
    have : (fst A A).left ((iota A).left x) = η[A].left (A.hom x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, iota_fst]
    rw [this]
    have h2 : A.hom x ∈ η[A].left ⁻¹ᵁ (S.u a₀).1 := by rw [ha]; trivial
    exact h2
  have h2 : (snd A A).left ((iota A).left x) = x := by
    rw [← Scheme.Hom.comp_apply, iota_snd]; rfl
  have h3 : μ[A].left ((iota A).left x) = x := by
    rw [← Scheme.Hom.comp_apply, iota_mul]; rfl
  refine ⟨⟨h1, ?_⟩, ?_⟩
  · change (snd A A).left ((iota A).left x) ∈ (S.u b.unop).1
    rw [h2]; exact hx
  · change μ[A].left ((iota A).left x) ∈ (S.u b.unop).1
    rw [h3]; exact hx
def kMap {a₀ : P} (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) : CoefMap (RingHom.id R) (GG A S) (OSys A.hom S) :=
  liftAlong (wOver (iota A)) (wFn A S) (tK a₀) S.fn (kle ha)
end Main5
end GlobalTheory.CompanionTheory.HopfSys
namespace GlobalTheory.CompanionTheory.HopfSys
section Main6
variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {P : Type} [SemilatticeInf P] {S : Sys A.left P}
  [IsSeparated A.hom] {a₀ : P}
theorem unit_isAffine : IsAffine (𝟙_ (Over (Sp R))).left := inferInstanceAs (IsAffine (Sp R))
attribute [local instance] unit_isAffine
theorem unit_bijective (R : Type) [CommRing R] : Function.Bijective (algebraMap R (Sec (𝟙_ (Over (Sp R))).hom ⊤)) :=
  ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv
def ptPair (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) : Pair η[A].left := ⟨(⟨⊤, isAffineOpen_top _⟩, S.u a₀), ha.ge⟩
def epsA (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) : (OSys A.hom S).obj (op a₀) →ₐ[R] R :=
  (AlgEquiv.ofBijective (Algebra.ofId R (Sec (𝟙_ (Over (Sp R))).hom ⊤)) (unit_bijective R)).symm.toAlgHom.comp
    (secA (wOver η[A]) (ptPair ha) : Sec A.hom (S.u a₀).1 →ₐ[R] Sec (𝟙_ (Over (Sp R))).hom ⊤)
end Main6
end GlobalTheory.CompanionTheory.HopfSys


