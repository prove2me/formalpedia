-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleHenselianComponentGerms
-- name    : AlgebraicGeometry_EtaleHenselianComponentGerms
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-22T00:40:41.384296+00:00
-- url     : https://prove2.me/theorems/1245770e-ff83-44a9-95e6-27fcb0b3a0ce
-- title:
--   Germs on strictly henselian components
-- statement:
--   Global sections on strictly henselian schemes and evaluation on disjoint finite components.

import Definitions.Def_AlgebraicGeometry_EtaleStrictHenselianSectionGerms
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.FieldTheory.IsAlgClosed.Basic

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleNeighborhoodRestriction (along restrictionIso)
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtaleStalkPullback (stalkPullbackIso)
open PhilipponStrictHenselianEtaleCohomology (globalSectionsIsoClosedStalk)


namespace PhilipponEtaleDisjointSections

universe u

variable {X : Scheme.{u}} {I : Type u} {U : I → Scheme.{u}} (j : ∀ i, U i ⟶ X)
  [∀ i, IsOpenImmersion (j i)]

private abbrev terminal (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)

/-- Sections on an étale chart agree naturally with global sections of
the inverse image on the chart scheme. -/
def chartSectionsNatIso {V : Scheme.{u}} (p : V ⟶ X) [Etale p] :
    (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op (Scheme.Etale.mk p)) ≅
      pullbackSheaves p ⋙ globalSections V := by
  let e : (along p).obj (terminal V) ≅ Scheme.Etale.mk p :=
    MorphismProperty.Over.isoMk (Iso.refl V) rfl
  let α : (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op (Scheme.Etale.mk p)) ≅
      PhilipponEtaleNeighborhoodRestriction.restrict p ⋙ globalSections V :=
    NatIso.ofComponents (fun F => F.obj.mapIso e.op) (fun a => (a.hom.naturality e.hom.op).symm)
  exact α ≪≫ Functor.isoWhiskerRight (restrictionIso p) (globalSections V)

/-- The chart-sections comparison at a single sheaf. -/
abbrev chartSectionsIso {V : Scheme.{u}} (p : V ⟶ X) [Etale p]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) := (chartSectionsNatIso p).app F

private abbrev chart (i : I) : X.Etale := Scheme.Etale.mk (j i)

/-- The arrow from an open component to the terminal étale chart. -/
def toTerminal (i : I) : chart j i ⟶ terminal X :=
  MorphismProperty.Over.homMk (j i) (Category.comp_id _) trivial

private theorem bijective_sections (hCover : ⋃ i, Set.range (j i) = Set.univ)
    (hDisj : Pairwise fun i k => Disjoint (Set.range (j i)) (Set.range (j k)))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Function.Bijective (fun a : F.obj.obj (op (terminal X)) =>
      fun i => F.obj.map (toTerminal j i).op a) := by
  let P := F.obj ⋙ CategoryTheory.forget AddCommGrpCat
  have hP := Presheaf.isSheaf_comp_of_isSheaf X.smallEtaleTopology F.obj
    (CategoryTheory.forget AddCommGrpCat) F.property
  have hc : Sieve.ofArrows (chart j) (toTerminal j) ∈ X.smallEtaleTopology (terminal X) :=
    (Scheme.ofArrows_mem_smallEtaleTopology_iff (toTerminal j)).mpr hCover
  have hSheaf : Presieve.IsSheafFor P (.ofArrows (chart j) (toTerminal j)) :=
    (Presieve.isSheafFor_iff_generate (.ofArrows (chart j) (toTerminal j))).mpr
      ((isSheaf_iff_isSheaf_of_type _ _).mp hP _ hc)
  constructor
  · intro s t h
    apply hSheaf.isSeparatedFor.ext
    rintro _ _ ⟨i⟩
    exact congrFun h i
  · intro s
    have hCompat : Presieve.Arrows.Compatible P (toTerminal j) s := by
      intro i k W a b h
      have hh : a.left ≫ j i = b.left ≫ j k :=
        congrArg (fun t : W ⟶ terminal X => t.left) h
      by_cases he : i = k
      · subst k
        have hab : a = b := MorphismProperty.Over.Hom.ext ((cancel_mono (j i)).mp hh)
        rw [hab]
      · have hW : IsEmpty W.left := ⟨fun w =>
          (Set.disjoint_left.mp (hDisj he)) ⟨a.left w, rfl⟩
            ⟨b.left w, (congrArg (fun t : W.left ⟶ X => t w) hh).symm⟩⟩
        exact (Scheme.subsingleton_sections_of_isEmpty hW F).elim _ _
    obtain ⟨a, ha, _⟩ := (Presieve.isSheafFor_arrows_iff (π := toTerminal j) (P := P)).mp
      hSheaf s hCompat
    exact ⟨a, funext ha⟩

/-- Sections over a disjoint open cover are the product of sections on
its components, with the isomorphism given by restriction. -/
def sectionsEquiv (hCover : ⋃ i, Set.range (j i) = Set.univ)
    (hDisj : Pairwise fun i k => Disjoint (Set.range (j i)) (Set.range (j k)))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    F.obj.obj (op (terminal X)) ≃+ ∀ i, F.obj.obj (op (chart j i)) := by
  let r : (F.obj.obj (op (terminal X))) →+ (∀ i, F.obj.obj (op (chart j i))) :=
    { toFun := fun a i => F.obj.map (toTerminal j i).op a
      map_zero' := funext fun i => (F.obj.map (toTerminal j i).op).hom.map_zero
      map_add' := fun a b => funext fun i => (F.obj.map (toTerminal j i).op).hom.map_add a b }
  exact AddEquiv.ofBijective r (bijective_sections j hCover hDisj F)

/-- Global sections on a scheme presented as a coproduct are the product
of sections over the coproduct inclusions. -/
def sectionsCoproductEquiv (c : (∐ U) ≅ X) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    F.obj.obj (op (terminal X)) ≃+
      ∀ i, F.obj.obj (op (Scheme.Etale.mk (Sigma.ι U i ≫ c.hom))) := by
  let k (i : I) := Sigma.ι U i ≫ c.hom
  have : ∀ i, IsOpenImmersion (k i) := fun i => inferInstanceAs
    (IsOpenImmersion (Sigma.ι U i ≫ c.hom))
  apply sectionsEquiv k _ _ F
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨⟨i, y⟩, hy⟩ := (sigmaMk U).surjective (c.inv x)
    have hh : Sigma.ι U i y = c.inv x := (sigmaMk_mk U i y).symm.trans hy
    refine Set.mem_iUnion.mpr ⟨i, y, ?_⟩
    change (Sigma.ι U i ≫ c.hom) y = x
    rw [Scheme.Hom.comp_apply, hh, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  · intro i k' hik
    apply Set.disjoint_left.mpr
    rintro x ⟨a, rfl⟩ ⟨b, hb⟩
    have eq : Sigma.ι U i a = Sigma.ι U k' b := c.hom.isOpenEmbedding.injective hb.symm
    exact hik (congrArg (fun x : (Σ i, U i) => x.1) ((sigmaι_eq_iff U i k' a b).mp eq))

section StrictlyHenselian

variable (R : I → Type u) [∀ i, CommRing (R i)] [∀ i, HenselianLocalRing (R i)]
  [∀ i, IsSepClosed (IsLocalRing.ResidueField (R i))]

private abbrev component (i : I) := Spec (CommRingCat.of (R i))

private abbrev closedPoint (i : I) :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue (R i)))

private abbrev inclusion (c : (∐ component R) ≅ X) (i : I) :=
  Sigma.ι (component R) i ≫ c.hom

private abbrev closedStalk (c : (∐ component R) ≅ X) (i : I) :=
  (Scheme.pointSmallEtale (closedPoint R i ≫ inclusion R c i)).sheafFiber (A := AddCommGrpCat.{u})

private def componentChartStalkIso (c : (∐ component R) ≅ X) (i : I) :
    (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (op (Scheme.Etale.mk (inclusion R c i))) ≅ closedStalk R c i :=
  chartSectionsNatIso (inclusion R c i) ≪≫
    Functor.isoWhiskerLeft (pullbackSheaves (inclusion R c i)) (globalSectionsIsoClosedStalk (R i)) ≪≫
    stalkPullbackIso (inclusion R c i) (closedPoint R i)

/-- On a disjoint union of strictly henselian local schemes, global sections
of an étale sheaf are the product of its stalks at the closed points. -/
def sectionsEquivClosedStalks (c : (∐ component R) ≅ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    F.obj.obj (op (terminal X)) ≃+ ∀ i, (closedStalk R c i).obj F :=
  (sectionsCoproductEquiv c F).trans (AddEquiv.piCongrRight fun i =>
    ((componentChartStalkIso R c i).app F).addCommGroupIsoToAddEquiv)

/-- The closed-point components of the section comparison commute with
morphisms of sheaves. -/
theorem sectionsEquivClosedStalks_naturality (c : (∐ component R) ≅ X)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (a : F ⟶ G)
    (x : F.obj.obj (op (terminal X))) (i : I) :
    sectionsEquivClosedStalks R c G (a.hom.app (op (terminal X)) x) i =
      (closedStalk R c i).map a (sectionsEquivClosedStalks R c F x i) := by
  let d := (toTerminal (inclusion R c) i).op
  let e := componentChartStalkIso R c i
  change e.hom.app G (G.obj.map d (a.hom.app (op (terminal X)) x)) =
    (closedStalk R c i).map a (e.hom.app F (F.obj.map d x))
  rw [← NatTrans.naturality_apply a.hom d x]
  exact ConcreteCategory.congr_hom (e.hom.naturality a) (F.obj.map d x)

end StrictlyHenselian

end PhilipponEtaleDisjointSections

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleDisjointSections (sectionsCoproductEquiv toTerminal)
open PhilipponEtaleStalkPullback (pointFiberIso pointFiberIso_inv_fst)
open PhilipponStrictHenselianEtaleCohomology
  (chartGerm_bijective_of_pointedSections exists_pointed_section_at_closedPoint terminalGerm)


namespace PhilipponEtaleCoproductGerms

universe u

variable {X : Scheme.{u}} {I : Type u}
  (R : I → Type u) [∀ i, CommRing (R i)] [∀ i, HenselianLocalRing (R i)]
  [∀ i, IsSepClosed (IsLocalRing.ResidueField (R i))]

private abbrev component (i : I) := Spec (CommRingCat.of (R i))

private abbrev inclusion (c : (∐ component R) ≅ X) (i : I) :=
  Sigma.ι (component R) i ≫ c.hom

private abbrev terminal (Y : Scheme.{u}) := Scheme.Etale.mk (𝟙 Y)

variable {K : Type u} [Field K] [IsSepClosed K]

private abbrev componentPoint (c : (∐ component R) ≅ X) (i : I)
    (q : Spec (.of K) ⟶ component R i) :
    (Scheme.pointSmallEtale (q ≫ inclusion R c i)).fiber.obj (Scheme.Etale.mk (inclusion R c i)) :=
  Over.homMk q rfl

private theorem componentGerm_bijective (c : (∐ component R) ≅ X) (i : I)
    (q : Spec (.of K) ⟶ component R i) (hq : q default = IsLocalRing.closedPoint (R i))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Function.Bijective ((Scheme.pointSmallEtale (q ≫ inclusion R c i)).toPresheafFiber
      (Scheme.Etale.mk (inclusion R c i)) (componentPoint R c i q) F.obj) := by
  let k := inclusion R c i
  let V := Scheme.Etale.mk k
  apply chartGerm_bijective_of_pointedSections (q ≫ k) V (componentPoint R c i q) _ _ F
  · intro g
    apply MorphismProperty.Over.Hom.ext
    exact (cancel_mono k).mp ((MorphismProperty.Over.w g).trans (Category.id_comp k).symm)
  · intro W w
    let z := (pointFiberIso k q).inv.app W w
    obtain ⟨g, hg⟩ := exists_pointed_section_at_closedPoint (R i) q hq ((baseChange k).obj W) z
    have hd : g.left ≫ pullback.snd W.hom k = 𝟙 _ := MorphismProperty.Over.w g
    let l : V ⟶ W := MorphismProperty.Over.homMk (g.left ≫ pullback.fst W.hom k) (by
      change (g.left ≫ pullback.fst W.hom k) ≫ W.hom = k
      rw [Category.assoc, pullback.condition, ← Category.assoc, hd, Category.id_comp]) trivial
    refine ⟨l, Over.OverMorphism.ext ?_⟩
    have hg' : q ≫ g.left = z.left := congrArg Over.Hom.left hg
    change q ≫ g.left ≫ pullback.fst W.hom k = w.left
    rw [← Category.assoc, hg']
    exact pointFiberIso_inv_fst k q W w

set_option maxRecDepth 4096 in
/-- Taking the global-section germs at chosen closed geometric points
identifies sections on a strictly henselian coproduct with a product of stalks. -/
theorem terminalGerms_bijective (c : (∐ component R) ≅ X)
    (q : ∀ i, Spec (.of K) ⟶ component R i)
    (hq : ∀ i, q i default = IsLocalRing.closedPoint (R i))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Function.Bijective (fun a : F.obj.obj (op (terminal X)) =>
      fun i => (terminalGerm (q i ≫ inclusion R c i)).app F a) := by
  let e := sectionsCoproductEquiv c F
  let ev (i : I) := (Scheme.pointSmallEtale (q i ≫ inclusion R c i)).toPresheafFiber
    (Scheme.Etale.mk (inclusion R c i)) (componentPoint R c i (q i)) F.obj
  have h : Function.Bijective (fun (a : F.obj.obj (op (terminal X))) => fun i => ev i (e a i)) :=
    (Function.Bijective.piMap fun i => componentGerm_bijective R c i (q i) (hq i) F).comp e.bijective
  have he : (fun (a : F.obj.obj (op (terminal X))) => fun i => ev i (e a i)) =
      (fun a i => (terminalGerm (q i ≫ inclusion R c i)).app F a) := by
    funext a i
    let P := Scheme.pointSmallEtale (q i ≫ inclusion R c i)
    let g := toTerminal (inclusion R c) i
    exact ConcreteCategory.congr_hom (P.toPresheafFiber_w g (componentPoint R c i (q i)) F.obj) a
  exact he ▸ h

end PhilipponEtaleCoproductGerms

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory


namespace PhilipponFiniteLocalGeometricPoint

universe u

/-- A geometric point obtained from the residue field of the base local
ring lifts to the closed point of a finite local scheme over it. -/
theorem exists_closed_lift {R B K : Type u} [CommRing R] [IsLocalRing R]
    [CommRing B] [IsLocalRing B] [Field K] [IsAlgClosed K]
    (p : Spec (.of B) ⟶ Spec (.of R)) [IsFinite p]
    (ι : IsLocalRing.ResidueField R →+* K) :
    ∃ t : Spec (.of K) ⟶ Spec (.of B),
      t ≫ p = Spec.map (CommRingCat.ofHom (ι.comp (IsLocalRing.residue R))) ∧
        t default = IsLocalRing.closedPoint B := by
  let r := Spec.preimage p
  let _ : Algebra R B := r.hom.toAlgebra
  have hr : IsFinite (Spec.map r) := by
    rw [Spec.map_preimage]
    infer_instance
  have : Module.Finite R B := RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff r).mp hr)
  have hMax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (IsLocalRing.maximalIdeal B)
  have : IsLocalHom (algebraMap R B) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap R B)).out 4 0).mp (IsLocalRing.eq_maximalIdeal hMax)
  let _ : Algebra (IsLocalRing.ResidueField R) K := ι.toAlgebra
  let ψ : IsLocalRing.ResidueField B →ₐ[IsLocalRing.ResidueField R] K := IsAlgClosed.lift
  let t := Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))
  refine ⟨t, ?_, ?_⟩
  · change (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))) ≫ p = _
    rw [← Spec.map_preimage p, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact ψ.commutes (IsLocalRing.residue R x)
  · change (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))) default = _
    rw [Scheme.Hom.comp_apply]
    exact IsLocalRing.PrimeSpectrum.comap_residue B _

end PhilipponFiniteLocalGeometricPoint

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleHenselianStalk (henselianLocalRing residueEmbedding)
open PhilipponEtaleLocalRing (evaluateGerm stalkRing)
open PhilipponEtaleStrictHenselization (closedPointInclusion evaluation_comp_projection
  neighborhoodLimitCone pullbackNeighborhoodLimitCone toBase)


namespace PhilipponStrictLocalFinitePoints

universe u

/-- Each local component of the strict localization of a finite morphism
has a closed-point lift over the original algebraically closed field. -/
theorem exists_closed_component_lift {X Y : Scheme.{u}} {K B : Type u}
    [Field K] [IsAlgClosed K] [CommRing B] [IsLocalRing B]
    (s : Spec (.of K) ⟶ X) (p : Y ⟶ X) [IsFinite p]
    (j : Spec (.of B) ⟶ pullback (toBase s) p) [IsClosedImmersion j] :
    ∃ t : Spec (.of K) ⟶ Spec (.of B),
      t ≫ j ≫ pullback.fst (toBase s) p =
        Spec.map (CommRingCat.ofHom (residueEmbedding s)) ≫ closedPointInclusion s ∧
        t default = IsLocalRing.closedPoint B := by
  let hR : IsLocalRing (stalkRing s) := (henselianLocalRing s).toIsLocalRing
  let _ := hR
  have hFinite : IsFinite (j ≫ pullback.fst (toBase s) p) := inferInstance
  obtain ⟨t, ht, hPt⟩ := @PhilipponFiniteLocalGeometricPoint.exists_closed_lift
    (stalkRing s) B K _ hR _ _ _ _ (j ≫ pullback.fst (toBase s) p) hFinite (residueEmbedding s)
  refine ⟨t, ht.trans ?_, hPt⟩
  change Spec.map (CommRingCat.ofHom ((residueEmbedding s).comp (IsLocalRing.residue (stalkRing s)))) =
    Spec.map (CommRingCat.ofHom (residueEmbedding s)) ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue (stalkRing s)))
  rw [← Spec.map_comp]
  rfl

/-- A lift of the geometric point to the strict-local pullback induces
the original geometric lift in each pulled-back étale neighborhood. -/
theorem comp_neighborhoodProjection {X Y : Scheme.{u}} {K : Type u}
    [Field K] [IsSepClosed K] (s : Spec (.of K) ⟶ X) (p : Y ⟶ X)
    (r : Spec (.of K) ⟶ pullback (toBase s) p)
    (hr : r ≫ pullback.fst (toBase s) p = Spec.map (evaluateGerm s))
    (W : (Scheme.pointSmallEtale s).fiber.Elements) :
    let k := (pullbackNeighborhoodLimitCone s p).cone.π.app W
    (r ≫ k) ≫ pullback.fst W.fst.hom p = W.snd.left ∧
      (r ≫ k) ≫ pullback.snd W.fst.hom p = r ≫ pullback.snd (toBase s) p := by
  let k : pullback (toBase s) p ⟶ pullback W.fst.hom p :=
    (pullbackNeighborhoodLimitCone s p).cone.π.app W
  let d : Spec (stalkRing s) ⟶ W.fst.left := (neighborhoodLimitCone s).cone.π.app W
  let w : Spec (.of K) ⟶ W.fst.left := W.snd.left
  have hf : k ≫ pullback.fst W.fst.hom p = pullback.fst (toBase s) p ≫ d := pullback.lift_fst ..
  have hh : k ≫ pullback.snd W.fst.hom p = pullback.snd (toBase s) p := pullback.lift_snd ..
  change (r ≫ k) ≫ pullback.fst W.fst.hom p = w ∧
    (r ≫ k) ≫ pullback.snd W.fst.hom p = r ≫ pullback.snd (toBase s) p
  constructor
  · calc
      (r ≫ k) ≫ pullback.fst W.fst.hom p = r ≫ (k ≫ pullback.fst W.fst.hom p) :=
        Category.assoc _ _ _
      _ = r ≫ pullback.fst (toBase s) p ≫ d := congrArg (r ≫ ·) hf
      _ = (r ≫ pullback.fst (toBase s) p) ≫ d := (Category.assoc _ _ _).symm
      _ = Spec.map (evaluateGerm s) ≫ d := congrArg (· ≫ d) hr
      _ = w := evaluation_comp_projection s W
  · exact (Category.assoc _ _ _).trans (congrArg (r ≫ ·) hh)

end PhilipponStrictLocalFinitePoints

end

end


