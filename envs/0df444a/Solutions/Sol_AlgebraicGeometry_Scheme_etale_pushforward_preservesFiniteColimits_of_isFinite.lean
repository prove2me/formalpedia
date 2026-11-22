-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.etale_pushforward_preservesFiniteColimits_of_isFinite
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-21T16:27:46.537457+00:00
-- url     : https://prove2.me/submissions/678f6ebd-a437-4b62-9aed-4948f3e461ae

import Definitions.Def_AlgebraicGeometry_EtaleModeledInverseImages
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Unramified.LocalStructure
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_coproduct_strictlyHenselian_of_finite

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial


namespace PhilipponHenselianEtaleSection

variable (R : Type*) [CommRing R] [HenselianLocalRing R]

private abbrev ρ := Algebra.ofId R (ResidueField R)

private theorem exists_section_standardPair (P : StandardEtalePair R) (φ : P.Ring →ₐ[R] ResidueField R) :
    ∃ ψ : P.Ring →ₐ[R] R, (ρ R).comp ψ = φ := by
  have hx := (StandardEtalePair.hasMap_X (P := P)).map φ
  have hLift : ∀ p : R[X], p.Monic → ∀ a : ResidueField R,
      aeval a p = 0 → aeval a p.derivative ≠ 0 →
      ∃ b : R, p.IsRoot b ∧ residue R b = a :=
    ((HenselianLocalRing.TFAE R).out 0 1).mp (show HenselianLocalRing R from inferInstance)
  obtain ⟨b, hb, hres⟩ := hLift P.f P.monic_f (φ P.X)
    hx.1 (hx.isUnit_derivative_f.ne_zero)
  have hb' : P.HasMap b := by
    refine ⟨?_, ?_⟩
    · simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id,
        Polynomial.IsRoot.def] using hb
    · have h := hx.2.ne_zero
      rw [← hres, Polynomial.aeval_def, IsLocalRing.ResidueField.algebraMap_eq,
        Polynomial.eval₂_at_apply] at h
      simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using
        (residue_ne_zero_iff_isUnit _).mp h
  refine ⟨P.lift b hb', P.hom_ext ?_⟩
  change residue R (P.lift b hb' P.X) = φ P.X
  rw [P.lift_X, hres]

private theorem exists_section_standard {S : Type*} [CommRing S] [Algebra R S]
    [Algebra.IsStandardEtale R S] (φ : S →ₐ[R] ResidueField R) :
    ∃ ψ : S →ₐ[R] R, (ρ R).comp ψ = φ := by
  let P : StandardEtalePresentation R S := Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  obtain ⟨ψ, hψ⟩ := exists_section_standardPair R P.P (φ.comp P.equivRing.symm.toAlgHom)
  refine ⟨ψ.comp P.equivRing.toAlgHom, ?_⟩
  ext x
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using
    DFunLike.congr_fun hψ (P.equivRing x)

/-- An algebra map from an étale algebra to the residue field of a Henselian
local ring lifts to an algebra map to the ring. -/
theorem exists_section {S : Type*} [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (φ : S →ₐ[R] ResidueField R) : ∃ ψ : S →ₐ[R] R, (ρ R).comp ψ = φ := by
  let Q := RingHom.ker φ.toRingHom
  let : Q.IsPrime := RingHom.ker_isPrime φ.toRingHom
  let : Algebra.IsEtaleAt R Q := Algebra.FormallyEtale.comp R S _
  obtain ⟨g, hg, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) Q
  have hu : IsUnit (φ g) := isUnit_iff_ne_zero.mpr hg
  let φ' : Localization.Away g →ₐ[R] ResidueField R := IsLocalization.Away.liftAlgHom g hu
  obtain ⟨ψ, hψ⟩ := exists_section_standard R φ'
  refine ⟨ψ.comp (IsScalarTower.toAlgHom R S (Localization.Away g)), ?_⟩
  ext x
  exact (DFunLike.congr_fun hψ (algebraMap S (Localization.Away g) x)).trans
    (IsLocalization.Away.lift_eq g hu x)

universe u

/-- A lift of the residue point to an étale scheme over a Henselian local
ring extends to a section over the ring. -/
theorem exists_scheme_section {R : Type u} [CommRing R] [HenselianLocalRing R]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R)) [Etale g]
    (x : Spec (CommRingCat.of (ResidueField R)) ⟶ Y)
    (hx : x ≫ g = Spec.map (CommRingCat.ofHom (residue R))) :
    ∃ t : Spec (CommRingCat.of R) ⟶ Y,
      t ≫ g = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (residue R)) ≫ t = x := by
  obtain ⟨A, i, hi, hxI, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := x default) (U := ⊤) trivial
  have hr : Set.range x ⊆ Set.range i := by
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  let e := IsOpenImmersion.lift i x hr
  have he : e ≫ i = x := IsOpenImmersion.lift_fac ..
  obtain ⟨p, hp⟩ := Spec.map_surjective (i ≫ g)
  obtain ⟨q, hq⟩ := Spec.map_surjective e
  have hpq : p ≫ q = CommRingCat.ofHom (residue R) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hq, hp, ← Category.assoc, he, hx]
  have hpe : Etale (Spec.map p) := hp.symm ▸ (inferInstance : Etale (i ≫ g))
  let : Algebra R A := p.hom.toAlgebra
  let : Algebra.Etale R A := (HasRingHomProperty.Spec_iff (P := @Etale)).mp hpe
  let q' : A →ₐ[R] ResidueField R :=
    { toRingHom := q.hom
      commutes' := fun a => ConcreteCategory.congr_hom hpq a }
  obtain ⟨k, hk⟩ := exists_section R q'
  let k' : A ⟶ CommRingCat.of R := CommRingCat.ofHom k.toRingHom
  have hpk : p ≫ k' = 𝟙 _ := ConcreteCategory.hom_ext_iff.mpr k.commutes
  have hkq : k' ≫ CommRingCat.ofHom (residue R) = q := by
    apply ConcreteCategory.hom_ext
    intro a
    exact DFunLike.congr_fun hk a
  refine ⟨Spec.map k' ≫ i, ?_, ?_⟩
  · rw [Category.assoc, ← hp, ← Spec.map_comp, hpk, Spec.map_id]
  · rw [← Category.assoc, ← Spec.map_comp, hkq, hq, he]

end PhilipponHenselianEtaleSection

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponHenselianEtaleSection (exists_scheme_section)


namespace PhilipponStrictHenselianEtaleCohomology

universe u

/-- A finite local algebra over a local ring with separably closed
residue field again has separably closed residue field. -/
theorem residueField_isSepClosed_of_moduleFinite {R B : Type*} [CommRing R] [IsLocalRing R]
    [IsSepClosed (ResidueField R)] [CommRing B] [IsLocalRing B] [Algebra R B] [Module.Finite R B] :
    IsSepClosed (ResidueField B) := by
  have h := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (maximalIdeal B)
  have : IsLocalHom (algebraMap R B) :=
    ((local_hom_TFAE (algebraMap R B)).out 4 0).mp (eq_maximalIdeal h)
  exact Algebra.IsAlgebraic.isSepClosed (F := ResidueField R)

variable (R : Type u) [CommRing R] [HenselianLocalRing R] [IsSepClosed (ResidueField R)]

private abbrev X := Spec (CommRingCat.of R)
private abbrev s := Spec.map (CommRingCat.ofHom (residue R))
private abbrev Φ := Scheme.pointSmallEtale (s R)
private abbrev T := Scheme.Etale.mk (𝟙 (X R))
private abbrev t : (Φ R).fiber.obj (T R) := Over.homMk (s R) (Category.comp_id _)
private abbrev Ab := Sheaf (X R).smallEtaleTopology AddCommGrpCat.{u}

private theorem pointed_section (W : (X R).Etale) (w : (Φ R).fiber.obj W) :
    ∃ g : T R ⟶ W, (Φ R).fiber.map g (t R) = w := by
  obtain ⟨a, ha, hw⟩ := exists_scheme_section W.hom w.left (Over.w w)
  refine ⟨MorphismProperty.Over.homMk a ha trivial, Over.OverMorphism.ext hw⟩

private abbrev sectionsToStalk : globalSections (X R) ⟶ (Φ R).sheafFiber (A := AddCommGrpCat.{u}) :=
  Functor.whiskerLeft (sheafToPresheaf _ _) ((Φ R).toPresheafFiberNatTrans (T R) (t R))

private theorem sectionsToStalk_bijective (F : Ab R) :
    Function.Bijective ((sectionsToStalk R).app F) := by
  constructor
  · intro a b hab
    obtain ⟨W, g, w, _, he⟩ := ((Φ R).toPresheafFiber_eq_iff' (T R) (t R) a b).mp hab
    obtain ⟨j, _⟩ := pointed_section R W w
    have hT : IsTerminal (T R) := IsTerminal.isTerminalOfObj (Scheme.Etale.forget (X R))
      _ Over.mkIdTerminal
    have hjg : j ≫ g = 𝟙 (T R) := hT.hom_ext _ _
    have hr : F.obj.map g.op ≫ F.obj.map j.op = 𝟙 _ := by
      rw [← F.obj.map_comp, ← op_comp, hjg]
      exact F.obj.map_id _
    change F.obj.map g.op a = F.obj.map g.op b at he
    have h := congrArg (fun z => F.obj.map j.op z) he
    simpa only [← ConcreteCategory.comp_apply, hr, ConcreteCategory.id_apply] using h
  · intro a
    obtain ⟨W, w, b, rfl⟩ := (Φ R).toPresheafFiber_jointly_surjective a
    obtain ⟨g, hg⟩ := pointed_section R W w
    refine ⟨F.obj.map g.op b, ?_⟩
    change (Φ R).toPresheafFiber (T R) (t R) F.obj (F.obj.map g.op b) =
      (Φ R).toPresheafFiber W w F.obj b
    rw [(Φ R).toPresheafFiber_w_apply, hg]

/-- For a strictly Henselian local scheme, global sections of an étale
abelian sheaf are its stalk at the residue point. -/
def globalSectionsIsoClosedStalk : globalSections (X R) ≅ (Φ R).sheafFiber (A := AddCommGrpCat.{u}) :=
  NatIso.ofComponents
    (fun F => (AddEquiv.ofBijective ((sectionsToStalk R).app F).hom
      (sectionsToStalk_bijective R F)).toAddCommGrpIso)
    (fun a => (sectionsToStalk R).naturality a)

end PhilipponStrictHenselianEtaleCohomology

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackSheaves pullbackAdjunction)
open PhilipponEtaleStrictHenselization
  (IsAffineNeighborhood affineInclusion pullbackNeighborhoodLimitCone affinePullbackTransition toBase)


namespace PhilipponStrictLocalPresheaf

universe u

variable {X Y : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
  (s : Spec (CommRingCat.of K) ⟶ X) (f : Y ⟶ X)

private abbrev Local : Scheme.{u} := pullback (toBase s) f
private abbrev π : Local s f ⟶ Y := pullback.snd (toBase s) f
private abbrev T : (Local s f).Etale := Scheme.Etale.mk (𝟙 _)

private abbrev PullbackPointwise (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :=
  (Functor.LeftExtension.mk ((pullbackSheaves (π s f)).obj F).obj
    ((pullbackAdjunction (π s f)).unit.app F).hom).IsPointwiseLeftKanExtensionAt (op (T s f))

private abbrev Φ := Scheme.pointSmallEtale s
private abbrev C := (IsAffineNeighborhood s).FullSubcategory
private abbrev Index := InitiallySmall.CofilteredInitialModel.{u} (C s)
private abbrev H := InitiallySmall.fromCofilteredInitialModel.{u} (C s)
private abbrev J := H s ⋙ affineInclusion s
private abbrev E := J s ⋙ CategoryOfElements.π (Φ s).fiber ⋙ baseChange f
private abbrev D := E s f ⋙ Scheme.Etale.forget Y ⋙ Over.forget Y
private abbrev limitCone : Cone (D s f) := (pullbackNeighborhoodLimitCone s f).cone.whisker (J s)
private abbrev t : (limitCone s f).pt ⟶ Local s f := 𝟙 _

private theorem stageComm (i : Index s) :
    (limitCone s f).π.app i ≫ ((E s f).obj i).hom = t s f ≫ π s f := by
  change pullback.lift _ _ _ ≫ pullback.snd _ _ = 𝟙 _ ≫ pullback.snd _ _
  exact (pullback.lift_snd ..).trans (Category.id_comp _).symm

private def limitWitness : IsLimit (limitCone s f) :=
  (Functor.Initial.isLimitWhiskerEquiv (J s) _).symm (pullbackNeighborhoodLimitCone s f).isLimit

private abbrev q (i : Index s) : (D s f).obj i ⟶ ((H s).obj i).obj.1.left :=
  pullback.fst ((H s).obj i).obj.1.hom f

local instance stageCompact [IsProper f] (i : Index s) : CompactSpace ((D s f).obj i) := by
  let : IsAffine ((H s).obj i).obj.1.left := ((H s).obj i).property
  let : IsProper (q s f i) := inferInstanceAs (IsProper (pullback.fst ((H s).obj i).obj.1.hom f))
  exact (quasiCompact_iff_compactSpace (q s f i)).mp inferInstance

local instance stageQuasiSeparated [IsProper f] (i : Index s) :
    QuasiSeparatedSpace ((D s f).obj i) := by
  let : IsAffine ((H s).obj i).obj.1.left := ((H s).obj i).property
  let : IsProper (q s f i) := inferInstanceAs (IsProper (pullback.fst ((H s).obj i).obj.1.hom f))
  exact quasiSeparatedSpace_of_quasiSeparated (q s f i)

local instance stageAffine {i j : Index s} (b : i ⟶ j) : IsAffineHom ((D s f).map b) :=
  affinePullbackTransition s f ((H s).map b)

private def stageCocone (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    ColimitCocone ((E s f).op ⋙ F.obj) :=
  ⟨((Φ s).presheafFiberCocone ((pushforward f).obj F).obj).whisker (J s).op,
    (Functor.Final.isColimitWhiskerEquiv (J s).op _).symm
      ((Φ s).isColimitPresheafFiberCocone ((pushforward f).obj F).obj)⟩

private theorem modeledTerminal [IsProper f] :
    PhilipponEtaleRefinementGluing.modeledCharts (E s f) (limitCone s f) (T s f) := by
  let c := limitCone s f
  let i := Classical.choice (IsCofiltered.nonempty (C := Index s))
  let V := Scheme.Etale.mk (𝟙 ((D s f).obj i))
  let g := pullback.fst (c.π.app i) (𝟙 ((D s f).obj i))
  let e : T s f ≅ (PhilipponEtaleModeledSections.chartLimitFunctor (E s f) c i).obj V :=
    MorphismProperty.Over.isoMk (asIso g).symm (IsIso.inv_hom_id g)
  exact ⟨i, V, ⟨stageCompact s f i, stageQuasiSeparated s f i⟩, ⟨e⟩⟩

private def strictLocalCocones [IsProper f] (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    ColimitCocone (CostructuredArrow.proj (baseChange (π s f)).op (op (T s f)) ⋙ F.obj) ×
      PullbackPointwise s f F := by
  let c := limitCone s f
  let hc := limitWitness s f
  refine ⟨PhilipponEtaleLimitPresheaf.pointwisePullbackCocone (π s f) (E s f) c (t s f)
    (stageComm s f) hc F.obj (stageCocone s f F), ?_⟩
  let U : (PhilipponEtaleRefinementGluing.modeledCharts (E s f) c).FullSubcategory :=
    ⟨T s f, modeledTerminal s f⟩
  exact PhilipponEtaleModeledInverseImage.inverseImageIsPointwiseOnModeledChart (E s f) c hc
    (π s f) (fun j => (stageComm s f j).trans (Category.id_comp _)) F U

/-- For proper (f), the geometric stalk of (f_*F) computes the value
at the terminal étale object of the presheaf inverse image of (F) to
the pullback over the strict henselization. -/
def stalkPresheafPullbackCocone [IsProper f] (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    ColimitCocone (CostructuredArrow.proj (baseChange (π s f)).op (op (T s f)) ⋙ F.obj) :=
  (strictLocalCocones s f F).1

@[simp] theorem stalkPresheafPullbackCocone_pt [IsProper f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (stalkPresheafPullbackCocone s f F).cocone.pt =
      (Scheme.pointSmallEtale s).sheafFiber.obj ((pushforward f).obj F) := rfl

/-- Degree-zero comparison for a proper morphism at a geometric point.
The geometric direct-image stalk is the sections of the sheaf inverse
image over the strict henselization pullback. -/
def stalkDirectImageIsoStrictLocalSections [IsProper f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (Scheme.pointSmallEtale s).sheafFiber.obj ((pushforward f).obj F) ≅
      ((pullbackSheaves (π s f)).obj F).obj.obj (op (T s f)) :=
  (stalkPresheafPullbackCocone s f F).isColimit.coconePointUniqueUpToIso
    (strictLocalCocones s f F).2

@[reassoc]
theorem stalkDirectImageIsoStrictLocalSections_ι [IsProper f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (j : CostructuredArrow (baseChange (π s f)).op (op (T s f))) :
    (stalkPresheafPullbackCocone s f F).cocone.ι.app j ≫
        (stalkDirectImageIsoStrictLocalSections s f F).hom =
      ((pullbackAdjunction (π s f)).unit.app F).hom.app j.left ≫
        ((pullbackSheaves (π s f)).obj F).obj.map j.hom :=
  (stalkPresheafPullbackCocone s f F).isColimit.comp_coconePointUniqueUpToIso_hom
    (strictLocalCocones s f F).2 j

private abbrev comparisonIndex := PhilipponEtaleLimitPresheaf.neighborhoodIndex
  (π s f) (E s f) (limitCone s f) (t s f) (stageComm s f)

private theorem stalkPresheafPullbackCocone_ι_stage [IsProper f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (i : (Index s)ᵒᵖ) :
    (stalkPresheafPullbackCocone s f F).cocone.ι.app ((comparisonIndex s f).obj i) =
      (stageCocone s f F).cocone.ι.app i :=
  PhilipponEtaleLimitPresheaf.pointwisePullbackCocone_ι (π s f) (E s f) (limitCone s f)
    (t s f) (stageComm s f) (limitWitness s f) F.obj (stageCocone s f F) i

private theorem stageCocone_naturality [IsProper f]
    {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}} (a : F ⟶ G) (i : (Index s)ᵒᵖ) :
    (stalkPresheafPullbackCocone s f F).cocone.ι.app ((comparisonIndex s f).obj i) ≫
      (pushforward f ⋙ (Φ s).sheafFiber).map a =
    a.hom.app ((comparisonIndex s f).obj i).left ≫
      (stalkPresheafPullbackCocone s f G).cocone.ι.app ((comparisonIndex s f).obj i) := by
  rw [stalkPresheafPullbackCocone_ι_stage, stalkPresheafPullbackCocone_ι_stage]
  let U := (J s).obj i.unop
  exact (Φ s).toPresheafFiber_naturality ((pushforward f).map a).hom U.1 U.2

/-- The degree-zero strict-local comparison is natural in the sheaf. -/
def stalkDirectImageNatIsoStrictLocalSections [IsProper f] :
    pushforward f ⋙ (Φ s).sheafFiber ≅ pullbackSheaves (π s f) ⋙ globalSections (Local s f) :=
  NatIso.ofComponents (stalkDirectImageIsoStrictLocalSections s f) (fun {F G} a => by
    let B := comparisonIndex s f
    let : B.Final := PhilipponEtaleLimitPresheaf.neighborhoodIndex_final (π s f) (E s f)
      (limitCone s f) (t s f) (stageComm s f) (limitWitness s f)
    let dF := stalkPresheafPullbackCocone s f F
    apply ((Functor.Final.isColimitWhiskerEquiv B dF.cocone).symm dF.isColimit).hom_ext
    intro i
    let j := B.obj i
    change dF.cocone.ι.app j ≫ (pushforward f ⋙ (Φ s).sheafFiber).map a ≫
        (stalkDirectImageIsoStrictLocalSections s f G).hom =
      dF.cocone.ι.app j ≫ (stalkDirectImageIsoStrictLocalSections s f F).hom ≫
        ((pullbackSheaves (π s f)).map a).hom.app (op (T s f))
    rw [← Category.assoc, stageCocone_naturality, Category.assoc,
      stalkDirectImageIsoStrictLocalSections_ι, stalkDirectImageIsoStrictLocalSections_ι_assoc]
    let L := pullbackSheaves (π s f)
    let η := (pullbackAdjunction (π s f)).unit
    have hη := congrArg (fun h : F ⟶ (pushforward (π s f)).obj (L.obj G) => h.hom.app j.left)
      (η.naturality a)
    change a.hom.app j.left ≫ (η.app G).hom.app j.left =
      (η.app F).hom.app j.left ≫ (L.map a).hom.app ((baseChange (π s f)).op.obj j.left) at hη
    change a.hom.app j.left ≫ (η.app G).hom.app j.left ≫ (L.obj G).obj.map j.hom =
      (η.app F).hom.app j.left ≫ (L.obj F).obj.map j.hom ≫ (L.map a).hom.app (op (T s f))
    rw [← Category.assoc, hη, Category.assoc, ← (L.map a).hom.naturality j.hom]
    rfl)

end PhilipponStrictLocalPresheaf

end

section

open AlgebraicGeometry CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

universe u

/-- The empty étale object has a unique section of any abelian sheaf. -/
theorem subsingleton_sections_of_isEmpty {X : Scheme.{u}} {W : X.Etale}
    (hW : IsEmpty W.left) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Subsingleton (F.obj.obj (op W)) := by
  let V : Empty → X.Etale := Empty.elim
  let p (i : Empty) : V i ⟶ W := Empty.elim i
  have hCover : Sieve.ofArrows V p ∈ X.smallEtaleTopology W :=
    (Scheme.ofArrows_mem_smallEtaleTopology_iff p).mpr (Set.ext fun x => (hW.false x).elim)
  have hBot : (⊥ : Sieve W) ∈ X.smallEtaleTopology W := by
    apply X.smallEtaleTopology.superset_covering _ hCover
    apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨i⟩
    exact Empty.elim i
  refine ⟨fun x y => ?_⟩
  have hs := Presheaf.isSheaf_comp_of_isSheaf X.smallEtaleTopology F.obj
    (CategoryTheory.forget AddCommGrpCat) F.property
  apply ((isSheaf_iff_isSheaf_of_type _ _).mp hs _ hBot).isSeparatedFor.ext
  intro _ _ h
  exact h.elim

end AlgebraicGeometry.Scheme

end

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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleDisjointSections (sectionsEquivClosedStalks sectionsEquivClosedStalks_naturality)
open PhilipponEtaleGeometricStalks (geometricMap geometricPoint)
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtaleStalkPullback (stalkPullbackIso)
open PhilipponEtaleStrictHenselization (toBase)
open PhilipponStrictLocalPresheaf (stalkDirectImageIsoStrictLocalSections
  stalkDirectImageNatIsoStrictLocalSections)


namespace PhilipponFiniteEtaleStalks

universe u

variable {X Y : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
  (s : Spec (CommRingCat.of K) ⟶ X) (p : Y ⟶ X) [IsFinite p]
  {I : Type u} (R : I → Type u) [∀ i, CommRing (R i)] [∀ i, HenselianLocalRing (R i)]
  [∀ i, IsSepClosed (IsLocalRing.ResidueField (R i))]

private abbrev spectrum (i : I) := Spec (CommRingCat.of (R i))

private abbrev localTotal := pullback (toBase s) p

private abbrev toTotal := pullback.snd (toBase s) p

private abbrev closedPoint (c : (∐ spectrum R) ≅ localTotal s p) (i : I) :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue (R i))) ≫ Sigma.ι (spectrum R) i ≫ c.hom

private abbrev baseStalk := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})

private abbrev componentStalk (c : (∐ spectrum R) ≅ localTotal s p) (i : I) :=
  (Scheme.pointSmallEtale (closedPoint s p R c i ≫ toTotal s p)).sheafFiber (A := AddCommGrpCat.{u})

/-- The stalk of a finite direct image is the product of the original
stalks at the closed points of the strict-local components. -/
def directImageStalkEquivClosedStalks (c : (∐ spectrum R) ≅ localTotal s p)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (baseStalk s).obj ((pushforward p).obj F) ≃+ ∀ i, (componentStalk s p R c i).obj F := by
  let G := (pullbackSheaves (toTotal s p)).obj F
  exact (stalkDirectImageIsoStrictLocalSections s p F).addCommGroupIsoToAddEquiv.trans
    ((sectionsEquivClosedStalks R c G).trans (AddEquiv.piCongrRight fun i =>
      ((stalkPullbackIso (toTotal s p) (closedPoint s p R c i)).app F).addCommGroupIsoToAddEquiv))

set_option maxRecDepth 4096 in
/-- The product description of the stalk is natural in the sheaf. -/
theorem directImageStalkEquivClosedStalks_naturality (c : (∐ spectrum R) ≅ localTotal s p)
    {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}} (a : F ⟶ G)
    (x : (baseStalk s).obj ((pushforward p).obj F)) (i : I) :
    directImageStalkEquivClosedStalks s p R c G ((baseStalk s).map ((pushforward p).map a) x) i =
      (componentStalk s p R c i).map a (directImageStalkEquivClosedStalks s p R c F x i) := by
  let d := stalkDirectImageNatIsoStrictLocalSections s p
  let L := pullbackSheaves (toTotal s p)
  let e := stalkPullbackIso (toTotal s p) (closedPoint s p R c i)
  let T := Scheme.Etale.mk (𝟙 (localTotal s p))
  have hd : d.hom.app G ((baseStalk s).map ((pushforward p).map a) x) =
      (L.map a).hom.app (op T) (d.hom.app F x) := ConcreteCategory.congr_hom (d.hom.naturality a) x
  have hs := sectionsEquivClosedStalks_naturality R c (L.map a) (d.hom.app F x) i
  change e.hom.app G (sectionsEquivClosedStalks R c (L.obj G)
      (d.hom.app G ((baseStalk s).map ((pushforward p).map a) x)) i) =
    (componentStalk s p R c i).map a
      (e.hom.app F (sectionsEquivClosedStalks R c (L.obj F) (d.hom.app F x) i))
  rw [hd, hs]
  exact ConcreteCategory.congr_hom (e.hom.naturality a)
    (sectionsEquivClosedStalks R c (L.obj F) (d.hom.app F x) i)

/-- The direct image of an epimorphism is surjective on a stalk whose
strict-local pullback has the indicated decomposition. -/
theorem epi_directImageStalk (c : (∐ spectrum R) ≅ localTotal s p)
    {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}} (a : F ⟶ G) [Epi a] :
    Epi ((baseStalk s).map ((pushforward p).map a)) := by
  classical
  apply (AddCommGrpCat.epi_iff_surjective _).2
  intro y
  let E (H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :=
    directImageStalkEquivClosedStalks s p R c H
  have h (i : I) : Function.Surjective ((componentStalk s p R c i).map a) :=
    (AddCommGrpCat.epi_iff_surjective _).1 inferInstance
  choose b hb using fun i => h i (E G y i)
  refine ⟨(E F).symm b, (E G).injective ?_⟩
  funext i
  rw [show E G ((baseStalk s).map ((pushforward p).map a) ((E F).symm b)) i =
    (componentStalk s p R c i).map a (E F ((E F).symm b) i) from
    directImageStalkEquivClosedStalks_naturality s p R c a ((E F).symm b) i,
    AddEquiv.apply_symm_apply]
  exact hb i

/-- A decomposition into spectra of strictly henselian local rings. -/
def HasStrictlyHenselianComponents (W : Scheme.{u}) : Prop :=
  ∃ (J : Type u) (B : J → Type u) (_ : ∀ j, CommRing (B j))
    (h : ∀ j, HenselianLocalRing (B j)),
      (∀ j, let _ := h j; IsSepClosed (IsLocalRing.ResidueField (B j))) ∧
        Nonempty ((∐ fun j ↦ Spec (.of (B j))) ≅ W)

/-- Finite direct image is exact when the strict-local pullbacks split
into strictly henselian local components. -/
theorem preservesFiniteColimits_of_strictLocalComponents
    (hSplit : ∀ x : X, HasStrictlyHenselianComponents (localTotal (geometricMap x) p)) :
    PreservesFiniteColimits (pushforward p) := by
  have : (pushforward p).PreservesEpimorphisms := by
    constructor
    intro F G a ha
    let P := ObjectProperty.ofObj (fun x : X => geometricPoint x)
    have hP : P.IsConservativeFamilyOfPoints := Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X
    let : ∀ Φ : P.FullSubcategory, Epi (Φ.obj.sheafFiber.map ((pushforward p).map a)) := by
      intro Φ
      have h := Φ.property
      change ObjectProperty.ofObj (fun x : X => geometricPoint x) Φ.obj at h
      obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ _).mp h
      rw [← hx]
      obtain ⟨J, B, hB, hH, hSep, ⟨c⟩⟩ := hSplit x
      let _ : ∀ j, CommRing (B j) := hB
      let _ : ∀ j, HenselianLocalRing (B j) := hH
      let _ : ∀ j, IsSepClosed (IsLocalRing.ResidueField (B j)) := hSep
      exact epi_directImageStalk (geometricMap x) p B c a
    exact (hP.jointlyReflectEpimorphisms AddCommGrpCat.{u}).epi ((pushforward p).map a)
  have : (pushforward p).PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact Functor.preservesFiniteColimits_of_preservesHomology _

end PhilipponFiniteEtaleStalks

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    {X Y : Scheme.{u}} (p : Y ⟶ X) [IsFinite p] :
    PreservesFiniteColimits (PhilipponEtaleClosedPushforward.pushforward p) := by
  apply PhilipponFiniteEtaleStalks.preservesFiniteColimits_of_strictLocalComponents p
  intro x
  let s := PhilipponEtaleGeometricStalks.geometricMap x
  let R : Type u := PhilipponEtaleLocalRing.stalkRing s
  let hR : HenselianLocalRing R := PhilipponEtaleHenselianStalk.henselianLocalRing s
  let _ := hR
  let hSep : IsSepClosed (IsLocalRing.ResidueField R) :=
    PhilipponEtaleHenselianStalk.residueFieldIsSepClosed s
  let q := pullback.fst (PhilipponEtaleStrictHenselization.toBase s) p
  have hq : IsFinite q := inferInstanceAs (IsFinite (pullback.fst
    (PhilipponEtaleStrictHenselization.toBase s) p))
  obtain ⟨I, _, B, hRing, hH, hB, c, _⟩ := @AlgebraicGeometry.Scheme.exists_finite_coproduct_strictlyHenselian_of_finite R _ hR hSep _ q hq
  exact ⟨I, B, hRing, hH, hB, ⟨c⟩⟩

end

end
