-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleFiniteDirectImageBaseChange
-- name    : AlgebraicGeometry_EtaleFiniteDirectImageBaseChange
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-26T07:49:34.652831+00:00
-- url     : https://prove2.me/theorems/4aa49d1b-cfe6-5fdd-aab8-0256f713b308
-- title:
--   Exactness and base change for finite étale direct images
-- statement:
--   Direct image along a finite morphism is exact on abelian étale sheaves and commutes with arbitrary base change.
-- source:
--   Stacks Project, Section 59.83, https://stacks.math.columbia.edu/tag/03SB.

import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestriction
import Definitions.Def_AlgebraicGeometry_EtaleFiniteLiftEvaluation
import Definitions.Def_AlgebraicGeometry_EtaleOpenCoefficientComparison
import Definitions.Def_AlgebraicGeometry_EtalePullbackGermNaturality
import Definitions.Def_AlgebraicGeometry_EtaleStrictLocalSectionGerms
import Definitions.Def_AlgebraicGeometry_FreeEtaleChartSheaves
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.Tactic.FinCases
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_coproduct_strictlyHenselian_of_finite

noncomputable section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) etaleFiniteDirectImageBaseChangeHasSheafify (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) etaleFiniteDirectImageBaseChangeHasExt (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) etaleFiniteDirectImageBaseChangeEnoughInjectives (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeGerms (evalAtLift_baseChangeOver)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleDirectImageGerms (evalAtLiftOver)
open PhilipponEtaleGeometricStalks
open PhilipponEtaleLocalRing (stalkRing)
open PhilipponEtalePullbackSquareUnits (restrictionBaseChangeOver)
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtaleStalkPullback (stalkPullbackIso)
open PhilipponEtaleStrictHenselization (toBase)


namespace PhilipponEtaleFiniteBaseChange

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

section Points

variable {K : Type u} [Field K] [IsAlgClosed K]

private abbrev stalk {X : Scheme.{u}} (s : Spec (.of K) ⟶ X) :=
  (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})

private abbrev Lifts {X Y : Scheme.{u}} (p : Y ⟶ X) (s : Spec (.of K) ⟶ X) :=
  {r : Spec (.of K) ⟶ Y // r ≫ p = s}

private abbrev evaluate {X Y : Scheme.{u}} (p : Y ⟶ X) (s : Spec (.of K) ⟶ X) (F : Ab Y)
    (x : (stalk s).obj ((pushforward p).obj F)) (r : Lifts p s) : (stalk r.val).obj F :=
  evalAtLiftOver p r.val s r.property F x

private theorem evaluate_bijective {X Y : Scheme.{u}} (p : Y ⟶ X) [IsFinite p]
    (s : Spec (.of K) ⟶ X) (F : Ab Y) : Function.Bijective (evaluate p s F) := by
  let q := pullback.fst (toBase s) p
  let : IsFinite q := inferInstanceAs (IsFinite (pullback.fst (toBase s) p))
  obtain ⟨I, _, B, hB, hH, hSep, c, hClosed⟩ :=
    Scheme.exists_finite_coproduct_strictlyHenselian_of_finite (stalkRing s) q
  let : ∀ i, CommRing (B i) := hB
  let : ∀ i, HenselianLocalRing (B i) := hH
  let : ∀ i, IsSepClosed (IsLocalRing.ResidueField (B i)) := hSep
  constructor
  · intro x y he
    exact PhilipponFiniteStalkEvaluation.ext_of_evaluations_equal s p B c hClosed F
      (fun r hr => congrFun he ⟨r, hr⟩)
  · intro z
    obtain ⟨x, hx⟩ := PhilipponFiniteStalkEvaluation.exists_of_evaluations s p B c hClosed F
      (fun r hr => z ⟨r, hr⟩)
    exact ⟨x, funext fun r => hx r.val r.property⟩

variable {X S Y W : Scheme.{u}} (f : S ⟶ X) (p : Y ⟶ X) (j : W ⟶ S) (b : W ⟶ Y)

private abbrev comparison (h : IsPullback j b f p) (F : Ab Y) :=
  restrictionBaseChangeOver f p j b (j ≫ f) rfl h.w.symm F

private def liftEquiv (h : IsPullback j b f p) (s : Spec (.of K) ⟶ S) :
    Lifts j s ≃ Lifts p (s ≫ f) where
  toFun r := ⟨r.val ≫ b, by rw [Category.assoc, ← h.w, ← Category.assoc, r.property]⟩
  invFun r := ⟨h.lift s r.val r.property.symm, h.lift_fst _ _ _⟩
  left_inv r := by
    apply Subtype.ext
    apply h.hom_ext
    · exact (h.lift_fst _ _ _).trans r.property.symm
    · exact h.lift_snd _ _ _
  right_inv r := Subtype.ext (h.lift_snd _ _ _)

private theorem evaluate_comparison (h : IsPullback j b f p) (F : Ab Y)
    (s : Spec (.of K) ⟶ S) (v : Lifts j s)
    (x : (stalk s).obj ((pullbackSheaves f).obj ((pushforward p).obj F))) :
    (stalkPullbackIso b v.val).hom.app F
        (evaluate j s ((pullbackSheaves b).obj F) ((stalk s).map (comparison f p j b h F) x) v) =
      evaluate p (s ≫ f) F ((stalkPullbackIso f s).hom.app ((pushforward p).obj F) x)
        (liftEquiv f p j b h s v) := by
  obtain ⟨v, hv⟩ := v
  subst s
  have hn := evalAtLift_baseChangeOver f p j b (j ≫ f) rfl h.w.symm v F
  have he := ConcreteCategory.congr_hom hn x
  simp only [evaluate, liftEquiv, Equiv.coe_fn_mk, comparison, stalk, evalAtLiftOver,
    eqToHom_refl, Category.id_comp, ConcreteCategory.comp_apply] at he ⊢
  exact he

private theorem isIso_stalk_comparison [IsFinite p] (h : IsPullback j b f p)
    (F : Ab Y) (s : Spec (.of K) ⟶ S) :
    IsIso ((stalk s).map (comparison f p j b h F)) := by
  let e := liftEquiv f p j b h s
  let G := (pullbackSheaves b).obj F
  let m := (stalk s).map (comparison f p j b h F)
  let e₀ := (stalkPullbackIso f s).app ((pushforward p).obj F)
  let reindex := Equiv.piCongrLeft' (fun r : Lifts p (s ≫ f) => ↥((stalk r.val).obj F)) e.symm
  let changeStalks := Equiv.piCongrRight
    (fun v : Lifts j s => ((stalkPullbackIso b v.val).app F).addCommGroupIsoToAddEquiv.toEquiv)
  let L := changeStalks ∘ evaluate j s G
  let R := reindex ∘ evaluate p (s ≫ f) F ∘ e₀.hom
  let : IsFinite j := MorphismProperty.of_isPullback h.flip inferInstance
  have hL : Function.Bijective L := changeStalks.bijective.comp (evaluate_bijective j s G)
  have hR : Function.Bijective R := reindex.bijective.comp
    ((evaluate_bijective p (s ≫ f) F).comp (ConcreteCategory.bijective_of_isIso e₀.hom))
  have hEq : L ∘ m = R := by
    funext x v
    exact evaluate_comparison f p j b h F s v x
  apply (ConcreteCategory.isIso_iff_bijective m).mpr
  exact (Function.Bijective.of_comp_iff' hL m).mp (hEq.symm ▸ hR)

end Points

/-- On abelian étale sheaves, direct image by a finite morphism commutes
with arbitrary base change via the canonical base-change morphism. -/
theorem isIso_comparison {X S Y W : Scheme.{u}} (f : S ⟶ X) (p : Y ⟶ X) [IsFinite p]
    (j : W ⟶ S) (b : W ⟶ Y) (h : IsPullback j b f p) (F : Ab Y) :
    IsIso (comparison f p j b h F) := by
  let P := ObjectProperty.ofObj fun x : S => Scheme.pointSmallEtale (algebraicallyClosedGeometricMap x)
  have hP : P.IsConservativeFamilyOfPoints := algebraicallyClosedGeometricPoints_conservative S
  apply ((hP.jointlyReflectIsomorphisms AddCommGrpCat.{u}).isIso_iff _).mpr
  intro Φ
  obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ _).mp Φ.property
  rw [← hx]
  exact isIso_stalk_comparison f p j b h F (algebraicallyClosedGeometricMap x)

end PhilipponEtaleFiniteBaseChange

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


