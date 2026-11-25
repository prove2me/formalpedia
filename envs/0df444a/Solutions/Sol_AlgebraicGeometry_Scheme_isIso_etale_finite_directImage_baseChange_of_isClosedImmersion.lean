-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.isIso_etale_finite_directImage_baseChange_of_isClosedImmersion
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-25T00:31:12.184325+00:00
-- url     : https://prove2.me/submissions/4bb54134-d4c5-4794-8ce3-998548501d7d

import Definitions.Def_AlgebraicGeometry_EtaleFiniteStalkEvaluation
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_coproduct_strictlyHenselian_of_finite

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeMap (pushforwardCompIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleDirectImageGerms
open PhilipponEtalePullbackComposition (pullbackCompIso unit_comp)
open PhilipponEtalePullbackSquareUnits
  (restrictionBaseChangeOver)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStalkPullback (stalkPullbackIso)


namespace PhilipponEtaleBaseChangeGerms

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

variable {K : Type u} [Field K] [IsSepClosed K]

private abbrev stalk {X : Scheme.{u}} (s : Spec (.of K) ⟶ X) :=
  (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})

@[reassoc]
theorem evalAtLiftOver_naturality {X Y : Scheme.{u}} (p : Y ⟶ X) (v : Spec (.of K) ⟶ Y)
    (s : Spec (.of K) ⟶ X) (h : v ≫ p = s) {F G : Ab Y} (a : F ⟶ G) :
    (stalk s).map ((pushforward p).map a) ≫ evalAtLiftOver p v s h G =
      evalAtLiftOver p v s h F ≫ (stalk v).map a := by
  subst s
  simpa only [evalAtLiftOver, eqToHom_refl, Category.id_comp] using evalAtLift_naturality p v a

end PhilipponEtaleBaseChangeGerms

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

end PhilipponFiniteEtaleStalks

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeGerms (evalAtLiftOver_naturality)
open PhilipponEtaleClosedPushforward (fullyFaithfulPushforward pushforward)
open PhilipponEtaleDirectImageGerms (evalAtLiftOver)
open PhilipponEtaleGeometricStalks (algebraicallyClosedGeometricMap algebraicallyClosedGeometricPoints_conservative)
open PhilipponEtalePullbackSquareUnits (restrictionBaseChangeOver)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStalkPullback (stalkPullbackIso stalk_unit_isIso unit_epi_of_isClosedImmersion)
open PhilipponEtaleStrictHenselization (toBase)
open PhilipponFiniteEtaleStalks (epi_directImageStalk)
open PhilipponFiniteStalkEvaluation (ext_of_evaluations_equal)


namespace PhilipponEtaleFiniteClosedBaseChange

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private abbrev stalk {K : Type u} [Field K] [IsSepClosed K] {X : Scheme.{u}}
    (s : Spec (.of K) ⟶ X) := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})

set_option maxHeartbeats 1200000 in
/-- An epimorphism inducing isomorphisms at the lifts of a geometric point
induces an isomorphism on the stalk of a finite direct image. -/
theorem isIso_stalk_directImage_of_lifts {X Y : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (s : Spec (.of K) ⟶ X) (p : Y ⟶ X) [IsFinite p]
    {I : Type u} (B : I → Type u) [∀ i, CommRing (B i)] [∀ i, HenselianLocalRing (B i)]
    [∀ i, IsSepClosed (IsLocalRing.ResidueField (B i))]
    (c : (∐ fun i ↦ Spec (.of (B i))) ≅ pullback (toBase s) p)
    (hClosed : ∀ i, IsClosedImmersion (Sigma.ι (fun j ↦ Spec (.of (B j))) i ≫ c.hom))
    {F G : Ab Y} (a : F ⟶ G) [Epi a]
    (hLift : ∀ (r : Spec (.of K) ⟶ Y), r ≫ p = s → IsIso ((stalk r).map a)) :
    IsIso ((stalk s).map ((pushforward p).map a)) := by
  let b := (stalk s).map ((pushforward p).map a)
  have hEpi : Epi b := epi_directImageStalk s p B c a
  apply (ConcreteCategory.isIso_iff_bijective b).mpr
  refine ⟨?_, (AddCommGrpCat.epi_iff_surjective b).mp hEpi⟩
  intro x y hxy
  apply ext_of_evaluations_equal s p B c hClosed F
  intro r hr
  let _ := hLift r hr
  apply (ConcreteCategory.bijective_of_isIso ((stalk r).map a)).injective
  let e := evalAtLiftOver p r s hr G
  have hn := evalAtLiftOver_naturality p r s hr a
  exact (ConcreteCategory.congr_hom hn x).symm.trans
    ((congrArg (fun t => e t) hxy).trans (ConcreteCategory.congr_hom hn y))

set_option maxHeartbeats 1200000 in
/-- Canonical étale base change for a finite direct image along a closed
immersion follows from the strict-local component decomposition. -/
theorem isIso_finite_baseChange_along_closed_immersion
    {X Z Y W : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (p : Y ⟶ X) [IsFinite p] (p₀ : W ⟶ Z) (j : W ⟶ Y) (h : IsPullback p₀ j i p)
    (hSplit : ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ X),
      ∃ (I : Type u) (B : I → Type u) (_ : ∀ k, CommRing (B k))
        (hH : ∀ k, HenselianLocalRing (B k)),
        (∀ k, let _ := hH k; IsSepClosed (IsLocalRing.ResidueField (B k))) ∧
          ∃ c : (∐ fun k ↦ Spec (.of (B k))) ≅ pullback (toBase s) p,
            ∀ k, IsClosedImmersion (Sigma.ι (fun l ↦ Spec (.of (B l))) k ≫ c.hom))
    (F : Ab Y) : IsIso (restrictionBaseChangeOver i p p₀ j (p₀ ≫ i) rfl h.w.symm F) := by
  let : IsClosedImmersion j := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h inferInstance
  let η := (pullbackAdjunction j).unit.app F
  let : Epi η := unit_epi_of_isClosedImmersion j F
  let b := (pushforward p).map η
  have hb : IsIso ((pullbackSheaves i).map b) := by
    let Q := ObjectProperty.ofObj fun x : Z => Scheme.pointSmallEtale (algebraicallyClosedGeometricMap x)
    have hQ : Q.IsConservativeFamilyOfPoints := algebraicallyClosedGeometricPoints_conservative Z
    apply ((hQ.jointlyReflectIsomorphisms AddCommGrpCat.{u}).isIso_iff _).mpr
    intro Φ
    obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ _).mp Φ.property
    rw [← hx]
    let K := AlgebraicClosure (Z.residueField x)
    let s := algebraicallyClosedGeometricMap x
    apply (NatIso.isIso_map_iff (stalkPullbackIso i s) b).mpr
    obtain ⟨I, B, hB, hH, hSep, c, hClosed⟩ := hSplit K (s ≫ i)
    let _ : ∀ k, CommRing (B k) := hB
    let _ : ∀ k, HenselianLocalRing (B k) := hH
    let _ : ∀ k, IsSepClosed (IsLocalRing.ResidueField (B k)) := hSep
    apply isIso_stalk_directImage_of_lifts (s ≫ i) p B c hClosed η
    intro r hr
    let w := h.lift s r hr.symm
    have hw : w ≫ j = r := h.lift_snd _ _ _
    rw [← hw]
    exact stalk_unit_isIso j w F
  let ff := fullyFaithfulPushforward i
  let : (pushforward i).Full := ff.full
  let : (pushforward i).Faithful := ff.faithful
  unfold restrictionBaseChangeOver
  rw [(pullbackAdjunction i).homEquiv_counit, Functor.map_comp]
  infer_instance

end PhilipponEtaleFiniteClosedBaseChange

end

open PhilipponEtalePullbackSquareUnits (restrictionBaseChangeOver)
open PhilipponEtaleLocalRing (stalkRing)
open PhilipponEtaleStrictHenselization (toBase)

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    {X Z Y W : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (p : Y ⟶ X) [IsFinite p] (p₀ : W ⟶ Z) (j : W ⟶ Y) (h : IsPullback p₀ j i p)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso (restrictionBaseChangeOver i p p₀ j (p₀ ≫ i) rfl h.w.symm F) := by
  apply PhilipponEtaleFiniteClosedBaseChange.isIso_finite_baseChange_along_closed_immersion
    i p p₀ j h _ F
  intro K _ _ s
  let R : Type u := stalkRing s
  let hR : HenselianLocalRing R := PhilipponEtaleHenselianStalk.henselianLocalRing s
  let _ := hR
  let hResidue : IsSepClosed (IsLocalRing.ResidueField R) :=
    PhilipponEtaleHenselianStalk.residueFieldIsSepClosed s
  let q := pullback.fst (toBase s) p
  have hq : IsFinite q := inferInstanceAs (IsFinite (pullback.fst (toBase s) p))
  obtain ⟨I, _, B, hB, hH, hSep, e, he⟩ :=
    @AlgebraicGeometry.Scheme.exists_finite_coproduct_strictlyHenselian_of_finite R _ hR hResidue _ q hq
  exact ⟨I, B, hB, hH, hSep, e, he⟩

end
