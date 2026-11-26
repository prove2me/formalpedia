-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleFiniteLiftEvaluation
-- name    : AlgebraicGeometry_EtaleFiniteLiftEvaluation
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-26T07:42:19.996907+00:00
-- url     : https://prove2.me/theorems/c6cb4133-09ca-449c-84f1-bcc8035ac9e4
-- title:
--   Étale geometric stalk evaluation under a finite morphism
-- statement:
--   For a finite morphism, evaluate a section germ at all lifts of the geometric point to recover the stalk of its direct image.
-- source:
--   Stacks Project, Section 59.83, https://stacks.math.columbia.edu/tag/03SB.

import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestriction
import Definitions.Def_AlgebraicGeometry_EtaleOpenCoefficientComparison
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

local instance (priority := 2000) etaleFiniteLiftEvaluationHasSheafify (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) etaleFiniteLiftEvaluationHasExt (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) etaleFiniteLiftEvaluationEnoughInjectives (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory


namespace PhilipponFiniteLocalGeometricPoint

universe u

/-- Over the closed point of a local ring with separably closed residue
field, a geometric lift into an integral local algebra is unique. -/
theorem eq_lifts_of_isIntegral {R B K : Type u} [CommRing R] [IsLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] [CommRing B] [IsLocalRing B] [Field K]
    (p : Spec (.of B) ⟶ Spec (.of R)) [IsIntegralHom p]
    (ι : IsLocalRing.ResidueField R →+* K) (t t' : Spec (.of K) ⟶ Spec (.of B))
    (h : t ≫ p = Spec.map (CommRingCat.ofHom (ι.comp (IsLocalRing.residue R))))
    (h' : t' ≫ p = Spec.map (CommRingCat.ofHom (ι.comp (IsLocalRing.residue R)))) :
    t = t' := by
  let r := Spec.preimage p
  let : Algebra R B := r.hom.toAlgebra
  have hr : IsIntegralHom (Spec.map r) := by rw [Spec.map_preimage]; infer_instance
  let : Algebra.IsIntegral R B := algebraMap_isIntegral_iff.mp (IsIntegralHom.SpecMap_iff.mp hr)
  let : IsLocalHom (algebraMap R B) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap R B)).out 4 0).mp
      (IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
        (R := R) (IsLocalRing.maximalIdeal B)))
  let : Algebra.IsIntegral R (IsLocalRing.ResidueField B) := Algebra.IsIntegral.trans B
  let : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField B) :=
    IsLocalRing.ResidueField.algebraOfIsIntegral
  let : IsScalarTower R (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField B) :=
    IsLocalRing.ResidueField.isScalarTowerOfIsIntegral
  let : Algebra.IsIntegral (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField B) :=
    Algebra.IsIntegral.tower_top (R := R)
  let : Algebra (IsLocalRing.ResidueField R) K := ι.toAlgebra
  have hker (f : B →+* K) (hf : f.comp (algebraMap R B) = ι.comp (IsLocalRing.residue R)) :
      RingHom.ker f = IsLocalRing.maximalIdeal B := by
    let : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
    have hm : (RingHom.ker f).comap (algebraMap R B) = IsLocalRing.maximalIdeal R := by
      change RingHom.ker (f.comp (algebraMap R B)) = IsLocalRing.maximalIdeal R
      rw [hf, RingHom.ker_comp_of_injective _ ι.injective, IsLocalRing.ker_residue]
    exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
      (RingHom.ker f) (hm.symm ▸ (inferInstance : (IsLocalRing.maximalIdeal R).IsMaximal)))
  let descend (f : B →+* K) (hf : f.comp (algebraMap R B) = ι.comp (IsLocalRing.residue R)) :
      IsLocalRing.ResidueField B →ₐ[IsLocalRing.ResidueField R] K :=
    { toRingHom := Ideal.Quotient.lift (IsLocalRing.maximalIdeal B) f
        (fun x hx => RingHom.mem_ker.mp ((hker f hf).symm ▸ hx))
      commutes' := by
        intro x
        obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective (R := R) x
        change f (algebraMap R B y) = ι (IsLocalRing.residue R y)
        exact DFunLike.congr_fun hf y }
  have toRing (a : Spec (.of K) ⟶ Spec (.of B))
      (ha : a ≫ p = Spec.map (CommRingCat.ofHom (ι.comp (IsLocalRing.residue R)))) :
      (Spec.preimage a).hom.comp (algebraMap R B) = ι.comp (IsLocalRing.residue R) := by
    change (Spec.preimage a).hom.comp (Spec.preimage p).hom = _
    have ha' := congrArg (fun m : Spec (.of K) ⟶ Spec (.of R) => (Spec.preimage m).hom) ha
    simpa only [Spec.preimage_comp, Spec.preimage_map, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
      using ha'
  have he : descend (Spec.preimage t).hom (toRing t h) =
      descend (Spec.preimage t').hom (toRing t' h') := Subsingleton.elim _ _
  have hEq : Spec.preimage t = Spec.preimage t' := by
    ext x
    exact congrArg (fun a : IsLocalRing.ResidueField B →ₐ[IsLocalRing.ResidueField R] K =>
      a (IsLocalRing.residue B x)) he
  exact (Spec.map_preimage t).symm.trans ((congrArg Spec.map hEq).trans (Spec.map_preimage t'))

end PhilipponFiniteLocalGeometricPoint

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleCoproductGerms (terminalGerms_bijective)
open PhilipponEtaleDirectImageGerms (evalAtLiftOver)
open PhilipponEtaleHenselianStalk (henselianLocalRing residueEmbedding residueFieldIsSepClosed)
open PhilipponEtaleLocalRing (evaluateGerm stalkRing)
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtaleStalkPullback (stalkPullbackIso)
open PhilipponEtaleStrictHenselization (evaluation_comp_toBase toBase)
open PhilipponStrictHenselianEtaleCohomology (terminalGerm)
open PhilipponStrictLocalFinitePoints (exists_closed_component_lift)
open PhilipponStrictLocalPresheaf
  (germ_of_stalkDirectImageIsoStrictLocalSections stalkDirectImageIsoStrictLocalSections)


namespace PhilipponFiniteStalkEvaluation

universe u

variable {X Y : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (s : Spec (.of K) ⟶ X) (p : Y ⟶ X) [IsFinite p]

private abbrev localTotal := pullback (toBase s) p
private abbrev projection := pullback.snd (toBase s) p

omit [IsFinite p] in
private theorem lift_to_base (r : Spec (.of K) ⟶ localTotal s p)
    (hr : r ≫ pullback.fst (toBase s) p = Spec.map (evaluateGerm s)) :
    (r ≫ projection s p) ≫ p = s := by
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, hr, evaluation_comp_toBase]

private theorem exists_center_lift {D : Type u} [CommRing D] [IsLocalRing D]
    (j : Spec (.of D) ⟶ localTotal s p) [IsClosedImmersion j] :
    ∃ q : Spec (.of K) ⟶ Spec (.of D),
      (q ≫ j) ≫ pullback.fst (toBase s) p = Spec.map (evaluateGerm s) ∧
        q default = IsLocalRing.closedPoint D := by
  obtain ⟨q, hq, hClosed⟩ := exists_closed_component_lift s p j
  refine ⟨q, ?_, hClosed⟩
  rw [Category.assoc, hq]
  exact (Spec.map_comp (CommRingCat.ofHom (IsLocalRing.residue (stalkRing s)))
    (CommRingCat.ofHom (residueEmbedding s))).symm

variable {I : Type u} (B : I → Type u) [∀ i, CommRing (B i)]
    [∀ i, HenselianLocalRing (B i)] [∀ i, IsSepClosed (IsLocalRing.ResidueField (B i))]

private abbrev spectrum (i : I) := Spec (.of (B i))
private abbrev inclusion (c : (∐ spectrum B) ≅ localTotal s p) (i : I) :=
  Sigma.ι (spectrum B) i ≫ c.hom

private theorem exists_representative (c : (∐ spectrum B) ≅ localTotal s p)
    (hClosed : ∀ i, IsClosedImmersion (inclusion s p B c i))
    (q : ∀ i, Spec (.of K) ⟶ spectrum B i)
    (hq : ∀ i, (q i ≫ inclusion s p B c i) ≫ pullback.fst (toBase s) p =
      Spec.map (evaluateGerm s))
    (r : Spec (.of K) ⟶ Y) (hr : r ≫ p = s) :
    ∃ i, r = (q i ≫ inclusion s p B c i) ≫ projection s p := by
  let u := pullback.lift (Spec.map (evaluateGerm s)) r ((evaluation_comp_toBase s).trans hr.symm)
  obtain ⟨⟨i, z⟩, hz⟩ := (sigmaMk (spectrum B)).surjective (c.inv (u default))
  let k := inclusion s p B c i
  let : IsClosedImmersion k := hClosed i
  have hRange : Set.range u ⊆ Set.range k := by
    rintro _ ⟨x, rfl⟩
    have hx : x = default := Subsingleton.elim _ _
    refine ⟨z, ?_⟩
    change c.hom (Sigma.ι (spectrum B) i z) = u x
    rw [hx, ← sigmaMk_mk, hz]
    have hc := congrArg (fun m : localTotal s p ⟶ localTotal s p => m (u default)) c.inv_hom_id
    exact hc
  let v := IsOpenImmersion.lift k u hRange
  have hv : v ≫ k = u := IsOpenImmersion.lift_fac k u hRange
  let f := k ≫ pullback.fst (toBase s) p
  let : IsFinite f := inferInstanceAs (IsFinite (k ≫ pullback.fst (toBase s) p))
  have he : Spec.map (evaluateGerm s) = Spec.map
      (CommRingCat.ofHom ((residueEmbedding s).comp (IsLocalRing.residue (stalkRing s)))) := rfl
  have hvf : v ≫ f = Spec.map (evaluateGerm s) := by
    change v ≫ k ≫ pullback.fst (toBase s) p = _
    rw [← Category.assoc, hv, pullback.lift_fst]
  have hqf : q i ≫ f = Spec.map (evaluateGerm s) :=
    (Category.assoc _ _ _).symm.trans (hq i)
  have hvq : v = q i := @PhilipponFiniteLocalGeometricPoint.eq_lifts_of_isIntegral
    (stalkRing s) (B i) K inferInstance (henselianLocalRing s).toIsLocalRing
    (residueFieldIsSepClosed s) inferInstance inferInstance inferInstance f inferInstance
    (residueEmbedding s) v (q i) (hvf.trans he) (hqf.trans he)
  refine ⟨i, ?_⟩
  change r = (q i ≫ k) ≫ pullback.snd (toBase s) p
  rw [← hvq, hv, pullback.lift_snd]

set_option maxRecDepth 4096 in
/-- Every family of values on the geometric lifts comes from a germ of the
finite direct image. The values are indexed by lifts over the same field. -/
theorem exists_of_evaluations (c : (∐ spectrum B) ≅ localTotal s p)
    (hClosed : ∀ i, IsClosedImmersion (inclusion s p B c i))
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (value : ∀ (r : Spec (.of K) ⟶ Y), r ≫ p = s →
      ((Scheme.pointSmallEtale r).sheafFiber (A := AddCommGrpCat.{u})).obj F) :
    ∃ x : ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})).obj ((pushforward p).obj F),
      ∀ (r : Spec (.of K) ⟶ Y) (hr : r ≫ p = s), evalAtLiftOver p r s hr F x = value r hr := by
  have hLift (i : I) := by
    let k := inclusion s p B c i
    let : IsClosedImmersion k := hClosed i
    exact exists_center_lift s p k
  choose q hqBase hqClosed using hLift
  let r (i : I) := q i ≫ inclusion s p B c i
  let h (i : I) := lift_to_base s p (r i) (hqBase i)
  let L := pullbackSheaves (projection s p)
  let e := stalkDirectImageIsoStrictLocalSections s p F
  let eᵢ (i : I) := (stalkPullbackIso (projection s p) (r i)).app F
  let b (i : I) := (eᵢ i).inv (value (r i ≫ projection s p) (h i))
  obtain ⟨t, ht⟩ := (terminalGerms_bijective B c q hqClosed (L.obj F)).2 b
  let x := e.inv t
  have hx : e.hom x = t := ConcreteCategory.congr_hom e.inv_hom_id t
  refine ⟨x, ?_⟩
  intro w hw
  obtain ⟨i, hi⟩ := exists_representative s p B c hClosed q hqBase w hw
  subst w
  have htᵢ : (terminalGerm (r i)).app (L.obj F) t = b i := congrFun ht i
  calc
    _ = (eᵢ i).hom ((terminalGerm (r i)).app (L.obj F) (e.hom x)) :=
      (ConcreteCategory.congr_hom
        (germ_of_stalkDirectImageIsoStrictLocalSections s p (r i) (hqBase i) (h i) F) x).symm
    _ = (eᵢ i).hom (b i) := congrArg ((eᵢ i).hom)
      ((congrArg ((terminalGerm (r i)).app (L.obj F)) hx).trans htᵢ)
    _ = _ := ConcreteCategory.congr_hom (eᵢ i).inv_hom_id _

set_option maxRecDepth 4096 in
/-- Evaluations at the lifts of an algebraically closed point jointly
detect equality in a finite direct-image stalk. -/
theorem ext_of_evaluations_equal (c : (∐ spectrum B) ≅ localTotal s p)
    (hClosed : ∀ i, IsClosedImmersion (inclusion s p B c i))
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    {a b : ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})).obj
      ((pushforward p).obj F)}
    (h : ∀ (r : Spec (.of K) ⟶ Y) (hr : r ≫ p = s),
      evalAtLiftOver p r s hr F a = evalAtLiftOver p r s hr F b) : a = b := by
  have hLift (i : I) := by
    let j := inclusion s p B c i
    let : IsClosedImmersion j := hClosed i
    exact exists_center_lift s p j
  choose q hqBase hqClosed using hLift
  let L := pullbackSheaves (projection s p)
  let e := stalkDirectImageIsoStrictLocalSections s p F
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  apply (terminalGerms_bijective B c q hqClosed (L.obj F)).1
  funext i
  let r := q i ≫ inclusion s p B c i
  have hr : r ≫ pullback.fst (toBase s) p = Spec.map (evaluateGerm s) := hqBase i
  let hs := lift_to_base s p r hr
  let η := (stalkPullbackIso (projection s p) r).hom.app F
  apply (ConcreteCategory.bijective_of_isIso η).1
  have hGerm := germ_of_stalkDirectImageIsoStrictLocalSections s p r hr hs F
  exact (ConcreteCategory.congr_hom hGerm a).trans
    ((h (r ≫ projection s p) hs).trans (ConcreteCategory.congr_hom hGerm b).symm)

/-- A finite surjection has a lift over an algebraically closed geometric
point when its strict-local pullback is given by the indicated components. -/
theorem exists_lift [Surjective p] (c : (∐ spectrum B) ≅ localTotal s p)
    (hClosed : ∀ i, IsClosedImmersion (inclusion s p B c i)) :
    ∃ r : Spec (.of K) ⟶ Y, r ≫ p = s := by
  obtain ⟨y, _⟩ := (pullback.fst (toBase s) p).surjective (IsLocalRing.closedPoint (stalkRing s))
  obtain ⟨⟨i, _⟩, _⟩ := (sigmaMk (spectrum B)).surjective (c.inv y)
  let j := inclusion s p B c i
  let : IsClosedImmersion j := hClosed i
  obtain ⟨q, hq, _⟩ := exists_center_lift s p j
  exact ⟨(q ≫ j) ≫ projection s p, lift_to_base s p (q ≫ j) hq⟩

end PhilipponFiniteStalkEvaluation

end


