-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleFiniteStalkEvaluation
-- name    : AlgebraicGeometry_EtaleFiniteStalkEvaluation
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-22T01:01:24.452378+00:00
-- url     : https://prove2.me/theorems/e051bb9e-62aa-420c-9b45-f2c5131310cd
-- title:
--   Evaluation on the finite components of a strict localization
-- statement:
--   Separatedness and lifting for the evaluations of an étale direct-image stalk on strictly henselian components.

import Definitions.Def_AlgebraicGeometry_EtaleStrictLocalSectionGerms

noncomputable section

section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleCoproductGerms (terminalGerms_bijective)
open PhilipponEtaleDirectImageGerms (evalAtLiftOver)
open PhilipponEtaleHenselianStalk (residueEmbedding)
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

end


