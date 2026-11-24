-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleHenselianNeighborhoodAcyclicity
-- name    : AlgebraicGeometry_EtaleHenselianNeighborhoodAcyclicity
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-24T23:22:58.170254+00:00
-- url     : https://prove2.me/theorems/48bf6c3c-1232-40b6-bfce-bb7b045abd32
-- title:
--   Acyclicity of injective module sheaves on an affine henselization
-- statement:
--   For a closed subscheme of an affine scheme, the inverse image of the underlying abelian sheaf of an injective étale module sheaf is acyclic on the affine henselization. The proof uses Čech exactness on covers descended to affine étale neighborhoods.
-- source:
--   Stacks Project, Theorem 59.51.3, https://stacks.math.columbia.edu/tag/09YQ.

import Definitions.Def_AlgebraicGeometry_AffineHenselianNeighborhoods
import Definitions.Def_AlgebraicGeometry_EtaleModuleCechExactness

set_option maxHeartbeats 1600000

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCech
open PhilipponEtaleBaseChangeComparison (baseChange map_isPullback)
open PhilipponEtaleNeighborhoodRestriction (restrict)
open PhilipponEtaleSmallSite (pullbackSheaves pullbackAdjunction)
open PhilipponEtaleModeledGluing (qcqsCharts stageSectionIso)
open PhilipponEtaleModeledSections PhilipponEtaleRefinementGluing
open PhilipponEtaleModeledInverseImage (inverseImageIsPointwiseOnModeledChart)
open PhilipponEtaleModeledCoverArrow (singleton_cover_of_surjective)


namespace PhilipponEtaleModeledCech

universe u

variable {I : Type u} [Category.{u} I] {Y : Scheme.{u}} (E : I ⥤ Y.Etale)

private abbrev D := E ⋙ Scheme.Etale.forget Y ⋙ Over.forget Y

/-- Positive-degree Čech exactness after restriction along an étale map. -/
def RestrictionCechExact (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) : Prop :=
  ∀ {X : Scheme.{u}} (b : X ⟶ Y) [Etale b] {U V : X.Etale} (a : V ⟶ U),
    Sieve.generate (Presieve.singleton a) ∈ X.smallEtaleTopology U →
    ∀ n, Function.Exact (sectionCechD a X.smallEtaleTopology ((restrict b).obj F) n)
      (sectionCechD a X.smallEtaleTopology ((restrict b).obj F) (n + 1))

theorem restrictionCechExact_of_injective (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    [Injective F] : RestrictionCechExact F := by
  intro X b hb U V a hcover n
  let : Injective ((restrict b).obj F) := (restrict b).injective_obj_of_injective inferInstance
  exact sectionCechD_exact_of_injective a X.smallEtaleTopology hcover ((restrict b).obj F) n

variable {i : I} {U V : ((D E).obj i).Etale} (a : V ⟶ U)
  (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})

private theorem stageCech_exact_at (hF : RestrictionCechExact F) [Surjective a.left]
    (j : (Over i)ᵒᵖ) (n : ℕ) :
    (cofaceShortComplex (cechSections a (chartStageSections E i F.obj) ⋙ (evaluation _ _).obj j) n).Exact := by
  let X := (D E).obj j.unop.left
  let r := (D E).map j.unop.hom
  let b := (E.obj j.unop.left).hom
  let B := baseChange r
  let F' := (restrict b).obj F
  let j' := j.unop
  let e₁ : chartStageSections E i F.obj ⋙ (evaluation _ _).obj j ≅ B.op ⋙ F'.obj :=
    Functor.isoWhiskerRight (NatIso.op (chartAtStageIso E j').symm) F.obj
  let : PreservesFiniteLimits B := inferInstanceAs
    (PreservesFiniteLimits (MorphismProperty.Over.pullback (@Etale) ⊤ r))
  let e := cechNerveMapIso B a
  let e₂ : (Arrow.mk a).cechNerve.rightOp ⋙ B.op ≅ (Arrow.mk (B.map a)).cechNerve.rightOp :=
    (Functor.leftOpRightOpEquiv SimplexCategory X.Etale).functor.mapIso (Iso.op e.symm)
  let eqSections : cechSections a (chartStageSections E i F.obj) ⋙ (evaluation _ _).obj j ≅
      cechSections (B.map a) F'.obj :=
    Functor.isoWhiskerLeft (Arrow.mk a).cechNerve.rightOp e₁ ≪≫ Functor.isoWhiskerRight e₂ F'.obj
  let hsurj : Surjective (B.map a).left :=
    MorphismProperty.of_isPullback (P := @Surjective) (map_isPullback r a) inferInstance
  have hcover := singleton_cover_of_surjective (B.map a) hsurj.surj
  have h := (cofaceShortComplex_cech_exact_iff (B.map a) X.smallEtaleTopology F' n).mpr
    (hF b (B.map a) hcover n)
  exact ShortComplex.exact_of_iso (cofaceShortComplexIso eqSections n).symm h

variable [IsCofiltered I] (c : Cone (D E)) (hc : IsLimit c)
  [∀ {j k : I} (b : j ⟶ k), IsAffineHom ((D E).map b)]
  (p : c.pt ⟶ Y) (hp : ∀ j, c.π.app j ≫ (E.obj j).hom = p)

include hc hp in
/-- Čech exactness passes to modeled covers on the inverse limit. -/
theorem inverseImage_cech_exact_of_stage_exactness [Surjective a.left]
    (hF : RestrictionCechExact F) (hU : qcqsCharts ((D E).obj i) U)
    (hV : qcqsCharts ((D E).obj i) V) (n : ℕ) :
    Function.Exact
      (sectionCechD ((chartLimitFunctor E c i).map a) c.pt.smallEtaleTopology ((pullbackSheaves p).obj F) n)
      (sectionCechD ((chartLimitFunctor E c i).map a) c.pt.smallEtaleTopology ((pullbackSheaves p).obj F) (n + 1)) := by
  let N := (Arrow.mk a).cechNerve
  let M := qcqsCharts ((D E).obj i)
  let N' := M.lift N (qcqsCharts_cechNerve a hU hV)
  let K := chartLimitFunctor E c i
  let P := ((pullbackSheaves p).obj F).obj
  let η := ((pullbackAdjunction p).unit.app F).hom
  let e₁ : M.ι.op ⋙ (chartStageSections E i F.obj ⋙ colim) ≅ (M.ι ⋙ K).op ⋙ P :=
    stageSectionIso E c hc p hp F.obj P η (fun W =>
      inverseImageIsPointwiseOnModeledChart E c hc p hp F ((stageToModeled E c i).obj W))
  let e := cechNerveMapIso K a
  let e₂ : N.rightOp ⋙ K.op ≅ (Arrow.mk (K.map a)).cechNerve.rightOp :=
    (Functor.leftOpRightOpEquiv SimplexCategory c.pt.Etale).functor.mapIso (Iso.op e.symm)
  let isoSections : cechSections a (chartStageSections E i F.obj) ⋙ colim ≅ cechSections (K.map a) P :=
    Functor.isoWhiskerLeft N'.rightOp e₁ ≪≫ Functor.isoWhiskerRight e₂ P
  have hx := cofaceShortComplex_exact_colim (cechSections a (chartStageSections E i F.obj)) n
    (fun j => stageCech_exact_at E a F hF j n)
  apply (cofaceShortComplex_cech_exact_iff (K.map a) c.pt.smallEtaleTopology ((pullbackSheaves p).obj F) n).mp
  exact ShortComplex.exact_of_iso (cofaceShortComplexIso isoSections n) hx

end PhilipponEtaleModeledCech

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
open PhilipponCech
open PhilipponEtaleModeledGluing (qcqsCharts)
open PhilipponEtaleModeledSections (chartLimitFunctor)
open PhilipponEtaleModeledCech (RestrictionCechExact restrictionCechExact_of_injective
  inverseImage_cech_exact_of_stage_exactness)
open PhilipponEtaleModeledCoverArrow (exists_modeled_covering_arrow_refinement)
open PhilipponEtaleRefinementGluing (qcqsCharts_cechNerve modeledCharts)
open PhilipponEtaleSmallSite (pullbackSheaves)


namespace PhilipponEtaleModeledAcyclicity

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {Y : Scheme.{u}} (E : I ⥤ Y.Etale)

private abbrev D := E ⋙ Scheme.Etale.forget Y ⋙ Over.forget Y

variable (c : Cone (D E)) (hc : IsLimit c)
  [∀ {j k : I} (b : j ⟶ k), IsAffineHom ((D E).map b)]
  (p : c.pt ⟶ Y) (hp : ∀ j, c.π.app j ≫ (E.obj j).hom = p)
  (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})

private abbrev P {X Z : Scheme.{u}} (f : X ⟶ Z)
    (T : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) := (pullbackSheaves f).obj T

include hc hp in
/-- Stagewise Čech exactness gives acyclicity on the modeled qcqs charts. -/
theorem inverseImage_acyclic_on_modeled_of_stage_exactness (hF : RestrictionCechExact F) (q : ℕ) :
    ∀ (i : I) (U : ((D E).obj i).Etale), qcqsCharts ((D E).obj i) U →
      Subsingleton ((P p F).H' (q + 1) ((chartLimitFunctor E c i).obj U)) := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
      intro i U hU
      let X := c.pt
      let J := X.smallEtaleTopology
      let P' := P p F
      let A := (chartLimitFunctor E c i).obj U
      let Cq := P'.cohomologyPresheaf (q + 1)
      let : CompactSpace ((𝟭 Scheme.{u}).obj U.left) := hU.1
      let : IsAffineHom (c.π.app i) := AlgebraicGeometry.isAffineHom_π_app (D E) c hc i
      let : CompactSpace A.left := inferInstanceAs (CompactSpace ↥(pullback (c.π.app i) U.hom))
      refine subsingleton_of_forall_eq 0 (fun x => ?_)
      obtain ⟨B, a, hB, ha, hx⟩ := Scheme.exists_surjective_affine_arrow_killing_class A P' q x
      obtain ⟨j, T, V, e, b, g, hT, hV, hb, hcover, hfac⟩ :=
        exists_modeled_covering_arrow_refinement E c hc hU a ha
      let : Surjective b.left := ⟨hb⟩
      let : IsAffine V.left := hV
      let hV' : qcqsCharts ((D E).obj j) V := ⟨inferInstance, inferInstance⟩
      let K := chartLimitFunctor E c j
      let x' := Cq.map e.inv.op x
      have hx' : Cq.map (K.map b).op x' = 0 := by
        change Cq.map (K.map b).op (Cq.map e.inv.op x) = 0
        rw [← ConcreteCategory.comp_apply, ← Cq.map_comp, ← op_comp, ← hfac,
          op_comp, Cq.map_comp, ConcreteCategory.comp_apply, hx, map_zero]
      have hz : x' = 0 := by
        apply class_eq_zero_of_cech_exact (K.map b) J hcover P' q ?_
          (inverseImage_cech_exact_of_stage_exactness E b F c hc p hp hF hT hV') x' hx'
        intro m k hk hle
        cases k with
        | zero => exact (Nat.not_lt_zero _ hk).elim
        | succ k =>
          let W := (Arrow.mk b).cechNerve.obj (op ⦋m⦌)
          let L := P'.cohomologyPresheaf (k + 1)
          let : Subsingleton ↥(L.obj (op (K.obj W))) :=
            ih k (Nat.lt_of_succ_le hle) j W (qcqsCharts_cechNerve b hT hV' (op ⦋m⦌))
          let e' : K.obj W ≅ (Arrow.mk (K.map b)).cechNerve.obj (op ⦋m⦌) :=
            (cechNerveMapIso K b).app (op ⦋m⦌)
          let d := (P'.cohomologyPresheaf (k + 1)).mapIso e'.op
          exact d.addCommGroupIsoToAddEquiv.injective.subsingleton
      let d : Cq.obj (op A) ≅ Cq.obj (op (K.obj T)) := Cq.mapIso e.symm.op
      have he : x' = Cq.map e.inv.op 0 := hz.trans (map_zero _).symm
      exact d.addCommGroupIsoToAddEquiv.injective he

include hc hp in
/-- Stagewise Čech exactness and a model of the terminal chart give
acyclicity for global sections on the limit. -/
theorem inverseImage_acyclic_of_modeled_terminal_of_stage_exactness (hF : RestrictionCechExact F)
    (hT : modeledCharts E c (Scheme.Etale.mk (𝟙 c.pt))) (q : ℕ) :
    Subsingleton ((P p F).H (q + 1)) := by
  let T := Scheme.Etale.mk (𝟙 c.pt)
  obtain ⟨i, U, hU, ⟨e⟩⟩ := hT
  let L := (P p F).cohomologyPresheaf (q + 1)
  let : Subsingleton ↥(L.obj (op ((chartLimitFunctor E c i).obj U))) :=
    inverseImage_acyclic_on_modeled_of_stage_exactness E c hc p hp F hF q i U hU
  let d := (L.mapIso e.symm.op).addCommGroupIsoToAddEquiv
  let hTerminal : IsTerminal T := IsTerminal.isTerminalOfObj (Scheme.Etale.forget c.pt) _ Over.mkIdTerminal
  let eT := PhilipponSheafCohomology.terminalComparison c.pt.smallEtaleTopology hTerminal (P p F) (q + 1)
  exact (eT.trans d).injective.subsingleton

end PhilipponEtaleModeledAcyclicity

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtaleModuleSkyscrapers (underlying)
open PhilipponEtaleModeledCech (RestrictionCechExact)
open PhilipponModuleEtaleNeighborhoodRestriction (along restriction_preservesInjectiveObjects)
open PhilipponEtaleRefinementGluing (modeledCharts)
open PhilipponEtaleModeledSections (chartLimitFunctor)
open PhilipponHenselianPairNeighborhoods


namespace PhilipponHenselianNeighborhoodAcyclicity

universe u

private theorem restrictionCechExact_underlying {Y : Scheme.{u}} {R : Type u} [Ring R]
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) [Injective J] :
    RestrictionCechExact (underlying.obj J) := by
  intro X b hb U V a h n
  let L := (along b).sheafPushforwardContinuous (ModuleCat.{u} R) X.smallEtaleTopology Y.smallEtaleTopology
  let : L.PreservesInjectiveObjects := restriction_preservesInjectiveObjects b
  let : Injective (L.obj J) := L.injective_obj_of_injective inferInstance
  exact PhilipponEtaleModuleCech.sectionCechD_exact a h (L.obj J) n

/-- Pulling an injective module sheaf back along the affine henselization
map gives an acyclic underlying abelian sheaf. -/
theorem subsingleton_H_toBase {X Z : Scheme.{u}} [IsAffine X]
    (i : Z ⟶ X) [IsClosedImmersion i] {R : Type u} [Ring R]
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) [Injective J] (q : ℕ) :
    Subsingleton (((pullbackSheaves (toBase i)).obj (underlying.obj J)).H (q + 1)) := by
  let F := InitiallySmall.fromCofilteredInitialModel.{u} (ExactAffinePointed i)
  let E := F ⋙ exactInclusion i ⋙ (IsAffinePointed i).ι ⋙
    CategoryOfElements.π (Scheme.Etale.forget X ⋙ coyoneda.obj (Opposite.op (Over.mk i)))
  let D := E ⋙ Scheme.Etale.forget X ⋙ Over.forget X
  let L := limitCone i
  let c : Cone D := L.cone.whisker F
  let hc : IsLimit c := (Functor.Initial.isLimitWhiskerEquiv F L.cone).symm L.isLimit
  let instAffine (j : _) : IsAffine (D.obj j) := inferInstanceAs
    (IsAffine ((schemes i).obj (F.obj j)))
  let : ∀ {j k : _} (b : j ⟶ k), IsAffineHom (D.map b) := by
    intro j k b
    let : IsAffine (D.obj j) := instAffine j
    let : IsAffine (D.obj k) := instAffine k
    infer_instance
  let p := toBase i
  have hp (j : _) : c.π.app j ≫ (E.obj j).hom = p := projection_toBase i (F.obj j)
  have hT : modeledCharts E c (Scheme.Etale.mk (𝟙 c.pt)) := by
    classical
    let j := Classical.choice (IsCofiltered.nonempty (C := InitiallySmall.CofilteredInitialModel.{u}
      (ExactAffinePointed i)))
    let V := Scheme.Etale.mk (𝟙 (D.obj j))
    let f := pullback.fst (c.π.app j) (𝟙 (D.obj j))
    let e : Scheme.Etale.mk (𝟙 c.pt) ≅ (chartLimitFunctor E c j).obj V :=
      MorphismProperty.Over.isoMk (asIso f).symm (IsIso.inv_hom_id f)
    let : IsAffine (D.obj j) := instAffine j
    exact ⟨j, V, ⟨inferInstanceAs (CompactSpace (D.obj j)), inferInstanceAs (QuasiSeparatedSpace (D.obj j))⟩, ⟨e⟩⟩
  exact PhilipponEtaleModeledAcyclicity.inverseImage_acyclic_of_modeled_terminal_of_stage_exactness
    E c hc p hp (underlying.obj J) (restrictionCechExact_underlying J) hT q

end PhilipponHenselianNeighborhoodAcyclicity

end

end


