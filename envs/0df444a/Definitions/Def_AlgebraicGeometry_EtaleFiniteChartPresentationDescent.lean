-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleFiniteChartPresentationDescent
-- name    : AlgebraicGeometry_EtaleFiniteChartPresentationDescent
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-26T00:09:31.58127+00:00
-- url     : https://prove2.me/theorems/3229e7bb-0eab-413f-a696-a02f2c951bb9
-- title:
--   Descent of finite affine étale presentations
-- statement:
--   Finitely many affine étale charts, coefficients and relation maps descend together to one Noetherian affine stage.
-- source:
--   Stacks Project, 59.73.2 (https://stacks.math.columbia.edu/tag/03SA) and 59.74.4 (https://stacks.math.columbia.edu/tag/09Z7).

import Definitions.Def_AlgebraicGeometry_EtaleFinitePresentationModels
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.RingTheory.FiniteType

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleChartLimitDiagram (stageCharts toOriginal toOriginal_natural toLimitIso toLimitIso_hom)
open PhilipponEtaleLimitAffinePresheaf (AffineModel exists_affineModel)
open PhilipponEtaleStageMapDescent (exists_stage_factorization)
open PhilipponEtaleTotalStageSite (StageChart atStage atStage_toLimit toLimit)


namespace PhilipponEtaleFiniteChartDescent

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  {D : I ⥤ Scheme.{u}} [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)

include hc in
set_option maxHeartbeats 1500000 in
/-- Finitely many affine étale charts and finitely many maps between them
are represented simultaneously at a common stage of an affine inverse limit. -/
theorem exists_stage_of_finite_charts_and_maps (hI : Quiver.IsThin I)
    {B E : Type u} [Finite B] [Finite E] (U : B → c.pt.Etale)
    (hU : ∀ b, IsAffine (U b).left) (src tgt : E → B) (a : ∀ j, U (src j) ⟶ U (tgt j)) :
    ∃ (i : I) (V : B → (D.obj i).Etale) (v : ∀ j, V (src j) ⟶ V (tgt j))
      (e : ∀ b, (baseChange (c.π.app i)).obj (V b) ≅ U b),
      (∀ b, IsAffine (V b).left) ∧ ∀ j,
        (baseChange (c.π.app i)).map (v j) ≫ (e (tgt j)).hom = (e (src j)).hom ≫ a j := by
  classical
  let : Fintype B := Fintype.ofFinite B
  let : Fintype E := Fintype.ofFinite E
  let M (b : B) : AffineModel c (U b) :=
    let : IsAffine (U b).left := hU b
    (exists_affineModel c hc (U b)).some
  let A (b : B) := (M b).chart
  let h (j : E) : (toLimit c).obj (A (src j)) ⟶ (toLimit c).obj (A (tgt j)) :=
    (M (src j)).comparison.inv ≫ a j ≫ (M (tgt j)).comparison.hom
  let : ∀ b, IsAffine (A b).etale.left := fun b => (M b).affine
  choose k g hg using fun j => exists_stage_factorization c hc (A (src j)) (A (tgt j)) (h j)
  let O := (Finset.univ.image fun b => (A b).index) ∪ (Finset.univ.image fun j => (k j).left)
  obtain ⟨i, hi⟩ := IsCofiltered.inf_objs_exists O
  let p (b : B) : i ⟶ (A b).index :=
    (hi (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ b)))).some
  let q (j : E) : i ⟶ (k j).left :=
    (hi (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))).some
  let K (b : B) : Over (A b).index := Over.mk (p b)
  let Q (j : E) : K (src j) ⟶ k j := Over.homMk (q j) ((hI _ _).elim _ _)
  let V (b : B) : (D.obj i).Etale := ((stageCharts (A b)).obj (K b)).etale
  let F (j : E) : (stageCharts (A (src j))).obj (K (src j)) ⟶ A (tgt j) :=
    (stageCharts (A (src j))).map (Q j) ≫ g j
  have hw (j : E) : (V (src j)).hom ≫ D.map (p (tgt j)) = (F j).left ≫ (A (tgt j)).etale.hom := by
    have hIndex : (F j).indexMap = p (tgt j) := (hI _ _).elim _ _
    rw [(F j).over, hIndex]
  let v (j : E) : V (src j) ⟶ V (tgt j) :=
    MorphismProperty.Over.homMk (pullback.lift (V (src j)).hom (F j).left (hw j))
      (pullback.lift_fst ..) trivial
  have hv (j : E) : (atStage (D := D) i).map (v j) ≫ toOriginal (A (tgt j)) (K (tgt j)) = F j := by
    apply PhilipponEtaleTotalStageSite.StageHom.ext
    · exact (hI _ _).elim _ _
    · exact pullback.lift_snd ..
  let e (b : B) : (baseChange (c.π.app i)).obj (V b) ≅ U b :=
    toLimitIso (A b) c (K b) ≪≫ (M b).comparison.symm
  refine ⟨i, V, v, e, ?_, ?_⟩
  · intro b
    let f : D.obj i ⟶ D.obj (A b).index := D.map (p b)
    let g : (A b).etale.left ⟶ D.obj (A b).index := (A b).etale.hom
    let : IsAffine (A b).etale.left := (M b).affine
    let : IsAffineHom f := isAffineHom_of_isAffine _
    let : IsAffineHom (pullback.snd f g) :=
      MorphismProperty.pullback_snd f g (inferInstance : IsAffineHom f)
    exact isAffine_of_isAffineHom (pullback.snd f g)
  · intro j
    have hmap : (baseChange (c.π.app i)).map (v j) = (toLimit c).map ((atStage i).map (v j)) := by
      have hn := (atStage_toLimit c i).hom.naturality (v j)
      change (toLimit c).map ((atStage i).map (v j)) ≫ 𝟙 _ =
        𝟙 _ ≫ (baseChange (c.π.app i)).map (v j) at hn
      simpa only [Category.comp_id, Category.id_comp] using hn.symm
    have hF : (toLimit c).map (F j) = (toLimit c).map (toOriginal (A (src j)) (K (src j))) ≫ h j := by
      dsimp only [F]
      rw [Functor.map_comp, hg, ← Category.assoc, ← Functor.map_comp, toOriginal_natural]
    dsimp only [e, Iso.trans_hom, Iso.symm_hom]
    rw [hmap, toLimitIso_hom, toLimitIso_hom, ← Category.assoc, ← Functor.map_comp, hv, hF,
      Category.assoc]
    simp only [h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end PhilipponEtaleFiniteChartDescent

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators
open PhilipponFiniteModulePresheafPresentation (freeChart unitModule)


namespace PhilipponFinitePresheafRelations

universe u

variable (R : Type u) [Ring R] {C : Type u} [SmallCategory C]
  {B : Type u} (V : B → C) (U : C)

private abbrev rankOneGenerator : unitModule R := ModuleCat.freeMk PUnit.unit

private abbrev charts := fun i => freeChart R C (V i)

private abbrev basisIndex := Σ i, U ⟶ V i

private def basisMap (b : basisIndex V U) : unitModule R ⟶ (∐ charts R V).obj (op U) :=
  Sigma.ι (fun (_ : (yoneda.obj (V b.1)).obj (op U)) => unitModule R) b.2 ≫
    (Sigma.ι (charts R V) b.1).app (op U)

private def coefficients :
    (ModuleCat.free R).obj (basisIndex V U) ⟶ (∐ charts R V).obj (op U) :=
  ModuleCat.freeDesc (↾fun b => basisMap R V U b (rankOneGenerator R))

private theorem epi_coefficients : Epi (coefficients R V U) := by
  constructor
  intro Z g h he
  let L := (evaluation Cᵒᵖ (ModuleCat.{u} R)).obj (op U)
  have hc := isColimitOfPreserves L (colimit.isColimit (Discrete.functor (charts R V)))
  apply hc.hom_ext
  rintro ⟨i⟩
  change (Sigma.ι (charts R V) i).app (op U) ≫ g =
    (Sigma.ι (charts R V) i).app (op U) ≫ h
  apply Sigma.hom_ext
  intro a
  apply ModuleCat.free_hom_ext
  rintro ⟨⟩
  have hh := ConcreteCategory.congr_hom he
    (ModuleCat.freeMk (R := R) (X := basisIndex V U) ⟨i, a⟩)
  simpa [coefficients, basisMap, rankOneGenerator] using hh

/-- One term of a relation, given by an affine chart map and a coefficient.
The associated module map sends the distinguished generator to that
coefficient times the generator indexed by the chart map. -/
def chartTerm (i : B) (a : U ⟶ V i) (r : R) : freeChart R C U ⟶ ∐ charts R V :=
  Presheaf.freeYonedaHomEquiv.symm
    (ModuleCat.freeDesc (↾fun _ => r • rankOneGenerator R) ≫ basisMap R V U ⟨i, a⟩)

/-- Each term is an ordinary map of free representables followed by a
summand inclusion. -/
theorem chartTerm_eq (i : B) (a : U ⟶ V i) (r : R) :
    chartTerm R V U i a r = PhilipponFreeYonedaMaps.mapFreeYoneda a
      (ModuleCat.freeDesc (↾fun _ => r • rankOneGenerator R)) ≫ Sigma.ι (charts R V) i := by
  rw [chartTerm, PhilipponFreeYonedaMaps.mapFreeYoneda, Presheaf.freeYonedaHomEquiv_symm_comp]
  simp only [basisMap, Category.assoc]

private def value (f : freeChart R C U ⟶ ∐ charts R V) : (∐ charts R V).obj (op U) :=
  Presheaf.freeYonedaHomEquiv f (rankOneGenerator R)

private theorem value_injective : Function.Injective (value R V U) := by
  intro f g h
  apply Presheaf.freeYonedaHomEquiv.injective
  apply ModuleCat.free_hom_ext
  rintro ⟨⟩
  exact h

private def valueAddHom : (freeChart R C U ⟶ ∐ charts R V) →+ (∐ charts R V).obj (op U) where
  toFun := value R V U
  map_zero' := by simp [value, Presheaf.freeYonedaHomEquiv]
  map_add' f g := by simp [value, Presheaf.freeYonedaHomEquiv, Preadditive.comp_add]

private theorem value_chartTerm (b : basisIndex V U) (r : R) :
    value R V U (chartTerm R V U b.1 b.2 r) =
      coefficients R V U (Finsupp.single b r) := by
  have hsingle : (Finsupp.single b r : (ModuleCat.free R).obj (basisIndex V U)) =
      r • ModuleCat.freeMk (R := R) b := by
    change Finsupp.single b r = r • Finsupp.single b (1 : R)
    simp [Finsupp.smul_single]
  rw [hsingle]
  simp [value, chartTerm, coefficients, rankOneGenerator]

/-- Every map from a free representable into a sum of free representables
is a finitely supported linear combination of maps of the representing
objects, followed by the summand inclusions. -/
theorem exists_finite_chart_expansion (f : freeChart R C U ⟶ ∐ charts R V) :
    ∃ w : (Σ i, U ⟶ V i) →₀ R,
      f = ∑ b ∈ w.support, chartTerm R V U b.1 b.2 (w b) := by
  classical
  let : Epi (coefficients R V U) := epi_coefficients R V U
  obtain ⟨w, hw⟩ := (ModuleCat.epi_iff_surjective (coefficients R V U)).mp inferInstance
    (value R V U f)
  change (basisIndex V U →₀ R) at w
  refine ⟨w, value_injective R V U ?_⟩
  change value R V U f = (valueAddHom R V U) _
  rw [map_sum, ← hw]
  simp only [valueAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, value_chartTerm]
  have hsum := Finsupp.sum_single (α := basisIndex V U) w
  change (∑ b ∈ w.support, Finsupp.single b (w b)) = w at hsum
  exact (congrArg (coefficients R V U).hom hsum).symm.trans (map_sum _ _ _)

end PhilipponFinitePresheafRelations

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators


namespace PhilipponFiniteRelationTransport

universe u v w v' w'

variable {C : Type w} [Category.{v} C] [Preadditive C] [HasCoproducts.{u} C]
  {D : Type w'} [Category.{v'} D] [Preadditive D] [HasCoproducts.{u} D]
  {I J : Type u} {T : I → Type u} [∀ i, Fintype (T i)]
  {A : I → C} {B : J → C} {A' : I → D} {B' : J → D}

/-- The map from a coproduct of relations to a coproduct of generators,
with each relation a finite sum of maps to summands. -/
def relationMap (target : ∀ i, T i → J)
    (q : ∀ i (t : T i), A i ⟶ B (target i t)) : (∐ A) ⟶ (∐ B) :=
  Sigma.desc fun i => ∑ t : T i, q i t ≫ Sigma.ι B (target i t)

variable (F : C ⥤ D) [F.Additive] [PreservesColimitsOfSize.{u, u} F]

private def sumIso {K : Type u} {U : K → C} {V : K → D} (e : ∀ k, F.obj (U k) ≅ V k) :
    F.obj (∐ U) ≅ ∐ V := PreservesCoproduct.iso F U ≪≫ Sigma.mapIso e

omit [Preadditive C] [Preadditive D] [F.Additive] in
@[reassoc]
private theorem map_ι_sumIso_hom {K : Type u} {U : K → C} {V : K → D}
    (e : ∀ k, F.obj (U k) ≅ V k) (k : K) :
    F.map (Sigma.ι U k) ≫ (sumIso F e).hom = (e k).hom ≫ Sigma.ι V k := by
  have ha : (PreservesCoproduct.iso F U).hom = inv (sigmaComparison F U) := by
    exact IsIso.eq_inv_of_hom_inv_id (PreservesCoproduct.iso F U).inv_hom_id
  simp only [sumIso, Iso.trans_hom, ha, map_ι_comp_inv_sigmaComparison_assoc, Sigma.ι_mapIso_hom]

private theorem transport_relationMap (target : ∀ i, T i → J)
    (q : ∀ i (t : T i), A i ⟶ B (target i t))
    (q' : ∀ i (t : T i), A' i ⟶ B' (target i t))
    (e : ∀ i, F.obj (A i) ≅ A' i) (e' : ∀ j, F.obj (B j) ≅ B' j)
    (h : ∀ i (t : T i), F.map (q i t) ≫ (e' (target i t)).hom = (e i).hom ≫ q' i t) :
    F.map (relationMap target q) ≫ (sumIso F e').hom = (sumIso F e).hom ≫ relationMap target q' := by
  apply (isColimitOfHasCoproductOfPreservesColimit F A).hom_ext
  rintro ⟨i⟩
  change F.map (Sigma.ι A i) ≫ F.map (relationMap target q) ≫ (sumIso F e').hom =
    F.map (Sigma.ι A i) ≫ (sumIso F e).hom ≫ relationMap target q'
  rw [← F.map_comp_assoc, map_ι_sumIso_hom_assoc, relationMap, Sigma.ι_desc, relationMap,
    Sigma.ι_desc, F.map_sum]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Functor.map_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro t _
  rw [map_ι_sumIso_hom, ← Category.assoc, h, Category.assoc]

/-- An additive colimit-preserving functor transports an explicit finite
relation presentation whenever it transports the individual terms. -/
def cokernelIsoOfTerms (target : ∀ i, T i → J)
    (q : ∀ i (t : T i), A i ⟶ B (target i t))
    (q' : ∀ i (t : T i), A' i ⟶ B' (target i t))
    [HasCokernel (relationMap target q)] [HasCokernel (relationMap target q')]
    (e : ∀ i, F.obj (A i) ≅ A' i) (e' : ∀ j, F.obj (B j) ≅ B' j)
    (h : ∀ i (t : T i), F.map (q i t) ≫ (e' (target i t)).hom = (e i).hom ≫ q' i t)
    [PreservesColimitsOfShape WalkingParallelPair F] :
    F.obj (cokernel (relationMap target q)) ≅ cokernel (relationMap target q') :=
  PreservesCokernel.iso F (relationMap target q) ≪≫
    cokernel.mapIso _ _ (sumIso F e) (sumIso F e') (transport_relationMap F target q q' e e' h)

end PhilipponFiniteRelationTransport


namespace PhilipponFiniteRelationTransport

universe u v w x y

/-- A map out of a cokernel with finitely many generator summands
factors through a common filtered stage if each generator does and all
the stage maps to the target are monomorphisms. -/
theorem exists_factor_of_finite_generators {C : Type w} [Category.{v} C]
    [HasZeroMorphisms C] [HasCoproducts.{u} C] {B : Type u} [Finite B]
    (G : B → C) {R W : C} (d : R ⟶ ∐ G) [HasCokernel d] (f : cokernel d ⟶ W)
    {I : Type x} [Category.{y} I] [IsFiltered I] (Q : I → C)
    (m : ∀ i, Q i ⟶ W) (hm : ∀ i, Mono (m i))
    (t : ∀ {i j} (_ : i ⟶ j), Q i ⟶ Q j) (ht : ∀ {i j} (a : i ⟶ j), t a ≫ m j = m i)
    (hGen : ∀ b, ∃ (i : I) (g : G b ⟶ Q i), g ≫ m i = Sigma.ι G b ≫ cokernel.π d ≫ f) :
    ∃ (i : I) (g : cokernel d ⟶ Q i), g ≫ m i = f := by
  classical
  let : Fintype B := Fintype.ofFinite B
  choose i g hg using hGen
  obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (Finset.univ.image i)
  let a (b : B) : i b ⟶ j := (hj (Finset.mem_image_of_mem i (Finset.mem_univ b))).some
  let g' : (∐ G) ⟶ Q j := Sigma.desc fun b => g b ≫ t (a b)
  have hg' : g' ≫ m j = cokernel.π d ≫ f := by
    apply Sigma.hom_ext
    intro b
    rw [show Sigma.ι G b ≫ g' ≫ m j = (g b ≫ t (a b)) ≫ m j from Sigma.ι_desc_assoc ..,
      Category.assoc, ht, hg]
  let : Mono (m j) := hm j
  have hz : d ≫ g' = 0 := by
    apply (cancel_mono (m j)).mp
    rw [Category.assoc, hg', cokernel.condition_assoc, zero_comp, zero_comp]
  refine ⟨j, cokernel.desc d g' hz, (cancel_epi (cokernel.π d)).mp ?_⟩
  rw [cokernel.π_desc_assoc, hg']

end PhilipponFiniteRelationTransport

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 30000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators
open PhilipponFiniteModulePresheafPresentation
  (finitePresentations finitePresentations_iff_cokernelPresentation freeChart unitModule)
open PhilipponFinitePresheafRelations (chartTerm_eq exists_finite_chart_expansion)
open PhilipponFiniteRelationTransport (relationMap cokernelIsoOfTerms)
open PhilipponFreeYonedaMaps (mapFreeYoneda)
open PhilipponFreeEtaleSheaf (freeSheaf mapFreeSheaf freeSheafIsoOfChartIso
  freeSheafIsoOfChartIso_naturality)


namespace PhilipponEtaleFinitePresentations

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev SmallAffine (X : Scheme.{u}) := SmallModel.{u} X.AffineEtale
private abbrev R (N : ℕ) := ULift.{u} (ZMod N)
private abbrev affineChart (X : Scheme.{u}) (U : SmallAffine X) : X.Etale :=
  (affineChartFunctor X).obj U

private instance (priority := 1100) abColimits (X : Scheme.{u}) :
    HasColimitsOfSize.{u, u} (Ab X) := by
  have : HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u} := inferInstance
  have : HasColimitsOfSize.{u, u} AddCommGrpCat.{u} := inferInstance
  exact Sheaf.instHasColimitsOfSize (J := X.smallEtaleTopology) (D := AddCommGrpCat.{u})

private instance (priority := 1100) (X : Scheme.{u}) : HasCoproducts.{u} (Ab X) :=
  fun J => (abColimits X).has_colimits_of_shape (Discrete J)

private instance (X : Scheme.{u}) (N : ℕ) : PreservesColimitsOfSize.{u, u} (modelSheaf X N) := by
  let : PreservesColimitsOfSize.{u, u} (abCoefficients.{u} N) := by
    change PreservesColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u} (ULift.{u} (ZMod N))) AddCommGrpCat.{u})
    infer_instance
  let : PreservesColimitsOfSize.{u, u} (forgetCoefficients X N) :=
    whiskeringRightPreservesColimits (C := (SmallAffine X)ᵒᵖ) (abCoefficients.{u} N)
  change PreservesColimitsOfSize.{u, u} (forgetCoefficients X N ⋙
    presheafToSheaf (smallTopology X) AddCommGrpCat.{u} ⋙ (restrictEquivalence X).inverse)
  infer_instance

private instance (X : Scheme.{u}) (N : ℕ) : PreservesFiniteColimits (modelSheaf X N) := by
  let : PreservesColimitsOfSize.{0, 0} (modelSheaf X N) :=
    preservesColimitsOfSize_of_univLE.{u, u, 0, 0} (modelSheaf X N)
  exact ⟨fun _ => inferInstance⟩

private instance (X : Scheme.{u}) (N : ℕ) : (modelSheaf X N).Additive := by
  let L := modelSheaf X N
  let : L.PreservesZeroMorphisms := inferInstanceAs ((modelSheaf X N).PreservesZeroMorphisms)
  let : PreservesBinaryBiproducts L := preservesBinaryBiproducts_of_preservesBinaryCoproducts L
  exact Functor.additive_of_preservesBinaryBiproducts L

/-- A presentation specified by affine étale charts and finitely many
coefficient-weighted chart maps from each relation chart. -/
structure ChartPresentation (X : Scheme.{u}) (N : ℕ) where
  generators : Type u
  relations : Type u
  [finiteGenerators : Finite generators]
  [finiteRelations : Finite relations]
  generator : generators → X.Etale
  relation : relations → X.Etale
  affineGenerator : ∀ i, IsAffine (generator i).left
  affineRelation : ∀ i, IsAffine (relation i).left
  terms : relations → Type u
  [finiteTerms : ∀ i, Fintype (terms i)]
  target : ∀ i, terms i → generators
  chartMap : ∀ i (t : terms i), relation i ⟶ generator (target i t)
  coefficient : ∀ i, terms i → (unitModule (R.{u} N) ⟶ unitModule (R.{u} N))

attribute [instance] ChartPresentation.finiteGenerators ChartPresentation.finiteRelations
  ChartPresentation.finiteTerms

namespace ChartPresentation

variable {X : Scheme.{u}} {N : ℕ} (p : ChartPresentation X N)

/-- A term of the relation map after freely adjoining its coefficients. -/
def termMap (i : p.relations) (t : p.terms i) :
    freeSheaf (p.relation i) (generatorCoefficients N) ⟶
      freeSheaf (p.generator (p.target i t)) (generatorCoefficients N) :=
  mapFreeSheaf (p.chartMap i t) ((abCoefficients N).map (p.coefficient i t))

/-- The map from the direct sum of relation charts to the direct sum of
generator charts. -/
def differential : (∐ fun i => freeSheaf (p.relation i) (generatorCoefficients N)) ⟶
    (∐ fun j => freeSheaf (p.generator j) (generatorCoefficients N)) := relationMap
  (A := fun i => freeSheaf (p.relation i) (generatorCoefficients N))
  (B := fun j => freeSheaf (p.generator j) (generatorCoefficients N)) p.target p.termMap

/-- The associated abelian étale sheaf is the cokernel of the relations. -/
def sheaf : Ab X := cokernel p.differential

end ChartPresentation

private theorem exists_smallAffine_chart (X : Scheme.{u}) (U : X.Etale)
    (hU : IsAffine U.left) : ∃ V : SmallAffine X, Nonempty (affineChart X V ≅ U) := by
  let : IsAffine U.left := hU
  let e := U.left.isoSpec
  let f := e.inv ≫ U.hom
  let : Etale f := inferInstanceAs (Etale (e.inv ≫ U.hom))
  let T := Scheme.AffineEtale.mk f
  let K := equivSmallModel.{u} X.AffineEtale
  exact ⟨K.functor.obj T, ⟨(Scheme.AffineEtale.Spec X).mapIso (K.unitIso.symm.app T) ≪≫
    MorphismProperty.Over.isoMk e.symm rfl⟩⟩

set_option maxHeartbeats 1600000 in
/-- The presheaf definition yields finite affine charts with explicit
relations and an isomorphism of their cokernel with the given sheaf. -/
theorem exists_chartPresentation {X : Scheme.{u}} {N : ℕ} {F : Ab X}
    (hF : finiteEtalePresentations X N F) :
    ∃ p : ChartPresentation X N, Nonempty (p.sheaf ≅ F) := by
  classical
  obtain ⟨P, hP, ⟨eP⟩⟩ := hF
  obtain ⟨q⟩ := (finitePresentations_iff_cokernelPresentation (R.{u} N) (SmallAffine X) P).mp hP
  let K := affineChartFunctor X
  let G := freeChart (R.{u} N) (SmallAffine X)
  let M := unitModule (R.{u} N)
  choose w hw using fun i : q.relations => exists_finite_chart_expansion (R.{u} N) q.generator
    (q.relation i) (Sigma.ι (fun r => G (q.relation r)) i ≫ q.differential)
  let T (i : q.relations) := ↥(w i).support
  let : ∀ i, Fintype (T i) := fun i => inferInstanceAs (Fintype (↥(w i).support))
  let t (i : q.relations) (b : T i) : q.generators := b.1.1
  let a (i : q.relations) (b : T i) : q.relation i ⟶ q.generator (t i b) := b.1.2
  let m (i : q.relations) (b : T i) : M ⟶ M :=
    ModuleCat.freeDesc (↾fun _ => w i b.1 • ModuleCat.freeMk PUnit.unit)
  let p : ChartPresentation X N :=
    { generators := q.generators
      relations := q.relations
      generator := fun j => K.obj (q.generator j)
      relation := fun i => K.obj (q.relation i)
      affineGenerator := fun _ => inferInstanceAs (IsAffine (Spec _))
      affineRelation := fun _ => inferInstanceAs (IsAffine (Spec _))
      terms := T
      target := t
      chartMap := fun i b => K.map (a i b)
      coefficient := m }
  let d (i : q.relations) (b : T i) : G (q.relation i) ⟶ G (q.generator (t i b)) :=
    mapFreeYoneda (a i b) (m i b)
  let d' := relationMap (A := fun i => G (q.relation i)) (B := fun j => G (q.generator j)) t d
  have hD : d' = q.differential := by
    apply Sigma.hom_ext
    intro i
    dsimp only [d']
    rw [relationMap, Sigma.ι_desc, hw i]
    let qTerm (b : Σ j, q.relation i ⟶ q.generator j) : G (q.relation i) ⟶ q.target :=
      PhilipponFinitePresheafRelations.chartTerm (R.{u} N) q.generator (q.relation i) b.1 b.2 (w i b)
    calc
      _ = ∑ b ∈ (w i).support.attach, qTerm b.val := by
        apply Finset.sum_congr rfl
        intro b _
        exact (chartTerm_eq (R.{u} N) q.generator (q.relation i) b.val.1 b.val.2 (w i b.val)).symm
      _ = _ := Finset.sum_attach (w i).support qTerm
  let L := modelSheaf X N
  let e : L.obj (cokernel d') ≅ p.sheaf := cokernelIsoOfTerms
    (A := fun i => G (q.relation i)) (B := fun j => G (q.generator j))
    (A' := fun i => freeSheaf (p.relation i) (generatorCoefficients N))
    (B' := fun j => freeSheaf (p.generator j) (generatorCoefficients N)) L t d p.termMap
    (fun i => modelSheafFreeYonedaIso X N (q.relation i) M)
    (fun j => modelSheafFreeYonedaIso X N (q.generator j) M)
    (fun i b => modelSheafFreeYonedaIso_naturality X N (a i b) (m i b))
  exact ⟨p, ⟨e.symm ≪≫ L.mapIso (cokernelIsoOfEq hD ≪≫ q.quotientIso) ≪≫ eP⟩⟩

set_option maxHeartbeats 1600000 in
/-- Every explicit finite affine chart presentation gives a finite
presentation in presheaves on the small affine site. -/
theorem ChartPresentation.finiteEtalePresentations {X : Scheme.{u}} {N : ℕ}
    (p : ChartPresentation X N) : finiteEtalePresentations X N p.sheaf := by
  classical
  choose U hU using fun i => exists_smallAffine_chart X (p.relation i) (p.affineRelation i)
  choose V hV using fun j => exists_smallAffine_chart X (p.generator j) (p.affineGenerator j)
  let K := affineChartFunctor X
  let M := unitModule (R.{u} N)
  let G := freeChart (R.{u} N) (SmallAffine X)
  let u (i : p.relations) := (hU i).some
  let v (j : p.generators) := (hV j).some
  let a (i : p.relations) (b : p.terms i) : U i ⟶ V (p.target i b) :=
    K.preimage ((u i).hom ≫ p.chartMap i b ≫ (v (p.target i b)).inv)
  let d (i : p.relations) (b : p.terms i) : G (U i) ⟶ G (V (p.target i b)) :=
    mapFreeYoneda (a i b) (p.coefficient i b)
  let d' := relationMap (A := fun i => G (U i)) (B := fun j => G (V j)) p.target d
  let P := cokernel d'
  have hP : finitePresentations (R.{u} N) (SmallAffine X) P :=
    (finitePresentations_iff_cokernelPresentation (R.{u} N) (SmallAffine X) P).mpr ⟨{
      generators := p.generators
      relations := p.relations
      generator := V
      relation := U
      differential := d'
      quotientIso := Iso.refl _ }⟩
  let L := modelSheaf X N
  let e (i : p.relations) := modelSheafFreeYonedaIso X N (U i) M ≪≫
    freeSheafIsoOfChartIso (u i) (generatorCoefficients N)
  let e' (j : p.generators) := modelSheafFreeYonedaIso X N (V j) M ≪≫
    freeSheafIsoOfChartIso (v j) (generatorCoefficients N)
  refine ⟨P, hP, ⟨cokernelIsoOfTerms (A := fun i => G (U i)) (B := fun j => G (V j))
    (A' := fun i => freeSheaf (p.relation i) (generatorCoefficients N))
    (B' := fun j => freeSheaf (p.generator j) (generatorCoefficients N)) L p.target d p.termMap e e' ?_⟩⟩
  intro i b
  have ha : K.map (a i b) ≫ (v (p.target i b)).hom = (u i).hom ≫ p.chartMap i b := by
    simp only [a, Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h := modelSheafFreeYonedaIso_naturality X N (a i b) (p.coefficient i b)
  have h' := freeSheafIsoOfChartIso_naturality (u i) (v (p.target i b))
    (K.map (a i b)) (p.chartMap i b) ((abCoefficients N).map (p.coefficient i b)) ha
  let z := (freeSheafIsoOfChartIso (v (p.target i b)) (generatorCoefficients N)).hom
  let x := (modelSheafFreeYonedaIso X N (U i) M).hom
  have hz := congrArg (fun k => k ≫ z) h
  have hx := congrArg (fun k => x ≫ k) h'
  change (modelSheaf X N).map (mapFreeYoneda (a i b) (p.coefficient i b)) ≫
    (modelSheafFreeYonedaIso X N (V (p.target i b)) M).hom ≫ z = x ≫ _ ≫ _
  rw [← Category.assoc, hz, Category.assoc]
  exact hx

end PhilipponEtaleFinitePresentations

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 35000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleFiniteChartDescent (exists_stage_of_finite_charts_and_maps)
open PhilipponEtaleFinitePresentations
  (ChartPresentation abCoefficients exists_chartPresentation finiteEtalePresentations generatorCoefficients)
open PhilipponEtaleRefinementAffine
  (finiteSubalgebraDiagram finiteSubalgebraCocone finiteSubalgebraIsColimit)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponFiniteRelationTransport (cokernelIsoOfTerms)
open PhilipponFreeEtaleSheaf (freeSheaf mapFreeSheaf freeSheafIsoOfChartIso
  freeSheafIsoOfChartIso_naturality pullbackFreeSheafIso pullbackFreeSheafIso_naturality)


namespace PhilipponEtaleFinitePresentationDescent

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

set_option maxHeartbeats 1600000 in
/-- An explicit chart presentation on an affine inverse limit is the
inverse image of a chart presentation on one stage. -/
theorem exists_stage_chartPresentation {I : Type u} [Category.{u} I]
    [IsCofiltered I] (hI : Quiver.IsThin I) {D : I ⥤ Scheme.{u}}
    [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c) {N : ℕ}
    (p : ChartPresentation c.pt N) :
    ∃ (i : I) (pᵢ : ChartPresentation (D.obj i) N),
      Nonempty (((pullbackSheaves (c.π.app i)).obj pᵢ.sheaf) ≅ p.sheaf) := by
  let B := p.relations ⊕ p.generators
  let E := Σ i, p.terms i
  let : Finite B := inferInstanceAs (Finite (p.relations ⊕ p.generators))
  let : ∀ i, Finite (p.terms i) := fun i => inferInstance
  let : Finite E := inferInstanceAs (Finite (Σ i, p.terms i))
  let U : B → c.pt.Etale := Sum.elim p.relation p.generator
  let src (e : E) : B := .inl e.1
  let tgt (e : E) : B := .inr (p.target e.1 e.2)
  have hU : ∀ b, IsAffine (U b).left := by
    rintro (i | j)
    · exact p.affineRelation i
    · exact p.affineGenerator j
  obtain ⟨i, V, a, e, hV, ha⟩ := exists_stage_of_finite_charts_and_maps c hc hI U hU src tgt
    (fun b => p.chartMap b.1 b.2)
  let pᵢ : ChartPresentation (D.obj i) N :=
    { generators := p.generators
      relations := p.relations
      generator := fun j => V (.inr j)
      relation := fun j => V (.inl j)
      affineGenerator := fun j => hV (.inr j)
      affineRelation := fun j => hV (.inl j)
      terms := p.terms
      target := p.target
      chartMap := fun r t => a ⟨r, t⟩
      coefficient := p.coefficient }
  let f : c.pt ⟶ D.obj i := c.π.app i
  let L := pullbackSheaves f
  let adj := pullbackAdjunction f
  let : PreservesColimitsOfSize.{u, u} L := adj.leftAdjoint_preservesColimits
  let : PreservesFiniteColimits L := ⟨fun _ => adj.leftAdjoint_preservesColimits.preservesColimitsOfShape⟩
  let : PreservesBinaryBiproducts L := preservesBinaryBiproducts_of_preservesBinaryCoproducts L
  let : L.Additive := Functor.additive_of_preservesBinaryBiproducts L
  let M := generatorCoefficients.{u} N
  let d (b : B) : L.obj (freeSheaf (V b) M) ≅ freeSheaf (U b) M :=
    pullbackFreeSheafIso f (V b) M ≪≫ freeSheafIsoOfChartIso (e b) M
  refine ⟨i, pᵢ, ⟨cokernelIsoOfTerms
    (A := fun j => freeSheaf (pᵢ.relation j) M) (B := fun j => freeSheaf (pᵢ.generator j) M)
    (A' := fun j => freeSheaf (p.relation j) M) (B' := fun j => freeSheaf (p.generator j) M)
    L p.target pᵢ.termMap p.termMap
    (fun r => d (.inl r)) (fun j => d (.inr j)) ?_⟩⟩
  intro r t
  let b : E := ⟨r, t⟩
  let m := (abCoefficients.{u} N).map (p.coefficient r t)
  have h := pullbackFreeSheafIso_naturality f (a b) m
  have h' := freeSheafIsoOfChartIso_naturality (e (src b)) (e (tgt b))
    ((baseChange f).map (a b)) (p.chartMap r t) m (ha b)
  let z := (freeSheafIsoOfChartIso (e (tgt b)) M).hom
  let x := (pullbackFreeSheafIso f (V (src b)) M).hom
  have hz := congrArg (fun k => k ≫ z) h
  have hx := congrArg (fun k => x ≫ k) h'
  exact (Category.assoc _ _ _).symm.trans (hz.trans
    ((Category.assoc _ _ _).trans (hx.trans (Category.assoc _ _ _).symm)))

/-- For a cofiltered affine inverse limit with thin index category,
every finite étale presentation descends to one affine stage. -/
theorem exists_stage_finiteEtalePresentations {I : Type u} [Category.{u} I]
    [IsCofiltered I] (hI : Quiver.IsThin I) {D : I ⥤ Scheme.{u}}
    [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c) {N : ℕ} {F : Ab c.pt}
    (hF : finiteEtalePresentations c.pt N F) :
    ∃ (i : I) (Fᵢ : Ab (D.obj i)), finiteEtalePresentations (D.obj i) N Fᵢ ∧
      Nonempty (((pullbackSheaves (c.π.app i)).obj Fᵢ) ≅ F) := by
  obtain ⟨p, ⟨e⟩⟩ := exists_chartPresentation hF
  obtain ⟨i, pᵢ, ⟨eᵢ⟩⟩ := exists_stage_chartPresentation hI c hc p
  exact ⟨i, pᵢ.sheaf, pᵢ.finiteEtalePresentations, ⟨eᵢ ≪≫ e⟩⟩

set_option maxHeartbeats 800000 in
private theorem exists_noetherian_model_of_isoSpec {X : Scheme.{u}} (R : CommRingCat.{u})
    (e : X ≅ Spec R) {N : ℕ} {F : Ab X}
    (hF : finiteEtalePresentations X N F) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsNoetherianRing A)
      (f : X ⟶ Spec (.of A)) (F₀ : Ab (Spec (.of A))),
      finiteEtalePresentations (Spec (.of A)) N F₀ ∧ Nonempty (((pullbackSheaves f).obj F₀) ≅ F) := by
  let Z := ULift.{u} ℤ
  let : Algebra Z R := ((Int.castRingHom R).comp
    (ULift.ringEquiv : Z ≃+* ℤ).toRingHom).toAlgebra
  let D : (Finset R)ᵒᵖ ⥤ Scheme.{u} := (finiteSubalgebraDiagram Z R).op ⋙ Scheme.Spec
  let c₀ : Cone D := Scheme.Spec.mapCone (finiteSubalgebraCocone Z R).op
  let c : Cone D := c₀.extend e.hom
  have hc₀ : IsLimit c₀ := isLimitOfPreserves Scheme.Spec (finiteSubalgebraIsColimit Z R).op
  have hc : IsLimit c := hc₀.extendIso e.hom
  let (i : (Finset R)ᵒᵖ) : IsAffine (D.obj i) :=
    inferInstanceAs (IsAffine (Spec (.of (Algebra.adjoin Z (i.unop : Set R)))))
  have hI : Quiver.IsThin (Finset R)ᵒᵖ :=
    fun _ _ => ⟨fun a b => Quiver.Hom.unop_inj (Subsingleton.elim a.unop b.unop)⟩
  obtain ⟨i, F₀, h₀, e₀⟩ := exists_stage_finiteEtalePresentations (D := D) hI c hc hF
  let A := Algebra.adjoin Z (i.unop : Set R)
  have hA : A.FG := Subalgebra.fg_def.mpr ⟨_, i.unop.finite_toSet, rfl⟩
  let : Algebra.FiniteType Z A := A.fg_iff_finiteType.mp hA
  let : IsNoetherianRing Z := isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv : Z ≃+* ℤ).symm
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing Z A
  exact ⟨A, inferInstance, inferInstance, c.π.app i, F₀, h₀, e₀⟩

/-- A finite affine étale presentation over any affine scheme spreads
out over a Noetherian affine scheme. -/
theorem exists_noetherian_model {X : Scheme.{u}} [IsAffine X] {N : ℕ} {F : Ab X}
    (hF : finiteEtalePresentations X N F) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsNoetherianRing A)
      (f : X ⟶ Spec (.of A)) (F₀ : Ab (Spec (.of A))),
      finiteEtalePresentations (Spec (.of A)) N F₀ ∧ Nonempty (((pullbackSheaves f).obj F₀) ≅ F) :=
  exists_noetherian_model_of_isoSpec _ X.isoSpec hF

end PhilipponEtaleFinitePresentationDescent

end

end


