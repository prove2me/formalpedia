-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleFinitePresentationFieldModels
-- name    : AlgebraicGeometry_EtaleFinitePresentationFieldModels
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-25T23:59:43.787158+00:00
-- url     : https://prove2.me/theorems/17247097-05ba-50e6-b2a7-32e2d36cc24b
-- title:
--   Finite constant models over fields
-- statement:
--   Free sheaves on affine étale charts over a field become finite constant after a common finite separable extension.
-- source:
--   Stacks Project, 59.73.2 (https://stacks.math.columbia.edu/tag/03SA) and 59.74.4 (https://stacks.math.columbia.edu/tag/09Z7).

import Definitions.Def_AlgebraicGeometry_FreeEtaleChartSheaves
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TotallySplit

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace


namespace PhilipponEtaleConstantDegreeZero

universe u
variable (X : Scheme.{u}) (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]

private def constantMap : (Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of A) ⟶
    (continuousSheaf X A).obj where
  app W := AddCommGrpCat.ofHom
    { toFun := fun a => ContinuousMap.const W.unop.left a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  naturality := by
    intro U V f
    apply ConcreteCategory.hom_ext
    intro a
    apply ContinuousMap.ext
    intro x
    rfl

private theorem constantMap_locallyInjective :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (constantMap X A) := by
  constructor
  intro W a b hab
  by_cases h : a = b
  · subst b
    rw [Presheaf.equalizerSieve_self_eq_top]
    exact X.smallEtaleTopology.top_mem _
  · have hW : IsEmpty W.unop.left := ⟨fun x => h (congrArg (fun f : C(W.unop.left, A) => f x) hab)⟩
    let V : Fin 0 → X.Etale := fun _ => W.unop
    let r : ∀ i, V i ⟶ W.unop := fun _ => 𝟙 W.unop
    have hcover : Sieve.ofArrows V r ∈ X.smallEtaleTopology W.unop :=
      (Scheme.ofArrows_mem_smallEtaleTopology_iff r).mpr (Set.eq_univ_of_forall fun x => isEmptyElim x)
    apply X.smallEtaleTopology.superset_covering _ hcover
    apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨i⟩
    exact Fin.elim0 i

private theorem constantMap_locallySurjective :
    Presheaf.IsLocallySurjective X.smallEtaleTopology (constantMap X A) := by
  constructor
  intro W s
  change C(W.left, A) at s
  let U (a : A) : W.left.Opens := ⟨s ⁻¹' {a}, (isOpen_discrete {a}).preimage s.continuous⟩
  let V (a : A) := Scheme.Etale.mk ((U a).ι ≫ W.hom)
  let r (a : A) : V a ⟶ W := MorphismProperty.Over.homMk (U a).ι rfl
  have hcover : Sieve.ofArrows V r ∈ X.smallEtaleTopology W := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff r).mpr
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨s x, ⟨⟨x, rfl⟩, rfl⟩⟩
  apply X.smallEtaleTopology.superset_covering _ hcover
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨a⟩
  refine ⟨a, ?_⟩
  apply ContinuousMap.ext
  intro x
  exact x.property.symm

/-- For discrete coefficients, sheafifying constant functions gives the
small étale sheaf of continuous functions. -/
def constantSheafIso : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of A) ≅ continuousSheaf X A := by
  let J := X.smallEtaleTopology
  let G := presheafToSheaf J AddCommGrpCat.{u}
  have h := (J.W_iff_isLocallyBijective (constantMap X A)).mpr
    ⟨constantMap_locallyInjective X A, constantMap_locallySurjective X A⟩
  let : IsIso (G.map (constantMap X A)) := (J.W_iff _).mp h
  exact (asIso (G.map (constantMap X A))).trans (sheafificationIso (continuousSheaf X A)).symm

/-- Under the continuous-function model, the adjunction unit sends a
coefficient to the function with that constant value. -/
theorem homEquiv_constantSheafIso {T : X.Etale} (hT : IsTerminal T) :
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT).homEquiv
      (AddCommGrpCat.of A) (continuousSheaf X A) (constantSheafIso X A).hom =
      (constantMap X A).app (op T) := by
  let J := X.smallEtaleTopology
  let P := (Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of A)
  have h : toSheafify J P ≫ (constantSheafIso X A).hom.hom = constantMap X A := by
    change toSheafify J P ≫ sheafifyMap J (constantMap X A) ≫
      (isoSheafify J (continuousSheaf X A).property).inv = _
    rw [← toSheafify_naturality_assoc, isoSheafify_inv, toSheafify_sheafifyLift, Category.comp_id]
  rw [Adjunction.homEquiv_unit, constantSheafAdj, Adjunction.comp_unit_app]
  change (𝟙 _ ≫ (toSheafify J P).app (op T)) ≫ (constantSheafIso X A).hom.hom.app (op T) = _
  rw [Category.id_comp]
  exact NatTrans.congr_app h (op T)

theorem homEquiv_constantSheafIso_apply {T : X.Etale} (hT : IsTerminal T) (a : A) :
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT).homEquiv
      (AddCommGrpCat.of A) (continuousSheaf X A) (constantSheafIso X A).hom a =
      ContinuousMap.const T.left a := by
  rw [homEquiv_constantSheafIso X A hT]
  rfl

end PhilipponEtaleConstantDegreeZero

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleConstantDegreeZero (constantSheafIso homEquiv_constantSheafIso_apply)


namespace PhilipponEtaleFiniteConstantColimits

universe u

/-- The finite abelian groups killed by a fixed integer. -/
def finiteCoefficients (N : ℕ) : ObjectProperty AddCommGrpCat.{u} :=
  fun M => Finite M ∧ N • 𝟙 M = 0

private theorem finiteCoefficients_of_iso {N : ℕ} {M V : AddCommGrpCat.{u}}
    (e : M ≅ V) (h : finiteCoefficients N M) : finiteCoefficients N V := by
  let : Finite M := h.1
  refine ⟨Finite.of_injective e.inv e.addCommGroupIsoToAddEquiv.symm.injective, ?_⟩
  apply (cancel_epi e.hom).mp
  rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero, ← Category.id_comp e.hom,
    ← Preadditive.nsmul_comp, h.2, zero_comp]

instance (N : ℕ) : (finiteCoefficients.{u} N).IsClosedUnderIsomorphisms where
  of_iso e h := finiteCoefficients_of_iso e h

instance (N : ℕ) (J : Type u) [Category.{u} J] [Finite J] :
    (finiteCoefficients.{u} N).IsClosedUnderColimitsOfShape J := by
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  let (j : J) : Finite (F.obj j) := (hF j).1
  let e : (∐ fun j => F.obj j) ≅ AddCommGrpCat.of (∀ j, F.obj j) :=
    (biproduct.isoCoproduct _).symm ≪≫ biproduct.isoProduct _ ≪≫
      (productIsProduct _).conePointUniqueUpToIso
        (AddCommGrpCat.HasLimit.productLimitCone _).isLimit
  let : Finite (AddCommGrpCat.of (∀ j, F.obj j)) := inferInstanceAs (Finite (∀ j, F.obj j))
  let : Finite ↑(∐ fun j => F.obj j) :=
    Finite.of_injective e.hom e.addCommGroupIsoToAddEquiv.injective
  refine ⟨Finite.of_surjective (colimitQuotientCoproduct F)
    ((AddCommGrpCat.epi_iff_surjective _).mp inferInstance), ?_⟩
  apply colimit.hom_ext
  intro j
  rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero, ← Category.id_comp (colimit.ι F j),
    ← Preadditive.nsmul_comp, (hF j).2, zero_comp]

private abbrev terminal (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)

private def isTerminalTerminal (X : Scheme.{u}) : IsTerminal (terminal X) :=
  IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal

/-- Over a connected nonempty scheme, the étale constant sheaf functor is fully faithful. -/
def constantSheafFullyFaithful (X : Scheme.{u}) [PreconnectedSpace X] [Nonempty X] :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).FullyFaithful := by
  let hT := isTerminalTerminal X
  let adj := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT
  letI : ∀ M, IsIso (adj.unit.app M) := by
    intro M
    let : TopologicalSpace M := ⊥
    let : DiscreteTopology M := ⟨rfl⟩
    let e := constantSheafIso X M
    have h : IsIso (adj.homEquiv M _ e.hom) := by
      apply (ConcreteCategory.isIso_iff_bijective _).mpr
      let x : X := Classical.choice inferInstance
      constructor
      · intro a b hab
        change (adj.homEquiv M _ e.hom a : C(X, M)) =
          (adj.homEquiv M _ e.hom b : C(X, M)) at hab
        rw [homEquiv_constantSheafIso_apply X M hT a,
          homEquiv_constantSheafIso_apply X M hT b] at hab
        exact congrArg (fun f : C(X, M) => f x) hab
      · intro f
        change C(X, M) at f
        refine ⟨f x, ?_⟩
        change (adj.homEquiv M _ e.hom (f x) : C(X, M)) = f
        rw [homEquiv_constantSheafIso_apply X M hT (f x)]
        change ContinuousMap.const X (f x) = f
        ext y
        exact ((IsLocallyConstant.iff_continuous f).mpr f.continuous).apply_eq_of_preconnectedSpace x y
    rw [Adjunction.homEquiv_unit] at h
    exact IsIso.of_isIso_comp_right (adj.unit.app M)
      (((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op (terminal X))).map e.hom)
  letI : IsIso adj.unit := NatIso.isIso_of_isIso_app _
  exact adj.fullyFaithfulLOfIsIsoUnit

/-- Étale constant sheaves with finite coefficients killed by `N`. -/
def finiteConstant (X : Scheme.{u}) (N : ℕ) :
    ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  (finiteCoefficients N).map (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u})

instance (X : Scheme.{u}) (N : ℕ) : (finiteConstant X N).IsClosedUnderIsomorphisms :=
  inferInstanceAs (((finiteCoefficients N).map
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u})).IsClosedUnderIsomorphisms)

instance (X : Scheme.{u}) [PreconnectedSpace X] [Nonempty X] (N : ℕ)
    (J : Type u) [Category.{u} J] [Finite J] :
    (finiteConstant X N).IsClosedUnderColimitsOfShape J := by
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  let C := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}
  let ff : C.FullyFaithful := constantSheafFullyFaithful X
  let : C.Full := ff.full
  let : C.Faithful := ff.faithful
  let hE (j : J) : C.essImage (F.obj j) := by
    obtain ⟨M, _, hM⟩ := hF j
    exact ⟨M, hM⟩
  let G := Functor.essImage.liftFunctor F C hE
  let e := Functor.essImage.liftFunctorCompIso F C hE
  have hG (j : J) : finiteCoefficients N (G.obj j) := by
    obtain ⟨M, hM, ⟨i⟩⟩ := hF j
    exact finiteCoefficients_of_iso (ff.preimageIso (i ≪≫ (e.app j).symm)) hM
  let : C.IsLeftAdjoint := (constantSheafAdj _ _ (isTerminalTerminal X)).isLeftAdjoint
  exact ⟨colimit G, (finiteCoefficients N).prop_colimit G hG,
    ⟨preservesColimitIso C G ≪≫ HasColimit.isoOfNatIso e⟩⟩

end PhilipponEtaleFiniteConstantColimits

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtalePullbackComposition (pullbackCompIso)
namespace PhilipponEtaleCohomologyAlong
universe u

/-- The pullback composition comparison for a given composite arrow. -/
def pullbackComposition {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (ρ : Z ⟶ X) (h : g ≫ f = ρ) :
    pullbackSheaves f ⋙ pullbackSheaves g ≅ pullbackSheaves ρ :=
  pullbackCompIso f g ≪≫ eqToIso (congrArg pullbackSheaves h)

end PhilipponEtaleCohomologyAlong

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace PhilipponFiniteEtaleSplittingField

universe u v

/-- An étale algebra over a field becomes a finite product of copies of
the base after a finite separable field extension. -/
theorem exists_splittingField (K S : Type u) [Field K] [CommRing S] [Algebra K S] [Algebra.Etale K S] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L), Algebra.IsFiniteSplit L (L ⊗[K] S) := by
  classical
  let : Module.Finite K S := Algebra.FormallyUnramified.finite_of_free K S
  let n := Module.rankAtStalk (R := K) S default
  have hn : Module.rankAtStalk (R := K) S = n := by
    funext q
    rw [Subsingleton.elim q default]
    rfl
  obtain ⟨T, hT, hAlgebra, hFlat, hFinite, hEtale, hSplit⟩ :=
    Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hn
  let : CommRing T := hT
  let : Algebra K T := hAlgebra
  let : Module.FaithfullyFlat K T := hFlat
  let : Module.Finite K T := hFinite
  let : Algebra.Etale K T := hEtale
  let : Algebra.IsFiniteSplit T (T ⊗[K] S) := hSplit
  let : Nontrivial T := (FaithfulSMul.algebraMap_injective K T).nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (α := T)
  let : m.IsMaximal := hm
  let L := T ⧸ m
  let : Field L := Ideal.Quotient.field m
  let : Module.Finite K L := Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap
    Ideal.Quotient.mk_surjective
  let : Algebra.IsSeparable K L := Algebra.FormallyUnramified.isSeparable K L
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  let e := Algebra.TensorProduct.cancelBaseChange K T L L S
  exact Algebra.IsFiniteSplit.of_algEquiv e

/-- A single finite separable field extension splits any finite list of
étale algebras. -/
theorem exists_splittingField_finset (K : Type u) [Field K] {I : Type v} (S : I → Type u)
    [∀ i, CommRing (S i)] [∀ i, Algebra K (S i)] [∀ i, Algebra.Etale K (S i)] (s : Finset I) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L), ∀ i ∈ s, Algebra.IsFiniteSplit L (L ⊗[K] S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, by simp⟩
  | insert i s _ ih =>
    obtain ⟨F, _, _, _, _, hF⟩ := ih
    obtain ⟨L, _, _, _, _, hL⟩ := exists_splittingField F (F ⊗[K] S i)
    let : Algebra K L := ((algebraMap F L).comp (algebraMap K F)).toAlgebra
    let : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq' rfl
    let : FiniteDimensional K L := Module.Finite.trans F L
    let : Algebra.IsSeparable K L := Algebra.IsSeparable.trans K F L
    refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    intro j hj
    have hj' : Algebra.IsFiniteSplit L (L ⊗[F] (F ⊗[K] S j)) := by
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact hL
      · let : Algebra.IsFiniteSplit F (F ⊗[K] S j) := hF j hjs
        infer_instance
    exact Algebra.IsFiniteSplit.of_algEquiv (Algebra.TensorProduct.cancelBaseChange K F L L (S j))

/-- A finite family of finite separable field extensions admits embeddings
over the base field into a common finite separable extension. -/
theorem exists_common_extension (K : Type u) [Field K] {I : Type v} [Finite I] (S : I → Type u)
    [∀ i, Field (S i)] [∀ i, Algebra K (S i)] [∀ i, FiniteDimensional K (S i)]
    [∀ i, Algebra.IsSeparable K (S i)] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L), ∀ i, Nonempty (S i →ₐ[K] L) := by
  let : Fintype I := Fintype.ofFinite I
  let (i : I) : Algebra.Etale K (S i) :=
    ⟨Algebra.FormallyEtale.of_isSeparable K (S i), Algebra.FinitePresentation.of_finiteType.mp
      inferInstance⟩
  obtain ⟨L, _, _, _, _, hL⟩ := exists_splittingField_finset K S Finset.univ
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, fun i => ?_⟩
  let B := L ⊗[K] S i
  let inc : L →ₐ[K] B := Algebra.TensorProduct.includeLeft
  have hinj : Function.Injective inc :=
    Algebra.TensorProduct.includeLeft_injective (algebraMap K (S i)).injective
  let : Nontrivial B := hinj.nontrivial
  obtain ⟨n, ⟨e⟩⟩ := (hL i (Finset.mem_univ i)).nonempty_algEquiv_fun
  have hn : Nonempty (Fin n) := by
    by_contra h
    let : IsEmpty (Fin n) := not_nonempty_iff.mp h
    exact zero_ne_one (e.injective (Subsingleton.elim (e 0) (e 1)))
  let j : Fin n := Classical.choice hn
  let ev : (Fin n → L) →ₐ[L] L := Pi.evalAlgHom L (fun _ : Fin n => L) j
  exact ⟨((ev.comp e.toAlgHom).restrictScalars K).comp Algebra.TensorProduct.includeRight⟩

end PhilipponFiniteEtaleSplittingField

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleNeighborhoodRestriction (along restrictionIso)
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtaleStalkPullback (stalkPullbackIso)


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

end PhilipponEtaleDisjointSections

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleDisjointSections (sectionsCoproductEquiv toTerminal)
open PhilipponEtaleNeighborhoodRestriction (along restrict)
open PhilipponFreeEtaleSheaf (freeSheaf homEquiv homEquiv_comp)


namespace PhilipponFreeEtaleSplitChart

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev terminal (X : Scheme.{u}) := Scheme.Etale.mk (𝟙 X)

variable (X : Scheme.{u}) (I : Type u)

private abbrev Y := ∐ (fun _ : I => X)
private abbrev p : Y X I ⟶ X := Sigma.desc (fun _ : I => 𝟙 X)

private instance : Etale (p X I) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @Etale) (sigmaOpenCover (fun _ : I => X))
  intro i
  change Etale (Sigma.ι _ i ≫ p X I)
  simp only [p, Sigma.ι_desc]
  infer_instance

/-- The étale chart consisting of disjoint copies of the base scheme. -/
abbrev splitChart : X.Etale := Scheme.Etale.mk (p X I)

private abbrev j (i : I) : X ⟶ Y X I := Sigma.ι (fun _ : I => X) i ≫ (Iso.refl _).hom

private def terminalIso :
    (along (p X I)).obj (terminal (Y X I)) ≅ splitChart X I :=
  MorphismProperty.Over.isoMk (Iso.refl _) rfl

private def pieceIso (i : I) :
    (along (p X I)).obj (Scheme.Etale.mk (j X I i)) ≅ terminal X :=
  MorphismProperty.Over.isoMk (Iso.refl X)

private def componentArrow (i : I) : terminal X ⟶ splitChart X I :=
  (pieceIso X I i).inv ≫ (along (p X I)).map (toTerminal (j X I) i) ≫ (terminalIso X I).hom

private def sectionsEquiv (F : Ab X) :
    F.obj.obj (op (splitChart X I)) ≃+ ∀ _ : I, F.obj.obj (op (terminal X)) :=
  ((F.obj.mapIso (terminalIso X I).op).addCommGroupIsoToAddEquiv.trans
    (sectionsCoproductEquiv (Iso.refl (Y X I)) ((restrict (p X I)).obj F))).trans
      (AddEquiv.piCongrRight fun i => (F.obj.mapIso (pieceIso X I i).symm.op).addCommGroupIsoToAddEquiv)

private theorem sectionsEquiv_apply (F : Ab X) (x : F.obj.obj (op (splitChart X I))) (i : I) :
    sectionsEquiv X I F x i = F.obj.map (componentArrow X I i).op x := by
  change F.obj.map (pieceIso X I i).inv.op
      (F.obj.map ((along (p X I)).map (toTerminal (j X I) i)).op
        (F.obj.map (terminalIso X I).hom.op x)) = _
  simp only [componentArrow, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

private abbrev coefficient (M : AddCommGrpCat.{u}) := ∐ (fun _ : I => M)

private def onComponents (M : AddCommGrpCat.{u}) (F : Ab X)
    (a : M ⟶ F.obj.obj (op (splitChart X I))) : coefficient I M ⟶ F.obj.obj (op (terminal X)) :=
  Sigma.desc (fun i => a ≫ F.obj.map (componentArrow X I i).op)

private theorem onComponents_bijective (M : AddCommGrpCat.{u}) (F : Ab X) :
    Function.Bijective (onComponents X I M F) := by
  let e := sectionsEquiv X I F
  constructor
  · intro a b h
    apply ConcreteCategory.hom_ext
    intro x
    apply e.injective
    funext i
    have h' := congrArg (fun l => Sigma.ι (fun _ : I => M) i ≫ l) h
    simp only [onComponents, Sigma.ι_desc] at h'
    simpa only [e, sectionsEquiv_apply, ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom h' x
  · intro a
    let b (i : I) := Sigma.ι (fun _ : I => M) i ≫ a
    let φ : M →+ (∀ _ : I, F.obj.obj (op (terminal X))) :=
      { toFun := fun x i => b i x
        map_zero' := funext fun i => (b i).hom.map_zero
        map_add' := fun x y => funext fun i => (b i).hom.map_add x y }
    let c := AddCommGrpCat.ofHom (e.symm.toAddMonoidHom.comp φ)
    refine ⟨c, Sigma.hom_ext _ _ fun i => ?_⟩
    rw [onComponents, Sigma.ι_desc]
    apply ConcreteCategory.hom_ext
    intro x
    change F.obj.map (componentArrow X I i).op (e.symm (φ x)) = b i x
    rw [← sectionsEquiv_apply]
    exact congrFun (e.apply_symm_apply (φ x)) i

private theorem onComponents_naturality (M : AddCommGrpCat.{u}) {F G : Ab X} (a : F ⟶ G)
    (v : M ⟶ F.obj.obj (op (splitChart X I))) :
    onComponents X I M G (v ≫ a.hom.app (op (splitChart X I))) =
      onComponents X I M F v ≫ a.hom.app (op (terminal X)) := by
  apply Sigma.hom_ext
  intro i
  simp only [onComponents, Sigma.ι_desc_assoc, Sigma.ι_desc, Category.assoc]
  exact congrArg (v ≫ ·) (a.hom.naturality (componentArrow X I i).op).symm

/-- For a split chart the free étale sheaf is constant with coefficient
group the coproduct of a copy of the input group for each sheet. -/
def freeSheafSplitIso (M : AddCommGrpCat.{u}) :
    freeSheaf (splitChart X I) M ≅
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (coefficient I M) := by
  let T := terminal X
  let hT : IsTerminal T := IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal
  let C := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}
  let K := coefficient I M
  let A := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT
  let α (F : Ab X) := (homEquiv (splitChart X I) M F).trans
    (Equiv.ofBijective _ (onComponents_bijective X I M F))
  let β (F : Ab X) := A.homEquiv K F
  let e : coyoneda.obj (op (freeSheaf (splitChart X I) M)) ≅ coyoneda.obj (op (C.obj K)) :=
    NatIso.ofComponents (fun F => ((α F).trans (β F).symm).toIso) (by
      intro F G a
      apply ConcreteCategory.hom_ext
      intro v
      change (β G).symm (α G (v ≫ a)) = (β F).symm (α F v) ≫ a
      apply (β G).injective
      rw [Equiv.apply_symm_apply]
      have hr : β G ((β F).symm (α F v) ≫ a) = α F v ≫ a.hom.app (op T) := by
        change A.homEquiv K G ((A.homEquiv K F).symm (α F v) ≫ a) = _
        rw [A.homEquiv_naturality_right, Equiv.apply_symm_apply]
        rfl
      have hl : α G (v ≫ a) = α F v ≫ a.hom.app (op T) := by
        dsimp only [α, Equiv.trans_apply, Equiv.ofBijective_apply]
        rw [homEquiv_comp]
        exact onComponents_naturality X I M a _
      exact hl.trans hr.symm)
  exact (Coyoneda.fullyFaithful.preimageIso e).unop.symm

/-- The coefficient group of a finite split chart is finite and has the
same annihilator as the group on each sheet. -/
theorem exists_finite_constant_of_split [Finite I] (M : AddCommGrpCat.{u}) [Finite M]
    (N : ℕ) (hM : N • 𝟙 M = 0) :
    ∃ (K : AddCommGrpCat.{u}) (_ : Finite K), N • 𝟙 K = 0 ∧
      Nonempty (freeSheaf (splitChart X I) M ≅
        (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj K) := by
  let f (_ : I) := M
  let P := (AddCommGrpCat.HasLimit.productLimitCone f).isLimit
  let e : coefficient I M ≅ AddCommGrpCat.of (I → M) :=
    (biproduct.isoCoproduct f).symm ≪≫ biproduct.isoProduct f ≪≫
      (productIsProduct f).conePointUniqueUpToIso P
  let : Finite (AddCommGrpCat.of (I → M)) := inferInstanceAs (Finite (I → M))
  have hFin : Finite (coefficient I M) :=
    Finite.of_injective e.hom (ConcreteCategory.bijective_of_isIso e.hom).1
  refine ⟨coefficient I M, hFin, ?_, ⟨freeSheafSplitIso X I M⟩⟩
  apply Sigma.hom_ext
  intro i
  rw [Preadditive.comp_nsmul, Category.comp_id, ← Category.id_comp (Sigma.ι f i),
    ← Preadditive.nsmul_comp, hM, zero_comp, comp_zero]

end PhilipponFreeEtaleSplitChart

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponFreeEtaleSheaf (freeSheaf freeSheafIsoOfChartIso pullbackFreeSheafIso)
open PhilipponFreeEtaleSplitChart (splitChart exists_finite_constant_of_split)
open scoped TensorProduct


namespace PhilipponFreeEtaleFieldTrivialization

universe u

private abbrev specMap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    Spec (.of S) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R S))

private instance (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S] :
    Etale (specMap R S) := (HasRingHomProperty.Spec_iff (P := @Etale)).2
      (RingHom.etale_algebraMap.mpr inferInstance)

/-- An affine étale algebra specifies an object of the small étale site. -/
abbrev chart (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S] :
    (Spec (.of R)).Etale := Scheme.Etale.mk (specMap R S)

/-- An affine chart of the small étale site of a spectrum is represented
by an étale algebra over the base ring. -/
theorem exists_affineChartIso (R : Type u) [CommRing R] (U : (Spec (.of R)).Etale)
    [IsAffine U.left] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Algebra.Etale R S),
      Nonempty (chart R S ≅ U) := by
  let S := Γ(U.left, ⊤)
  let k : CommRingCat.of R ⟶ S := Spec.preimage (U.left.isoSpec.inv ≫ U.hom)
  have hk : Spec.map k = U.left.isoSpec.inv ≫ U.hom := Spec.map_preimage _
  let : Algebra R S := k.hom.toAlgebra
  let : Algebra.Etale R S := by
    apply RingHom.etale_algebraMap.mp
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    rw [hk]
    infer_instance
  exact ⟨S, inferInstance, inferInstance, inferInstance,
    ⟨MorphismProperty.Over.isoMk U.left.isoSpec.symm hk.symm⟩⟩

/-- A splitting of the base-changed ring yields a split étale chart. -/
def splitBaseChangeIso (R S L : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S]
    [CommRing L] [Algebra R L] (I : Type u) [Finite I] (e : L ⊗[R] S ≃ₐ[L] (I → L)) :
    splitChart (Spec (.of L)) I ≅ ((baseChange (specMap R L)).obj (chart R S)) := by
  let B := L ⊗[R] S
  let a : Spec (.of B) ⟶ Spec (.of L) := specMap L B
  let b : Spec (.of B) ⟶ Spec (.of S) :=
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S →ₐ[R] B).toRingHom)
  have h : IsPullback a b (specMap R L) (specMap R S) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R L S)
  let E := (e.toRingEquiv.toCommRingCatIso).op
  let c := asIso (sigmaSpec (fun _ : I => CommRingCat.of L)) ≪≫
    Scheme.Spec.mapIso E ≪≫ h.flip.isoPullback
  refine MorphismProperty.Over.isoMk c ?_
  change sigmaSpec (fun _ : I => CommRingCat.of L) ≫
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        h.flip.isoPullback.hom ≫ pullback.snd (specMap R S) (specMap R L) =
    Sigma.desc (fun _ : I => 𝟙 (Spec (.of L)))
  rw [h.flip.isoPullback_hom_snd, ← Spec.map_comp]
  apply Sigma.hom_ext
  intro i
  rw [ι_sigmaSpec_assoc, Sigma.ι_desc, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  ext l
  exact congrFun (e.commutes l) i

private theorem trivialization_of_isFiniteSplit (R S L : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.Etale R S] [CommRing L] [Algebra R L]
    (hL : Algebra.IsFiniteSplit L (L ⊗[R] S)) (M : AddCommGrpCat.{u}) [Finite M]
    (N : ℕ) (hM : N • 𝟙 M = 0) :
    ∃ (A : AddCommGrpCat.{u}) (_ : Finite A),
      N • 𝟙 A = 0 ∧ Nonempty
        ((pullbackSheaves (specMap R L)).obj (freeSheaf (chart R S) M) ≅
          (constantSheaf (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{u}).obj A) := by
  obtain ⟨n, ⟨e⟩⟩ := hL.nonempty_algEquiv_fun
  let I := ULift.{u} (Fin n)
  let e' : L ⊗[R] S ≃ₐ[L] (I → L) :=
    e.trans (AlgEquiv.piCongrLeft' L (fun _ : Fin n => L) Equiv.ulift.symm)
  let d := splitBaseChangeIso R S L I e'
  obtain ⟨A, hA, hz, ⟨a⟩⟩ := exists_finite_constant_of_split (Spec (.of L)) I M N hM
  exact ⟨A, hA, hz,
    ⟨pullbackFreeSheafIso (specMap R L) (chart R S) M ≪≫ freeSheafIsoOfChartIso d.symm M ≪≫ a⟩⟩

/-- A finite separable field extension trivializes the coefficient sheaf
freely generated by an affine étale chart over a field. Finite coefficients
and their annihilator are preserved. -/
theorem exists_finite_separable_trivialization (K S : Type u) [Field K] [CommRing S]
    [Algebra K S] [Algebra.Etale K S] (M : AddCommGrpCat.{u}) [Finite M]
    (N : ℕ) (hM : N • 𝟙 M = 0) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L) (A : AddCommGrpCat.{u}) (_ : Finite A),
      N • 𝟙 A = 0 ∧ Nonempty
        ((pullbackSheaves (specMap K L)).obj (freeSheaf (chart K S) M) ≅
          (constantSheaf (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{u}).obj A) := by
  obtain ⟨L, _, _, _, _, hL⟩ := PhilipponFiniteEtaleSplittingField.exists_splittingField K S
  obtain ⟨A, hA, hz, hIso⟩ := trivialization_of_isFiniteSplit K S L hL M N hM
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, A, hA, hz,
    hIso⟩

/-- A finite family of free étale coefficient sheaves over a field can be
trivialized over one finite separable extension. -/
theorem exists_simultaneous_finite_separable_trivialization (K : Type u) [Field K] {I : Type u}
    [Finite I] (S : I → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra K (S i)]
    [∀ i, Algebra.Etale K (S i)] (M : AddCommGrpCat.{u}) [Finite M] (N : ℕ)
    (hM : N • 𝟙 M = 0) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L), ∀ i : I, ∃ (A : AddCommGrpCat.{u}) (_ : Finite A),
      N • 𝟙 A = 0 ∧ Nonempty
        ((pullbackSheaves (specMap K L)).obj (freeSheaf (chart K (S i)) M) ≅
          (constantSheaf (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{u}).obj A) := by
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨L, _, _, _, _, hL⟩ := PhilipponFiniteEtaleSplittingField.exists_splittingField_finset K S Finset.univ
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, fun i =>
    trivialization_of_isFiniteSplit K (S i) L (hL i (Finset.mem_univ i)) M N hM⟩

end PhilipponFreeEtaleFieldTrivialization

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (pullbackConstantIso)
open PhilipponEtaleCohomologyAlong (pullbackComposition)
open PhilipponEtaleFiniteConstantColimits (finiteConstant)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponFiniteEtaleSplittingField (exists_common_extension)


namespace PhilipponEtaleFiniteFieldModels

universe u

private abbrev fieldScheme (K : Type u) [Field K] := Spec (CommRingCat.of K)

private abbrev specMap (K L : Type u) [Field K] [Field L] [Algebra K L] :
    fieldScheme L ⟶ fieldScheme K := Spec.map (CommRingCat.ofHom (algebraMap K L))

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- Bounded finite coefficient sheaves that become constant over a
finite separable extension of the base field. -/
def finiteFieldModel (K : Type u) [Field K] (N : ℕ) : ObjectProperty (Ab (fieldScheme K)) :=
  fun F => ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
    (_ : Algebra.IsSeparable K L),
    finiteConstant (fieldScheme L) N ((pullbackSheaves (specMap K L)).obj F)

instance (K : Type u) [Field K] (N : ℕ) : (finiteFieldModel K N).IsClosedUnderIsomorphisms where
  of_iso e h := by
    obtain ⟨L, _, _, _, _, hL⟩ := h
    exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
      (finiteConstant (fieldScheme L) N).prop_of_iso ((pullbackSheaves (specMap K L)).mapIso e) hL⟩

private theorem finiteConstant_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) (N : ℕ) (F : Ab X)
    (hF : finiteConstant X N F) : finiteConstant Y N ((pullbackSheaves f).obj F) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hF
  exact ⟨M, hM, ⟨((pullbackConstantIso f).app M).symm ≪≫ (pullbackSheaves f).mapIso e⟩⟩

private theorem finiteConstant_of_extension (K D L : Type u) [Field K] [Field D] [Field L]
    [Algebra K D] [Algebra K L] (e : D →ₐ[K] L) (N : ℕ) (F : Ab (fieldScheme K))
    (hF : finiteConstant (fieldScheme D) N ((pullbackSheaves (specMap K D)).obj F)) :
    finiteConstant (fieldScheme L) N ((pullbackSheaves (specMap K L)).obj F) := by
  let g : fieldScheme L ⟶ fieldScheme D := Spec.map (CommRingCat.ofHom e.toRingHom)
  have hg : g ≫ specMap K D = specMap K L := by
    rw [specMap, specMap, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext e.commutes)
  exact (finiteConstant (fieldScheme L) N).prop_of_iso
    ((pullbackComposition (specMap K D) g (specMap K L) hg).app F)
    (finiteConstant_pullback g N _ hF)

instance (K : Type u) [Field K] (N : ℕ) (J : Type u) [Category.{u} J] [Finite J] :
    (finiteFieldModel K N).IsClosedUnderColimitsOfShape J := by
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  choose D hD hKD hFin hSep hConst using hF
  let : ∀ j, Field (D j) := hD
  let : ∀ j, Algebra K (D j) := hKD
  let : ∀ j, FiniteDimensional K (D j) := hFin
  let : ∀ j, Algebra.IsSeparable K (D j) := hSep
  obtain ⟨L, _, _, _, _, hL⟩ := exists_common_extension K D
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  let f := specMap K L
  let : (pullbackSheaves f).IsLeftAdjoint := (pullbackAdjunction f).isLeftAdjoint
  apply (finiteConstant (fieldScheme L) N).prop_of_isColimit
    (isColimitOfPreserves (pullbackSheaves f) (colimit.isColimit F))
  intro j
  exact finiteConstant_of_extension K (D j) L (Classical.choice (hL j)) N (F.obj j) (hConst j)

/-- The bounded free coefficient sheaf of an affine étale chart over a
field belongs to the class of finite field models. -/
theorem freeSheaf_finiteFieldModel (K S : Type u) [Field K] [CommRing S] [Algebra K S]
    [Algebra.Etale K S] (M : AddCommGrpCat.{u}) [Finite M] (N : ℕ) (hM : N • 𝟙 M = 0) :
    finiteFieldModel K N
      (PhilipponFreeEtaleSheaf.freeSheaf (PhilipponFreeEtaleFieldTrivialization.chart K S) M) := by
  obtain ⟨L, _, _, _, _, A, hA, hz, ⟨e⟩⟩ :=
    PhilipponFreeEtaleFieldTrivialization.exists_finite_separable_trivialization K S M N hM
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, A, ⟨hA, hz⟩, ⟨e.symm⟩⟩

/-- The same finite field model property holds for any affine étale
chart over the field scheme. -/
theorem affineChart_finiteFieldModel (K : Type u) [Field K] (U : (fieldScheme K).Etale)
    [IsAffine U.left] (M : AddCommGrpCat.{u}) [Finite M] (N : ℕ) (hM : N • 𝟙 M = 0) :
    finiteFieldModel K N (PhilipponFreeEtaleSheaf.freeSheaf U M) := by
  obtain ⟨S, _, _, _, ⟨e⟩⟩ := PhilipponFreeEtaleFieldTrivialization.exists_affineChartIso K U
  exact (finiteFieldModel K N).prop_of_iso (PhilipponFreeEtaleSheaf.freeSheafIsoOfChartIso e M)
    (freeSheaf_finiteFieldModel K S M N hM)

end PhilipponEtaleFiniteFieldModels

end

end


