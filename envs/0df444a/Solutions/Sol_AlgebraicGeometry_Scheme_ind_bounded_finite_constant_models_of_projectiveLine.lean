-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.ind_bounded_finite_constant_models_of_projectiveLine
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-26T06:07:51.297124+00:00
-- url     : https://prove2.me/submissions/c21d8613-7f07-454f-ba4c-c6062d4bb66d

import Definitions.Def_AlgebraicGeometry_EtaleNoetherianBoundedConstantModels
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GroupWithZero.Pi
import Mathlib.Algebra.Module.ZMod
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.VanKampen
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleBoundedFiniteModelReduction (boundedFiniteModel)
open PhilipponEtaleFiniteConstantColimits (finiteConstant finiteCoefficients)
open PhilipponEtaleFiniteFieldModels (finiteFieldModel affineChart_finiteFieldModel)
open PhilipponEtaleRelativeCoefficients (boundedTorsionModule boundedTorsionModule_forget)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponFiniteModulePresheafPresentation (finitePresentations ind_finitePresentations)
open PhilipponFreeYonedaMaps (mapFreeYoneda ι_mapFreeYoneda_app ι_mapFreeYoneda_app_assoc
  homEquiv_mapFreeYoneda_comp)
open PhilipponFreeEtaleSplitChart (splitChart exists_finite_constant_of_split)


namespace PhilipponEtaleFinitePresentations

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev SmallAffine (X : Scheme.{u}) := SmallModel.{u} X.AffineEtale

private abbrev affineChart (X : Scheme.{u}) (U : SmallAffine X) : X.Etale :=
  (affineChartFunctor X).obj U

/-- A base-changed affine étale chart is affine when the base change is from
an affine scheme to a separated scheme. -/
theorem isAffine_baseChange_of_isSeparated {X Y : Scheme.{u}} [X.IsSeparated] [IsAffine Y]
    (f : Y ⟶ X) (V : X.Etale) [IsAffine V.left] : IsAffine ((baseChange f).obj V).left := by
  let : IsAffineHom (V.hom ≫ terminal.from X) :=
    isAffineHom_of_isAffine (X := V.left) (Y := ⊤_ Scheme.{u}) _
  let : IsSeparated (terminal.from X) := ‹X.IsSeparated›.isSeparated_terminal_from
  let : IsAffineHom V.hom := IsAffineHom.of_comp V.hom (terminal.from X)
  exact inferInstanceAs (IsAffine (pullback V.hom f))

/-- The restriction of a finite presentation on a separated scheme to a
field-valued point becomes finite constant over a finite separable extension. -/
theorem finiteFieldModel_pullback_of_isSeparated (X : Scheme.{u}) [X.IsSeparated]
    (K : Type u) [Field K]
    (f : Spec (.of K) ⟶ X) (N : ℕ) (hN : N ≠ 0) (F : Ab X)
    (hF : finiteEtalePresentations X N F) :
    finiteFieldModel K N ((pullbackSheaves f).obj F) := by
  let G := pullbackSheaves f
  let P := finiteFieldModel K N
  let : G.IsLeftAdjoint := (pullbackAdjunction f).isLeftAdjoint
  refine finiteEtalePresentations_le X N (P.inverseImage G) ?_ ?_ F hF
  · intro J _ _
    let : P.IsClosedUnderColimitsOfShape J :=
      inferInstanceAs ((finiteFieldModel K N).IsClosedUnderColimitsOfShape J)
    apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
    rintro _ ⟨D, hD⟩
    change P (G.obj (colimit D))
    exact P.prop_of_isColimit (c := G.mapCocone (colimit.cocone D))
      (isColimitOfPreserves G (colimit.isColimit D)) hD
  · intro U
    let V := affineChart X U
    let T := generatorCoefficients.{u} N
    let : Finite T := (generatorCoefficients_finite N hN).1
    let : IsAffine V.left := inferInstanceAs (IsAffine (Spec _))
    let : IsAffine ((baseChange f).obj V).left := isAffine_baseChange_of_isSeparated f V
    exact P.prop_of_iso (PhilipponFreeEtaleSheaf.pullbackFreeSheafIso f V T).symm
      (affineChart_finiteFieldModel K ((baseChange f).obj V) T N (generatorCoefficients_finite N hN).2)

end PhilipponEtaleFinitePresentations

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

open scoped BigOperators TensorProduct
open Algebra.TensorProduct
open PhilipponEtaleGenericIdempotents (exists_lift_completeOrthogonalIdempotents)
open PhilipponGenericMorphismCoefficients (factor_fg_base_subalgebra)


namespace PhilipponEtaleGenericSplittingSpread
universe u v

/-- A finite family of affine étale algebras over a domain splits on a
dense principal open of the normalization in one finite separable extension
of the fraction field. -/
theorem exists_simultaneous_split_on_normalization_of_isFractionRing
    {R : Type u} [CommRing R] [IsDomain R] {J : Type v}
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : J → Type u) [∀ j, CommRing (S j)] [∀ j, Algebra R (S j)]
    [∀ j, Algebra.Etale R (S j)] (s : Finset J) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : FiniteDimensional K L) (_ : Algebra.IsSeparable K L),
      letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
      ∃ b : integralClosure R L, b ≠ 0 ∧
      ∀ j ∈ s, ∃ (I : Type u) (_ : Finite I), Nonempty
        (Localization.Away b ⊗[R] S j ≃ₐ[Localization.Away b] (I → Localization.Away b)) := by
  classical
  obtain ⟨L, _, _, _, _, hL⟩ :=
    PhilipponFiniteEtaleSplittingField.exists_splittingField_finset K (fun j => K ⊗[R] S j) s
  let : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  let B := integralClosure R L
  let : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  let : IsIntegrallyClosed B := integralClosure.isIntegrallyClosedOfFiniteExtension K
  have hsplit (j : s) : ∃ n : ℕ, Nonempty (L ⊗[B] (B ⊗[R] S j) ≃ₐ[L] (Fin n → L)) := by
    obtain ⟨n, ⟨a⟩⟩ := (hL j j.property).nonempty_algEquiv_fun
    exact ⟨n, ⟨(cancelBaseChange R B L L (S j)).trans
      ((cancelBaseChange R K L L (S j)).symm.trans a)⟩⟩
  choose n hn using hsplit
  let I (j : s) := ULift.{u} (Fin (n j))
  let (j : s) : Finite (I j) := inferInstanceAs (Finite (ULift (Fin (n j))))
  let e (j : s) : L ⊗[B] (B ⊗[R] S j) ≃ₐ[L] (I j → L) :=
    (Classical.choice (hn j)).trans (AlgEquiv.piCongrLeft' L (fun _ : Fin (n j) => L) Equiv.ulift.symm)
  obtain ⟨b, hb, h⟩ := exists_away_algEquiv_finset (fun j : s => B ⊗[R] S j) I e Finset.univ
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, b, hb, fun j hj => ?_⟩
  let A := Localization.Away b
  let j' : s := ⟨j, hj⟩
  obtain ⟨a⟩ := h j' (Finset.mem_univ j')
  exact ⟨I j', inferInstance, ⟨(cancelBaseChange R B A A (S j)).symm.trans a⟩⟩

end PhilipponEtaleGenericSplittingSpread

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleFiniteConstantColimits (finiteConstant)
open PhilipponEtaleFinitePresentations
  (chartSplits exists_trivializing_charts finiteEtalePresentations isAffine_baseChange_of_isSeparated)
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponFreeEtaleFieldTrivialization (chart exists_affineChartIso splitBaseChangeIso)


namespace PhilipponEtaleFinitePresentationTrivialization

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private abbrev specMap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    Spec (.of S) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- A bounded finite presentation on a separated scheme becomes finite
constant on a dense principal open of the normalization of any integral
affine base change in a suitable finite separable extension. -/
theorem exists_trivialization_on_normalization_of_isFractionRing
    {X : Scheme.{u}} [X.IsSeparated] (R : Type u) [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (i : Spec (.of R) ⟶ X) (N : ℕ) (hN : N ≠ 0) (F : Ab X)
    (hF : finiteEtalePresentations X N F) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : FiniteDimensional K L) (_ : Algebra.IsSeparable K L),
      letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
      ∃ b : integralClosure R L, b ≠ 0 ∧
      finiteConstant (Spec (.of (Localization.Away b))) N
        ((pullbackSheaves (specMap R (Localization.Away b) ≫ i)).obj F) := by
  classical
  obtain ⟨s, hs⟩ := exists_trivializing_charts X N hN F hF
  let U (j : s) := (Scheme.AffineEtale.Spec X).obj j.val
  let (j : s) : IsAffine (U j).left := inferInstanceAs (IsAffine (Spec _))
  let V (j : s) := (baseChange i).obj (U j)
  let (j : s) : IsAffine (V j).left := isAffine_baseChange_of_isSeparated i (U j)
  choose S hc ha he e using fun j : s => exists_affineChartIso R (V j)
  let : ∀ j, CommRing (S j) := hc
  let : ∀ j, Algebra R (S j) := ha
  let : ∀ j, Algebra.Etale R (S j) := he
  obtain ⟨L, _, _, _, _, b, hb, hsplit⟩ :=
    PhilipponEtaleGenericSplittingSpread.exists_simultaneous_split_on_normalization_of_isFractionRing
      (R := R) K S Finset.univ
  let : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, b, hb, ?_⟩
  let A := Localization.Away b
  let : IsDomain A := Localization.Away.isDomain hb
  let hA : IrreducibleSpace (PrimeSpectrum A) := PrimeSpectrum.irreducibleSpace
  let : PreconnectedSpace (Spec (.of A)) :=
    @PreirreducibleSpace.preconnectedSpace (PrimeSpectrum A) _ hA.toPreirreducibleSpace
  let : Nonempty (Spec (.of A)) := hA.toNonempty
  let f := specMap R A
  refine hs (Spec (.of A)) (f ≫ i) ?_
  intro W hW
  let j : s := ⟨W, hW⟩
  obtain ⟨I, _, ⟨a⟩⟩ := hsplit j (Finset.mem_univ j)
  let c := splitBaseChangeIso R (S j) A I a
  let d := (baseChange f).mapIso (Classical.choice (e j))
  let g := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f i).symm.app (U j)
  exact ⟨I, inferInstance, ⟨c ≪≫ d ≪≫ g⟩⟩

end PhilipponEtaleFinitePresentationTrivialization

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponFiniteSchemeCoproduct

universe u

variable {I : Type u} {X : Scheme.{u}} {Y : I → Scheme.{u}} (p : ∀ i, Y i ⟶ X)

/-- A finite coproduct of finite morphisms to a scheme is finite. -/
theorem isFinite_sigmaDesc_of_finite [Finite I] [∀ i, IsFinite (p i)] :
    IsFinite (Sigma.desc p) := by
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) X.affineCover).2 fun j => ?_
  let T := X.affineCover.X j
  let f : T ⟶ X := X.affineCover.f j
  let e := pullbackCoproductIso p f
  let a (i : I) := pullback.fst f (p i)
  let : ∀ i, IsFinite (a i) := fun i => by dsimp [a]; infer_instance
  let : IsFinite (Sigma.desc a) := isFinite_sigmaDesc a
  have he : e.hom ≫ pullback.fst f (Sigma.desc p) = Sigma.desc a := by
    apply Sigma.hom_ext
    intro i
    rw [ι_pullbackCoproductIso_assoc, pullbackInclusion_fst, Sigma.ι_desc]
  have h : pullback.fst f (Sigma.desc p) = e.inv ≫ Sigma.desc a := by
    rw [← he, Iso.inv_hom_id_assoc]
  change IsFinite (pullback.snd (Sigma.desc p) f)
  rw [← pullbackSymmetry_hom_comp_fst, h]
  infer_instance

end PhilipponFiniteSchemeCoproduct

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleBoundedFiniteModelReduction (boundedFiniteModel)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleConstantDegreeZero (constantSheafIso continuousSheaf)
open PhilipponFiniteSchemeCoproduct


namespace PhilipponEtaleProjectiveModelCoproduct

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

variable {I : Type u} [Finite I] {X : Scheme.{u}} {Y : I → Scheme.{u}}
  (p : ∀ i, Y i ⟶ X) (M : I → AddCommGrpCat.{u})

local instance (i : I) : TopologicalSpace (M i) := ⊥
local instance (i : I) : DiscreteTopology (M i) := ⟨rfl⟩
local instance : TopologicalSpace (∀ i, M i) := ⊥
local instance : DiscreteTopology (∀ i, M i) := ⟨rfl⟩

private abbrev atComponent (i : I) := (pushforward (p i)).obj (continuousSheaf (Y i) (M i))
private abbrev fiber {Y : Scheme.{u}} (p : Y ⟶ X) (W : X.Etale) : Scheme.{u} :=
  pullback W.hom p

private def baseHomeo (W : X.Etale) :
    (Σ i, fiber (p i) W) ≃ₜ fiber (Sigma.desc p) W :=
  (sigmaMk (fun i => fiber (p i) W)).trans (pullbackCoproductIso p W.hom).hom.homeomorph

private theorem baseHomeo_mk (W : X.Etale) (i : I) (z : fiber (p i) W) :
    baseHomeo p W ⟨i, z⟩ = pullbackInclusion p W.hom i z := by
  change (pullbackCoproductIso p W.hom).hom (sigmaMk _ ⟨i, z⟩) = _
  rw [sigmaMk_mk, ← Scheme.Hom.comp_apply, ι_pullbackCoproductIso]

private abbrev chartMap {T : Scheme.{u}} (r : T ⟶ X) {U V : X.Etale} (a : U ⟶ V) :
    fiber r U ⟶ fiber r V := ((baseChange r).map a).left

@[reassoc]
private theorem chartMap_fst {T : Scheme.{u}} (r : T ⟶ X) {U V : X.Etale} (a : U ⟶ V) :
    chartMap r a ≫ pullback.fst V.hom r = pullback.fst U.hom r ≫ a.left :=
  pullback.lift_fst _ _ _

@[reassoc]
private theorem chartMap_snd {T : Scheme.{u}} (r : T ⟶ X) {U V : X.Etale} (a : U ⟶ V) :
    chartMap r a ≫ pullback.snd V.hom r = pullback.snd U.hom r :=
  pullback.lift_snd _ _ _

omit [Finite I] in
private theorem chartMap_inclusion {U V : X.Etale} (a : U ⟶ V) (i : I) :
    pullbackInclusion p U.hom i ≫ chartMap (Sigma.desc p) a =
      chartMap (p i) a ≫ pullbackInclusion p V.hom i := by
  apply pullback.hom_ext
  · simp only [Category.assoc, chartMap_fst, pullbackInclusion_fst_assoc, pullbackInclusion_fst]
  · simp only [Category.assoc, chartMap_snd, pullbackInclusion_snd, chartMap_snd_assoc]

variable {F : Ab X} (m : ∀ i, F ⟶ atComponent p M i)

private abbrev componentSection (i : I) (W : X.Etale) (s : F.obj.obj (op W)) :
    C(fiber (p i) W, M i) := (m i).hom.app (op W) s

variable {B : AddCommGrpCat.{u}} [TopologicalSpace B] [DiscreteTopology B]
  (l : ∀ i, M i ⟶ B)

private def assembled (W : X.Etale) (s : F.obj.obj (op W)) :
    C(fiber (Sigma.desc p) W, B) := by
  let a (i : I) := componentSection p M m i W s
  let k (z : Σ i, fiber (p i) W) : B := l z.1 (a z.1 z.2)
  have hk : Continuous k := continuous_sigma fun i =>
    (continuous_of_discreteTopology (f := l i)).comp (a i).continuous
  exact ⟨k ∘ (baseHomeo p W).symm, hk.comp (baseHomeo p W).symm.continuous⟩

omit [DiscreteTopology B] in
private theorem assembled_component (W : X.Etale) (s : F.obj.obj (op W)) (i : I)
    (z : fiber (p i) W) :
    assembled p M m l W s (pullbackInclusion p W.hom i z) =
      l i (componentSection p M m i W s z) := by
  rw [← baseHomeo_mk]
  exact congrArg (fun t : Σ j, fiber (p j) W =>
    l t.1 (componentSection p M m t.1 W s t.2))
    ((baseHomeo p W).symm_apply_apply ⟨i, z⟩)

private def combined : F ⟶ (pushforward (Sigma.desc p)).obj (continuousSheaf (∐ Y) B) := by
  classical
  refine ⟨{
    app := fun W => AddCommGrpCat.ofHom {
      toFun := assembled p M m l W.unop
      map_zero' := ?_
      map_add' := fun s t => ?_ }
    naturality := ?_ }⟩
  · apply ContinuousMap.ext
    intro z
    obtain ⟨⟨i, w⟩, rfl⟩ := (baseHomeo p W.unop).surjective z
    simp only [baseHomeo_mk, assembled_component, componentSection, map_zero,
      ContinuousMap.zero_apply]
  · apply ContinuousMap.ext
    intro z
    obtain ⟨⟨i, w⟩, rfl⟩ := (baseHomeo p W.unop).surjective z
    rw [baseHomeo_mk, assembled_component]
    change l i (componentSection p M m i W.unop (s + t) w) =
      assembled p M m l W.unop s _ + assembled p M m l W.unop t _
    have hm : componentSection p M m i W.unop (s + t) =
        componentSection p M m i W.unop s + componentSection p M m i W.unop t :=
      ((m i).hom.app (op W.unop)).hom.map_add s t
    rw [assembled_component, assembled_component, hm, ContinuousMap.add_apply, map_add]
  · intro U V a
    apply ConcreteCategory.hom_ext
    intro s
    apply ContinuousMap.ext
    intro z
    obtain ⟨⟨i, w⟩, rfl⟩ := (baseHomeo p V.unop).surjective z
    rw [baseHomeo_mk]
    let b := chartMap (Sigma.desc p) a.unop
    let bᵢ := chartMap (p i) a.unop
    have h : b (pullbackInclusion p V.unop.hom i w) =
        pullbackInclusion p U.unop.hom i (bᵢ w) :=
      congrArg (fun d : fiber (p i) V.unop ⟶ fiber (Sigma.desc p) U.unop => d w)
        (chartMap_inclusion p a.unop i)
    change assembled p M m l V.unop (F.obj.map a s) (pullbackInclusion p V.unop.hom i w) =
      assembled p M m l U.unop s (b (pullbackInclusion p V.unop.hom i w))
    rw [h, assembled_component, assembled_component]
    have hm := ConcreteCategory.congr_hom ((m i).hom.naturality a) s
    exact congrArg (fun c : C(fiber (p i) V.unop, M i) => l i (c w)) hm

/-- Coefficient homomorphisms that jointly detect sections can be assembled into
a single map to the constant direct image on the coproduct. -/
private theorem mono_combined
    (h : ∀ (G : Ab X) (a b : G ⟶ F),
      (∀ i W s z, l i (componentSection p M m i W (a.hom.app (op W) s) z) =
        l i (componentSection p M m i W (b.hom.app (op W) s) z)) → a = b) :
    Mono (combined p M m l) := by
  refine ⟨fun {G} a b e => h G a b fun i W s z => ?_⟩
  have eW := ConcreteCategory.congr_hom (congrArg (fun g => g.hom.app (op W)) e) s
  have ev := congrArg (fun c : C(fiber (Sigma.desc p) W, B) =>
    c (pullbackInclusion p W.hom i z)) eW
  change assembled p M m l W (a.hom.app (op W) s) _ =
    assembled p M m l W (b.hom.app (op W) s) _ at ev
  simpa only [assembled_component] using ev

/-- A finite jointly monic family of finite constant direct images can
be replaced by a single finite constant direct image with the same bound. -/
theorem boundedFiniteModel_of_jointly_mono [∀ i, IsFinite (p i)]
    [∀ i, LocallyOfFinitePresentation (p i)] [∀ i, Finite (M i)]
    (N : ℕ) (hM : ∀ i, N • 𝟙 (M i) = 0)
    (v : ∀ i, F ⟶ (pushforward (p i)).obj
      ((constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u}).obj (M i)))
    (hv : ∀ (G : Ab X) (a b : G ⟶ F), (∀ i, a ≫ v i = b ≫ v i) → a = b) :
    boundedFiniteModel X N F := by
  classical
  let e (i : I) := (pushforward (p i)).mapIso (constantSheafIso (Y i) (M i))
  let m (i : I) : F ⟶ atComponent p M i := v i ≫ (e i).hom
  let B := AddCommGrpCat.of (∀ i, M i)
  let l (i : I) : M i ⟶ B := AddCommGrpCat.ofHom (show M i →+ (∀ j, M j) from {
    toFun := fun x => (Pi.single i x : ∀ j, M j)
    map_zero' := Pi.single_zero i
    map_add' := fun x y => by
      change (Pi.single i (x + y) : ∀ j, M j) = Pi.single i x + Pi.single i y
      rw [Pi.single_add] })
  let k := combined p M m l
  let e' := (pushforward (Sigma.desc p)).mapIso (constantSheafIso (∐ Y) (∀ i, M i))
  have hB : N • 𝟙 B = 0 := by
    apply ConcreteCategory.hom_ext
    intro x
    funext i
    exact ConcreteCategory.congr_hom (hM i) (x i)
  let : Mono k := mono_combined p M m l fun G a b h => hv G a b fun i => (cancel_mono (e i).hom).mp (by
    rw [Category.assoc, Category.assoc]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    apply ConcreteCategory.hom_ext
    intro s
    apply ContinuousMap.ext
    intro z
    have hl (x : M i) : l i x i = x := by
      change (Pi.single i x : ∀ j, M j) i = x
      exact Pi.single_eq_same (M := fun j => M j) i x
    have hEval := congrArg (fun x : B => x i) (h i W.unop s z)
    change componentSection p M m i W.unop (a.hom.app W s) z =
      componentSection p M m i W.unop (b.hom.app W s) z
    simpa only [hl] using hEval)
  exact ⟨∐ Y, Sigma.desc p, isFinite_sigmaDesc_of_finite p, locallyOfFinitePresentation_sigmaDesc p,
    B, inferInstance, hB, k ≫ e'.inv, inferInstance⟩

end PhilipponEtaleProjectiveModelCoproduct

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponEtaleBoundedFiniteModelReduction (boundedFiniteModel)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleGeometricStalks

namespace PhilipponEtaleGenericModelDetection

universe u v

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- On a Noetherian scheme, finite constant maps that are injective
on relative generic neighborhoods give a single bounded finite model. -/
theorem boundedFiniteModel_of_generic_injectivity_global {X : Scheme.{u}} [NoetherianSpace X]
    (N : ℕ) (F : Ab X) (h : ∀ x : X, ∃ b : FiniteConstantMap F N, ∃ U : X.Opens,
      x ∈ U ∧ ∀ y ∈ closure ({x} : Set X), y ∈ U → injectiveAt b y) :
    boundedFiniteModel X N F := by
  classical
  obtain ⟨s, hs⟩ := exists_finite_detection (fun b : FiniteConstantMap F N => injectiveAt b) h
  let e := Fintype.equivFin s
  let I := ULift.{u} (Fin (Fintype.card s))
  let b (i : I) : FiniteConstantMap F N := (e.symm i.down).val
  let P := ObjectProperty.ofObj (fun x : X => Scheme.pointSmallEtale (algebraicallyClosedGeometricMap x))
  have hP : P.IsConservativeFamilyOfPoints := algebraicallyClosedGeometricPoints_conservative X
  let G (i : I) : Ab X :=
    (pushforward (b i).p).obj ((constantSheaf (b i).Y.smallEtaleTopology AddCommGrpCat.{u}).obj (b i).M)
  let v (i : I) : F ⟶ G i := (b i).map
  let m := Pi.lift v
  have hm : Mono m := by
    let : ∀ Φ : P.FullSubcategory, Mono (Φ.obj.sheafFiber.map m) := by
      intro Φ
      obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ _).mp Φ.property
      rw [← hx]
      obtain ⟨c, hc, hg⟩ := hs x
      let i : I := ⟨e ⟨c, hc⟩⟩
      let T := (Scheme.pointSmallEtale (algebraicallyClosedGeometricMap x)).sheafFiber (A := AddCommGrpCat.{u})
      have hi : b i = c := congrArg Subtype.val (e.symm_apply_apply ⟨c, hc⟩)
      have hi' : injectiveAt (b i) x := by rw [hi]; exact hg
      have hMono : Mono (T.map (v i)) := (AddCommGrpCat.mono_iff_injective _).2 hi'
      have hEq : T.map m ≫ T.map (Pi.π G i) = T.map (v i) := by
        rw [← T.map_comp, Pi.lift_π]
      exact mono_of_mono_fac hEq
    exact (hP.jointlyReflectMonomorphisms AddCommGrpCat.{u}).mono m
  let : ∀ i, IsFinite (b i).p := fun i => (b i).finite
  let : ∀ i, LocallyOfFinitePresentation (b i).p := fun i => (b i).presentation
  let : ∀ i, Finite (b i).M := fun i => (b i).finiteGroup
  refine PhilipponEtaleProjectiveModelCoproduct.boundedFiniteModel_of_jointly_mono
    (fun i => (b i).p) (fun i => (b i).M) N (fun i => (b i).killed) v ?_
  intro H a a' heq
  apply (cancel_mono m).mp
  apply Pi.hom_ext
  intro i
  change a ≫ (Pi.lift v) ≫ Pi.π G i = a' ≫ (Pi.lift v) ≫ Pi.π G i
  simpa only [Category.assoc, Pi.lift_π] using heq i

end PhilipponEtaleGenericModelDetection

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

open AlgebraicGeometry CategoryTheory
open PhilipponEtaleAcyclicCohomology (pullbackConstantIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleDirectImageGerms (evalAtLift evalAtLift_naturality evalAtLift_unit)
open PhilipponEtaleGenericConstantImage (genericInclusion isIso_unit_genericInclusion)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStalkPullback (stalkPullbackIso)


namespace PhilipponEtaleGenericConstantExtension

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- An isomorphism after pullback extends to a coefficient map when the
target coefficient is recovered by the inverse-image unit. -/
theorem exists_extension_of_unit_iso {Y Z : Scheme.{u}} (j : Z ⟶ Y) (E C : Ab Y)
    [IsIso ((pullbackAdjunction j).unit.app C)]
    (e : (pullbackSheaves j).obj E ≅ (pullbackSheaves j).obj C) :
    ∃ a : E ⟶ C, IsIso ((pullbackSheaves j).map a) := by
  let a := pullbackAdjunction j
  let η := a.unit.app C
  let b := a.homEquiv E ((pullbackSheaves j).obj C) e.hom
  let α : E ⟶ C := b ≫ inv η
  have hα : (pullbackSheaves j).map α = e.hom := by
    apply (a.homEquiv E ((pullbackSheaves j).obj C)).injective
    calc
      _ = α ≫ η := by
        simpa only [Category.comp_id, a.homEquiv_id] using
          a.homEquiv_naturality_left α (𝟙 ((pullbackSheaves j).obj C))
      _ = b := by
        change (b ≫ inv η) ≫ η = b
        rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact ⟨α, hα.symm ▸ (inferInstance : IsIso e.hom)⟩

/-- The adjoint of an isomorphism after pullback is injective at geometric
stalks that lift through that pullback. -/
theorem stalk_mono_homEquiv_of_isIso_pullback {X Y Z : Scheme.{u}} (j : Z ⟶ Y) (p : Y ⟶ X)
    {F : Ab X} {G : Ab Y} (α : (pullbackSheaves p).obj F ⟶ G)
    [IsIso ((pullbackSheaves j).map α)]
    {L : Type u} [Field L] [IsSepClosed L] (t : Spec (.of L) ⟶ Z) :
    Mono ((Scheme.pointSmallEtale ((t ≫ j) ≫ p)).sheafFiber.map ((pullbackAdjunction p).homEquiv F G α)) := by
  let E := (pullbackSheaves p).obj F
  let T := (Scheme.pointSmallEtale (t ≫ j)).sheafFiber (A := AddCommGrpCat.{u})
  let U := (Scheme.pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u})
  let d := stalkPullbackIso j t
  have hn : U.map ((pullbackSheaves j).map α) ≫ d.hom.app G = d.hom.app E ≫ T.map α :=
    d.hom.naturality α
  let : IsIso (d.hom.app E ≫ T.map α) := hn ▸ inferInstance
  let : IsIso (T.map α) := IsIso.of_isIso_comp_left (d.hom.app E) (T.map α)
  exact stalk_mono_homEquiv p α (t ≫ j)

end PhilipponEtaleGenericConstantExtension

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleNeighborhoodRestriction (along)


namespace PhilipponEtaleRepresentabilityLocal

universe u

/-- The section over the representing chart that corresponds to its
identity after restriction to an étale neighborhood. -/
abbrev localSection {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    {P : X.Etaleᵒᵖ ⥤ Type u} {W : Y.Etale}
    (e : yoneda.obj W ≅ (along f).op ⋙ P) : P.obj (op ((along f).obj W)) :=
  e.hom.app (op W) (𝟙 W)

theorem map_localSection {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    {P : X.Etaleᵒᵖ ⥤ Type u} {W : Y.Etale} (e : yoneda.obj W ≅ (along f).op ⋙ P)
    {U : Y.Etale} (g : U ⟶ W) :
    P.map ((along f).map g).op (localSection f e) = e.hom.app (op U) g := by
  have h := NatTrans.naturality_apply e.hom g.op (𝟙 W)
  change e.hom.app (op U) (g ≫ 𝟙 W) = P.map ((along f).map g).op (localSection f e) at h
  rw [Category.comp_id] at h
  exact h.symm

section Cover

variable {X : Scheme.{u}} {I : Type u} {Y : I → Scheme.{u}} (f : ∀ i, Y i ⟶ X) [∀ i, Etale (f i)]

private def coverMap (i : I) (U : X.Etale) :
    (along (f i)).obj ((baseChange (f i)).obj U) ⟶ U :=
  MorphismProperty.Over.homMk (pullback.fst U.hom (f i)) (pullback.condition) trivial

private theorem coverMap_covers (hCover : ∀ x : X, ∃ (i : I) (y : Y i), f i y = x) (U : X.Etale) :
    Sieve.ofArrows (fun i => (along (f i)).obj ((baseChange (f i)).obj U))
      (fun i => coverMap f i U) ∈ X.smallEtaleTopology U := by
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, y, hy⟩ := hCover (U.hom x)
  obtain ⟨p, hp, _⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback U.hom (f i)) x y hy.symm
  exact Set.mem_iUnion.mpr ⟨i, ⟨p, hp⟩⟩

/-- A map of étale sheaves is an isomorphism if its restrictions are
isomorphisms on a jointly surjective family of étale neighborhoods. -/
theorem isIso_of_etale_cover_restrictions
    {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type*}
    [∀ a b, FunLike (FA a b) (CA a) (CA b)] [ConcreteCategory A FA]
    [(forget A).ReflectsIsomorphisms] [X.smallEtaleTopology.HasSheafCompose (forget A)]
    (F G : Sheaf X.smallEtaleTopology A) (m : F ⟶ G)
    (hCover : ∀ x : X, ∃ (i : I) (y : Y i), f i y = x)
    (hIso : ∀ i, IsIso (Functor.whiskerLeft (along (f i)).op m.hom)) : IsIso m := by
  have hB (i : I) (U : (Y i).Etale) : Function.Bijective (m.hom.app (op ((along (f i)).obj U))) := by
    let := hIso i
    exact ConcreteCategory.isIso_iff_bijective _ |>.mp
      (inferInstance : IsIso ((Functor.whiskerLeft (along (f i)).op m.hom).app (op U)))
  apply (Sheaf.isLocallyBijective_iff_isIso m).mp
  constructor
  · constructor
    intro U a b hab
    apply X.smallEtaleTopology.superset_covering _ (coverMap_covers f hCover U.unop)
    apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨i⟩
    let p := coverMap f i U.unop
    have hn (s : ToType (F.obj.obj U)) :
        m.hom.app (op ((along (f i)).obj ((baseChange (f i)).obj U.unop))) (F.obj.map p.op s) =
          G.obj.map p.op (m.hom.app U s) := by
      have hh := ConcreteCategory.congr_hom (m.hom.naturality p.op) s
      simp only [ConcreteCategory.comp_apply, Functor.comp_obj, Functor.id_obj, op_unop] at hh
      exact hh
    apply (hB i ((baseChange (f i)).obj U.unop)).1
    exact (hn a).trans ((congrArg (G.obj.map p.op) hab).trans (hn b).symm)
  · constructor
    intro U a
    apply X.smallEtaleTopology.superset_covering _ (coverMap_covers f hCover U)
    apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨i⟩
    exact (hB i ((baseChange (f i)).obj U)).2 (G.obj.map (coverMap f i U).op a)

end Cover

end PhilipponEtaleRepresentabilityLocal

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace


namespace PhilipponGenericFieldNormalization

universe u

variable (X : Scheme.{u}) [IsIntegral X] (L : Type u) [Field L] [Algebra X.functionField L]

/-- The morphism from a field extension of the function field to the generic point. -/
def genericMap : Spec (.of L) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫ X.fromSpecStalk (genericPoint X)

instance : QuasiCompact (genericMap X L) where
  isCompact_preimage U _ _ := (Set.toFinite ((genericMap X L) ⁻¹' U)).isCompact

instance : QuasiSeparated (genericMap X L) :=
  QuasiSeparated.of_quasiSeparatedSpace _

theorem genericMap_apply (x : Spec (.of L)) : genericMap X L x = genericPoint X := by
  have hs : (Spec.map (CommRingCat.ofHom (algebraMap X.functionField L))) x =
      IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X)) := Subsingleton.elim _ _
  exact (Scheme.Hom.comp_apply _ _ _).trans
    ((congrArg (X.fromSpecStalk (genericPoint X)) hs).trans Scheme.fromSpecStalk_closedPoint)

instance : IsDominant (genericMap X L) := by
  constructor
  rw [denseRange_iff_closure_range]
  have hmem : genericPoint X ∈ Set.range (genericMap X L) :=
    ⟨IsLocalRing.closedPoint L, genericMap_apply X L _⟩
  have hs : ({genericPoint X} : Set X) ⊆ Set.range (genericMap X L) :=
    Set.singleton_subset_iff.mpr hmem
  exact Set.eq_univ_of_univ_subset ((genericPoint_spec X).symm ▸ closure_mono hs)

instance : Surjective (genericMap X L).fromNormalization := by
  let f := genericMap X L
  let : IsDominant (f.toNormalization ≫ f.fromNormalization) :=
    f.toNormalization_fromNormalization.symm ▸ inferInstanceAs (IsDominant f)
  let : IsDominant f.fromNormalization := IsDominant.of_comp f.toNormalization f.fromNormalization
  exact surjective_of_isDominant_of_isClosed_range f.fromNormalization
    f.fromNormalization.isClosedMap.isClosed_range

variable {X L}

private theorem generic_preimage_top (U : X.Opens) [Nonempty U] :
    genericMap X L ⁻¹ᵁ U = ⊤ := by
  apply eq_top_iff.mpr
  intro x _
  change genericMap X L x ∈ U
  rw [genericMap_apply]
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by
    obtain ⟨x⟩ := ‹Nonempty U›
    exact ⟨x.val, Set.mem_univ _, x.property⟩)

variable (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)

include hU in
private theorem genericMap_eq_fromSpec :
    genericMap X L =
      Spec.map (X.germToFunctionField U ≫ CommRingCat.ofHom (algebraMap X.functionField L)) ≫
        hU.fromSpec := by
  rw [genericMap, ← hU.fromSpecStalk_eq_fromSpecStalk
    (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by
      obtain ⟨x⟩ := ‹Nonempty U›
      exact ⟨x.val, Set.mem_univ _, x.property⟩)), IsAffineOpen.fromSpecStalk, ← Spec.map_comp_assoc]

private def sectionsIso : Γ(Spec (.of L), genericMap X L ⁻¹ᵁ U) ≅ .of L :=
  (Spec (.of L)).presheaf.mapIso (eqToIso (generic_preimage_top (X := X) (L := L) U).symm).op ≪≫
    Scheme.ΓSpecIso _

include hU in
private theorem app_sectionsIso :
    (genericMap X L).app U ≫ (sectionsIso (L := L) U).hom =
      X.germToFunctionField U ≫ CommRingCat.ofHom (algebraMap X.functionField L) := by
  let f := genericMap X L
  have hPre := generic_preimage_top (X := X) (L := L) U
  have hLE : (⊤ : (Spec (.of L)).Opens) ≤ f ⁻¹ᵁ U := hPre.ge
  let t := X.germToFunctionField U ≫ CommRingCat.ofHom (algebraMap X.functionField L)
  have hs : Spec.map (f.appLE U ⊤ hLE) ≫ hU.fromSpec =
      Spec.map (t ≫ (Scheme.ΓSpecIso (.of L)).inv) ≫ hU.fromSpec := by
    calc
      _ = (isAffineOpen_top (Spec (.of L))).fromSpec ≫ f :=
        hU.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hLE
      _ = _ := by rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv,
        show f = Spec.map t ≫ hU.fromSpec from genericMap_eq_fromSpec U hU, ← Spec.map_comp_assoc]
  have he := Spec.map_injective ((cancel_mono hU.fromSpec).mp hs)
  simp only [sectionsIso, Functor.mapIso_hom, Iso.trans_hom, Iso.op_hom]
  rw [← Category.assoc, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  change f.appLE U ⊤ hLE ≫ (Scheme.ΓSpecIso (.of L)).hom = _
  rw [he, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The integral closure in the source sections identifies with the integral
closure in the original field extension on every nonempty affine chart. -/
def chartIntegralClosureIso :
    letI : Algebra Γ(X, U) L :=
      ((algebraMap X.functionField L).comp (algebraMap Γ(X, U) X.functionField)).toAlgebra
    letI : Algebra Γ(X, U) Γ(Spec (.of L), genericMap X L ⁻¹ᵁ U) :=
      ((genericMap X L).app U).hom.toAlgebra
    integralClosure Γ(X, U) Γ(Spec (.of L), genericMap X L ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      integralClosure Γ(X, U) L := by
  let : Algebra Γ(X, U) L :=
    ((algebraMap X.functionField L).comp (algebraMap Γ(X, U) X.functionField)).toAlgebra
  let : Algebra Γ(X, U) Γ(Spec (.of L), genericMap X L ⁻¹ᵁ U) :=
    ((genericMap X L).app U).hom.toAlgebra
  let e := (sectionsIso (L := L) U).commRingCatIsoToRingEquiv
  refine (AlgEquiv.ofRingEquiv (f := e) ?_).mapIntegralClosure
  intro x
  exact ConcreteCategory.congr_hom (app_sectionsIso (L := L) U hU) x

/-- The affine chart of the normalization indexed by a nonempty affine
open of the base, expressed directly in the extension field. -/
def chartMap :
    letI : Algebra Γ(X, U) L :=
      ((algebraMap X.functionField L).comp (algebraMap Γ(X, U) X.functionField)).toAlgebra
    Spec (.of (integralClosure Γ(X, U) L)) ⟶ (genericMap X L).normalization := by
  let f := genericMap X L
  let : Algebra Γ(X, U) L :=
    ((algebraMap X.functionField L).comp (algebraMap Γ(X, U) X.functionField)).toAlgebra
  let e := (chartIntegralClosureIso (L := L) U hU).toRingEquiv.toCommRingCatIso
  exact Spec.map e.hom ≫ f.normalizationOpenCover.f ⟨U, hU⟩

instance : IsOpenImmersion (chartMap (L := L) U hU) := by
  unfold chartMap
  infer_instance

theorem chartMap_opensRange : (chartMap (L := L) U hU).opensRange =
    (genericMap X L).fromNormalization ⁻¹ᵁ U := by
  unfold chartMap
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact ((genericMap X L).fromNormalization_preimage ⟨U, hU⟩).symm

theorem chartMap_fromNormalization :
    letI : Algebra Γ(X, U) L :=
      ((algebraMap X.functionField L).comp (algebraMap Γ(X, U) X.functionField)).toAlgebra
    chartMap (L := L) U hU ≫ (genericMap X L).fromNormalization =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (integralClosure Γ(X, U) L))) ≫ hU.fromSpec := by
  let f := genericMap X L
  let : Algebra Γ(X, U) L :=
    ((algebraMap X.functionField L).comp (algebraMap Γ(X, U) X.functionField)).toAlgebra
  let e := chartIntegralClosureIso (L := L) U hU
  unfold chartMap
  rw [Category.assoc, f.ι_fromNormalization ⟨U, hU⟩, ← Spec.map_comp_assoc]
  congr 2
  apply CommRingCat.hom_ext
  exact RingHom.ext e.commutes

/-- The inclusion of the extension field into the normalization agrees
on each chart with the canonical map from the fraction field. -/
theorem toNormalization_eq_chartMap :
    letI : Algebra Γ(X, U) L :=
      ((algebraMap X.functionField L).comp (algebraMap Γ(X, U) X.functionField)).toAlgebra
    Spec.map (CommRingCat.ofHom (integralClosure Γ(X, U) L).val.toRingHom) ≫
      chartMap (L := L) U hU = (genericMap X L).toNormalization := by
  let S := Spec (.of L)
  let f := genericMap X L
  let W := f ⁻¹ᵁ U
  let e := sectionsIso (L := L) U
  let : Algebra Γ(X, U) L :=
    ((algebraMap X.functionField L).comp (algebraMap Γ(X, U) X.functionField)).toAlgebra
  let : Algebra Γ(X, U) Γ(S, W) := (f.app U).hom.toAlgebra
  let B := integralClosure Γ(X, U) L
  let C := integralClosure Γ(X, U) Γ(S, W)
  let c := (chartIntegralClosureIso (L := L) U hU).toRingEquiv.toCommRingCatIso
  let a := CommRingCat.ofHom C.val.toRingHom
  let b := CommRingCat.ofHom B.val.toRingHom
  have hEq : a ≫ e.hom = c.hom ≫ b := by
    apply CommRingCat.hom_ext
    ext z
    rfl
  have hW : W = ⊤ := generic_preimage_top (X := X) (L := L) U
  have he : W.ι ≫ Spec.map e.hom = W.toSpecΓ := by
    have hLE : (⊤ : S.Opens) ≤ W := hW.ge
    have eHom : e.hom = S.presheaf.map (homOfLE hLE).op ≫ (Scheme.ΓSpecIso (.of L)).hom := by
      unfold e sectionsIso
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom]
      congr 2
    rw [eHom, Spec.map_comp, ← Category.assoc, ← Scheme.isoSpec_Spec_hom]
    change (W.ι ≫ S.toSpecΓ) ≫ Spec.map (S.presheaf.map (homOfLE hLE).op) = W.toSpecΓ
    have hh : S.presheaf.map (homOfLE hLE).op ≫ S.presheaf.map (homOfLE le_top).op =
        𝟙 Γ(S, W) := by
      rw [← Functor.map_comp]
      exact congrArg S.presheaf.map (Subsingleton.elim _ (𝟙 (op W))) |>.trans (S.presheaf.map_id _)
    rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top, Category.assoc, ← Spec.map_comp,
      hh, Spec.map_id, Category.comp_id]
  have hIso : IsIso W.ι := isIso_of_isOpenImmersion_of_opensRange_eq_top W.ι (by simpa using hW)
  let : IsIso W.ι := hIso
  apply (cancel_epi W.ι).mp
  calc
    _ = W.ι ≫ Spec.map (a ≫ e.hom) ≫ f.normalizationOpenCover.f ⟨U, hU⟩ := by
      unfold chartMap
      change W.ι ≫ Spec.map b ≫ Spec.map c.hom ≫ f.normalizationOpenCover.f ⟨U, hU⟩ = _
      rw [← Spec.map_comp_assoc, ← hEq]
    _ = W.toSpecΓ ≫ Spec.map a ≫ f.normalizationOpenCover.f ⟨U, hU⟩ := by
      rw [Spec.map_comp, ← Category.assoc, ← Category.assoc, he, Category.assoc]
    _ = _ := (f.ι_toNormalization ⟨U, hU⟩).symm

variable (X L) in
/-- The nonempty affine charts of the base cover the normalization. -/
theorem exists_chartMap_range (y : (genericMap X L).normalization) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V) (hVn : Nonempty V),
      letI : Nonempty V := hVn
      y ∈ Set.range (chartMap (L := L) V hV) := by
  let f := genericMap X L
  let C := f.normalizationOpenCover
  let V := C.idx y
  have hy : y ∈ (C.f V).opensRange := C.covers y
  rw [← f.fromNormalization_preimage V] at hy
  have hVn : Nonempty V.val := ⟨⟨f.fromNormalization y, hy⟩⟩
  let : Nonempty V.val := hVn
  refine ⟨V.val, V.property, hVn, ?_⟩
  change y ∈ (chartMap (L := L) V.val V.property).opensRange
  rw [chartMap_opensRange]
  exact hy

/-- A nonzero principal open of a nonempty normalized chart contains the
whole set of points of the normalization over the generic point of the base. -/
theorem genericFiber_subset_range_localization :
    letI : Algebra Γ(X, U) L :=
      ((algebraMap X.functionField L).comp (algebraMap Γ(X, U) X.functionField)).toAlgebra
    ∀ (b : integralClosure Γ(X, U) L), b ≠ 0 →
      (genericMap X L).fromNormalization ⁻¹' ({genericPoint X} : Set X) ⊆
        Set.range (Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away b))) ≫ chartMap (L := L) U hU) := by
  let R := Γ(X, U)
  let : Algebra R L := ((algebraMap X.functionField L).comp (algebraMap R X.functionField)).toAlgebra
  let B := integralClosure R L
  let f := genericMap X L
  let p := f.fromNormalization
  let k := chartMap (L := L) U hU
  let a := Spec.map (CommRingCat.ofHom (algebraMap R B))
  intro b hb y hy
  have hη : p y = genericPoint X := hy
  have hyU : y ∈ k.opensRange := by
    rw [chartMap_opensRange]
    change p y ∈ U
    rw [hη]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by
      obtain ⟨x⟩ := ‹Nonempty U›
      exact ⟨x.val, Set.mem_univ _, x.property⟩)
  obtain ⟨z, rfl⟩ := hyU
  have hz : a z = genericPoint (Spec R) := by
    apply hU.fromSpec.isOpenEmbedding.injective
    rw [genericPoint_eq_of_isOpenImmersion]
    have hh := congrArg (fun m : Spec (.of B) ⟶ X => m z) (chartMap_fromNormalization (L := L) U hU)
    exact hh.symm.trans hη
  have hzbot : z.asIdeal = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := R)
    rw [← show (a z).asIdeal = z.asIdeal.comap (algebraMap R B) from rfl, hz,
      genericPoint_eq_bot_of_affine]
    rfl
  let v := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b)))
  have hv : z ∈ v.opensRange := by
    rw [Scheme.Hom.opensRange_localizationAway (R := .of B) b]
    change b ∉ z.asIdeal
    rw [hzbot]
    exact hb
  obtain ⟨t, ht⟩ := hv
  exact ⟨t, congrArg k ht⟩

/-- A finite separable extension of the function field gives a finite relative
normalization when the base has integrally closed nonempty affine charts. -/
theorem isFinite_fromNormalization [IsLocallyNoetherian X]
    [FiniteDimensional X.functionField L] [Algebra.IsSeparable X.functionField L]
    (hNormal : ∀ V : X.Opens, IsAffineOpen V → Nonempty V → IsIntegrallyClosed Γ(X, V)) :
    IsFinite (genericMap X L).fromNormalization := by
  let f := genericMap X L
  constructor
  intro V hV
  change (f.fromNormalization.app V).hom.Finite
  by_cases hVn : Nonempty V
  · let : Nonempty V := hVn
    let R := Γ(X, V)
    let K := X.functionField
    let : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    let : IsIntegrallyClosed R := hNormal V hV hVn
    let : IsDomain R := inferInstanceAs (IsDomain Γ(X, V))
    let : IsFractionRing R K := functionField_isFractionRing_of_isAffineOpen X V hV
    let : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
    let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra R Γ(Spec (.of L), f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
    let : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L _
    let e := chartIntegralClosureIso (L := L) V hV
    have hFinite : Module.Finite R (integralClosure R Γ(Spec (.of L), f ⁻¹ᵁ V)) :=
      Module.Finite.equiv e.symm.toLinearEquiv
    rw [f.fromNormalization_app hV, CommRingCat.hom_comp]
    exact (f.normalizationObjIso hV).symm.commRingCatIsoToRingEquiv.finite.comp
      (RingHom.finite_algebraMap.mpr hFinite)
  · have hEmpty : (f.fromNormalization ⁻¹ᵁ V) = ⊥ := by
      simp only [show V = ⊥ from le_bot_iff.mp fun x hx => (hVn ⟨⟨x, hx⟩⟩).elim,
        Scheme.Hom.preimage_bot]
    let : Subsingleton Γ(f.normalization, f.fromNormalization ⁻¹ᵁ V) :=
      hEmpty.symm ▸ inferInstanceAs (Subsingleton Γ(f.normalization, ⊥))
    apply RingHom.Finite.of_surjective
    intro x
    refine ⟨0, Subsingleton.elim _ _⟩

end PhilipponGenericFieldNormalization

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (pullbackConstantIso)
open PhilipponEtaleClosedCover (restriction)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleConstantDegreeZero (constantSheafIso)
open PhilipponEtaleConstantRestriction (unit_comp_comparison)
open PhilipponEtaleGenericConstantImage (genericInclusion isIso_unit_genericInclusion)
open PhilipponEtaleNeighborhoodRestriction (along)
open PhilipponEtaleSmallSite (pullbackAdjunction)


namespace PhilipponEtaleGenericConstantCover

universe u

variable {X : Scheme.{u}} {K : Type u} [Field K] (j : Spec (.of K) ⟶ X)
  (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]

private theorem bijective_chart {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Algebra R K] [IsFractionRing R K] (k : Spec (.of R) ⟶ X) [IsOpenImmersion k]
    (hk : genericInclusion R K ≫ k = j) (U : (Spec (.of R)).Etale) :
    Function.Bijective ((restriction M j).hom.app (op ((along k).obj U))) := by
  let a := genericInclusion R K
  let T := pullback (U.hom ≫ k) j
  let S := pullback U.hom a
  let p : T ⟶ U.left := pullback.fst (U.hom ≫ k) j
  have hSquare : IsPullback a (𝟙 _) k j :=
    IsPullback.of_vert_isIso_mono ⟨hk.trans (Category.id_comp j).symm⟩
  have h : IsPullback (pullback.fst U.hom a) (pullback.snd U.hom a) (U.hom ≫ k) j := by
    simpa only [Category.comp_id] using (IsPullback.of_hasPullback U.hom a).paste_vert hSquare
  let e : S ≅ T := h.isoPullback
  let r (s : C(U.left, M)) : C(T, M) := s.comp ⟨p, p.continuous⟩
  let l (s : C(T, M)) : C(S, M) := s.comp ⟨e.hom, e.hom.continuous⟩
  have hl : Function.Bijective l := by
    refine ⟨?_, fun s => ⟨s.comp ⟨e.inv, e.inv.continuous⟩, ?_⟩⟩
    · intro s t he
      apply ContinuousMap.ext
      intro x
      obtain ⟨y, rfl⟩ := e.hom.homeomorph.surjective x
      exact congrArg (fun w : C(S, M) => w y) he
    · apply ContinuousMap.ext
      intro x
      change s (e.inv (e.hom x)) = s x
      rw [← Scheme.Hom.comp_apply, e.hom_inv_id]
      rfl
  let m := restriction M a
  let C := (constantSheaf (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of M)
  let η := (pullbackAdjunction a).unit.app C
  let e₀ := (constantSheafIso (Spec (.of R)) M).hom
  let a₀ := (pushforward a).map (((pullbackConstantIso a).app (AddCommGrpCat.of M)).hom ≫
    (constantSheafIso (Spec (.of K)) M).hom)
  let : IsIso η := isIso_unit_genericInclusion R K M
  have hη : η ≫ a₀ = e₀ ≫ m := unit_comp_comparison a M
  let : IsIso (e₀ ≫ m) := hη ▸ inferInstanceAs (IsIso (η ≫ a₀))
  let : IsIso m := IsIso.of_isIso_comp_left e₀ m
  let ev := (sheafSections (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u}).obj (op U)
  have hComp : l ∘ r = (m.hom.app (op U) : C(U.left, M) → C(S, M)) := by
    funext s
    apply ContinuousMap.ext
    intro x
    change s (p (e.hom x)) = s (pullback.fst U.hom a x)
    exact congrArg s (congrArg (fun g : S ⟶ U.left => g x) h.isoPullback_hom_fst)
  change Function.Bijective r
  apply (hl.of_comp_iff' r).mp
  rw [hComp]
  exact ConcreteCategory.bijective_of_isIso (ev.map m)

variable {I : Type u} (R : I → Type u) [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)]
  [∀ i, IsIntegrallyClosed (R i)] [∀ i, Algebra (R i) K] [∀ i, IsFractionRing (R i) K]
  (k : ∀ i, Spec (.of (R i)) ⟶ X) [∀ i, IsOpenImmersion (k i)]

/-- A finite constant sheaf extends uniquely from the generic point if
the base has a cover by normal affine domains with that fraction field. -/
theorem isIso_unit_of_cover
    (hCover : ∀ x : X, ∃ (i : I) (y : Spec (.of (R i))), k i y = x)
    (hk : ∀ i, genericInclusion (R i) K ≫ k i = j) :
    IsIso ((pullbackAdjunction j).unit.app
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of M))) := by
  let m := restriction M j
  have hm : IsIso m := by
    refine PhilipponEtaleRepresentabilityLocal.isIso_of_etale_cover_restrictions k _ _ m hCover ?_
    intro i
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact bijective_chart j M (k i) (hk i) U.unop
  let F := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of M)
  let η := (pullbackAdjunction j).unit.app F
  let a := (pushforward j).map (((pullbackConstantIso j).app (AddCommGrpCat.of M)).hom ≫
    (constantSheafIso (Spec (.of K)) M).hom)
  have h : η ≫ a = (constantSheafIso X M).hom ≫ m := unit_comp_comparison j M
  let : IsIso (η ≫ a) := h ▸ inferInstanceAs (IsIso ((constantSheafIso X M).hom ≫ m))
  exact IsIso.of_isIso_comp_right η a

end PhilipponEtaleGenericConstantCover

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 950000

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PhilipponEtaleCohomologyAlong (pullbackComposition)
open PhilipponEtaleFinitePresentations (finiteEtalePresentations finiteFieldModel_pullback_of_isSeparated)
open PhilipponEtaleGenericConstantCover (isIso_unit_of_cover)
open PhilipponEtaleGenericModelDetection (FiniteConstantMap injectiveAt)
open PhilipponEtaleGeometricStalks (algebraicallyClosedGeometricMap)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponGenericFieldNormalization
  (genericMap chartMap exists_chartMap_range toNormalization_eq_chartMap isFinite_fromNormalization)


namespace PhilipponEtaleNormalizationCoefficientMap

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev constant (X : Scheme.{u}) (M : AddCommGrpCat.{u}) :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj M

variable (X : Scheme.{u}) [IsIntegral X] (L : Type u) [Field L]
  [Algebra X.functionField L] [FiniteDimensional X.functionField L]

/-- Finite constant coefficients on the normalization are recovered by
direct image from the given extension of the function field. -/
theorem isIso_unit_of_normalization (M : AddCommGrpCat.{u}) [Finite M] :
    IsIso ((pullbackAdjunction (genericMap X L).toNormalization).unit.app
      (constant (genericMap X L).normalization M)) := by
  let K := X.functionField
  let f := genericMap X L
  let I := {V : X.affineOpens // Nonempty V.val}
  let U (i : I) : X.Opens := i.val.val
  let hU (i : I) : IsAffineOpen (U i) := i.val.property
  let : ∀ i : I, Nonempty (U i) := fun i => i.property
  let R (i : I) := Γ(X, U i)
  let : ∀ i : I, IsDomain (R i) := fun i => inferInstanceAs (IsDomain Γ(X, U i))
  let : ∀ i : I, IsFractionRing (R i) K := fun i =>
    functionField_isFractionRing_of_isAffineOpen X (U i) (hU i)
  let : ∀ i : I, Algebra (R i) L := fun i => ((algebraMap K L).comp (algebraMap (R i) K)).toAlgebra
  let : ∀ i : I, IsScalarTower (R i) K L := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let B (i : I) := integralClosure (R i) L
  let : ∀ i : I, IsIntegrallyClosed (B i) := fun _ => integralClosure.isIntegrallyClosedOfFiniteExtension K
  let : ∀ i : I, IsFractionRing (B i) L := fun _ => integralClosure.isFractionRing_of_finite_extension K L
  let k (i : I) : Spec (.of (B i)) ⟶ f.normalization := chartMap (L := L) (U i) (hU i)
  let : ∀ i : I, IsOpenImmersion (k i) := fun i =>
    inferInstanceAs (IsOpenImmersion (chartMap (L := L) (U i) (hU i)))
  let : TopologicalSpace M := ⊥
  let : DiscreteTopology M := ⟨rfl⟩
  apply isIso_unit_of_cover f.toNormalization M (fun i => B i) k ?_ ?_
  · intro x
    obtain ⟨V, hV, hn, h⟩ := exists_chartMap_range X L x
    exact ⟨⟨⟨V, hV⟩, hn⟩, h⟩
  · intro i
    exact toNormalization_eq_chartMap (L := L) (U i) (hU i)

end PhilipponEtaleNormalizationCoefficientMap

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PhilipponEtaleAcyclicCohomology (pullbackConstantIso)
open PhilipponEtaleCohomologyAlong (pullbackComposition)
open PhilipponEtaleBoundedFiniteModelReduction (boundedFiniteModel)
open PhilipponEtaleFiniteConstantColimits (finiteConstant)
open PhilipponEtaleFinitePresentations (finiteEtalePresentations finiteFieldModel_pullback_of_isSeparated)
open PhilipponEtaleGenericConstantExtension
  (exists_extension_of_unit_iso isIso_of_pullback_of_finiteConstant stalk_mono_homEquiv
    stalk_mono_homEquiv_of_isIso_pullback)
open PhilipponEtaleGenericModelDetection (FiniteConstantMap injectiveAt boundedFiniteModel_of_generic_injectivity_global)
open PhilipponEtaleGeometricStalks (algebraicallyClosedGeometricMap algebraicallyClosedGeometricMap_apply)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponGenericFieldNormalization
  (genericMap chartMap chartMap_fromNormalization toNormalization_eq_chartMap
    isFinite_fromNormalization genericFiber_subset_range_localization)


namespace PhilipponEtaleDenseFiniteModel

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev constant (X : Scheme.{u}) (M : AddCommGrpCat.{u}) :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj M
private abbrev specAlgMap (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] :
    Spec (.of B) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R B))

/-- A bounded finite presentation embeds on a dense open into the direct
image of a finite constant sheaf on a finite integral cover. The coefficient
map is defined on the whole base. -/
theorem exists_finiteConstantMap_on_dense_open (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated]
    [IsLocallyNoetherian X]
    (hNormal : ∀ W : X.Opens, IsAffineOpen W → Nonempty W → IsIntegrallyClosed Γ(X, W))
    (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V)
    (N : ℕ) (hN : N ≠ 0) (F : Ab X) (hF : finiteEtalePresentations X N F) :
    ∃ (D : FiniteConstantMap F N) (U : X.Opens), IsIntegral D.Y ∧ genericPoint X ∈ U ∧
      ∀ x ∈ U, injectiveAt D x := by
  let R := Γ(X, V)
  let K := X.functionField
  let : IsDomain R := inferInstanceAs (IsDomain Γ(X, V))
  let : IsFractionRing R K := functionField_isFractionRing_of_isAffineOpen X V hV
  obtain ⟨L, _, _, _, _, b, hb, hC⟩ :=
    PhilipponEtaleFinitePresentationTrivialization.exists_trivialization_on_normalization_of_isFractionRing
      R K hV.fromSpec N hN F hF
  let : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  let B := integralClosure R L
  let A := Localization.Away b
  let f := genericMap X L
  let p := f.fromNormalization
  let j := f.toNormalization
  let k := chartMap (L := L) V hV
  let a := specAlgMap B A
  let v := a ≫ k
  let : IsFinite p := isFinite_fromNormalization (L := L) hNormal
  let : Surjective p := inferInstanceAs (Surjective (genericMap X L).fromNormalization)
  let : IsOpenImmersion a := Scheme.isOpenImmersion_SpecMap_localizationAway (R := .of B) b
  let : IsOpenImmersion k := inferInstanceAs (IsOpenImmersion (chartMap (L := L) V hV))
  let : IsOpenImmersion v := inferInstanceAs (IsOpenImmersion (a ≫ k))
  let : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  let : IsDomain A := Localization.Away.isDomain hb
  let q : A →ₐ[B] L := IsLocalization.Away.liftAlgHom b (f := Algebra.ofId B L)
    (isUnit_iff_ne_zero.mpr (by
      change algebraMap B L b ≠ 0
      simpa only [map_zero] using (IsFractionRing.injective B L).ne hb))
  let t := Spec.map (CommRingCat.ofHom q.toRingHom)
  have htv : t ≫ v = j := by
    have hta : t ≫ a = specAlgMap B L := by
      change Spec.map (CommRingCat.ofHom q.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap B A)) = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg (fun g : B →+* L => Spec.map (CommRingCat.ofHom g)) q.comp_algebraMap
    change t ≫ a ≫ k = j
    rw [← Category.assoc, hta]
    exact toNormalization_eq_chartMap (L := L) V hV
  have hvp : v ≫ p = specAlgMap R A ≫ hV.fromSpec := by
    change (a ≫ k) ≫ p = _
    rw [Category.assoc, chartMap_fromNormalization, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq R B A]
  obtain ⟨M, hM, ⟨e⟩⟩ := hC
  let : Finite M := hM.1
  let E := (pullbackSheaves p).obj F
  let C := constant f.normalization M
  let eV := (pullbackComposition p v _ hvp).app F ≪≫ e.symm
  let eC := (pullbackConstantIso v).app M
  let eJ := pullbackComposition v t j htv
  let β := (eJ.app E).symm ≪≫ (pullbackSheaves t).mapIso (eV ≪≫ eC.symm) ≪≫ eJ.app C
  let : IsIso ((pullbackAdjunction j).unit.app C) :=
    PhilipponEtaleNormalizationCoefficientMap.isIso_unit_of_normalization X L M
  obtain ⟨α, hα⟩ := exists_extension_of_unit_iso j E C β
  let : IsIso ((pullbackSheaves j).map α) := hα
  have hn : (pullbackSheaves t).map ((pullbackSheaves v).map α) ≫ (eJ.app C).hom =
      (eJ.app E).hom ≫ (pullbackSheaves j).map α := eJ.hom.naturality α
  let : IsIso ((pullbackSheaves t).map ((pullbackSheaves v).map α) ≫ (eJ.app C).hom) :=
    hn.symm ▸ inferInstance
  let : IsIso ((pullbackSheaves t).map ((pullbackSheaves v).map α)) :=
    IsIso.of_isIso_comp_right _ (eJ.app C).hom
  let hA : IrreducibleSpace (PrimeSpectrum A) := PrimeSpectrum.irreducibleSpace
  let hL : IrreducibleSpace (PrimeSpectrum L) := PrimeSpectrum.irreducibleSpace
  let : PreconnectedSpace (Spec (.of A)) :=
    @PreirreducibleSpace.preconnectedSpace (PrimeSpectrum A) _ hA.toPreirreducibleSpace
  let : Nonempty (Spec (.of A)) := hA.toNonempty
  let : PreconnectedSpace (Spec (.of L)) :=
    @PreirreducibleSpace.preconnectedSpace (PrimeSpectrum L) _ hL.toPreirreducibleSpace
  let : Nonempty (Spec (.of L)) := hL.toNonempty
  let : IsIso ((pullbackSheaves v).map α) := isIso_of_pullback_of_finiteConstant t _ N
    (show finiteConstant (Spec (.of A)) N _ from ⟨M, hM, ⟨eV.symm⟩⟩)
    (show finiteConstant (Spec (.of A)) N _ from ⟨M, hM, ⟨eC.symm⟩⟩) inferInstance
  let m := (pullbackAdjunction p).homEquiv F C α
  let D : FiniteConstantMap F N := ⟨f.normalization, p, inferInstance, inferInstance, M, hM.1, hM.2, m⟩
  let U : X.Opens := ⟨(p '' (Set.range v)ᶜ)ᶜ,
    (p.isClosedMap _ v.opensRange.isOpen.isClosed_compl).isOpen_compl⟩
  refine ⟨D, U, inferInstanceAs (IsIntegral f.normalization), ?_, ?_⟩
  · change genericPoint X ∉ p '' (Set.range v)ᶜ
    rintro ⟨y, hy, he⟩
    exact hy (genericFiber_subset_range_localization (L := L) V hV b hb he)
  · intro x hx
    let s := algebraicallyClosedGeometricMap x
    obtain ⟨y, hy⟩ := p.surjective x
    have hyU : y ∈ v.opensRange := by
      by_contra hn
      exact hx ⟨y, hn, hy⟩
    obtain ⟨w, hw, hwu⟩ := PhilipponEtaleFinitePointLifts.exists_lift_in_open_of_finite p s v.opensRange
      ⟨y, hyU, hy.trans (algebraicallyClosedGeometricMap_apply x).symm⟩
    have hRange : Set.range w ⊆ Set.range v := by
      rintro _ ⟨z, rfl⟩
      rw [Subsingleton.elim z default]
      exact hwu
    let u := IsOpenImmersion.lift v w hRange
    have he : (u ≫ v) ≫ p = s := by rw [IsOpenImmersion.lift_fac, hw]
    have hm := stalk_mono_homEquiv_of_isIso_pullback v p α u
    rw [he] at hm
    exact (AddCommGrpCat.mono_iff_injective _).mp hm

/-- A finite constant direct image supported at a closed point detects the
stalk there. -/
theorem exists_finiteConstantMap_at_closed_point (X : Scheme.{u}) [X.IsSeparated]
    [IsLocallyNoetherian X] (x : X) (hx : IsClosed ({x} : Set X))
    (N : ℕ) (hN : N ≠ 0) (F : Ab X) (hF : finiteEtalePresentations X N F) :
    ∃ D : FiniteConstantMap F N, injectiveAt D x := by
  let K := X.residueField x
  let i := X.fromSpecResidueField x
  let : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp hx
  obtain ⟨L, _, _, _, _, M, hM, ⟨e⟩⟩ := finiteFieldModel_pullback_of_isSeparated X K i N hN F hF
  let a := specAlgMap K L
  let p := a ≫ i
  let : IsFinite a := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr (inferInstance : Module.Finite K L))
  let : Subsingleton (Spec K) := inferInstanceAs (Subsingleton (PrimeSpectrum (X.residueField x)))
  let : Surjective a := ⟨fun z => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ z⟩⟩
  let : IsFinite p := inferInstanceAs (IsFinite (a ≫ i))
  let β := ((pullbackComposition i a p rfl).app F).symm ≪≫ e.symm
  let m := (pullbackAdjunction p).homEquiv F (constant (Spec (.of L)) M) β.hom
  let D : FiniteConstantMap F N := ⟨Spec (.of L), p, inferInstance, inferInstance, M, hM.1, hM.2, m⟩
  refine ⟨D, ?_⟩
  let s := algebraicallyClosedGeometricMap x
  have hRange : s default ∈ Set.range i := by
    rw [algebraicallyClosedGeometricMap_apply]
    exact ⟨IsLocalRing.closedPoint K, X.fromSpecResidueField_apply _ _⟩
  obtain ⟨s', hs'⟩ := PhilipponEtaleStalkPullback.exists_point_lift_of_mem_range i s hRange
  obtain ⟨t, ht⟩ := PhilipponEtaleFinitePointLifts.exists_lift_of_finite_surjective a s'
  have he : t ≫ p = s := by
    change t ≫ a ≫ i = s
    rw [← Category.assoc, ht, hs']
  have hg := stalk_mono_homEquiv p β.hom t
  rw [he] at hg
  exact (AddCommGrpCat.mono_iff_injective _).mp hg

/-- On a normal integral Noetherian curve every bounded finite presentation
embeds in a constant finite direct image. -/
theorem boundedFiniteModel_of_normal_curve (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated]
    [IsLocallyNoetherian X] [NoetherianSpace X]
    (hNormal : ∀ W : X.Opens, IsAffineOpen W → Nonempty W → IsIntegrallyClosed Γ(X, W))
    (hClosed : ∀ x : X, x ≠ genericPoint X → IsClosed ({x} : Set X))
    (N : ℕ) (hN : N ≠ 0) : finiteEtalePresentations X N ≤ boundedFiniteModel X N := by
  intro F hF
  obtain ⟨V, hV, hη, _⟩ := exists_isAffineOpen_mem_and_subset (show genericPoint X ∈ (⊤ : X.Opens) from trivial)
  let : Nonempty V := ⟨⟨_, hη⟩⟩
  obtain ⟨D, U, _, hU, hInj⟩ := exists_finiteConstantMap_on_dense_open X hNormal V hV N hN F hF
  apply boundedFiniteModel_of_generic_injectivity_global
  intro x
  by_cases hx : x = genericPoint X
  · subst x
    exact ⟨D, U, hU, fun _ _ hy => hInj _ hy⟩
  · obtain ⟨E, he⟩ := exists_finiteConstantMap_at_closed_point X x (hClosed x hx) N hN F hF
    refine ⟨E, ⊤, trivial, fun y hy _ => ?_⟩
    rw [(hClosed x hx).closure_eq] at hy
    exact (Set.mem_singleton_iff.mp hy).symm ▸ he

end PhilipponEtaleDenseFiniteModel

end

section

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped nonZeroDivisors
universe u

namespace PhilipponCartierBoundaryNormality

lemma isIntegrallyClosed_sections_of_stalks
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) [IsDomain Γ(X, U)]
    (hn : ∀ x : X, x ∈ U → IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIntegrallyClosed Γ(X, U) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro P _ hP
  let y : PrimeSpectrum Γ(X, U) := ⟨P, inferInstance⟩
  let S : Type u := X.presheaf.stalk (hU.fromSpec y)
  letI : Algebra Γ(X, U) S := TopCat.Presheaf.algebra_section_stalk X.presheaf
    (⟨hU.fromSpec y, (hU.isoSpec.inv y).property⟩ : U)
  haveI : IsLocalization.AtPrime S P :=
    hU.isLocalization_stalk' y (hU.isoSpec.inv y).property
  haveI : IsIntegrallyClosed S := hn _ (hU.isoSpec.inv y).property
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv P.primeCompl S (Localization.AtPrime P)).toRingEquiv

end PhilipponCartierBoundaryNormality

end

section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponNormalProjectiveCompactification

lemma normal_stalk_spec (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (x : Spec (.of A)) : IsIntegrallyClosed ((Spec (.of A)).presheaf.stalk x) := by
  letI : Algebra A ((Spec (.of A)).presheaf.stalk x) :=
    (StructureSheaf.toStalk A x).hom.toAlgebra
  haveI : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk x) x.asIdeal := by
    convert! StructureSheaf.IsLocalization.to_stalk A x
  exact isIntegrallyClosed_of_isLocalization ((Spec (.of A)).presheaf.stalk x)
    x.asIdeal.primeCompl x.asIdeal.primeCompl_le_nonZeroDivisors
end PhilipponNormalProjectiveCompactification

end

section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAlterationProjection

lemma projective_space_irreducible (K : Type u) [Field K] (n : ℕ) :
    IrreducibleSpace (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K
  have hprime : (⊥ : HomogeneousIdeal 𝒜).toIdeal.IsPrime := by
    change (⊥ : Ideal (MvPolynomial (Fin (n + 1)) K)).IsPrime
    infer_instance
  have hrel : ¬ HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥ := by
    intro h
    have hX : (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial _ K) ∈
        HomogeneousIdeal.irrelevant 𝒜 :=
      HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < 1)
        (ProjSpace.X_mem_one K n 0)
    have hz : (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial _ K) = 0 := by
      change MvPolynomial.X 0 ∈ (⊥ : Ideal (MvPolynomial (Fin (n + 1)) K))
      exact h hX
    exact MvPolynomial.X_ne_zero _ hz
  let η : ProjectiveSpectrum 𝒜 := ⟨⊥, hprime, hrel⟩
  have hη : IsGenericPoint η (Set.univ : Set (ProjectiveSpectrum 𝒜)) := by
    apply Set.eq_univ_of_forall
    intro y
    exact (ProjectiveSpectrum.le_iff_mem_closure 𝒜 η y).mp (show
      η.asHomogeneousIdeal ≤ y.asHomogeneousIdeal from bot_le)
  exact (irreducibleSpace_def _).mpr hη.isIrreducible
end PhilipponAlterationProjection

end

section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAlterationProjection

lemma projective_space_integral (K : Type u) [Field K] (r : ℕ) :
    IsIntegral (Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)) := by
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)
  letI : IrreducibleSpace P := projective_space_irreducible K r
  haveI (x : P) : _root_.IsReduced (P.presheaf.stalk x) := by
    let L := HomogeneousLocalization.AtPrime
      (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K) x.asHomogeneousIdeal.toIdeal
    letI : _root_.IsReduced L := isReduced_of_injective
      (algebraMap L (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
      (HomogeneousLocalization.val_injective x.asHomogeneousIdeal.toIdeal.primeCompl)
    let e := (Proj.stalkIso (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K) x).commRingCatIsoToRingEquiv
    exact isReduced_of_injective e e.injective
  letI : IsReduced P := isReduced_of_isReduced_stalk P
  exact isIntegral_of_irreducibleSpace_of_isReduced P

end PhilipponAlterationProjection

end

section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponProjectiveLineCharts
variable (R : Type u) [CommRing R] (i : Fin 2)

abbrev grading := MvPolynomial.homogeneousSubmodule (Fin 2) R
abbrev chartRing := Away (grading R) (MvPolynomial.X i)

noncomputable def specialize :
    MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 1) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun j => if j = i then 1 else MvPolynomial.X (0 : Fin 1))

lemma specialize_X_self : specialize R i (MvPolynomial.X i) = 1 := by
  simp [specialize]

lemma specialize_unit : IsUnit (specialize R i (MvPolynomial.X i)) :=
  isUnit_iff_exists_inv.mpr ⟨1, by rw [specialize_X_self]; simp⟩

noncomputable def fromAway : chartRing R i →+* MvPolynomial (Fin 1) R :=
  (Localization.awayLift (specialize R i) (MvPolynomial.X i)
    (specialize_unit R i)).comp
    (algebraMap (chartRing R i) (Localization.Away (MvPolynomial.X i :
      MvPolynomial (Fin 2) R)))

lemma fromAway_coeff (r : R) :
    fromAway R i (algebraMap R (chartRing R i) r) = MvPolynomial.C r := by
  change Localization.awayLift (specialize R i) _ (specialize_unit R i)
    ((algebraMap R (chartRing R i) r).val) = _
  rw [ProjSpace.val_algebraMap]
  simp only [Localization.awayLift, IsLocalization.Away.lift_eq]
  simp [specialize]

lemma fromAway_ratio (j : Fin 2) :
    fromAway R i (ProjSpace.ratio R 1 i j) = specialize R i (MvPolynomial.X j) := by
  change Localization.awayLift (specialize R i) _ (specialize_unit R i) (ProjSpace.ratio R 1 i j).val = _
  rw [ProjSpace.ratio, Away.val_mk]
  simpa only [one_pow, mul_one] using
    Localization.awayLift_mk (specialize R i) (MvPolynomial.X i)
      (MvPolynomial.X j) 1 (by rw [specialize_X_self]; simp) 1

noncomputable def fromAwayAlg : chartRing R i →ₐ[R] MvPolynomial (Fin 1) R where
  __ := fromAway R i
  commutes' := fromAway_coeff R i

lemma fromAwayAlg_apply (x : chartRing R i) : fromAwayAlg R i x = fromAway R i x := rfl

noncomputable def toAwayAlg : MvPolynomial (Fin 1) R →ₐ[R] chartRing R i :=
  MvPolynomial.aeval (fun _ : Fin 1 => ProjSpace.ratio R 1 i i.rev)

lemma toAwayAlg_X (j : Fin 1) : toAwayAlg R i (MvPolynomial.X j) = ProjSpace.ratio R 1 i i.rev :=
  MvPolynomial.aeval_X _ _

lemma from_to : (fromAwayAlg R i).comp (toAwayAlg R i) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, toAwayAlg_X, fromAwayAlg_apply, fromAway_ratio, AlgHom.id_apply]
  fin_cases i <;> fin_cases j <;> simp [specialize]

lemma to_from : (toAwayAlg R i).comp (fromAwayAlg R i) = AlgHom.id R _ := by
  apply AlgHom.ext_of_adjoin_eq_top (ProjSpace.adjoin_range_ratio R 1 i)
  rintro _ ⟨j, rfl⟩
  change toAwayAlg R i (fromAway R i (ProjSpace.ratio R 1 i j)) = ProjSpace.ratio R 1 i j
  rw [fromAway_ratio]
  fin_cases i <;> fin_cases j <;>
    simp [specialize, toAwayAlg, ProjSpace.ratio_self]

noncomputable def equiv : chartRing R i ≃ₐ[R] MvPolynomial (Fin 1) R :=
  AlgEquiv.ofAlgHom (fromAwayAlg R i) (toAwayAlg R i) (from_to R i) (to_from R i)

/-- The standard affine-space chart in projective space. -/
noncomputable def embedding : Spec (.of (MvPolynomial (Fin 1) R)) ⟶ Proj (grading R) :=
  Spec.map (CommRingCat.ofHom (equiv R i).toRingEquiv.toRingHom) ≫
    Proj.awayι (grading R) (MvPolynomial.X i)
      (ProjSpace.X_mem_one R 1 i) one_pos

instance embedding_isOpenImmersion : IsOpenImmersion (embedding R i) := by
  haveI : IsIso (CommRingCat.ofHom (equiv R i).toRingEquiv.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (equiv R i).bijective
  unfold embedding
  infer_instance

lemma embedding_over : embedding R i ≫ ProjSpace.π R 1 =
    Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin 1) R)) := by
  rw [embedding, Category.assoc, ProjSpace.awayι_comp_π, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (equiv R i).commutes r

end PhilipponProjectiveLineCharts

end

section

set_option autoImplicit false
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleProjectiveLineModels

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev Line (R : Type u) [CommRing R] := Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R)

/-- Pulling back a projective line over an affine base gives the usual
projective line over the new affine base. -/
lemma exists_standardLine_model (R A : Type u) [CommRing R] [CommRing A]
    (v : Spec (.of A) ⟶ Spec (.of R)) :
    ∃ m : Line A ⟶ Line R, IsPullback (ProjSpace.π A 1) m v (ProjSpace.π R 1) := by
  let ρ := (Spec.preimage v).hom
  let : Algebra R A := ρ.toAlgebra
  let m := ProjSpace.map R A 1
  have hv : Spec.map (CommRingCat.ofHom (algebraMap R A)) = v := Spec.map_preimage v
  refine ⟨m, ?_⟩
  rw [← hv]
  exact (ProjSpace.isPullback_map R A 1).flip

end PhilipponEtaleProjectiveLineModels

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponEtaleBoundedFiniteModelReduction (boundedFiniteModel)
open PhilipponEtaleFinitePresentations (finiteEtalePresentations ind_boundedFiniteModel_of_finitePresentations)


namespace PhilipponEtaleProjectiveLineGenericModel

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev Line (K : Type u) [CommRing K] :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)

private theorem exists_chart_lift (K : Type u) [Field K] (x : Line K) :
    ∃ (i : Fin 2) (z : Spec (.of (MvPolynomial (Fin 1) K))),
      PhilipponProjectiveLineCharts.embedding K i z = x := by
  let C := (ProjSpace.affineOpenCover K 1).openCover
  let i := C.idx x
  have hx : x ∈ (C.f i).opensRange := C.covers x
  have h : (PhilipponProjectiveLineCharts.embedding K i).opensRange = (C.f i).opensRange := by
    let e := PhilipponProjectiveLineCharts.equiv K i
    let a := CommRingCat.ofHom e.toRingEquiv.toRingHom
    let : IsIso a := (ConcreteCategory.isIso_iff_bijective _).mpr e.bijective
    unfold PhilipponProjectiveLineCharts.embedding
    rw [Scheme.Hom.opensRange_comp_of_isIso]
    rfl
  refine ⟨i, ?_⟩
  change x ∈ (PhilipponProjectiveLineCharts.embedding K i).opensRange
  exact h.symm ▸ hx

/-- Every stalk of a field-valued relative projective line is normal. -/
theorem isIntegrallyClosed_stalk_of_iso (K : Type u) [Field K] {P : Scheme.{u}}
    (e : Line K ≅ P) (x : P) : IsIntegrallyClosed (P.presheaf.stalk x) := by
  obtain ⟨y, rfl⟩ := e.hom.surjective x
  obtain ⟨i, z, rfl⟩ := exists_chart_lift K y
  let k := PhilipponProjectiveLineCharts.embedding K i ≫ e.hom
  let : IsOpenImmersion k := inferInstanceAs
    (IsOpenImmersion (PhilipponProjectiveLineCharts.embedding K i ≫ e.hom))
  let : UniqueFactorizationMonoid (MvPolynomial (Fin 1) K) := MvPolynomial.uniqueFactorizationMonoid (Fin 1)
  let : IsIntegrallyClosed (MvPolynomial (Fin 1) K) := UniqueFactorizationMonoid.instIsIntegrallyClosed
  let : IsIntegrallyClosed ((Spec (.of (MvPolynomial (Fin 1) K))).presheaf.stalk z) :=
    PhilipponNormalProjectiveCompactification.normal_stalk_spec _ z
  exact IsIntegrallyClosed.of_equiv (asIso (k.stalkMap z)).symm.commRingCatIsoToRingEquiv

private theorem isClosed_singleton_of_ne_generic {K : Type u} [Field K] {P : Scheme.{u}}
    [IsIntegral P] (e : Line K ≅ P) (x : P) (hx : x ≠ genericPoint P) :
    IsClosed ({x} : Set P) := by
  apply closure_subset_iff_isClosed.mp
  intro y hy
  have hxy := specializes_iff_mem_closure.mpr hy
  obtain ⟨y₁, hy₁⟩ := e.hom.surjective y
  obtain ⟨i, w, hw⟩ := exists_chart_lift K y₁
  let A := MvPolynomial (Fin 1) K
  let k := PhilipponProjectiveLineCharts.embedding K i ≫ e.hom
  let : IsOpenImmersion k := inferInstanceAs
    (IsOpenImmersion (PhilipponProjectiveLineCharts.embedding K i ≫ e.hom))
  have hkw : k w = y := (congrArg e.hom hw).trans hy₁
  have hr : x ∈ k.opensRange := hxy.mem_open k.opensRange.isOpen ⟨w, hkw⟩
  obtain ⟨z, hz⟩ := hr
  have hne : z.asIdeal ≠ ⊥ := by
    intro H
    have hgen : z = genericPoint (Spec (.of A)) := by
      rw [genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext H
    exact hx (hz.symm.trans ((congrArg k hgen).trans (genericPoint_eq_of_isOpenImmersion k)))
  let : Ring.KrullDimLE 1 A := by
    rw [Ring.krullDimLE_iff]
    simp [A, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  have hclosed : IsClosed ({z} : Set (Spec (.of A))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr (z.isPrime.isMaximal_of_ne_bot hne)
  have hk : k z ⤳ k w := by rwa [hz, hkw]
  have hzw : z ⤳ w := k.isOpenEmbedding.isInducing.specializes_iff.mp hk
  have hm := hzw.mem_closure
  rw [hclosed.closure_eq] at hm
  exact Set.mem_singleton_iff.mpr (hkw.symm.trans ((congrArg k (Set.mem_singleton_iff.mp hm)).trans hz))

/-- Every bounded finite étale presentation on an actual relative projective
line embeds in a finite constant direct image. -/
theorem boundedFiniteModel_of_projectiveLine
    (R K : Type u) [CommRing R] [Field K] (v : Spec (.of K) ⟶ Spec (.of R)) {P : Scheme.{u}}
    (r : P ⟶ Spec (.of K)) (d : P ⟶ Line R) (hP : IsPullback r d v (ProjSpace.π R 1))
    (N : ℕ) (hN : N ≠ 0) : finiteEtalePresentations P N ≤ boundedFiniteModel P N := by
  obtain ⟨w, hw⟩ := PhilipponEtaleProjectiveLineModels.exists_standardLine_model R K v
  let e := hw.isoPullback ≪≫ hP.isoPullback.symm
  let : IsIntegral (Line K) := PhilipponAlterationProjection.projective_space_integral K 1
  let : IsIntegral P := IsIntegral.of_isIso e.hom
  let : IsProper r := MorphismProperty.of_isPullback hP.flip (inferInstance : IsProper (ProjSpace.π R 1))
  let : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian r
  let : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace r
  let : IsNoetherian P := ⟨⟩
  have hTerminal : terminal.from P = r ≫ terminal.from (Spec (.of K)) := terminal.hom_ext _ _
  let : P.IsSeparated := ⟨hTerminal.symm ▸ inferInstanceAs
    (IsSeparated (r ≫ terminal.from (Spec (.of K))))⟩
  have hNormal (V : P.Opens) (hV : IsAffineOpen V) (hVn : Nonempty V) :
      IsIntegrallyClosed Γ(P, V) := by
    let : Nonempty V := hVn
    exact PhilipponCartierBoundaryNormality.isIntegrallyClosed_sections_of_stalks hV
      (fun x _ => isIntegrallyClosed_stalk_of_iso K e x)
  exact PhilipponEtaleDenseFiniteModel.boundedFiniteModel_of_normal_curve
    P hNormal (fun x hx => isClosed_singleton_of_ne_generic e x hx) N hN

/-- Bounded torsion sheaves on a field-valued projective line are filtered
colimits of sheaves that embed in finite constant direct images. -/
theorem ind_boundedFiniteModel_of_projectiveLine
    (R K : Type u) [CommRing R] [Field K] (v : Spec (.of K) ⟶ Spec (.of R)) {P : Scheme.{u}}
    (r : P ⟶ Spec (.of K)) (d : P ⟶ Line R) (hP : IsPullback r d v (ProjSpace.π R 1))
    (N : ℕ) (hN : N ≠ 0) (F : Sheaf P.smallEtaleTopology AddCommGrpCat.{u}) (hF : N • 𝟙 F = 0) :
    ObjectProperty.ind.{u} (boundedFiniteModel P N) F :=
  ind_boundedFiniteModel_of_finitePresentations P N F hF (boundedFiniteModel_of_projectiveLine R K v r d hP N hN)

end PhilipponEtaleProjectiveLineGenericModel

end

section

attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (R K : Type u) [CommRing R] [Field K] (v : Spec (.of K) ⟶ Spec (.of R))
    {P : Scheme.{u}} (r : P ⟶ Spec (.of K))
    (d : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R))
    (hP : IsPullback r d v (ProjSpace.π R 1)) (N : ℕ) (hN : N ≠ 0)
    (F : Sheaf P.smallEtaleTopology AddCommGrpCat.{u}) (hF : N • 𝟙 F = 0) :
    ObjectProperty.ind.{u} (PhilipponEtaleBoundedFiniteModelReduction.boundedFiniteModel P N) F := by
  exact PhilipponEtaleProjectiveLineGenericModel.ind_boundedFiniteModel_of_projectiveLine
    R K v r d hP N hN F hF

end

end
