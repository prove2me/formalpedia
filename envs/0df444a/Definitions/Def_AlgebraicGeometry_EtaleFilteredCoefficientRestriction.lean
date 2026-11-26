-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleFilteredCoefficientRestriction
-- name    : AlgebraicGeometry_EtaleFilteredCoefficientRestriction
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-26T07:40:57.726051+00:00
-- url     : https://prove2.me/theorems/91620a8b-3da6-551c-be49-5788b9fc5255
-- title:
--   Restriction through bounded coefficient embeddings and filtered colimits
-- statement:
--   Étale cohomology comparisons pass from bounded coefficient embeddings and their filtered stages to a given sheaf.
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

noncomputable section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) etaleFilteredCoefficientRestrictionHasSheafify (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) etaleFilteredCoefficientRestrictionHasExt (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) etaleFilteredCoefficientRestrictionEnoughInjectives (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits


namespace PhilipponExtComparison

universe u v u' v' w w'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  {Q : C} {P : D} (p : P ⟶ R.obj Q)

private theorem comparison_comp {M N : C} {n k m : ℕ} (x : Ext Q M n) (a : Ext M N k)
    (h : n + k = m) :
    comparison R p N m (x.comp a h) =
      (comparison R p M n x).comp (a.mapExactFunctor R) h := by
  change (Ext.mk₀ p).comp ((x.comp a h).mapExactFunctor R) (zero_add m) = _
  rw [Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc (Ext.mk₀ p) (x.mapExactFunctor R) (a.mapExactFunctor R)
    (zero_add n) h (by simpa using h)).symm

private theorem comparison_boundary {S : ShortComplex C} (hS : S.ShortExact)
    (n : ℕ) (x : Ext Q S.X₃ n) :
    comparison R p S.X₁ (n + 1) (x.comp hS.extClass rfl) =
      (comparison R p S.X₃ n x).comp (hS.map_of_exact R).extClass rfl := by
  rw [comparison_comp, Ext.mapExactFunctor_extClass]

private def post {A : Type*} [Category* A] [Abelian A] [HasExt A]
    (Z : A) (n : ℕ) {U V : A} (a : U ⟶ V) :=
  (Ext.mk₀ a).postcomp Z (add_zero n)

private theorem post_comm {U V : C} (a : U ⟶ V) (n : ℕ) :
    (post P n (R.map a)).comp (comparison R p U n) =
      (comparison R p V n).comp (post Q n a) :=
  AddMonoidHom.ext (fun x => (comparison_post R p a n x).symm)

private theorem boundary_comm {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    ((hS.map_of_exact R).extClass.postcomp P (rfl : n + 1 = n + 1)).comp
        (comparison R p S.X₃ n) =
      (comparison R p S.X₁ (n + 1)).comp (hS.extClass.postcomp Q rfl) :=
  AddMonoidHom.ext (fun x => (comparison_boundary R p hS n x).symm)

/-- Comparison passes from embedding targets to test coefficients by the
long exact sequence. The two transfer hypotheses promote injectivity and
surjectivity on the test coefficients to the full class. -/
theorem comparison_bijective_of_test_embeddings (B T : C → Prop)
    (h₀ : ∀ M, B M → Function.Bijective (comparison R p M 0))
    (hEmb : ∀ M, T M → ∃ (J : C) (i : M ⟶ J), Mono i ∧ B (cokernel i) ∧
      ∀ n, Function.Bijective (comparison R p J n))
    (hInj : ∀ n, (∀ M, T M → Function.Injective (comparison R p M n)) →
      ∀ M, B M → Function.Injective (comparison R p M n))
    (hSurj : ∀ n, (∀ M, T M → Function.Surjective (comparison R p M n)) →
      ∀ M, B M → Function.Surjective (comparison R p M n))
    (n : ℕ) (M : C) (hM : B M) : Function.Bijective (comparison R p M n) := by
  induction n generalizing M with
  | zero => exact h₀ M hM
  | succ n ih =>
    have inj (A : C) (hA : T A) : Function.Injective (comparison R p A (n + 1)) := by
      obtain ⟨J, i, _, hQ, hJ⟩ := hEmb A hA
      let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
      let hT := hS.map_of_exact R
      exact AddMonoidHom.injective_of_surjective_of_injective_of_injective
        (post Q n S.g) (hS.extClass.postcomp Q (rfl : n + 1 = n + 1))
        (post Q (n + 1) S.f) (post P n (R.map S.g))
        (hT.extClass.postcomp P (rfl : n + 1 = n + 1)) (post P (n + 1) (R.map S.f))
        (comparison R p S.X₂ n) (comparison R p S.X₃ n)
        (comparison R p S.X₁ (n + 1)) (comparison R p S.X₂ (n + 1))
        (post_comm R p S.g n) (boundary_comm R p hS n) (post_comm R p S.f (n + 1))
        ((ShortComplex.ab_exact_iff_function_exact _).mp (Ext.covariant_sequence_exact₃' Q hS n (n + 1) rfl))
        ((ShortComplex.ab_exact_iff_function_exact _).mp (Ext.covariant_sequence_exact₁' Q hS n (n + 1) rfl))
        ((ShortComplex.ab_exact_iff_function_exact _).mp (Ext.covariant_sequence_exact₃' P hT n (n + 1) rfl))
        (hJ n).surjective (ih S.X₃ hQ).injective (hJ (n + 1)).injective
    have injAll := hInj (n + 1) inj
    have surj (A : C) (hA : T A) : Function.Surjective (comparison R p A (n + 1)) := by
      obtain ⟨J, i, _, hQ, hJ⟩ := hEmb A hA
      let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
      let hT := hS.map_of_exact R
      exact AddMonoidHom.surjective_of_surjective_of_surjective_of_injective
        (hS.extClass.postcomp Q (rfl : n + 1 = n + 1)) (post Q (n + 1) S.f)
        (post Q (n + 1) S.g) (hT.extClass.postcomp P (rfl : n + 1 = n + 1))
        (post P (n + 1) (R.map S.f)) (post P (n + 1) (R.map S.g))
        (comparison R p S.X₃ n) (comparison R p S.X₁ (n + 1))
        (comparison R p S.X₂ (n + 1)) (comparison R p S.X₃ (n + 1))
        (boundary_comm R p hS n) (post_comm R p S.f (n + 1)) (post_comm R p S.g (n + 1))
        ((ShortComplex.ab_exact_iff_function_exact _).mp (Ext.covariant_sequence_exact₂' Q hS (n + 1)))
        ((ShortComplex.ab_exact_iff_function_exact _).mp (Ext.covariant_sequence_exact₁' P hT n (n + 1) rfl))
        ((ShortComplex.ab_exact_iff_function_exact _).mp (Ext.covariant_sequence_exact₂' P hT (n + 1)))
        (ih S.X₃ hQ).surjective (hJ (n + 1)).surjective (injAll S.X₃ hQ)
    exact ⟨injAll M hM, hSurj (n + 1) surj M hM⟩

end PhilipponExtComparison

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponExtComparison (comparison comparison_mk₀)


namespace PhilipponExtComparisonComposition

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasExt C] [HasExt D]

private theorem comparison_boundary (L : C ⥤ D)
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {A : C} {B : D} (a : B ⟶ L.obj A) {S : ShortComplex C} (hS : S.ShortExact)
    (n : ℕ) (x : Ext A S.X₃ n) :
    comparison L a S.X₁ (n + 1) (x.comp hS.extClass rfl) =
      (comparison L a S.X₃ n x).comp (hS.map_of_exact L).extClass rfl := by
  change (Ext.mk₀ a).comp ((x.comp hS.extClass rfl).mapExactFunctor L) (zero_add (n + 1)) = _
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc (Ext.mk₀ a) (x.mapExactFunctor L) (hS.map_of_exact L).extClass
    (zero_add n) rfl (zero_add (n + 1))).symm

/-- Ext comparison along an exact functor and a map of short exact
sequences commutes with the connecting maps. -/
theorem comparison_boundary_along (L : C ⥤ D)
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {A : C} {B : D} (a : B ⟶ L.obj A) {S : ShortComplex C} {T : ShortComplex D}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S.map L ⟶ T)
    (n : ℕ) (x : Ext A S.X₃ n) :
    (comparison L a S.X₁ (n + 1) (x.comp hS.extClass rfl)).comp
          (Ext.mk₀ φ.τ₁) (add_zero (n + 1)) =
      ((comparison L a S.X₃ n x).comp (Ext.mk₀ φ.τ₃) (add_zero n)).comp hT.extClass rfl := by
  let hL := hS.map_of_exact L
  let y := comparison L a S.X₃ n x
  have h := hL.extClass_naturality hT φ
  rw [comparison_boundary L a hS n x]
  exact (Ext.comp_assoc_of_third_deg_zero y hL.extClass (Ext.mk₀ φ.τ₁) rfl).trans
    ((congrArg (fun cls => y.comp cls rfl) h).trans
      (Ext.comp_assoc_of_second_deg_zero y (Ext.mk₀ φ.τ₃) hT.extClass rfl).symm)

variable {E : Type*} [Category* E] [Abelian E] [HasExt E] [EnoughInjectives C]

set_option maxHeartbeats 800000 in
/-- The Ext comparisons for two exact functors compose, including the
transport along an isomorphism with a third exact functor. -/
theorem comparison_comp_iso (L : C ⥤ D) (M : D ⥤ E) (N : C ⥤ E)
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [M.Additive] [PreservesFiniteLimits M] [PreservesFiniteColimits M]
    [N.Additive] [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    (e : L ⋙ M ≅ N) {A : C} {B : D} {T : E}
    (a : B ⟶ L.obj A) (b : T ⟶ M.obj B)
    (q : ℕ) (F : C) (x : Ext A F q) :
    (comparison M b (L.obj F) q (comparison L a F q x)).comp (Ext.mk₀ (e.hom.app F))
      (add_zero q) = comparison N (b ≫ M.map a ≫ e.hom.app A) F q x := by
  induction q generalizing F with
  | zero =>
    obtain ⟨v, rfl⟩ := (Ext.mk₀_bijective A F).surjective x
    rw [comparison_mk₀, comparison_mk₀, Ext.mk₀_comp_mk₀, comparison_mk₀]
    congr 1
    simp only [Functor.map_comp, Category.assoc]
    exact congrArg (fun m => b ≫ M.map a ≫ m) (e.hom.naturality v)
  | succ q ih =>
    let i := Injective.ι F
    let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
    let hL := hS.map_of_exact L
    let hM := hL.map_of_exact M
    let hN := hS.map_of_exact N
    have hKill : x.comp (Ext.mk₀ S.f) (add_zero (q + 1)) = 0 := Ext.eq_zero_of_injective _
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ A hS x hKill (n₀ := q) rfl
    let t : (S.map L).map M ⟶ S.map N :=
      { τ₁ := e.hom.app S.X₁
        τ₂ := e.hom.app S.X₂
        τ₃ := e.hom.app S.X₃
        comm₁₂ := (e.hom.naturality S.f).symm
        comm₂₃ := (e.hom.naturality S.g).symm }
    have hNat := hM.extClass_naturality hN t
    change hM.extClass.comp (Ext.mk₀ (e.hom.app S.X₁)) (add_zero 1) =
      (Ext.mk₀ (e.hom.app S.X₃)).comp hN.extClass (zero_add 1) at hNat
    let v := comparison M b (L.obj S.X₃) q (comparison L a S.X₃ q y)
    let η₁ := Ext.mk₀ (e.hom.app S.X₁)
    let η₃ := Ext.mk₀ (e.hom.app S.X₃)
    let d := comparison N (b ≫ M.map a ≫ e.hom.app A) S.X₃ q y
    let l := comparison L a S.X₃ q y
    let k := comparison M b (L.obj S.X₁) (q + 1)
    let c := comparison N (b ≫ M.map a ≫ e.hom.app A) S.X₁ (q + 1)
    calc
      _ = (k (comparison L a S.X₁ (q + 1) (y.comp hS.extClass rfl))).comp η₁
          (add_zero (q + 1)) :=
        congrArg (fun z => (k (comparison L a S.X₁ (q + 1) z)).comp η₁ _) hy.symm
      _ = (k (l.comp hL.extClass rfl)).comp η₁ (add_zero (q + 1)) :=
        congrArg (fun z => (k z).comp η₁ _) (comparison_boundary L a hS q y)
      _ = (v.comp hM.extClass rfl).comp η₁ (add_zero (q + 1)) :=
        congrArg (fun z : Ext T (M.obj (L.obj S.X₁)) (q + 1) =>
          z.comp η₁ (add_zero (q + 1))) (comparison_boundary M b hL q l)
      _ = v.comp (hM.extClass.comp η₁ (add_zero 1)) rfl :=
        Ext.comp_assoc_of_third_deg_zero _ _ _ rfl
      _ = v.comp (η₃.comp hN.extClass (zero_add 1)) rfl :=
        congrArg (fun z => v.comp z rfl) hNat
      _ = (v.comp η₃ (add_zero q)).comp hN.extClass rfl :=
        (Ext.comp_assoc_of_second_deg_zero _ _ _ rfl).symm
      _ = d.comp hN.extClass rfl := congrArg (fun z => z.comp hN.extClass rfl) (ih S.X₃ y)
      _ = c (y.comp hS.extClass rfl) := (comparison_boundary N _ hS q y).symm
      _ = _ := congrArg c hy

end PhilipponExtComparisonComposition

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (globalSections globalSectionsIso)
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtalePrimeTorsionComparison

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev constants (X : Scheme.{u}) := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev Z := AddCommGrpCat.of (ULift.{u} ℤ)

private def constantAdj (X : Scheme.{u}) : constants X ⊣ globalSections X :=
  constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u}
    (IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) (Scheme.Etale.mk (𝟙 X)) Over.mkIdTerminal)

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

private def composedAdj :=
  ((constantAdj X).comp (pullbackAdjunction f)).ofNatIsoRight (globalSectionsIso f)

private def constantComparison : (constants Y).obj Z ⟶
    (pullbackSheaves f).obj ((constants X).obj Z) :=
  ((constantAdj Y).leftAdjointUniq (composedAdj f)).hom.app Z

private instance : (pullbackSheaves f).Additive := (pullbackAdjunction f).left_adjoint_additive
private instance : (pullbackSheaves f).IsLeftAdjoint := (pullbackAdjunction f).isLeftAdjoint

private theorem homEquiv_restrict (F : Ab X) (a : (constants X).obj Z ⟶ F) :
    (constantAdj Y).homEquiv Z _ (constantComparison f ≫ (pullbackSheaves f).map a) =
      (constantAdj X).homEquiv Z F a ≫ (restrictGlobalSections f).app F := by
  let L := pullbackSheaves f
  let adj := pullbackAdjunction f
  let d := composedAdj f
  have hl : adj.homEquiv _ _ (L.map a) = a ≫ adj.unit.app F := by
    rw [Adjunction.homEquiv_unit]
    exact (adj.unit.naturality a).symm
  have hc : (constantAdj Y).homEquiv Z (L.obj ((constants X).obj Z)) (constantComparison f) =
      d.unit.app Z :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app (constantAdj Y) d Z
  calc
    _ = d.homEquiv Z _ (L.map a) := by
      rw [Adjunction.homEquiv_naturality_right, hc, Adjunction.homEquiv_unit]
    _ = _ := by
      dsimp only [d, composedAdj]
      rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
      change (constantAdj X).homEquiv Z _ (adj.homEquiv _ _ (L.map a)) ≫
        (globalSectionsIso f).hom.app (L.obj F) = _
      rw [hl, Adjunction.homEquiv_naturality_right,
        PhilipponEtalePullbackComposition.restrictGlobalSections_app_eq, Category.assoc]

private theorem homComparison_bijective
    (F : Ab X) (hF : IsIso ((restrictGlobalSections f).app F)) :
    Function.Bijective (fun a : (constants X).obj Z ⟶ F =>
      constantComparison f ≫ (pullbackSheaves f).map a) := by
  rw [← Function.Bijective.of_comp_iff' ((constantAdj Y).homEquiv Z _).bijective]
  have h : ((constantAdj Y).homEquiv Z _) ∘ (fun a : (constants X).obj Z ⟶ F =>
      constantComparison f ≫ (pullbackSheaves f).map a) =
      (fun a : Z ⟶ (globalSections X).obj F => a ≫ (restrictGlobalSections f).app F) ∘
        (constantAdj X).homEquiv Z F := funext (homEquiv_restrict f F)
  rw [h]
  exact (Iso.homCongr (Iso.refl Z) (asIso ((restrictGlobalSections f).app F))).bijective.comp
    ((constantAdj X).homEquiv Z F).bijective

/-- The degree-zero cohomology comparison agrees with the global-sections comparison. -/
theorem bijective_restrict_zero (F : Ab X) (hF : IsIso ((restrictGlobalSections f).app F)) :
    Function.Bijective (restrict f F 0) :=
  PhilipponExtComparison.comparison_zero_bijective (pullbackSheaves f) (constantComparison f) F
    (homComparison_bijective f F hF)

private theorem cokernel_killed {U V : Ab X} (a : U ⟶ V) {N : ℕ} (hV : N • 𝟙 V = 0) :
    N • 𝟙 (cokernel a) = 0 := by
  apply (cancel_epi (cokernel.π a)).mp
  rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero]
  simpa only [Preadditive.nsmul_comp, Category.id_comp, zero_comp] using
    congrArg (fun b => b ≫ cokernel.π a) hV

/-- It suffices to compare the embedding targets of a class of test sheaves
when injectivity and surjectivity each transfer from tests to bounded torsion. -/
theorem bijective_restrict_of_test_embeddings (N : ℕ) (T : ObjectProperty (Ab X))
    (h₀ : ∀ G : Ab X, N • 𝟙 G = 0 → Function.Bijective (restrict f G 0))
    (hEmb : ∀ G : Ab X, T G → ∃ (J : Ab X) (i : G ⟶ J),
      Mono i ∧ N • 𝟙 J = 0 ∧ ∀ q, Function.Bijective (restrict f J q))
    (hInj : ∀ n, (∀ G, T G → Function.Injective (restrict f G n)) →
      ∀ F : Ab X, N • 𝟙 F = 0 → Function.Injective (restrict f F n))
    (hSurj : ∀ n, (∀ G, T G → Function.Surjective (restrict f G n)) →
      ∀ F : Ab X, N • 𝟙 F = 0 → Function.Surjective (restrict f F n))
    (F : Ab X) (hF : N • 𝟙 F = 0) (n : ℕ) : Function.Bijective (restrict f F n) := by
  refine PhilipponExtComparison.comparison_bijective_of_test_embeddings
    (pullbackSheaves f) (constantComparison f) (fun G => N • 𝟙 G = 0) T h₀ ?_ hInj hSurj n F hF
  intro G hG
  obtain ⟨J, i, hi, hJ, hComp⟩ := hEmb G hG
  exact ⟨J, i, hi, cokernel_killed i hJ, hComp⟩

end PhilipponEtalePrimeTorsionComparison

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 120000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtalePrimeTorsionComparison (restrict)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleFilteredRestriction

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev cohomTypes (X : Scheme.{u}) (n : ℕ) :=
  Sheaf.functorH X.smallEtaleTopology n ⋙ forget AddCommGrpCat.{u}

private theorem restrict_map {X Y : Scheme.{u}} (f : Y ⟶ X) {F G : Ab X}
    (a : F ⟶ G) (n : ℕ) (x : F.H n) :
    restrict f G n (Sheaf.H.map a n x) =
      Sheaf.H.map ((pullbackSheaves f).map a) n (restrict f F n x) := by
  exact PhilipponExtComparison.comparison_post (pullbackSheaves f) _ a n x

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) (G : ObjectProperty (Ab X))

/-- Injectivity of cohomological restriction passes from filtered stages
to their colimit whenever the two cohomology functors preserve these colimits. -/
theorem restrict_injective_of_ind
    [PreservesFilteredColimitsOfSize.{u, u} (Sheaf.functorH X.smallEtaleTopology n)]
    [PreservesFilteredColimitsOfSize.{u, u} (Sheaf.functorH Y.smallEtaleTopology n)]
    (hStage : ∀ F : Ab X, G F → Function.Injective (restrict f F n))
    (F : Ab X) (hF : ObjectProperty.ind.{u} G F) : Function.Injective (restrict f F n) := by
  obtain ⟨J, _, _, p, hp⟩ := hF
  let L := pullbackSheaves f
  let : L.IsLeftAdjoint := (pullbackAdjunction f).isLeftAdjoint
  let s := Cocone.mk F p.ι
  let A := cohomTypes X n
  let B := L ⋙ cohomTypes Y n
  let c := A.mapCocone s
  let d := B.mapCocone s
  have hc : IsColimit c := isColimitOfPreserves A p.isColimit
  have hd : IsColimit d := isColimitOfPreserves B p.isColimit
  intro x y hxy
  obtain ⟨i, x₀, y₀, hx, hy⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂ hc x y
  change Sheaf.H.map (p.ι.app i) n x₀ = x at hx
  change Sheaf.H.map (p.ι.app i) n y₀ = y at hy
  have hEq : d.ι.app i (restrict f (p.diag.obj i) n x₀) =
      d.ι.app i (restrict f (p.diag.obj i) n y₀) := by
    change Sheaf.H.map (L.map (p.ι.app i)) n (restrict f (p.diag.obj i) n x₀) =
      Sheaf.H.map (L.map (p.ι.app i)) n (restrict f (p.diag.obj i) n y₀)
    rwa [← restrict_map, ← restrict_map, hx, hy]
  obtain ⟨j, a, ha⟩ := (Types.FilteredColimit.isColimit_eq_iff' hd _ _).mp hEq
  have hStageEq : (p.diag ⋙ A).map a x₀ = (p.diag ⋙ A).map a y₀ := by
    apply hStage _ (hp j)
    change restrict f (p.diag.obj j) n (Sheaf.H.map (p.diag.map a) n x₀) =
      restrict f (p.diag.obj j) n (Sheaf.H.map (p.diag.map a) n y₀)
    rw [restrict_map, restrict_map]
    exact ha
  exact hx.symm.trans (((Types.FilteredColimit.isColimit_eq_iff' hc _ _).mpr ⟨j, a, hStageEq⟩).trans hy)

/-- Surjectivity of cohomological restriction passes from filtered stages
to their colimit whenever the target cohomology preserves these colimits. -/
theorem restrict_surjective_of_ind
    [PreservesFilteredColimitsOfSize.{u, u} (Sheaf.functorH Y.smallEtaleTopology n)]
    (hStage : ∀ F : Ab X, G F → Function.Surjective (restrict f F n))
    (F : Ab X) (hF : ObjectProperty.ind.{u} G F) : Function.Surjective (restrict f F n) := by
  obtain ⟨J, _, _, p, hp⟩ := hF
  let L := pullbackSheaves f
  let : L.IsLeftAdjoint := (pullbackAdjunction f).isLeftAdjoint
  let B := L ⋙ cohomTypes Y n
  let d := B.mapCocone (Cocone.mk F p.ι)
  have hd : IsColimit d := isColimitOfPreserves B p.isColimit
  intro y
  obtain ⟨j, y₀, hy⟩ := Types.jointly_surjective_of_isColimit hd y
  obtain ⟨x₀, hx⟩ := hStage _ (hp j) y₀
  refine ⟨Sheaf.H.map (p.ι.app j) n x₀, ?_⟩
  exact (restrict_map f (p.ι.app j) n x₀).trans
    ((congrArg (fun z => Sheaf.H.map (L.map (p.ι.app j)) n z) hx).trans hy)

end PhilipponEtaleFilteredRestriction

end


