-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.subsingleton_etale_cohomology_projectiveLine_restrict_injective_closed_fiber_higher
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-24T04:27:08.13748+00:00
-- url     : https://prove2.me/submissions/b7261783-0d6f-42a4-b192-3df1c97db063

import Definitions.Def_AlgebraicGeometry_EtaleCechEvaluation
import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Module.ZMod
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FinCases
import Theorems.Thm_AlgebraicGeometry_Scheme_subsingleton_etale_cohomology_restrict_injective_prime_of_affine_closedImmersion

set_option maxHeartbeats 1300000

noncomputable section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) etaleHasSheafify (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) etaleHasExt (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) etaleEnoughInjectives (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

namespace PhilipponSmallEtaleOpenImmersion
universe u
variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

/-- View an étale scheme over the open subscheme as one over the ambient scheme. -/
def along : Y.Etale ⥤ X.Etale where
  obj U := Scheme.Etale.mk (U.hom ≫ f)
  map {U V} a := MorphismProperty.Over.homMk a.left
    ((Category.assoc a.left V.hom f).symm.trans
      (congrArg (· ≫ f) (MorphismProperty.Over.w a)))
  map_id _ := MorphismProperty.Over.Hom.ext rfl
  map_comp _ _ := MorphismProperty.Over.Hom.ext rfl

instance : (along f).Faithful where
  map_injective h := MorphismProperty.Over.Hom.ext (congrArg (fun a => a.left) h)

instance : (along f).Full where
  map_surjective {U V} a := by
    have h : a.left ≫ (V.hom ≫ f) = U.hom ≫ f := MorphismProperty.Over.w a
    rw [← Category.assoc] at h
    exact ⟨MorphismProperty.Over.homMk a.left ((cancel_mono f).mp h),
      MorphismProperty.Over.Hom.ext rfl⟩

/-- The source of an arrow into an object over the open subscheme is itself
an étale scheme over that open subscheme. -/
def liftObj {V : X.Etale} {U : Y.Etale} (a : V ⟶ (along f).obj U) : Y.Etale :=
  Scheme.Etale.mk (a.left ≫ U.hom)

def liftIso {V : X.Etale} {U : Y.Etale} (a : V ⟶ (along f).obj U) :
    (along f).obj (liftObj f a) ≅ V :=
  MorphismProperty.Over.isoMk (Iso.refl _)
    (by simp only [Iso.refl_hom, Category.id_comp]; exact
      (MorphismProperty.Over.w a).symm.trans (Category.assoc a.left U.hom f).symm)

def liftArrow {V : X.Etale} {U : Y.Etale} (a : V ⟶ (along f).obj U) :
    liftObj f a ⟶ U := MorphismProperty.Over.homMk a.left rfl

theorem along_liftArrow {V : X.Etale} {U : Y.Etale} (a : V ⟶ (along f).obj U) :
    (along f).map (liftArrow f a) = (liftIso f a).hom ≫ a :=
  MorphismProperty.Over.Hom.ext (Category.id_comp a.left).symm

theorem coverPreserving : CoverPreserving Y.smallEtaleTopology X.smallEtaleTopology (along f) := by
  constructor
  intro W S hS
  obtain ⟨U, hOver, hEtale, hle⟩ := (Scheme.mem_smallGrothendieckTopology W S).mp hS
  let : U.Over Y := hOver
  let V (i : U.I₀) := (U.X i).asOverProp Y (hEtale i)
  let r (i : U.I₀) : V i ⟶ W := (U.f i).asOverProp Y
  have hc : Sieve.ofArrows (fun i => (along f).obj (V i)) (fun i => (along f).map (r i))
      ∈ X.smallEtaleTopology ((along f).obj W) := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff (fun i => (along f).map (r i))).mpr
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨z, hz⟩ := U.covers x
    exact ⟨U.idx x, z, hz⟩
  apply X.smallEtaleTopology.superset_covering _ hc
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨i⟩
  exact S.image_mem_functorPushforward (along f) (hle _ _ ⟨i⟩)

instance : (along f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfDownwardsClosed X.smallEtaleTopology (along f)
      (fun a => ⟨liftObj f a, liftIso f a⟩))
    (coverPreserving f)

theorem pullback_cover {W : Y.Etale} (S : Sieve ((along f).obj W))
    (hS : S ∈ X.smallEtaleTopology ((along f).obj W)) :
    S.functorPullback (along f) ∈ Y.smallEtaleTopology W := by
  obtain ⟨U, hOver, hEtale, hle⟩ :=
    (Scheme.mem_smallGrothendieckTopology ((along f).obj W) S).mp hS
  let : U.Over X := hOver
  let V (i : U.I₀) := (U.X i).asOverProp X (hEtale i)
  let a (i : U.I₀) : V i ⟶ (along f).obj W := (U.f i).asOverProp X
  let V' (i : U.I₀) := liftObj f (a i)
  let r (i : U.I₀) : V' i ⟶ W := liftArrow f (a i)
  have hc : Sieve.ofArrows V' r ∈ Y.smallEtaleTopology W := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff r).mpr
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨z, hz⟩ := U.covers x
    exact ⟨U.idx x, z, hz⟩
  apply Y.smallEtaleTopology.superset_covering _ hc
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨i⟩
  change S ((along f).map (r i))
  rw [along_liftArrow f (a i)]
  exact S.downward_closed (hle _ _ ⟨i⟩) _

end PhilipponSmallEtaleOpenImmersion

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject


namespace PhilipponEtaleExtensionByZero

section Kan

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D)

private def terminalOfIso [L.Full] [L.Faithful] {A : C} {W : D} (e : L.obj A ≅ W) :
    IsTerminal (CostructuredArrow.mk e.hom) := by
  refine IsTerminal.ofUniqueHom (fun i => CostructuredArrow.homMk (L.preimage (i.hom ≫ e.inv))
    (by simp)) (fun i h => ?_)
  apply CostructuredArrow.hom_ext
  apply L.map_injective
  change L.map h.left = L.map (L.preimage (i.hom ≫ e.inv))
  rw [L.map_preimage]
  have hfac : L.map h.left ≫ e.hom = i.hom := CostructuredArrow.w h
  rw [← hfac, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable {A : Type*} [Category* A] [Abelian A]

private theorem pointwiseLeftKan_of_empty_or_terminal
    (h : ∀ W, IsEmpty (CostructuredArrow L W) ∨ ∃ t : CostructuredArrow L W, Nonempty (IsTerminal t))
    (P : C ⥤ A) : L.HasPointwiseLeftKanExtension P := by
  intro W
  rcases h W with he | ⟨t, ⟨ht⟩⟩
  · let c : Cocone (CostructuredArrow.proj L W ⋙ P) :=
      ⟨0, { app := fun j => he.false j |>.elim, naturality := fun {i} _ _ => he.false i |>.elim }⟩
    exact ⟨⟨c, (isColimitEquivIsInitialOfIsEmpty A c).symm (isZero_zero A).isInitial⟩⟩
  · exact ⟨⟨_, colimitOfDiagramTerminal ht _⟩⟩

private theorem lan_preservesMonomorphisms
    [∀ P : C ⥤ A, L.HasPointwiseLeftKanExtension P]
    (h : ∀ W, IsEmpty (CostructuredArrow L W) ∨ ∃ t : CostructuredArrow L W, Nonempty (IsTerminal t)) :
    (L.lan : (C ⥤ A) ⥤ D ⥤ A).PreservesMonomorphisms where
  preserves {P Q} α hα := by
    rw [NatTrans.mono_iff_mono_app] at hα ⊢
    intro W
    rcases h W with he | ⟨t, ⟨ht⟩⟩
    · let c := (Functor.LeftExtension.mk _ (L.leftKanExtensionUnit P)).coconeAt W
      let hC : IsColimit c := L.isPointwiseLeftKanExtensionLeftKanExtensionUnit P W
      have hz : IsZero ((L.lan.obj P).obj W) :=
        ((isColimitEquivIsInitialOfIsEmpty A c) hC).isZero
      exact ⟨fun a b _ => hz.eq_of_tgt a b⟩
    · let η (R : C ⥤ A) := (L.lanUnit.app R).app t.left ≫ (L.lan.obj R).map t.hom
      have hη (R : C ⥤ A) : IsIso (η R) :=
        (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit R W).isIso_ι_app_of_isTerminal t ht
      have hc : η P ≫ (L.lan.map α).app W = α.app t.left ≫ η Q := by
        dsimp only [η]
        rw [Category.assoc, (L.lan.map α).naturality t.hom, ← Category.assoc]
        have hn := NatTrans.congr_app (L.lanUnit.naturality α) t.left
        change α.app t.left ≫ (L.lanUnit.app Q).app t.left =
          (L.lanUnit.app P).app t.left ≫ (L.lan.map α).app (L.obj t.left) at hn
        rw [← hn, Category.assoc]
      let : IsIso (η P) := hη P
      let : IsIso (η Q) := hη Q
      exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.monomorphisms A)
        (Arrow.isoMk (asIso (η P)) (asIso (η Q)) hc)).mp (hα t.left)

end Kan

universe u
variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

open PhilipponSmallEtaleOpenImmersion (along liftObj liftIso pullback_cover)

instance : (along f).IsCocontinuous Y.smallEtaleTopology X.smallEtaleTopology where
  cover_lift h := pullback_cover f _ h

private theorem along_op_shape (W : X.Etaleᵒᵖ) :
    IsEmpty (CostructuredArrow (along f).op W) ∨
      ∃ t : CostructuredArrow (along f).op W, Nonempty (IsTerminal t) := by
  classical
  cases isEmpty_or_nonempty (CostructuredArrow (along f).op W) with
  | inl he => exact Or.inl he
  | inr ht =>
      let t := ht.some
      let e := (liftIso f t.hom.unop).symm.op
      exact Or.inr ⟨_, ⟨terminalOfIso (along f).op e⟩⟩

instance (P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (along f).op.HasPointwiseLeftKanExtension P :=
  pointwiseLeftKan_of_empty_or_terminal (along f).op (along_op_shape f) P

/-- Restriction to an open subscheme preserves injective sheaves with abelian
coefficients when sheafification is left exact. -/
theorem restriction_preservesInjectiveObjects (A : Type (u + 1)) [Category.{u} A] [Abelian A]
    [HasSheafify X.smallEtaleTopology A] :
    ((along f).sheafPushforwardContinuous A Y.smallEtaleTopology X.smallEtaleTopology).PreservesInjectiveObjects := by
  let : ∀ P : Y.Etaleᵒᵖ ⥤ A, (along f).op.HasPointwiseLeftKanExtension P :=
    pointwiseLeftKan_of_empty_or_terminal (along f).op (along_op_shape f)
  let : ((along f).op.lan : (Y.Etaleᵒᵖ ⥤ A) ⥤ X.Etaleᵒᵖ ⥤ A).PreservesMonomorphisms :=
    lan_preservesMonomorphisms (along f).op (along_op_shape f)
  let L := Functor.sheafPullbackConstruction.sheafPullback (along f) A
    Y.smallEtaleTopology X.smallEtaleTopology
  have : L.PreservesMonomorphisms := by
    unfold L Functor.sheafPullbackConstruction.sheafPullback
    infer_instance
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (along f) A
      Y.smallEtaleTopology X.smallEtaleTopology)

/-- Restriction of abelian étale sheaves to the open subscheme. -/
abbrev restrict : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  (along f).sheafPushforwardContinuous AddCommGrpCat Y.smallEtaleTopology X.smallEtaleTopology

/-- Restriction to an open subscheme preserves injective abelian sheaves. -/
instance restrict_preservesInjectiveObjects : (restrict f).PreservesInjectiveObjects :=
  restriction_preservesInjectiveObjects f AddCommGrpCat.{u}

instance restrict_additive : (restrict f).Additive where
  map_add := rfl

instance restrict_preservesFiniteLimits : PreservesFiniteLimits (restrict f) := by
  have : (restrict f).IsRightAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (along f) AddCommGrpCat
      Y.smallEtaleTopology X.smallEtaleTopology).isRightAdjoint
  infer_instance

instance restrict_preservesEpimorphisms : (restrict f).PreservesEpimorphisms where
  preserves φ h := by
    have hφ : Sheaf.IsLocallySurjective φ := (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat φ).2 h
    apply (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat ((restrict f).map φ)).1
    constructor
    intro U s
    exact pullback_cover f _ (hφ.imageSieve_mem s)

/-- The restriction functor is exact. -/
instance restrict_preservesFiniteColimits : PreservesFiniteColimits (restrict f) := by
  let : (restrict f).PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels (restrict f)
  exact Functor.preservesFiniteColimits_of_preservesHomology (restrict f)

end PhilipponEtaleExtensionByZero

end

section

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

/-- Apply an exact functor to Ext, then precompose with the comparison map. -/
def comparison (M : C) (n : ℕ) : Ext Q M n →+ Ext P (R.obj M) n :=
  ((Ext.mk₀ p).precomp (R.obj M) (zero_add n)).comp (R.mapExtAddHom Q M n)

private theorem comparison_comp {M N : C} {n k m : ℕ} (x : Ext Q M n) (a : Ext M N k)
    (h : n + k = m) :
    comparison R p N m (x.comp a h) =
      (comparison R p M n x).comp (a.mapExactFunctor R) h := by
  change (Ext.mk₀ p).comp ((x.comp a h).mapExactFunctor R) (zero_add m) = _
  rw [Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc (Ext.mk₀ p) (x.mapExactFunctor R) (a.mapExactFunctor R)
    (zero_add n) h (by simpa using h)).symm

theorem comparison_mk₀ {M : C} (x : Q ⟶ M) :
    comparison R p M 0 (Ext.mk₀ x) = Ext.mk₀ (p ≫ R.map x) := by
  change (Ext.mk₀ p).comp ((Ext.mk₀ x).mapExactFunctor R) (zero_add 0) = _
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

private theorem comparison_boundary {S : ShortComplex C} (hS : S.ShortExact)
    (n : ℕ) (x : Ext Q S.X₃ n) :
    comparison R p S.X₁ (n + 1) (x.comp hS.extClass rfl) =
      (comparison R p S.X₃ n x).comp (hS.map_of_exact R).extClass rfl := by
  rw [comparison_comp, Ext.mapExactFunctor_extClass]

theorem comparison_post {M N : C} (a : M ⟶ N) (n : ℕ) (x : Ext Q M n) :
    comparison R p N n (x.comp (Ext.mk₀ a) (add_zero n)) =
      (comparison R p M n x).comp (Ext.mk₀ (R.map a)) (add_zero n) := by
  rw [comparison_comp, Ext.mapExactFunctor_mk₀]

theorem comparison_zero_bijective (M : C)
    (h : Function.Bijective (fun a : Q ⟶ M => p ≫ R.map a)) :
    Function.Bijective (comparison R p M 0) := by
  have hz : (comparison R p M 0 : Ext Q M 0 → Ext P (R.obj M) 0) =
      fun x => Ext.mk₀ (p ≫ R.map (Ext.addEquiv₀ x)) := by
    funext x
    obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective Q M).surjective x
    rw [show Ext.addEquiv₀ (Ext.mk₀ a) = a from Ext.addEquiv₀.apply_symm_apply a]
    exact comparison_mk₀ R p a
  rw [hz]
  exact (Ext.mk₀_bijective _ _).comp (h.comp Ext.addEquiv₀.bijective)

/-- A class of coefficients admits comparison in all degrees if every
object embeds in a coefficient acyclic on both sides, with cokernel
still in the class. -/
theorem comparison_bijective_of_acyclic_embeddings (B : C → Prop)
    (h : ∀ M : C, B M → Function.Bijective (fun a : Q ⟶ M => p ≫ R.map a))
    (emb : ∀ M : C, B M → ∃ (J : C) (i : M ⟶ J), Mono i ∧ B J ∧ B (cokernel i) ∧
      ∀ n : ℕ, Subsingleton (Ext Q J (n + 1)) ∧ Subsingleton (Ext P (R.obj J) (n + 1)))
    (n : ℕ) (M : C) (hM : B M) : Function.Bijective (comparison R p M n) := by
  induction n generalizing M with
  | zero => exact comparison_zero_bijective R p M (h M hM)
  | succ n ih =>
      obtain ⟨J, i, hi, hJ, hQ, hA⟩ := emb M hM
      let _ : Mono i := hi
      let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
      have hSR := hS.map_of_exact R
      constructor
      · apply (AddMonoidHom.ker_eq_bot_iff _).mp
        rw [AddSubgroup.eq_bot_iff_forall]
        intro x hx
        have hx' : comparison R p S.X₁ (n + 1) x = 0 := hx
        obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ Q hS x
          ((hA n).1.elim _ _) (n₀ := n) rfl
        have hzero : (comparison R p S.X₃ n y).comp hSR.extClass rfl = 0 := by
          rw [← comparison_boundary R p hS n y, hy]
          exact hx'
        obtain ⟨z', hz'⟩ := Ext.covariant_sequence_exact₃ P hSR _ rfl hzero
        obtain ⟨z, hz⟩ := (ih S.X₂ hJ).surjective z'
        have hyz : z.comp (Ext.mk₀ S.g) (add_zero n) = y := (ih S.X₃ hQ).injective (by
          rw [comparison_post, hz]
          exact hz')
        rw [← hy, ← hyz, Ext.comp_assoc_of_second_deg_zero,
          ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]
      · intro x'
        obtain ⟨y', hy'⟩ := Ext.covariant_sequence_exact₁ P hSR x'
          ((hA n).2.elim _ _) (n₀ := n) rfl
        obtain ⟨y, hy⟩ := (ih S.X₃ hQ).surjective y'
        refine ⟨y.comp hS.extClass rfl, ?_⟩
        rw [comparison_boundary R p hS, hy]
        exact hy'

/-- A Hom comparison extends to all Ext degrees when the exact functor
also preserves injectives. -/
theorem comparison_bijective [EnoughInjectives C] [R.PreservesInjectiveObjects]
    (h : ∀ M : C, Function.Bijective (fun a : Q ⟶ M => p ≫ R.map a))
    (n : ℕ) (M : C) : Function.Bijective (comparison R p M n) := by
  refine comparison_bijective_of_acyclic_embeddings R p (fun _ => True) (fun M _ => h M) ?_ n M trivial
  intro A _
  refine ⟨Injective.under A, Injective.ι A, inferInstance, trivial, trivial, fun q => ?_⟩
  let : Injective (R.obj (Injective.under A)) := R.injective_obj_of_injective inferInstance
  exact ⟨⟨fun x y => (Ext.eq_zero_of_injective x).trans (Ext.eq_zero_of_injective y).symm⟩,
    ⟨fun x y => (Ext.eq_zero_of_injective x).trans (Ext.eq_zero_of_injective y).symm⟩⟩

end PhilipponExtComparison

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open PhilipponEtaleExtensionByZero (restrict)
open PhilipponSmallEtaleOpenImmersion (along)
open PhilipponSheafCohomology (freeOn representedSections representedSections_map
  representedSections_restrict terminalComparison)


namespace PhilipponEtaleOpenCohomology

universe u
variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

private abbrev T := Scheme.Etale.mk (𝟙 Y)

private abbrev V := Scheme.Etale.mk f

private def overIso : (along f).obj (T (Y := Y)) ≅ V f :=
  MorphismProperty.Over.isoMk (Iso.refl Y) (by
    change (𝟙 Y) ≫ f = (𝟙 Y) ≫ f
    rfl)

private abbrev baseFree := (freeOn X.smallEtaleTopology).obj (V f)

private abbrev openFree (Y : Scheme.{u}) := (freeOn Y.smallEtaleTopology).obj (T (Y := Y))

private def evaluationArrow : openFree Y ⟶ (restrict f).obj (baseFree f) :=
  (representedSections Y.smallEtaleTopology ((restrict f).obj (baseFree f)) (T (Y := Y))).symm
    (representedSections X.smallEtaleTopology (baseFree f) ((along f).obj (T (Y := Y)))
      ((freeOn X.smallEtaleTopology).map (overIso f).hom))

private theorem evaluationArrow_apply (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (a : baseFree f ⟶ F) :
    representedSections Y.smallEtaleTopology ((restrict f).obj F) (T (Y := Y))
      (evaluationArrow f ≫ (restrict f).map a) =
    F.obj.map (overIso f).hom.op (representedSections X.smallEtaleTopology F (V f) a) := by
  rw [representedSections_map]
  unfold evaluationArrow
  rw [Equiv.apply_symm_apply, ← representedSections_restrict]
  exact (representedSections_map X.smallEtaleTopology a _ _).symm

private theorem evaluationArrow_bijective (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Function.Bijective (fun a : baseFree f ⟶ F => evaluationArrow f ≫ (restrict f).map a) := by
  let e := representedSections Y.smallEtaleTopology ((restrict f).obj F) (T (Y := Y))
  let d := (F.obj.mapIso (overIso f).op).addCommGroupIsoToAddEquiv
  let c := representedSections X.smallEtaleTopology F (V f)
  have h : (fun a : baseFree f ⟶ F => evaluationArrow f ≫ (restrict f).map a) =
      e.symm ∘ d ∘ c := by
    funext a
    apply e.injective
    rw [Function.comp_apply, Equiv.apply_symm_apply]
    exact evaluationArrow_apply f F a
  rw [h]
  exact e.symm.bijective.comp (d.bijective.comp c.bijective)

/-- Cohomology of an open étale object is the cohomology of the restricted
sheaf on the small étale site of the open subscheme. -/
def openComparison (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ) :
    F.H' q (V f) ≃+ ((restrict f).obj F).H q := by
  let hT : IsTerminal (T (Y := Y)) := IsTerminal.isTerminalOfObj (Scheme.Etale.forget Y) _
    Over.mkIdTerminal
  let a := PhilipponExtComparison.comparison (restrict f) (evaluationArrow f) F q
  have ha := PhilipponExtComparison.comparison_bijective (restrict f) (evaluationArrow f)
    (evaluationArrow_bijective f) q F
  exact (AddEquiv.ofBijective a ha).trans
    (terminalComparison Y.smallEtaleTopology hT ((restrict f).obj F) q).symm

end PhilipponEtaleOpenCohomology

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleExtensionByZero (restrict)
open PhilipponEtalePullbackComposition (pullbackCompIso)
open PhilipponEtaleSmallSite (pullbackSheaves)


namespace PhilipponEtaleMayerVietoris

universe u

variable {X : Scheme.{u}} (U V : X.Opens)

private abbrev terminal (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)
private abbrev openChart (U : X.Opens) : X.Etale := Scheme.Etale.mk U.ι

private def inclusion (U : X.Opens) : openChart U ⟶ terminal X :=
  MorphismProperty.Over.homMk U.ι (Category.comp_id _) trivial

private def intersectionMap {U V : X.Opens} (h : U ≤ V) : openChart U ⟶ openChart V :=
  MorphismProperty.Over.homMk (X.homOfLE h) (X.homOfLE_ι h) trivial

private def square : Square X.Etale where
  X₁ := openChart (U ⊓ V)
  X₂ := openChart U
  X₃ := openChart V
  X₄ := terminal X
  f₁₂ := intersectionMap inf_le_left
  f₁₃ := intersectionMap inf_le_right
  f₂₄ := inclusion U
  f₃₄ := inclusion V
  fac := MorphismProperty.Over.Hom.ext
    ((X.homOfLE_ι inf_le_left).trans (X.homOfLE_ι inf_le_right).symm)

private abbrev underlying (X : Scheme.{u}) : X.Etale ⥤ Scheme.{u} :=
  Scheme.Etale.forget X ⋙ Over.forget X

private instance (U : X.Opens) : Mono (inclusion U) :=
  Functor.mono_of_mono_map (underlying X) (inferInstanceAs (Mono U.ι))

private theorem isPullback_square : (square U V).IsPullback :=
  IsPullback.of_map (underlying X) (square U V).fac (isPullback_opens_inf U V)

private theorem opens_cover (h : U ⊔ V = ⊤) :
    Sieve.ofTwoArrows (inclusion U) (inclusion V) ∈ X.smallEtaleTopology (terminal X) := by
  rw [Sieve.ofTwoArrows, Scheme.ofArrows_mem_smallEtaleTopology_iff]
  refine Set.eq_univ_of_forall ?_
  intro x
  have hx : x ∈ U ⊔ V := h.symm ▸ (show x ∈ (⊤ : X.Opens) from trivial)
  rcases hx with hx | hx
  · exact Set.mem_iUnion.mpr ⟨WalkingPair.left, ⟨⟨x, hx⟩, rfl⟩⟩
  · exact Set.mem_iUnion.mpr ⟨WalkingPair.right, ⟨⟨x, hx⟩, rfl⟩⟩

/-- Two open subschemes covering a scheme give a Mayer–Vietoris square in
the small étale site. -/
def mayerVietoris (h : U ⊔ V = ⊤) : X.smallEtaleTopology.MayerVietorisSquare := by
  let : Mono (square U V).f₂₄ := inferInstanceAs (Mono (inclusion U))
  let : Mono (square U V).f₃₄ := inferInstanceAs (Mono (inclusion V))
  exact GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback
    (J := X.smallEtaleTopology) (square U V) (isPullback_square U V) (opens_cover U V h)

/-- Vanishing in degree `q` on the overlap and in degree `q + 1` on
both members of a two-open cover gives vanishing in degree `q + 1`
on the entire scheme. -/
theorem subsingleton_H_succ (h : U ⊔ V = ⊤)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ)
    (h₁ : Subsingleton (((restrict (U ⊓ V).ι).obj F).H q))
    (h₂ : Subsingleton (((restrict U.ι).obj F).H (q + 1)))
    (h₃ : Subsingleton (((restrict V.ι).obj F).H (q + 1))) :
    Subsingleton (F.H (q + 1)) := by
  let _ := h₁
  let _ := h₂
  let _ := h₃
  let S := mayerVietoris U V h
  have z₁ : IsZero (F.H' q S.X₁) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr
      ((PhilipponEtaleOpenCohomology.openComparison (U ⊓ V).ι F q).injective.subsingleton)
  have z₂ : IsZero (F.H' (q + 1) S.X₂) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr
      ((PhilipponEtaleOpenCohomology.openComparison U.ι F (q + 1)).injective.subsingleton)
  have z₃ : IsZero (F.H' (q + 1) S.X₃) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr
      ((PhilipponEtaleOpenCohomology.openComparison V.ι F (q + 1)).injective.subsingleton)
  have hTo : S.toBiprod F (q + 1) = 0 := by
    apply biprod.hom_ext
    · exact z₂.eq_of_tgt _ _
    · exact z₃.eq_of_tgt _ _
  have hδ : S.δ F q (q + 1) rfl = 0 := z₁.eq_zero_of_src _
  have exactPair : Function.Exact (S.δ F q (q + 1) rfl) (S.toBiprod F (q + 1)) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp ((S.sequence_exact F q (q + 1) rfl).exact 2)
  have hZero (x : F.H' (q + 1) S.X₄) : x = 0 := by
    obtain ⟨y, hy⟩ := (exactPair x).mp (by rw [hTo]; rfl)
    rw [← hy, hδ]
    rfl
  have hT : IsTerminal (terminal X) := IsTerminal.isTerminalOfObj (Scheme.Etale.forget X)
    _ Over.mkIdTerminal
  exact ⟨fun a b => (PhilipponSheafCohomology.terminalComparison _ hT F (q + 1)).injective
    ((hZero _).trans (hZero _).symm)⟩

/-- The two-affine step in the affine reduction for closed-fiber
acyclicity. Local vanishing on all affine opens of the ambient scheme
implies the desired vanishing in degrees at least two on the fiber. -/
theorem subsingleton_pullback_H_succ_succ_of_affine_cover {Z : Scheme.{u}} (j : Z ⟶ X)
    [X.IsSeparated] (h : U ⊔ V = ⊤) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (localVanishing : ∀ (W : X.Opens), IsAffineOpen W → ∀ n : ℕ,
      Subsingleton (((pullbackSheaves (j ∣_ W)).obj ((pullbackSheaves W.ι).obj F)).H (n + 1)))
    (q : ℕ) : Subsingleton (((pullbackSheaves j).obj F).H (q + 1 + 1)) := by
  have hVanish (W : X.Opens) (hW : IsAffineOpen W) (n : ℕ) :
      Subsingleton (((restrict (j ⁻¹ᵁ W).ι).obj ((pullbackSheaves j).obj F)).H (n + 1)) := by
    let K := (pullbackSheaves j).obj F
    let e₀ : restrict (j ⁻¹ᵁ W).ι ≅ pullbackSheaves (j ⁻¹ᵁ W).ι :=
      PhilipponEtaleNeighborhoodRestriction.restrictionIso (j ⁻¹ᵁ W).ι
    let e₁ := (pullbackCompIso j (j ⁻¹ᵁ W).ι).app F
    let e₂ := eqToIso (congrArg (fun g => (pullbackSheaves g).obj F)
      (morphismRestrict_ι j W).symm)
    let e₃ := (pullbackCompIso W.ι (j ∣_ W)).symm.app F
    let e : (restrict (j ⁻¹ᵁ W).ι).obj K ≅
        (pullbackSheaves (j ∣_ W)).obj ((pullbackSheaves W.ι).obj F) :=
      e₀.app K ≪≫ e₁ ≪≫ e₂ ≪≫ e₃
    let eH : (((restrict (j ⁻¹ᵁ W).ι).obj K).H (n + 1)) ≃+
        (((pullbackSheaves (j ∣_ W)).obj ((pullbackSheaves W.ι).obj F)).H (n + 1)) :=
      ((Sheaf.functorH _ (n + 1)).mapIso e).addCommGroupIsoToAddEquiv
    exact ⟨fun a b => eH.injective ((localVanishing W hW n).elim (eH a) (eH b))⟩
  have hCover : j ⁻¹ᵁ U ⊔ j ⁻¹ᵁ V = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, h, Scheme.Hom.preimage_top]
  exact subsingleton_H_succ (j ⁻¹ᵁ U) (j ⁻¹ᵁ V) hCover _ (q + 1)
    (by rw [← Scheme.Hom.preimage_inf]; exact hVanish (U ⊓ V) (hU.inf hV) q)
    (hVanish U hU (q + 1)) (hVanish V hV (q + 1))

end PhilipponEtaleMayerVietoris

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleSmallSite (pullbackSheaves)


namespace PhilipponEtaleProjectiveLineTwoAffine

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
private abbrev Line (R : Type u) [CommRing R] := Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R)

/-- The two standard affine charts remain affine after base change to an affine scheme. -/
theorem exists_two_affine_opens {R A : Type u} [CommRing R] [CommRing A]
    (v : Spec (.of A) ⟶ Spec (.of R)) {P : Scheme.{u}}
    (r : P ⟶ Spec (.of A)) (d : P ⟶ Line R) (h : IsPullback r d v (ProjSpace.π R 1)) :
    ∃ U V : P.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ := by
  let D := ProjSpace.affineOpenCover R 1
  let C := D.openCover
  let W (i : Fin 2) := d ⁻¹ᵁ (C.f i).opensRange
  have hAffine (i : Fin 2) : IsAffineOpen (W i) := by
    let g := C.f i ≫ ProjSpace.π R 1
    let : IsAffine (C.X i) := inferInstanceAs (IsAffine (Spec (D.X i)))
    have hQ := (IsPullback.of_hasPullback (C.f i) d).paste_vert h.flip
    let e : pullback (C.f i) d ≅ pullback g v := hQ.isoPullback
    let : IsAffine (pullback (C.f i) d) := IsAffine.of_isIso e.hom
    rw [show W i = (pullback.snd (C.f i) d).opensRange from
      (Scheme.Hom.opensRange_pullbackSnd (C.f i) d).symm]
    exact isAffineOpen_opensRange _
  refine ⟨W 0, W 1, hAffine 0, hAffine 1, ?_⟩
  have hCover : ⨆ i, W i = ⊤ := d.iSup_preimage_eq_top C.iSup_opensRange
  rw [← hCover]
  apply le_antisymm
  · exact sup_le (le_iSup W 0) (le_iSup W 1)
  · apply iSup_le
    intro i
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right

/-- Affine-local vanishing of a restriction gives vanishing in degrees at
least two on the closed fiber of a relative projective line. -/
theorem subsingleton_H_of_local_vanishing {R A : Type u} [CommRing R] [CommRing A]
    (v : Spec (.of A) ⟶ Spec (.of R)) {P T : Scheme.{u}}
    (r : P ⟶ Spec (.of A)) (d : P ⟶ Line R) (h : IsPullback r d v (ProjSpace.π R 1))
    (j : T ⟶ P) (F : Sheaf P.smallEtaleTopology AddCommGrpCat.{u})
    (hVanishing : ∀ (W : P.Opens), IsAffineOpen W → ∀ m : ℕ,
      Subsingleton (((pullbackSheaves (j ∣_ W)).obj ((pullbackSheaves W.ι).obj F)).H (m + 1)))
    (q : ℕ) : Subsingleton (((pullbackSheaves j).obj F).H (q + 2)) := by
  let : IsProper r := MorphismProperty.of_isPullback h.flip (inferInstance : IsProper (ProjSpace.π R 1))
  have hTerminal : terminal.from P = r ≫ terminal.from (Spec (.of A)) := terminal.hom_ext _ _
  let : P.IsSeparated := ⟨hTerminal.symm ▸ inferInstanceAs
    (IsSeparated (r ≫ terminal.from (Spec (.of A))))⟩
  obtain ⟨U, V, hU, hV, hCover⟩ := exists_two_affine_opens v r d h
  exact PhilipponEtaleMayerVietoris.subsingleton_pullback_H_succ_succ_of_affine_cover U V j
    hCover hU hV F hVanishing q

end PhilipponEtaleProjectiveLineTwoAffine

end

section

open AlgebraicGeometry CategoryTheory
namespace PhilipponEtaleModuleSkyscrapers
universe u
variable {X : Scheme.{u}} {R : Type u} [Ring R]
private abbrev Modules := Sheaf X.smallEtaleTopology (ModuleCat.{u} R)
private abbrev forgetModule := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}

private instance : X.smallEtaleTopology.HasSheafCompose (forgetModule (R := R)) where
  isSheaf P hP := by
    apply Presheaf.isSheaf_of_isSheaf_comp _ _ (CategoryTheory.forget AddCommGrpCat.{u})
    exact Presheaf.isSheaf_comp_of_isSheaf _ P (CategoryTheory.forget (ModuleCat.{u} R)) hP

/-- Forget the module structure of an étale sheaf. -/
abbrev underlying : Modules (X := X) (R := R) ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  sheafCompose X.smallEtaleTopology (forgetModule (R := R))


end PhilipponEtaleModuleSkyscrapers

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleModuleSkyscrapers (underlying)
open PhilipponEtaleSmallSite (pullbackSheaves)


namespace PhilipponEtaleProjectiveLineHigherClosedFiber

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
private abbrev Line (R : Type u) [CommRing R] := Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R)
private abbrev Coeff (N : ℕ) := ModuleCat.{u} (ULift.{u} (ZMod N))
private abbrev Modules (X : Scheme.{u}) (N : ℕ) := Sheaf X.smallEtaleTopology (Coeff N)

/-- Affine closed-restriction acyclicity for injective prime module sheaves implies
vanishing in degrees at least two for a closed subscheme of the relative projective line. -/
theorem subsingleton_H_of_affine_closed_restriction {R A : Type u} [CommRing R] [CommRing A]
    (v : Spec (.of A) ⟶ Spec (.of R)) {P T : Scheme.{u}}
    (r : P ⟶ Spec (.of A)) (d : P ⟶ Line R) (h : IsPullback r d v (ProjSpace.π R 1))
    (j : T ⟶ P) [IsClosedImmersion j] (N : ℕ) (J : Modules P N) (hJ : Injective J)
    (hAffine : ∀ {X Y : Scheme.{u}} [IsAffine X] (i : Y ⟶ X) [IsClosedImmersion i]
      (I : Modules X N), Injective I → ∀ m : ℕ,
        Subsingleton (((pullbackSheaves i).obj (underlying.obj I)).H (m + 1)))
    (q : ℕ) : Subsingleton (((pullbackSheaves j).obj (underlying.obj J)).H (q + 2)) := by
  apply PhilipponEtaleProjectiveLineTwoAffine.subsingleton_H_of_local_vanishing v r d h j _ _ q
  intro W hW m
  let M := Coeff N
  let L := (PhilipponSmallEtaleOpenImmersion.along W.ι).sheafPushforwardContinuous M
    W.toScheme.smallEtaleTopology P.smallEtaleTopology
  let : L.PreservesInjectiveObjects := PhilipponEtaleExtensionByZero.restriction_preservesInjectiveObjects W.ι M
  let : IsAffine W.toScheme := hW
  let I := L.obj J
  have hI : Injective I := L.injective_obj_of_injective hJ
  have hVanish := hAffine (j ∣_ W) I hI m
  let e : underlying.obj I ≅ (pullbackSheaves W.ι).obj (underlying.obj J) :=
    (PhilipponEtaleNeighborhoodRestriction.restrictionIso W.ι).app (underlying.obj J)
  let H := Sheaf.functorH (j ⁻¹ᵁ W).toScheme.smallEtaleTopology (m + 1)
  let eH := (H.mapIso ((pullbackSheaves (j ∣_ W)).mapIso e)).addCommGroupIsoToAddEquiv
  exact ⟨fun a b => eH.symm.injective (hVanish.elim (eH.symm a) (eH.symm b))⟩

end PhilipponEtaleProjectiveLineHigherClosedFiber

end

section

attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (R A : Type u) [CommRing R] [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] (v : Spec (.of A) ⟶ Spec (.of R))
    {P : Scheme.{u}} (r : P ⟶ Spec (.of A)) (d : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R))
    (hr : IsPullback r d v (ProjSpace.π R 1)) (N : ℕ) (hN : N.Prime)
    (J : Sheaf P.smallEtaleTopology (ModuleCat.{u} (ULift.{u} (ZMod N)))) (hJ : Injective J)
    (G : Sheaf P.smallEtaleTopology AddCommGrpCat.{u})
    (hG : G.obj = J.obj ⋙ forget₂ (ModuleCat.{u} (ULift.{u} (ZMod N))) AddCommGrpCat.{u}) (m : ℕ) :
    Subsingleton (((PhilipponEtaleSmallSite.pullbackSheaves (pullback.snd
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) r)).obj G).H (m + 2)) := by
  let ρ := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  let i := pullback.snd ρ r
  let : IsClosedImmersion ρ := IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  let : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (pullback.snd ρ r))
  have hu : G = PhilipponEtaleModuleSkyscrapers.underlying.obj J := ObjectProperty.FullSubcategory.ext hG
  rw [hu]
  refine PhilipponEtaleProjectiveLineHigherClosedFiber.subsingleton_H_of_affine_closed_restriction
    v r d hr i N J hJ ?_ m
  intro X Y _ k _ M hM q
  exact AlgebraicGeometry.Scheme.subsingleton_etale_cohomology_restrict_injective_prime_of_affine_closedImmersion k N hN M hM (PhilipponEtaleModuleSkyscrapers.underlying.obj M) rfl q

end

end
