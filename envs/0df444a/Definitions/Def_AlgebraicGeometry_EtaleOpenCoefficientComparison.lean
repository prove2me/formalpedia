-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleOpenCoefficientComparison
-- name    : AlgebraicGeometry_EtaleOpenCoefficientComparison
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-26T02:38:45.953612+00:00
-- url     : https://prove2.me/theorems/600a6b54-1ce7-4c57-9577-6af306952f91
-- title:
--   Étale restriction, extension by zero and direct images
-- statement:
--   An open restriction commutes with direct image. The extension by zero of a monomorphism into a restricted sheaf is monic.
-- source:
--   Mayer–Vietoris and the finite model method for étale cohomology.

import Definitions.Def_AlgebraicGeometry_EtaleCechEvaluation
import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestriction
import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Data.Nat.Prime.Basic

noncomputable section

section

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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
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

private theorem lan_homEquiv_symm_mono
    [∀ P : C ⥤ A, L.HasPointwiseLeftKanExtension P]
    (h : ∀ W, IsEmpty (CostructuredArrow L W) ∨
      ∃ t : CostructuredArrow L W, Nonempty (IsTerminal t) ∧ IsIso t.hom)
    {P : C ⥤ A} {Q : D ⥤ A} (α : P ⟶ L ⋙ Q) [Mono α] :
    Mono (((L.lanAdjunction A).homEquiv P Q).symm α) := by
  let β := ((L.lanAdjunction A).homEquiv P Q).symm α
  have hβ : L.lanUnit.app P ≫ whiskerLeft L β = α := by
    have hb := ((L.lanAdjunction A).homEquiv P Q).apply_symm_apply α
    rw [Adjunction.homEquiv_unit, L.lanAdjunction_unit] at hb
    exact hb
  have hα := (NatTrans.mono_iff_mono_app α).mp ‹Mono α›
  change Mono β
  apply (NatTrans.mono_iff_mono_app β).mpr
  intro W
  rcases h W with he | ⟨t, ⟨ht⟩, hIso⟩
  · let c := (Functor.LeftExtension.mk _ (L.leftKanExtensionUnit P)).coconeAt W
    let hC : IsColimit c := L.isPointwiseLeftKanExtensionLeftKanExtensionUnit P W
    have hz : IsZero ((L.lan.obj P).obj W) :=
      ((isColimitEquivIsInitialOfIsEmpty A c) hC).isZero
    exact ⟨fun a b _ => hz.eq_of_tgt a b⟩
  · let η := (L.lanUnit.app P).app t.left ≫ (L.lan.obj P).map t.hom
    let : IsIso η :=
      (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit P W).isIso_ι_app_of_isTerminal t ht
    let : IsIso t.hom := hIso
    have hc : α.app t.left ≫ Q.map t.hom = η ≫ β.app W := by
      have hb := NatTrans.congr_app hβ t.left
      change (L.lanUnit.app P).app t.left ≫ β.app (L.obj t.left) = α.app t.left at hb
      rw [← hb, Category.assoc, ← β.naturality, ← Category.assoc]
    exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.monomorphisms A)
      (Arrow.isoMk (asIso η) (asIso (Q.map t.hom)) hc.symm)).mp (hα t.left)

end Kan

universe u
variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

open PhilipponSmallEtaleOpenImmersion (along liftObj liftIso pullback_cover)

instance : (along f).IsCocontinuous Y.smallEtaleTopology X.smallEtaleTopology where
  cover_lift h := pullback_cover f _ h

private theorem along_op_shape_with_iso (W : X.Etaleᵒᵖ) :
    IsEmpty (CostructuredArrow (along f).op W) ∨
      ∃ t : CostructuredArrow (along f).op W, Nonempty (IsTerminal t) ∧ IsIso t.hom := by
  classical
  cases isEmpty_or_nonempty (CostructuredArrow (along f).op W) with
  | inl he => exact Or.inl he
  | inr ht =>
      let t := ht.some
      let e := (liftIso f t.hom.unop).symm.op
      exact Or.inr ⟨CostructuredArrow.mk e.hom, ⟨terminalOfIso (along f).op e⟩,
        inferInstanceAs (IsIso e.hom)⟩

private theorem along_op_shape (W : X.Etaleᵒᵖ) :
    IsEmpty (CostructuredArrow (along f).op W) ∨
      ∃ t : CostructuredArrow (along f).op W, Nonempty (IsTerminal t) := by
  rcases along_op_shape_with_iso f W with he | ⟨t, ht, _⟩
  · exact Or.inl he
  · exact Or.inr ⟨t, ht⟩

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

/-- Extending a sheaf by zero transposes a monomorphism into a restricted
sheaf to a monomorphism on the ambient scheme. -/
theorem exists_extension_of_restriction_mono
    {F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}}
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (m : F ⟶ (restrict f).obj G) [Mono m] :
    ∃ (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (u : F ⟶ (restrict f).obj H)
      (a : H ⟶ G), Mono a ∧ u ≫ (restrict f).map a = m ∧
      ∀ (K : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (k : F ⟶ (restrict f).obj K),
        ∃ b : H ⟶ K, u ≫ (restrict f).map b = k := by
  let L := (along f).op
  let P := L.lan.obj F.obj
  let S := presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}
  let adj := sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u}
  let H := S.obj P
  let u : F ⟶ (restrict f).obj H :=
    ⟨L.lanUnit.app F.obj ≫ whiskerLeft L (adj.unit.app P)⟩
  let transpose (K : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      (k : F ⟶ (restrict f).obj K) : P ⟶ K.obj :=
    ((L.lanAdjunction AddCommGrpCat.{u}).homEquiv F.obj K.obj).symm k.hom
  let ext (K : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      (k : F ⟶ (restrict f).obj K) : H ⟶ K :=
    (adj.homEquiv P K).symm (transpose K k)
  have fac (K : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      (k : F ⟶ (restrict f).obj K) : u ≫ (restrict f).map (ext K k) = k := by
    have h := (adj.homEquiv P K).apply_symm_apply (transpose K k)
    rw [Adjunction.homEquiv_unit] at h
    have h' := ((L.lanAdjunction AddCommGrpCat.{u}).homEquiv F.obj K.obj).apply_symm_apply k.hom
    rw [Adjunction.homEquiv_unit, L.lanAdjunction_unit] at h'
    apply Sheaf.hom_ext
    change (L.lanUnit.app F.obj ≫ whiskerLeft L (adj.unit.app P)) ≫
      whiskerLeft L (ext K k).hom = k.hom
    change adj.unit.app P ≫ (ext K k).hom = transpose K k at h
    rw [Category.assoc, ← whiskerLeft_comp, h]
    exact h'
  let : Mono m.hom := Functor.map_mono (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat) m
  let : Mono (transpose G m) := lan_homEquiv_symm_mono L (along_op_shape_with_iso f) m.hom
  have hm : Mono (ext G m) := by
    change Mono (S.map (transpose G m) ≫ adj.counit.app G)
    infer_instance
  exact ⟨H, u, ext G m, hm, fac G m, fun K k => ⟨ext K k, fac K k⟩⟩

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

/-- A class of coefficients admits comparison in all degrees if each class
on either side can be killed by a monomorphism with cokernel in the class. -/
theorem comparison_bijective_of_effacement (B : C → Prop)
    (h : ∀ M : C, B M → Function.Bijective (fun a : Q ⟶ M => p ≫ R.map a))
    (left : ∀ M : C, B M → ∀ (n : ℕ) (x : Ext Q M (n + 1)),
      ∃ (J : C) (i : M ⟶ J), Mono i ∧ B J ∧ B (cokernel i) ∧
        x.comp (Ext.mk₀ i) (add_zero (n + 1)) = 0)
    (right : ∀ M : C, B M → ∀ (n : ℕ) (x : Ext P (R.obj M) (n + 1)),
      ∃ (J : C) (i : M ⟶ J), Mono i ∧ B J ∧ B (cokernel i) ∧
        x.comp (Ext.mk₀ (R.map i)) (add_zero (n + 1)) = 0)
    (n : ℕ) (M : C) (hM : B M) : Function.Bijective (comparison R p M n) := by
  induction n generalizing M with
  | zero => exact comparison_zero_bijective R p M (h M hM)
  | succ n ih =>
      constructor
      · apply (AddMonoidHom.ker_eq_bot_iff _).mp
        rw [AddSubgroup.eq_bot_iff_forall]
        intro x hx
        obtain ⟨J, i, hi, hJ, hQ, hkill⟩ := left M hM n x
        let _ : Mono i := hi
        let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
        have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
        have hSR := hS.map_of_exact R
        have hx' : comparison R p S.X₁ (n + 1) x = 0 := hx
        obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ Q hS x hkill (n₀ := n) rfl
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
        obtain ⟨J, i, hi, _, hQ, hkill⟩ := right M hM n x'
        let _ : Mono i := hi
        let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
        have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
        have hSR := hS.map_of_exact R
        obtain ⟨y', hy'⟩ := Ext.covariant_sequence_exact₁ P hSR x' hkill (n₀ := n) rfl
        obtain ⟨y, hy⟩ := (ih S.X₃ hQ).surjective y'
        refine ⟨y.comp hS.extClass rfl, ?_⟩
        rw [comparison_boundary R p hS, hy]
        exact hy'

/-- Acyclic embeddings give the class-by-class effacement criterion. -/
theorem comparison_bijective_of_acyclic_embeddings (B : C → Prop)
    (h : ∀ M : C, B M → Function.Bijective (fun a : Q ⟶ M => p ≫ R.map a))
    (emb : ∀ M : C, B M → ∃ (J : C) (i : M ⟶ J), Mono i ∧ B J ∧ B (cokernel i) ∧
      ∀ n : ℕ, Subsingleton (Ext Q J (n + 1)) ∧ Subsingleton (Ext P (R.obj J) (n + 1)))
    (n : ℕ) (M : C) (hM : B M) : Function.Bijective (comparison R p M n) := by
  apply comparison_bijective_of_effacement R p B h _ _ n M hM
  · intro M hM q x
    obtain ⟨J, i, hi, hJ, hQ, hA⟩ := emb M hM
    exact ⟨J, i, hi, hJ, hQ, (hA q).1.elim _ _⟩
  · intro M hM q x
    obtain ⟨J, i, hi, hJ, hQ, hA⟩ := emb M hM
    exact ⟨J, i, hi, hJ, hQ, (hA q).2.elim _ _⟩

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

/-- Cohomology on an open chart is functorial in the coefficient sheaf. -/
theorem openComparison_map {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (a : F ⟶ G)
    (q : ℕ) (t : F.H' q (V f)) :
    openComparison f G q (t.comp (Ext.mk₀ a) (add_zero q)) =
      Sheaf.H.map ((restrict f).map a) q (openComparison f F q t) := by
  let hT : IsTerminal (T (Y := Y)) := IsTerminal.isTerminalOfObj (Scheme.Etale.forget Y) _ Over.mkIdTerminal
  let e := (PhilipponSheafCohomology.freeTerminalIso Y.smallEtaleTopology hT).inv
  let b := PhilipponExtComparison.comparison (restrict f) (evaluationArrow f) F q t
  change (Ext.mk₀ e).comp
      (PhilipponExtComparison.comparison (restrict f) (evaluationArrow f) G q
        (t.comp (Ext.mk₀ a) (add_zero q))) (zero_add q) =
    ((Ext.mk₀ e).comp b (zero_add q)).comp (Ext.mk₀ ((restrict f).map a)) (add_zero q)
  rw [PhilipponExtComparison.comparison_post, Ext.comp_assoc_of_third_deg_zero]

end PhilipponEtaleOpenCohomology

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (pullbackConstantIso)
open PhilipponEtaleBaseChangeComparison (baseChange map_isPullback)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleExtensionByZero (restrict)
open PhilipponSmallEtaleOpenImmersion (along)


namespace PhilipponEtaleOpenDirectImage

universe u

variable {X Y W T : Scheme.{u}} (i : W ⟶ X) (p : Y ⟶ X) (q : T ⟶ W) (k : T ⟶ Y)
  (h : IsPullback q k i p)

include h
private theorem chartPullback (U : W.Etale) :
    IsPullback (pullback.fst U.hom q) (pullback.snd U.hom q ≫ k) (U.hom ≫ i) p :=
  (IsPullback.of_hasPullback U.hom q).paste_vert h

variable [IsOpenImmersion i] [IsOpenImmersion k]

/-- Restriction to an open commutes with direct image on the étale sites. -/
def chartSquare : baseChange q ⋙ along k ≅ along i ⋙ baseChange p := by
  let e (U : W.Etale) := (chartPullback i p q k h U).isoPullback
  refine NatIso.ofComponents (fun U => MorphismProperty.Over.isoMk (e U)
    (chartPullback i p q k h U).isoPullback_hom_snd) ?_
  intro U V a
  apply MorphismProperty.Over.Hom.ext
  let d : pullback U.hom q ⟶ pullback V.hom q := ((baseChange q).map a).left
  let d' : pullback (U.hom ≫ i) p ⟶ pullback (V.hom ≫ i) p :=
    ((baseChange p).map ((along i).map a)).left
  change d ≫ (e V).hom = (e U).hom ≫ d'
  apply pullback.hom_ext
  · have hd : d ≫ pullback.fst V.hom q = pullback.fst U.hom q ≫ a.left :=
      (map_isPullback q a).w.symm
    have hd' : d' ≫ pullback.fst (V.hom ≫ i) p = pullback.fst (U.hom ≫ i) p ≫ a.left :=
      (map_isPullback p ((along i).map a)).w.symm
    change d ≫ (e V).hom ≫ pullback.fst (V.hom ≫ i) p =
      ((e U).hom ≫ d') ≫ pullback.fst (V.hom ≫ i) p
    rw [Category.assoc, (chartPullback i p q k h V).isoPullback_hom_fst, hd, hd',
      (chartPullback i p q k h U).isoPullback_hom_fst_assoc]
  · have hd : d ≫ pullback.snd V.hom q = pullback.snd U.hom q :=
      MorphismProperty.Over.w ((baseChange q).map a)
    have hd' : d' ≫ pullback.snd (V.hom ≫ i) p = pullback.snd (U.hom ≫ i) p :=
      MorphismProperty.Over.w ((baseChange p).map ((along i).map a))
    change d ≫ (e V).hom ≫ pullback.snd (V.hom ≫ i) p =
      ((e U).hom ≫ d') ≫ pullback.snd (V.hom ≫ i) p
    rw [Category.assoc, (chartPullback i p q k h V).isoPullback_hom_snd,
      hd', (chartPullback i p q k h U).isoPullback_hom_snd, ← Category.assoc, hd]

def restrictDirectImageIso (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (restrict i).obj ((pushforward p).obj F) ≅ (pushforward q).obj ((restrict k).obj F) := by
  let e : (along i ⋙ baseChange p).op ≅ (baseChange q ⋙ along k).op :=
    NatIso.op (chartSquare i p q k h)
  exact (fullyFaithfulSheafToPresheaf W.smallEtaleTopology AddCommGrpCat.{u}).preimageIso
    (Functor.isoWhiskerRight e F.obj)

/-- For a constant sheaf, the restricted direct image has the same constant
coefficients on the inverse image of the open. -/
def restrictConstantDirectImageIso (A : AddCommGrpCat.{u}) :
    (restrict i).obj ((pushforward p).obj
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A)) ≅
    (pushforward q).obj ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u}).obj A) := by
  let F := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A
  exact restrictDirectImageIso i p q k h F ≪≫
    (pushforward q).mapIso ((PhilipponEtaleNeighborhoodRestriction.restrictionIso k).app F ≪≫
      (pullbackConstantIso k).app A)

end PhilipponEtaleOpenDirectImage

end

end


