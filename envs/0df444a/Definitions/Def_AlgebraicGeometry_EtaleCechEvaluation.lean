-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleCechEvaluation
-- name    : AlgebraicGeometry_EtaleCechEvaluation
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-21T03:11:34.939744+00:00
-- url     : https://prove2.me/theorems/570dea72-9d46-4ed4-98ff-2b84916d5f4b
-- title:
--   Evaluation of Čech complexes on the small étale site
-- statement:
--   Evaluation of the augmented Čech nerve and cohomology locality for abelian sheaves.

import Definitions.Def_AlgebraicGeometry_EtaleModeledInverseImages

noncomputable section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open scoped Simplicial


namespace PhilipponCech

universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]

open AlgebraicTopology.AlternatingFaceMapComplex

/-- The augmented chain numbered with the augmentation target in degree zero. -/
def augmentedTerm (X : SimplicialObject.Augmented A) (i : ℕ) : A :=
  match i with
  | 0 => X.right
  | n + 1 => X.left.obj (op ⦋n⦌)

def augmentedD (X : SimplicialObject.Augmented A) (i : ℕ) :
    augmentedTerm X (i + 1) ⟶ augmentedTerm X i :=
  match i with
  | 0 => X.hom.app (op ⦋0⦌)
  | n + 1 => (obj X.left).d (n + 1) n

theorem augmentedD_comp (X : SimplicialObject.Augmented A) (n : ℕ) :
    augmentedD X (n + 1) ≫ augmentedD X n = 0 := by
  cases n with
  | zero =>
      have h := (ε.app X).comm 1 0
      simpa [augmentedD] using h.symm
  | succ n => exact (obj X.left).d_comp_d _ _ _

/-- The consecutive pair of differentials at an augmented Čech term. -/
def augmentedSC (X : SimplicialObject.Augmented A) (n : ℕ) : ShortComplex A :=
  ShortComplex.mk (augmentedD X (n + 1)) (augmentedD X n) (augmentedD_comp X n)

/-- Additive functors carry the augmented alternating face maps to the
augmented alternating face maps of the image simplicial object. -/
def mapAugmentedSC {B : Type*} [Category* B] [Abelian B] (G : A ⥤ B) [G.Additive]
    (X : SimplicialObject.Augmented A) (n : ℕ) :
    (augmentedSC X n).map G ≅
      augmentedSC ((SimplicialObject.Augmented.whiskeringObj A B G).obj X) n := by
  cases n <;> refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  all_goals
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, ShortComplex.map_f,
      ShortComplex.map_g, augmentedSC, augmentedD,
      obj_d_eq, Functor.map_sum, Functor.map_zsmul]
    first
    | rfl
    | simp [SimplicialObject.Augmented.whiskeringObj]

private def augmentedMap {X Y : SimplicialObject.Augmented A} (φ : X ⟶ Y) (i : ℕ) :
    augmentedTerm X i ⟶ augmentedTerm Y i :=
  match i with
  | 0 => φ.right
  | n + 1 => φ.left.app (op ⦋n⦌)

private theorem augmentedMap_comm {X Y : SimplicialObject.Augmented A} (φ : X ⟶ Y) (n : ℕ) :
    augmentedMap φ (n + 1) ≫ augmentedD Y n = augmentedD X n ≫ augmentedMap φ n := by
  cases n with
  | zero => exact SimplicialObject.Augmented.w₀ φ
  | succ n =>
      exact ((AlgebraicTopology.alternatingFaceMapComplex A).map φ.left).comm (n + 1) n

/-- An isomorphism on simplices preserves and reflects exactness of the
augmented complexes when the map on augmentation targets is a monomorphism. -/
theorem augmented_exact_iff_of_iso_of_mono {X Y : SimplicialObject.Augmented A}
    (φ : X ⟶ Y) [IsIso φ.left] [Mono φ.right] (n : ℕ) :
    (ShortComplex.mk (augmentedD X (n + 1)) (augmentedD X n) (augmentedD_comp X n)).Exact ↔
      (ShortComplex.mk (augmentedD Y (n + 1)) (augmentedD Y n) (augmentedD_comp Y n)).Exact := by
  let ψ : ShortComplex.mk (augmentedD X (n + 1)) (augmentedD X n) (augmentedD_comp X n) ⟶
      ShortComplex.mk (augmentedD Y (n + 1)) (augmentedD Y n) (augmentedD_comp Y n) :=
    { τ₁ := augmentedMap φ (n + 2)
      τ₂ := augmentedMap φ (n + 1)
      τ₃ := augmentedMap φ n
      comm₁₂ := augmentedMap_comm φ (n + 1)
      comm₂₃ := augmentedMap_comm φ n }
  have : Epi ψ.τ₁ := by
    change Epi (φ.left.app (op ⦋n + 1⦌))
    infer_instance
  have : IsIso ψ.τ₂ := by
    change IsIso (φ.left.app (op ⦋n⦌))
    infer_instance
  have : Mono ψ.τ₃ := by
    cases n with
    | zero => exact ‹Mono φ.right›
    | succ n =>
        change Mono (φ.left.app (op ⦋n⦌))
        infer_instance
  exact ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ

/-- An extra degeneracy splits the augmented alternating face map complex
and implies exactness in every degree of its simplicial terms. -/
theorem augmented_exact_of_extraDegeneracy {X : SimplicialObject.Augmented A}
    (e : X.ExtraDegeneracy) (n : ℕ) :
    (ShortComplex.mk (augmentedD X (n + 1)) (augmentedD X n) (augmentedD_comp X n)).Exact := by
  cases n with
  | zero =>
      let S := ShortComplex.mk (augmentedD X 1) (augmentedD X 0) (augmentedD_comp X 0)
      apply (S.exact_iff_epi_kernel_lift).mpr
      let p := kernel.lift S.g S.f S.zero
      have h : e.s 0 ≫ S.f = 𝟙 _ - S.g ≫ e.s' := by
        let a : X.left.obj (op ⦋0⦌) ⟶ X.right := X.hom.app (op ⦋0⦌)
        change e.s 0 ≫ (obj X.left).d 1 0 = 𝟙 (X.left.obj (op ⦋0⦌)) - a ≫ e.s'
        rw [obj_d_eq, Fin.sum_univ_two]
        simp [comp_add, sub_eq_add_neg, a, e.s_comp_δ₀, e.s₀_comp_δ₁]
      have hp : (kernel.ι S.g ≫ e.s 0) ≫ p = 𝟙 _ := by
        apply (cancel_mono (kernel.ι S.g)).mp
        simp only [Category.assoc, p, kernel.lift_ι, h, comp_sub, Category.comp_id,
          kernel.condition_assoc, zero_comp, sub_zero, Category.id_comp]
      exact epi_of_epi_fac hp
  | succ n =>
      let K := obj X.left
      let h := e.homotopyEquiv
      have : QuasiIso h.hom := h.quasiIso_hom
      have hexact : K.ExactAt (n + 1) := by
        apply (exactAt_iff_of_quasiIsoAt h.hom (n + 1)).mpr
        apply HomologicalComplex.ExactAt.of_isZero
        exact HomologicalComplex.isZero_single_obj_X _ 0 _ _ (Nat.succ_ne_zero n)
      have hprev : (ComplexShape.down ℕ).prev (n + 1) = n + 2 := by
        apply ComplexShape.prev_eq'
        rfl
      have hnext : (ComplexShape.down ℕ).next (n + 1) = n := by
        apply ComplexShape.next_eq'
        rfl
      exact (K.exactAt_iff' (n + 2) (n + 1) n hprev hnext).mp hexact

end PhilipponCech

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial


namespace PhilipponCech

universe u v
variable {C : Type u} [Category.{v} C] {U V : C} (f : V ⟶ U) (W : C)

/-- The image of the covering arrow on the represented set at `W`. -/
abbrev Range := Set.range (fun a : W ⟶ V => a ≫ f)

/-- The arrow on represented sets with codomain restricted to its image. -/
def toRange : (W ⟶ V) ⟶ Range f W :=
  TypeCat.ofHom fun a => ⟨a ≫ f, a, rfl⟩

theorem toRange_surjective : Function.Surjective (toRange f W) := by
  rintro ⟨_, a, rfl⟩
  exact ⟨a, rfl⟩

/-- The image augmentation of the evaluated nerve is split. -/
def rangeExtraDegeneracy :
    (Arrow.mk (toRange f W)).augmentedCechNerve.ExtraDegeneracy := by
  let h := toRange_surjective f W
  let s : SplitEpi (toRange f W) :=
    { section_ := TypeCat.ofHom (Function.surjInv h)
      id := by
        apply ConcreteCategory.hom_ext
        intro a
        exact Function.rightInverse_surjInv h a }
  exact Arrow.AugmentedCechNerve.extraDegeneracy _ s

variable [HasFiniteLimits C]

local notation "N" => Arrow.cechNerve (Arrow.mk f)
local notation "M" => Arrow.cechNerve (Arrow.mk (toRange f W))

private theorem nerve_map_π {n m : SimplexCategoryᵒᵖ} (k : n ⟶ m)
    (i : Fin (m.unop.len + 1)) :
    (N).map k ≫ WidePullback.π (fun _ => f) i =
      WidePullback.π (fun _ => f) (k.unop.toOrderHom i) :=
  WidePullback.lift_π _ _ _ _ _

private theorem nerve_map_base {n m : SimplexCategoryᵒᵖ} (k : n ⟶ m) :
    (N).map k ≫ WidePullback.base (fun _ : Fin (m.unop.len + 1) => f) =
      WidePullback.base (fun _ : Fin (n.unop.len + 1) => f) :=
  WidePullback.lift_base _ _ _ _

/-- The zero-simplices of the Čech nerve are the source of the arrow. -/
def nerveZeroIso : (N).obj (op ⦋0⦌) ≅ V where
  hom := WidePullback.π (fun _ : Fin 1 => f) 0
  inv := WidePullback.lift f (fun _ : Fin 1 => 𝟙 V) (by simp)
  hom_inv_id := by
    change WidePullback.π (fun _ : Fin 1 => f) 0 ≫
      WidePullback.lift f (fun _ : Fin 1 => 𝟙 V) (by simp) =
      𝟙 (widePullback U (fun _ : Fin 1 => V) (fun _ => f))
    apply WidePullback.hom_ext
    · intro i
      have : i = 0 := Subsingleton.elim _ _
      subst i
      rw [Category.assoc, WidePullback.lift_π, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, WidePullback.lift_base, Category.id_comp]
      exact WidePullback.π_arrow (fun _ : Fin 1 => f) 0
  inv_hom_id := WidePullback.lift_π (fun _ : Fin 1 => f) _ _ _ 0

theorem nerveZeroIso_hom_comp :
    (nerveZeroIso f).hom ≫ f = (Arrow.mk f).augmentedCechNerve.hom.app (op ⦋0⦌) :=
  WidePullback.π_arrow (fun _ : Fin 1 => f) 0

private def toRangeBase (n : SimplexCategoryᵒᵖ) :
    (W ⟶ (N).obj n) ⟶ Range f W :=
  TypeCat.ofHom fun a => ⟨a ≫ WidePullback.base (fun _ : Fin (n.unop.len + 1) => f),
    a ≫ WidePullback.π (fun _ : Fin (n.unop.len + 1) => f) 0, by simp [Category.assoc]⟩

private def liftToRange (n : SimplexCategoryᵒᵖ) :
    (W ⟶ (N).obj n) ⟶ (M).obj n :=
  WidePullback.lift (toRangeBase f W n)
    (fun i => TypeCat.ofHom fun a => a ≫ WidePullback.π (fun _ => f) i) (by
      intro i
      apply ConcreteCategory.hom_ext
      intro a
      apply Subtype.ext
      change (a ≫ WidePullback.π _ i) ≫ f = a ≫ WidePullback.base _
      rw [Category.assoc]
      exact congrArg (a ≫ ·) (WidePullback.π_arrow (fun _ => f) i))

private def liftFromRange (n : SimplexCategoryᵒᵖ) : (M).obj n ⟶ (W ⟶ (N).obj n) :=
  TypeCat.ofHom fun a => WidePullback.lift
    (WidePullback.base (fun _ : Fin (n.unop.len + 1) => toRange f W) a).val
    (fun i => WidePullback.π (fun _ => toRange f W) i a) (fun i => by
      have h := ConcreteCategory.congr_hom
        (WidePullback.π_arrow (fun _ : Fin (n.unop.len + 1) => toRange f W) i) a
      exact congrArg Subtype.val h)

private theorem liftToRange_π (n : SimplexCategoryᵒᵖ) (i : Fin (n.unop.len + 1))
    (a : W ⟶ (N).obj n) :
    WidePullback.π (fun _ => toRange f W) i (liftToRange f W n a) =
      a ≫ WidePullback.π (fun _ => f) i :=
  ConcreteCategory.congr_hom (WidePullback.lift_π (fun _ => toRange f W) _ _ _ i) a

private theorem liftToRange_base (n : SimplexCategoryᵒᵖ) (a : W ⟶ (N).obj n) :
    WidePullback.base (fun _ : Fin (n.unop.len + 1) => toRange f W) (liftToRange f W n a) =
      toRangeBase f W n a :=
  ConcreteCategory.congr_hom
    (WidePullback.lift_base (fun _ : Fin (n.unop.len + 1) => toRange f W) _ _ _) a

private theorem liftFromRange_π (n : SimplexCategoryᵒᵖ) (a : (M).obj n)
    (i : Fin (n.unop.len + 1)) :
    liftFromRange f W n a ≫ WidePullback.π (fun _ => f) i =
      WidePullback.π (fun _ => toRange f W) i a :=
  WidePullback.lift_π _ _ _ _ i

private theorem liftFromRange_base (n : SimplexCategoryᵒᵖ) (a : (M).obj n) :
    liftFromRange f W n a ≫ WidePullback.base (fun _ : Fin (n.unop.len + 1) => f) =
      (WidePullback.base (fun _ : Fin (n.unop.len + 1) => toRange f W) a).val :=
  WidePullback.lift_base _ _ _ _

/-- The Čech nerve evaluated at a test object is the Čech nerve of the
map to the image on the represented sets. -/
def evaluatedNerveIso : N ⋙ coyoneda.obj (op W) ≅ M :=
  NatIso.ofComponents (fun n =>
    { hom := liftToRange f W n
      inv := liftFromRange f W n
      hom_inv_id := by
        ext a
        change liftFromRange f W n (liftToRange f W n a) = a
        apply WidePullback.hom_ext
        · intro i
          change liftFromRange f W n (liftToRange f W n a) ≫
            WidePullback.π (fun _ => f) i = a ≫ WidePullback.π (fun _ => f) i
          rw [liftFromRange_π, liftToRange_π]
        · change liftFromRange f W n (liftToRange f W n a) ≫
            WidePullback.base (fun _ : Fin (n.unop.len + 1) => f) = _
          rw [liftFromRange_base, liftToRange_base]
          rfl
      inv_hom_id := by
        apply WidePullback.hom_ext
        · intro i
          apply ConcreteCategory.hom_ext
          intro a
          change WidePullback.π (fun _ => toRange f W) i
            (liftToRange f W n (liftFromRange f W n a)) = _
          rw [liftToRange_π, liftFromRange_π]
          rfl
        · apply ConcreteCategory.hom_ext
          intro a
          apply Subtype.ext
          change (WidePullback.base (fun _ => toRange f W)
            (liftToRange f W n (liftFromRange f W n a))).val = _
          rw [liftToRange_base]
          exact liftFromRange_base f W n a }) (by
    intro n m k
    apply WidePullback.hom_ext
    · intro i
      apply ConcreteCategory.hom_ext
      intro a
      change WidePullback.π (fun _ => toRange f W) i
        (liftToRange f W m (a ≫ (N).map k)) =
        ((M).map k ≫ WidePullback.π (fun _ => toRange f W) i) (liftToRange f W n a)
      rw [liftToRange_π, Category.assoc, nerve_map_π, nerve_map_π]
      exact (liftToRange_π f W n (k.unop.toOrderHom i) a).symm
    · apply ConcreteCategory.hom_ext
      intro a
      apply Subtype.ext
      change (WidePullback.base (fun _ => toRange f W)
        (liftToRange f W m (a ≫ (N).map k))).val =
        (((M).map k ≫ WidePullback.base (fun _ => toRange f W)) (liftToRange f W n a)).val
      rw [liftToRange_base, nerve_map_base]
      refine Eq.trans ?_ (congrArg Subtype.val (liftToRange_base f W n a)).symm
      change (a ≫ (N).map k) ≫ WidePullback.base _ = a ≫ WidePullback.base _
      rw [Category.assoc]
      exact congrArg (a ≫ ·) (nerve_map_base f k))

/-- The split image augmentation maps to the full evaluated augmentation by
the identity on its represented tuples and inclusion on its target. -/
def evaluatedImageComparison : (Arrow.mk (toRange f W)).augmentedCechNerve ⟶
    (SimplicialObject.Augmented.whiskeringObj C (Type v) (coyoneda.obj (op W))).obj
      (Arrow.mk f).augmentedCechNerve where
  left := (evaluatedNerveIso f W).inv
  right := TypeCat.ofHom Subtype.val
  w := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro a
    exact liftFromRange_base f W n a

instance : IsIso (evaluatedImageComparison f W).left := by
  change IsIso (evaluatedNerveIso f W).inv
  infer_instance

instance : Mono (evaluatedImageComparison f W).right := by
  apply (mono_iff_injective _).mpr
  exact Subtype.val_injective

end PhilipponCech

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite


namespace PhilipponSheafCohomology

universe u v w
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]


private def freePresheaf :=
  (Functor.whiskeringRight Cᵒᵖ (Type v) AddCommGrpCat.{v}).obj AddCommGrpCat.free

/-- The free abelian sheaf on the representable presheaf of an object. -/
def freeOn : C ⥤ (Sheaf J AddCommGrpCat.{v}) :=
  yoneda ⋙ freePresheaf (C := C) ⋙ presheafToSheaf J _

private def freeAdjunction :
    (freePresheaf (C := C) ⋙ presheafToSheaf J _) ⊣
      (sheafToPresheaf J AddCommGrpCat.{v} ⋙
        (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{v} (Type v)).obj (forget AddCommGrpCat.{v})) :=
  (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).comp (sheafificationAdjunction J _)

/-- Maps out of a free representable sheaf correspond to sections. -/
def representedSections (F : Sheaf J AddCommGrpCat.{v}) (U : C) :
    ((freeOn J).obj U ⟶ F) ≃ F.obj.obj (op U) :=
  ((freeAdjunction J).homEquiv (yoneda.obj U) F).trans yonedaEquiv

theorem representedSections_restrict {F : Sheaf J AddCommGrpCat.{v}} {U V : C}
    (f : V ⟶ U) (x : (freeOn J).obj U ⟶ F) :
    representedSections J F V ((freeOn J).map f ≫ x) =
      F.obj.map f.op (representedSections J F U x) := by
  unfold representedSections
  change yonedaEquiv ((freeAdjunction J).homEquiv _ _
    ((freePresheaf ⋙ presheafToSheaf J _).map (yoneda.map f) ≫ x)) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact (yonedaEquiv_naturality _ _).symm

/-- The augmentation of the free abelian Čech complex of a covering
arrow is an epimorphism of sheaves. -/
theorem freeOn_map_epi_of_cover [J.HasSheafCompose (forget AddCommGrpCat.{v})]
    {U V : C} (f : V ⟶ U) (h : Sieve.generate (.singleton f) ∈ J U) :
    Epi ((freeOn J).map f) := by
  constructor
  intro F a b hab
  apply (representedSections J F U).injective
  have hs := Presheaf.isSheaf_comp_of_isSheaf J F.obj (forget AddCommGrpCat) F.property
  have hs' := (Presieve.isSheafFor_iff_generate (.singleton f)).mpr
    ((isSheaf_iff_isSheaf_of_type _ _).mp hs _ h)
  apply hs'.isSeparatedFor.ext
  rintro _ _ ⟨⟩
  change F.obj.map f.op (representedSections J F U a) =
    F.obj.map f.op (representedSections J F U b)
  rw [← representedSections_restrict, ← representedSections_restrict, hab]

/-- Representability of sections is natural in the coefficient sheaf. -/
theorem representedSections_map {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (U : C)
    (x : (freeOn J).obj U ⟶ F) :
    representedSections J G U (x ≫ f) =
      f.hom.app (op U) (representedSections J F U x) := by
  unfold representedSections
  change yonedaEquiv ((freeAdjunction J).homEquiv _ _ (x ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_right, yonedaEquiv_comp]
  rfl

/-- The representability equivalence is additive in the sheaf morphism. -/
def representedSectionsAddEquiv (F : Sheaf J AddCommGrpCat.{v}) (U : C) :
    ((freeOn J).obj U ⟶ F) ≃+ F.obj.obj (op U) :=
  { representedSections J F U with
    map_add' := by
      intro a b
      change representedSections J F U (a + b) =
        representedSections J F U a + representedSections J F U b
      let G := (freeOn J).obj U
      have happ (c : G ⟶ F) : representedSections J F U c =
          c.hom.app (op U) (representedSections J G U (𝟙 G)) := by
        rw [← representedSections_map, Category.id_comp]
      rw [happ (a + b), happ a, happ b]
      rfl }

private def constantIntegers : Sheaf J AddCommGrpCat.{v} :=
  (constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ))

private def constantSections {T : C} (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{v}) :
    (constantIntegers J ⟶ F) ≃ F.obj.obj (op T) :=
  ((constantSheafAdj J AddCommGrpCat.{v} hT).homEquiv _ _).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv

private theorem constantSections_map {T : C} (hT : IsTerminal T)
    {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (x : constantIntegers J ⟶ F) :
    constantSections J hT G (x ≫ f) = f.hom.app (op T) (constantSections J hT F x) := by
  unfold constantSections
  change AddCommGrpCat.uliftZMultiplesAddEquiv _
    ((constantSheafAdj J AddCommGrpCat.{v} hT).homEquiv _ _ (x ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

/-- The free abelian sheaf on a terminal object is the constant integer sheaf. -/
def freeTerminalIso {T : C} (hT : IsTerminal T) :
    (freeOn J).obj T ≅ constantIntegers J := by
  let Y := (freeOn J).obj T
  let Z := constantIntegers J
  let a : Y ⟶ Z := (representedSections J Z T).symm (constantSections J hT Z (𝟙 Z))
  let b : Z ⟶ Y := (constantSections J hT Y).symm (representedSections J Y T (𝟙 Y))
  have ha : representedSections J Z T a = constantSections J hT Z (𝟙 Z) :=
    (representedSections J Z T).apply_symm_apply _
  have hb : constantSections J hT Y b = representedSections J Y T (𝟙 Y) :=
    (constantSections J hT Y).apply_symm_apply _
  refine ⟨a, b, ?_, ?_⟩
  · apply (representedSections J Y T).injective
    rw [representedSections_map, ha, ← constantSections_map, Category.id_comp, hb]
  · apply (constantSections J hT Z).injective
    rw [constantSections_map, hb, ← representedSections_map, Category.id_comp, ha]

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-- Evaluation of the cohomology presheaf at a terminal object gives the
same cohomology as taking Ext from the constant sheaf of integers. -/
def terminalComparison {T : C} (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{v}) (q : ℕ) :
    F.H q ≃+ F.H' q T := by
  let e := freeTerminalIso J hT
  refine
    { toFun := fun x => (Ext.mk₀ e.hom).comp x (zero_add q)
      invFun := fun x => (Ext.mk₀ e.inv).comp x (zero_add q)
      map_add' := fun x y => Ext.comp_add _ _ _ _
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp x (zero_add q)) (zero_add q) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]
  · intro x
    change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp x (zero_add q)) (zero_add q) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]

private theorem restrict_apply {F : Sheaf J AddCommGrpCat.{v}} {U V : C} (f : V ⟶ U) (q : ℕ) (x : F.H' q U) :
    (F.cohomologyPresheaf q).map f.op x =
      (Ext.mk₀ ((freeOn J).map f)).comp x (zero_add q) := rfl

/-- If all abelian sheaves glue arbitrary tuples of sections over a finite
family, cohomology on its target is the product of cohomology on its members. -/
theorem class_eq_zero_of_disjoint_gluing {ι : Type*} [Fintype ι] {U : C} {V : ι → C}
    (f : ∀ i, V i ⟶ U)
    (h : ∀ F : Sheaf J AddCommGrpCat.{v}, Function.Bijective
      (fun x : F.obj.obj (op U) => fun i => F.obj.map (f i).op x))
    (F : Sheaf J AddCommGrpCat.{v}) (q : ℕ) (x : F.H' q U)
    (hx : ∀ i, (F.cohomologyPresheaf q).map (f i).op x = 0) : x = 0 := by
  classical
  let c : Cofan (fun i => (freeOn J).obj (V i)) :=
    Cofan.mk ((freeOn J).obj U) (fun i => (freeOn J).map (f i))
  let d (t : Cofan (fun i => (freeOn J).obj (V i))) : c.pt ⟶ t.pt :=
    (representedSections J t.pt U).symm
      ((Equiv.ofBijective _ (h t.pt)).symm
        (fun i => representedSections J t.pt (V i) (t.inj i)))
  have hd (t : Cofan (fun i => (freeOn J).obj (V i))) (i : ι) :
      c.inj i ≫ d t = t.inj i := by
    apply (representedSections J t.pt (V i)).injective
    change representedSections J t.pt (V i) ((freeOn J).map (f i) ≫ d t) = _
    rw [representedSections_restrict]
    change ((Equiv.ofBijective _ (h t.pt)) (representedSections J t.pt U (d t))) i = _
    simp only [d, Equiv.apply_symm_apply]
  let hc : IsColimit c := Cofan.IsColimit.mk c d hd (fun t m hm => by
    apply (representedSections J t.pt U).injective
    apply (h t.pt).injective
    funext i
    have hi := congrArg (representedSections J t.pt (V i)) ((hm i).trans (hd t i).symm)
    change representedSections J t.pt (V i) ((freeOn J).map (f i) ≫ m) =
      representedSections J t.pt (V i) ((freeOn J).map (f i) ≫ d t) at hi
    simpa only [representedSections_restrict] using hi)
  let e := Ext.biproductAddEquiv (biconeIsBilimitOfColimitCoconeOfIsColimit hc) F q
  apply e.injective
  rw [map_zero]
  funext i
  exact hx i

private theorem restrict_boundary {F G : Sheaf J AddCommGrpCat.{v}} {U V : C} (f : V ⟶ U)
    (n : ℕ) (δ : Ext G F 1) (y : Ext ((freeOn J).obj U) G n) :
    (Ext.mk₀ ((freeOn J).map f)).comp (y.comp δ rfl) (zero_add (n + 1)) =
      ((Ext.mk₀ ((freeOn J).map f)).comp y (zero_add n)).comp δ rfl := by
  symm
  exact Ext.comp_assoc _ _ _ (zero_add n) (rfl : n + 1 = _) (by simp)

private theorem evaluate_mk₀ {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) :
    (Ext.addEquiv₀ (Ext.mk₀ f) : F ⟶ G) = f :=
  Ext.addEquiv₀.apply_symm_apply f

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{v})]
  [J.HasSheafCompose (forget AddCommGrpCat.{v})] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- Every individual positive-degree sheaf cohomology class restricts to zero
on a covering sieve. The proof uses dimension shifting and local lifting along
an epimorphism for the last shift in degree zero. -/
theorem cohomologyClass_locally_zero (q : ℕ) (F : Sheaf J AddCommGrpCat.{v}) (U : C) (x : F.H' (q + 1) U) :
    Presheaf.equalizerSieve (F := F.cohomologyPresheaf (q + 1)) (X := op U) x 0 ∈ J U := by
  induction q generalizing F U with
  | zero =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
      (cokernel.condition (Injective.ι F))
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι F) }
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ ((freeOn J).obj U) hS x
      (Ext.eq_zero_of_injective _) (n₀ := 0) rfl
    let t := representedSections J S.X₃ U (Ext.addEquiv₀ y)
    letI : Sheaf.IsLocallySurjective S.g :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{v} S.g).mpr hS.epi_g
    apply J.superset_covering _ (Presheaf.imageSieve_mem J S.g.hom (U := op U) t)
    intro V f hf
    obtain ⟨s, hs⟩ := hf
    let z := Ext.mk₀ ((representedSections J S.X₂ V).symm s)
    have hz : z.comp (Ext.mk₀ S.g) (add_zero 0) =
        (Ext.mk₀ ((freeOn J).map f)).comp y (zero_add 0) := by
      apply Ext.addEquiv₀.injective
      apply (representedSections J S.X₃ V).injective
      let y₀ := Ext.addEquiv₀ y
      have hy0 : Ext.mk₀ y₀ = y := Ext.mk₀_addEquiv₀_apply y
      rw [← hy0]
      simp only [z, Ext.mk₀_comp_mk₀, evaluate_mk₀ J]
      rw [representedSections_restrict, representedSections_map, Equiv.apply_symm_apply]
      exact hs
    change (F.cohomologyPresheaf 1).map f.op x = (F.cohomologyPresheaf 1).map f.op 0
    rw [map_zero, restrict_apply, ← hy, restrict_boundary, ← hz]
    simp only [Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass,
      Ext.comp_zero]
  | succ n ih =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
      (cokernel.condition (Injective.ι F))
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι F) }
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ ((freeOn J).obj U) hS x
      (Ext.eq_zero_of_injective _) (n₀ := n + 1) rfl
    apply J.superset_covering _ (ih S.X₃ U y)
    intro V f hf
    change (S.X₃.cohomologyPresheaf (n + 1)).map f.op y =
      (S.X₃.cohomologyPresheaf (n + 1)).map f.op 0 at hf
    rw [map_zero, restrict_apply] at hf
    change (F.cohomologyPresheaf (n + 1 + 1)).map f.op x =
      (F.cohomologyPresheaf (n + 1 + 1)).map f.op 0
    rw [map_zero, restrict_apply, ← hy, restrict_boundary, hf, Ext.zero_comp]

end PhilipponSheafCohomology

end

end


