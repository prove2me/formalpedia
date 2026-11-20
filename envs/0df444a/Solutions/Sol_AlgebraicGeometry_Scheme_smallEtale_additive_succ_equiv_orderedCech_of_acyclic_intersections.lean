-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.smallEtale_additive_succ_equiv_orderedCech_of_acyclic_intersections
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-20T04:03:47.769212+00:00
-- url     : https://prove2.me/submissions/15af7fd9-9ae2-49e2-86da-34607971aa77

import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.Order.Fin.Tuple
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Homology.Functor
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_SmallEtaleAdditive
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.LinearAlgebra.Quotient.Basic

noncomputable section

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


end PhilipponSheafCohomology

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits


namespace PhilipponCech

universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The short exact sequences obtained by cutting an augmented resolution
at its cycles. `cycles 0` is the object being resolved. -/
structure Resolution where
  terms : ℕ → C
  cycles : ℕ → C
  inclusion (j : ℕ) : cycles (j + 1) ⟶ terms j
  projection (j : ℕ) : terms j ⟶ cycles j
  zero (j : ℕ) : inclusion j ≫ projection j = 0
  shortExact (j : ℕ) : (ShortComplex.mk (inclusion j) (projection j) (zero j)).ShortExact

namespace Resolution

section OfExact

variable {A : ℕ → C} (d : ∀ k, A (k + 1) ⟶ A k)
  (dd : ∀ k, d (k + 1) ≫ d k = 0)

private def cyclesOfExact : ℕ → C
  | 0 => A 0
  | k + 1 => kernel (d k)

private def projectionOfExact : ∀ k, A (k + 1) ⟶ cyclesOfExact d k
  | 0 => d 0
  | k + 1 => kernel.lift (d k) (d (k + 1)) (dd k)

private lemma inclusion_projection_zero (k : ℕ) :
    kernel.ι (d k) ≫ projectionOfExact d dd k = 0 := by
  cases k with
  | zero => exact kernel.condition _
  | succ k =>
      apply (cancel_mono (kernel.ι (d k))).mp
      simp only [Category.assoc, projectionOfExact, kernel.lift_ι, kernel.condition, zero_comp]

/-- Cut an exact augmented chain into short exact sequences of cycles. The
first object `A 0` is the target of the epimorphic augmentation `d 0`. -/
def ofExact [Epi (d 0)]
    (h : ∀ k, (ShortComplex.mk (d (k + 1)) (d k) (dd k)).Exact) : Resolution (C := C) where
  terms k := A (k + 1)
  cycles := cyclesOfExact d
  inclusion k := kernel.ι (d k)
  projection := projectionOfExact d dd
  zero := inclusion_projection_zero d dd
  shortExact k := by
    cases k with
    | zero =>
        refine ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel (d 0)) inferInstance ?_
        exact ‹Epi (d 0)›
    | succ k =>
        have he := (ShortComplex.exact_iff_epi_kernel_lift _).mp (h k)
        refine ShortComplex.ShortExact.mk' ?_ inferInstance he
        apply ShortComplex.exact_of_f_is_kernel
        refine KernelFork.IsLimit.ofι' (kernel.ι (d (k + 1)))
          (inclusion_projection_zero d dd (k + 1)) (fun s hs => ?_)
        have hs' : s ≫ d (k + 1) = 0 := by
          have hh := congrArg (fun z => z ≫ kernel.ι (d k)) hs
          simpa only [projectionOfExact, Category.assoc, kernel.lift_ι, zero_comp] using hh
        exact ⟨kernel.lift (d (k + 1)) s hs', kernel.lift_ι _ _ _⟩

@[simp] theorem ofExact_differential [Epi (d 0)]
    (h : ∀ k, (ShortComplex.mk (d (k + 1)) (d k) (dd k)).Exact) (j : ℕ) :
    (ofExact d dd h).projection (j + 1) ≫ (ofExact d dd h).inclusion j = d (j + 1) :=
  kernel.lift_ι _ _ _

end OfExact

variable (R : Resolution (C := C)) (F : C)

/-- The differential obtained by applying `Hom(-, F)` to the resolution. -/
def cochain (j : ℕ) (f : R.terms j ⟶ F) : R.terms (j + 1) ⟶ F :=
  R.projection (j + 1) ≫ R.inclusion j ≫ f

variable [HasExt.{w} C]

private theorem boundary_eq_zero_of_cochain_exact (j : ℕ)
    (h : Function.Exact (R.cochain F j) (R.cochain F (j + 1)))
    (a : Ext (R.cycles (j + 1)) F 0) :
    (R.shortExact j).extClass.comp a (rfl : 1 + 0 = 1) = 0 := by
  let b := Ext.addEquiv₀ a
  have hb : R.cochain F (j + 1) (R.projection (j + 1) ≫ b) = 0 := by
    unfold cochain
    rw [← Category.assoc (R.inclusion (j + 1)), R.zero, zero_comp, comp_zero]
  obtain ⟨c, hc⟩ := (h _).mp hb
  have : Epi (R.projection (j + 1)) := (R.shortExact (j + 1)).epi_g
  have he : R.inclusion j ≫ c = b := (cancel_epi (R.projection (j + 1))).mp hc
  have ha : a = (Ext.mk₀ (R.inclusion j)).comp (Ext.mk₀ c) (rfl : 0 + 0 = 0) := by
    rw [Ext.mk₀_comp_mk₀, he, Ext.mk₀_addEquiv₀_apply]
  rw [ha]
  exact (R.shortExact j).extClass_comp_assoc (Ext.mk₀ c)

/-- A positive-degree class that vanishes on the first term of the
resolution is zero if all smaller positive degrees vanish on its terms
and its complex of sections is exact in positive degrees. -/
theorem eq_zero_of_restrict_zero (n j : ℕ)
    (hvanish : ∀ k q, 0 < q → q ≤ n → Subsingleton (Ext (R.terms k) F q))
    (hcochain : ∀ k, Function.Exact (R.cochain F k) (R.cochain F (k + 1)))
    (x : Ext (R.cycles j) F (n + 1))
    (hx : (Ext.mk₀ (R.projection j)).comp x (zero_add (n + 1)) = 0) : x = 0 := by
  induction n generalizing j with
  | zero =>
      obtain ⟨a, ha⟩ := Ext.contravariant_sequence_exact₃ (R.shortExact j) F x hx
        (rfl : 1 + 0 = 0 + 1)
      exact ha.symm.trans (R.boundary_eq_zero_of_cochain_exact F j (hcochain j) a)
  | succ n ih =>
      obtain ⟨a, ha⟩ := Ext.contravariant_sequence_exact₃ (R.shortExact j) F x hx
        (Nat.add_comm 1 (n + 1))
      have hz : (Ext.mk₀ (R.projection (j + 1))).comp a (zero_add (n + 1)) = 0 :=
        (hvanish (j + 1) (n + 1) (Nat.succ_pos n) le_rfl).elim _ _
      have ha' := ih (j + 1)
        (fun k q hp hq => hvanish k q hp (hq.trans (Nat.le_succ n))) a hz
      rw [← ha, ha', Ext.comp_zero]

end Resolution

end PhilipponCech

end

section

set_option autoImplicit false

open scoped BigOperators


namespace PhilipponOrderedSimplex

variable (I : Type*) [LinearOrder I]

/-- Strictly ordered tuples, including the empty tuple in augmented degree. -/
abbrev Tuple (n : ℕ) := {x : Fin n → I // StrictMono x}

abbrev Chains (n : ℕ) := FreeAbelianGroup (Tuple I n)

variable {I}

def face {n : ℕ} (s : Tuple I (n + 1)) (i : Fin (n + 1)) : Tuple I n :=
  ⟨s.val ∘ i.succAbove, s.property.comp (Fin.strictMono_succAbove i)⟩

def cons {n : ℕ} (a : I) (s : Tuple I n) (hs : ∀ i, a < s.val i) : Tuple I (n + 1) :=
  ⟨Fin.cons a s.val, Fin.strictMono_cons.mpr ⟨hs, s.property⟩⟩

@[simp] theorem face_cons_zero {n : ℕ} (a : I) (s : Tuple I n) (hs : ∀ i, a < s.val i) :
    face (cons a s hs) 0 = s := by
  apply Subtype.ext
  funext i
  simp [face, cons]

theorem face_cons_succ {n : ℕ} (a : I) (s : Tuple I (n + 1)) (hs : ∀ i, a < s.val i)
    (i : Fin (n + 1)) :
    face (cons a s hs) i.succ = cons a (face s i) (fun k => hs (i.succAbove k)) := by
  apply Subtype.ext
  exact Fin.cons_comp_succ_succAbove a s.val i

private theorem cons_face_zero {n : ℕ} (s : Tuple I (n + 1)) :
    cons (s.val 0) (face s 0) (fun i => s.property (Fin.succ_pos i)) = s := by
  apply Subtype.ext
  exact Fin.cons_self_tail _

variable (I)

/-- The augmented oriented boundary is the signed sum of vertex deletions. -/
def boundary (n : ℕ) : Chains I (n + 1) →+ Chains I n :=
  FreeAbelianGroup.lift (fun s => ∑ i : Fin (n + 1), ((-1 : ℤ) ^ (i : ℕ)) •
    FreeAbelianGroup.of (face s i))

@[simp] theorem boundary_of (n : ℕ) (s : Tuple I (n + 1)) :
    boundary I n (FreeAbelianGroup.of s) =
      ∑ i : Fin (n + 1), ((-1 : ℤ) ^ (i : ℕ)) • FreeAbelianGroup.of (face s i) :=
  FreeAbelianGroup.lift_apply_of _ _

/-- Insert the chosen vertex whenever it is strictly below the tuple. -/
def cone (a : I) (n : ℕ) : Chains I n →+ Chains I (n + 1) :=
  FreeAbelianGroup.lift (fun s => if hs : ∀ i, a < s.val i then FreeAbelianGroup.of (cons a s hs) else 0)

@[simp] theorem cone_of_insert (a : I) {n : ℕ} (s : Tuple I n) (hs : ∀ i, a < s.val i) :
    cone I a n (FreeAbelianGroup.of s) = FreeAbelianGroup.of (cons a s hs) := by
  simp [cone, hs]

@[simp] theorem cone_of_skip (a : I) {n : ℕ} (s : Tuple I n) (hs : ¬∀ i, a < s.val i) :
    cone I a n (FreeAbelianGroup.of s) = 0 := by
  simp [cone, hs]

private theorem boundary_cone_insert (a : I) {n : ℕ} (s : Tuple I (n + 1)) (hs : ∀ i, a < s.val i) :
    boundary I (n + 1) (FreeAbelianGroup.of (cons a s hs)) =
      FreeAbelianGroup.of s - cone I a n (boundary I n (FreeAbelianGroup.of s)) := by
  rw [boundary_of, Fin.sum_univ_succ, boundary_of, map_sum]
  have hface (i : Fin (n + 1)) := cone_of_insert I a (face s i) (fun k => hs (i.succAbove k))
  simp only [Fin.val_zero, pow_zero, one_zsmul, face_cons_zero, face_cons_succ, map_zsmul,
    hface, Fin.val_succ, pow_succ, mul_neg_one,
    neg_zsmul, Finset.sum_neg_distrib, sub_eq_add_neg]

private theorem cone_boundary_of_head (a : I) {n : ℕ} (s : Tuple I (n + 1))
    (h : s.val 0 = a) : cone I a n (boundary I n (FreeAbelianGroup.of s)) = FreeAbelianGroup.of s := by
  subst a
  rw [boundary_of, Fin.sum_univ_succ, map_add, map_zsmul]
  have hs (i : Fin n) : s.val 0 < (face s 0).val i := s.property (Fin.succ_pos i)
  rw [cone_of_insert I _ _ hs, cons_face_zero]
  have hskip (i : Fin n) : ¬∀ k, s.val 0 < (face s i.succ).val k := by
    cases n with
    | zero => exact i.elim0
    | succ n =>
        intro hi
        exact (lt_irrefl (s.val 0)) (by simpa [face] using hi 0)
  simp [map_sum, map_zsmul, hskip]

/-- Coning at the least vertex gives the contraction identity for all
non-augmented terms of the ordered simplex. -/
theorem contraction (a : I) (ha : ∀ b : I, a ≤ b) (n : ℕ) (x : Chains I (n + 1)) :
    boundary I (n + 1) (cone I a (n + 1) x) + cone I a n (boundary I n x) = x := by
  have hh : (boundary I (n + 1)).comp (cone I a (n + 1)) +
      (cone I a n).comp (boundary I n) = AddMonoidHom.id _ := by
    apply FreeAbelianGroup.lift_ext
    intro s
    change boundary I (n + 1) (cone I a (n + 1) (FreeAbelianGroup.of s)) +
      cone I a n (boundary I n (FreeAbelianGroup.of s)) = FreeAbelianGroup.of s
    rcases eq_or_lt_of_le (ha (s.val 0)) with he | he
    · rw [cone_of_skip I a s (fun h => (lt_irrefl a) (by simpa [← he] using h 0)), map_zero, zero_add]
      exact cone_boundary_of_head I a s he.symm
    · have hs (i : Fin (n + 1)) : a < s.val i := he.trans_le (s.property.monotone (Fin.zero_le i))
      rw [cone_of_insert I a s hs, boundary_cone_insert I a s hs, sub_add_cancel]
  exact DFunLike.congr_fun hh x

/-- A vertex contracts the augmentation onto the empty tuple. -/
theorem contraction_augmented (a : I) (x : Chains I 0) :
    boundary I 0 (cone I a 0 x) = x := by
  have h : (boundary I 0).comp (cone I a 0) = AddMonoidHom.id _ := by
    apply FreeAbelianGroup.lift_ext
    intro s
    change boundary I 0 (cone I a 0 (FreeAbelianGroup.of s)) = FreeAbelianGroup.of s
    rw [cone_of_insert I a s (fun i => i.elim0), boundary_of, Fin.sum_univ_one]
    simp
  exact DFunLike.congr_fun h x

/-- Consecutive oriented boundaries compose to zero. -/
theorem boundary_squared (n : ℕ) : (boundary I n).comp (boundary I (n + 1)) = 0 := by
  induction n with
  | zero =>
      apply FreeAbelianGroup.lift_ext
      intro s
      let a := s.val 0
      let t := face s 0
      have ht (i : Fin 1) : a < t.val i := s.property (Fin.succ_pos i)
      change boundary I 0 (boundary I 1 (FreeAbelianGroup.of s)) = 0
      rw [← cons_face_zero s, boundary_cone_insert I a t ht, map_sub, contraction_augmented, sub_self]
  | succ n ih =>
      apply FreeAbelianGroup.lift_ext
      intro s
      let a := s.val 0
      let t := face s 0
      have ht (i : Fin (n + 2)) : a < t.val i := s.property (Fin.succ_pos i)
      have hdecomp : boundary I (n + 2) (FreeAbelianGroup.of s) =
          FreeAbelianGroup.of t - cone I a (n + 1) (boundary I (n + 1) (FreeAbelianGroup.of t)) :=
        (congrArg (fun v => boundary I (n + 2) (FreeAbelianGroup.of v)) (cons_face_zero s)).symm.trans
          (boundary_cone_insert I a t ht)
      have hz : boundary I n (boundary I (n + 1) (FreeAbelianGroup.of t)) = 0 :=
        DFunLike.congr_fun ih (FreeAbelianGroup.of t)
      have hc : boundary I (n + 1)
          (cone I a (n + 1) (boundary I (n + 1) (FreeAbelianGroup.of t))) =
          boundary I (n + 1) (FreeAbelianGroup.of t) -
            cone I a n (boundary I n (boundary I (n + 1) (FreeAbelianGroup.of t))) := by
        simp only [boundary_of I (n + 1) t, map_sum, map_zsmul, ← Finset.sum_sub_distrib,
          ← zsmul_sub]
        apply Finset.sum_congr rfl
        intro i _
        have hface (k : Fin (n + 1)) : a < (face t i).val k := ht (i.succAbove k)
        rw [cone_of_insert I a _ hface, boundary_cone_insert I a _ hface]
      change boundary I (n + 1) (boundary I (n + 2) (FreeAbelianGroup.of s)) = 0
      rw [hdecomp, map_sub, hc, hz, map_zero, sub_zero, sub_self]

/-- The augmented ordered simplex is exact whenever it has a least vertex. -/
theorem boundary_exact (a : I) (ha : ∀ b : I, a ≤ b) (n : ℕ) :
    Function.Exact (boundary I (n + 1)) (boundary I n) := by
  intro x
  constructor
  · intro hx
    exact ⟨cone I a (n + 1) x, by simpa [hx] using contraction I a ha n x⟩
  · rintro ⟨y, rfl⟩
    exact DFunLike.congr_fun (boundary_squared I n) y

/-- Exactness at the non-augmented terms also covers the empty ordered set. -/
theorem boundary_exact_of_finite [Finite I] (n : ℕ) :
    Function.Exact (boundary I (n + 1)) (boundary I n) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl h =>
      let : IsEmpty (Tuple I (n + 1)) := ⟨fun s => h.false (s.val 0)⟩
      intro x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp only [map_zero, eq_self, true_iff]
      exact ⟨0, map_zero _⟩
  | inr h =>
      let : Fintype I := Fintype.ofFinite I
      let a := Finset.univ.min' (Finset.univ_nonempty (α := I))
      exact boundary_exact I a (fun b => Finset.min'_le _ _ (Finset.mem_univ b)) n

variable {I} {J : Type*} [LinearOrder J]

/-- A strictly increasing map sends an oriented simplex to an oriented simplex. -/
def tupleMap {f : I → J} (hf : StrictMono f) {n : ℕ} (s : Tuple I n) : Tuple J n :=
  ⟨f ∘ s.val, hf.comp s.property⟩

/-- The induced map on augmented chains. -/
def chainMap {f : I → J} (hf : StrictMono f) (n : ℕ) : Chains I n →+ Chains J n :=
  FreeAbelianGroup.lift (fun s => FreeAbelianGroup.of (tupleMap hf s))

@[simp] theorem chainMap_of {f : I → J} (hf : StrictMono f) (n : ℕ) (s : Tuple I n) :
    chainMap hf n (FreeAbelianGroup.of s) = FreeAbelianGroup.of (tupleMap hf s) :=
  FreeAbelianGroup.lift_apply_of _ _

theorem chainMap_id (n : ℕ) : chainMap (strictMono_id : StrictMono (@id I)) n = AddMonoidHom.id _ := by
  apply FreeAbelianGroup.lift_ext
  intro s
  rw [chainMap_of]
  rfl

theorem chainMap_comp {K : Type*} [LinearOrder K] {f : I → J} {g : J → K}
    (hf : StrictMono f) (hg : StrictMono g) (n : ℕ) :
    chainMap (hg.comp hf) n = (chainMap hg n).comp (chainMap hf n) := by
  apply FreeAbelianGroup.lift_ext
  intro s
  rw [chainMap_of, AddMonoidHom.comp_apply, chainMap_of, chainMap_of]
  rfl

theorem boundary_naturality {f : I → J} (hf : StrictMono f) (n : ℕ) :
    (boundary J n).comp (chainMap hf (n + 1)) = (chainMap hf n).comp (boundary I n) := by
  apply FreeAbelianGroup.lift_ext
  intro s
  simp only [AddMonoidHom.comp_apply, chainMap_of, boundary_of, map_sum, map_zsmul]
  rfl

end PhilipponOrderedSimplex

end

section

open CategoryTheory CategoryTheory.Limits

namespace PhilipponCech

universe v

/-- Exactness of a short complex of presheaves of abelian groups can be
checked objectwise. -/
theorem exact_of_evaluation {D : Type*} [Category* D]
    (S : ShortComplex (D ⥤ AddCommGrpCat.{v}))
    (h : ∀ W : D, (S.map ((evaluation D AddCommGrpCat.{v}).obj W)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  apply Functor.isZero
  intro W
  let G := (evaluation D AddCommGrpCat.{v}).obj W
  exact IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology _).mp (h W))
    ((ShortComplex.homologyFunctorIso G).app S).symm

end PhilipponCech

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponOrderedSimplex


namespace PhilipponOrderedEtale

universe u
variable {X : Scheme.{u}} (U : X.OrderedAffineCover)

/-- The vertices on which the structural morphism of a test object factors. -/
abbrev Eligible (W : X.Etale) := { i : U.ι // ∀ x : W.left, W.hom x ∈ U.U i }

private def eligibleMap {W V : X.Etale} (f : W ⟶ V) : Eligible U V → Eligible U W :=
  fun i => ⟨i.val, fun x => by
    rw [← MorphismProperty.Over.w f]
    exact i.property (f.left x)⟩

private theorem eligibleMap_strictMono {W V : X.Etale} (f : W ⟶ V) :
    StrictMono (eligibleMap U f) := fun _ _ h => h

/- The presheaf of simplex generators of the ordered cover. Degree zero is the
augmentation, represented by the empty tuple. -/
def tuplePresheaf (n : ℕ) : X.Etaleᵒᵖ ⥤ Type u where
  obj W := Tuple (Eligible U W.unop) n
  map f := TypeCat.ofHom (tupleMap (eligibleMap_strictMono U f.unop))
  map_id W := by
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro s
    rfl

abbrev presheafTerm (n : ℕ) : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u} :=
  tuplePresheaf U n ⋙ AddCommGrpCat.free

/-- The alternating boundary on the ordered cover, as a presheaf morphism. -/
def presheafD (n : ℕ) : presheafTerm U (n + 1) ⟶ presheafTerm U n where
  app W := AddCommGrpCat.ofHom (boundary (Eligible U W.unop) n)
  naturality W V f := by
    exact congrArg AddCommGrpCat.ofHom (boundary_naturality (eligibleMap_strictMono U f.unop) n)

theorem presheafD_squared (n : ℕ) : presheafD U (n + 1) ≫ presheafD U n = 0 := by
  apply NatTrans.ext
  funext W
  exact congrArg AddCommGrpCat.ofHom (boundary_squared (Eligible U W.unop) n)

/-- The augmented ordered complex is exact at all simplex terms as a
presheaf complex. The proof also covers test objects landing in no chart. -/
theorem presheaf_exact (n : ℕ) :
    (ShortComplex.mk (presheafD U (n + 1)) (presheafD U n) (presheafD_squared U n)).Exact := by
  apply PhilipponCech.exact_of_evaluation
  intro W
  rw [ShortComplex.ab_exact_iff_function_exact]
  exact boundary_exact_of_finite (Eligible U W.unop) n

abbrev sheafTerm (n : ℕ) : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (presheafTerm U n)

abbrev sheafD (n : ℕ) : sheafTerm U (n + 1) ⟶ sheafTerm U n :=
  (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map (presheafD U n)

theorem sheafD_squared (n : ℕ) : sheafD U (n + 1) ≫ sheafD U n = 0 := by
  simp only [sheafD, ← Functor.map_comp, presheafD_squared, Functor.map_zero]

/-- The actual ordered Čech complex of free abelian sheaves is exact at
every simplex term by exactness of sheafification. -/
theorem sheaf_exact (n : ℕ) :
    (ShortComplex.mk (sheafD U (n + 1)) (sheafD U n) (sheafD_squared U n)).Exact :=
  (presheaf_exact U n).map (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u})

/-- View an open subscheme as an object of the small étale site. -/
abbrev openObject (V : X.Opens) : X.Etale := Scheme.Etale.mk V.ι

/-- The summand of the ordered complex attached to an intersection. -/
abbrev chart {n : ℕ} (s : U.Idx n) : X.Etale := openObject (U.inter s)

/-- An ordered face induces the inclusion of the intersections. -/
def chartFace {n : ℕ} (s : U.Idx (n + 1)) (i : Fin (n + 2)) :
    chart U s ⟶ chart U (U.face s i) :=
  MorphismProperty.Over.homMk (X.homOfLE (U.inter_le_inter_face s i))
    (X.homOfLE_ι (U.inter_le_inter_face s i)) trivial

private theorem mem_open_of_arrow {W : X.Etale} {V : X.Opens} (f : W ⟶ openObject V)
    (x : W.left) : W.hom x ∈ V := by
  have h : (f.left ≫ V.ι) x = W.hom x :=
    congrArg (fun g : W.left ⟶ X => g x) (MorphismProperty.Over.w f)
  rw [← h]
  exact (f.left x).property

private def factorThroughOpen {W : X.Etale} {V : X.Opens}
    (h : ∀ x : W.left, W.hom x ∈ V) : W ⟶ openObject V := by
  have hi : Set.range W.hom ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact h x
  exact MorphismProperty.Over.homMk (IsOpenImmersion.lift V.ι W.hom hi)
    (IsOpenImmersion.lift_fac V.ι W.hom hi) trivial

private theorem openHom_ext {W : X.Etale} {V : X.Opens} (f g : W ⟶ openObject V) : f = g := by
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono V.ι).mp
  exact (MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm

private def tupleOfChartMap {W : X.Etale} {n : ℕ} (s : U.Idx n) (f : W ⟶ chart U s) :
    Tuple (Eligible U W) (n + 1) :=
  ⟨fun i => ⟨s.val i, fun x => U.inter_le s i (mem_open_of_arrow f x)⟩, s.property⟩

private def chartMapsEquiv (n : ℕ) (W : X.Etale) :
    (Σ s : U.Idx n, W ⟶ chart U s) ≃ Tuple (Eligible U W) (n + 1) := by
  refine Equiv.ofBijective (fun a => tupleOfChartMap U a.1 a.2) ⟨?_, ?_⟩
  · rintro ⟨s, f⟩ ⟨t, g⟩ h
    have hst : s = t := Subtype.ext (funext fun i =>
      congrArg (fun z : Tuple (Eligible U W) (n + 1) => (z.val i).val) h)
    subst t
    rw [openHom_ext f g]
  · intro t
    let s : U.Idx n := ⟨fun i => (t.val i).val, t.property⟩
    have hs (x : W.left) : W.hom x ∈ U.inter s := by
      change W.hom x ∈ (↑(⨅ i, U.U (s.val i)) : Set X)
      rw [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
      exact fun i => (t.val i).property x
    exact ⟨⟨s, factorThroughOpen hs⟩, Subtype.ext (funext fun _ => Subtype.ext rfl)⟩

private def tupleInclusion {n : ℕ} (s : U.Idx n) :
    yoneda.obj (chart U s) ⟶ tuplePresheaf U (n + 1) where
  app W := TypeCat.ofHom (tupleOfChartMap U s (W := W.unop))
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro f
    rfl

private def tupleCofanIsColimit (n : ℕ) :
    IsColimit (Cofan.mk (tuplePresheaf U (n + 1)) (tupleInclusion U (n := n))) := by
  apply evaluationJointlyReflectsColimits
  intro W
  let G := (evaluation X.Etaleᵒᵖ (Type u)).obj W
  refine (isColimitMapCoconeCofanMkEquiv G _ _).symm ?_
  let c : Cofan (fun s : U.Idx n => W.unop ⟶ chart U s) :=
    Cofan.mk (Tuple (Eligible U W.unop) (n + 1))
      (fun s => TypeCat.ofHom (tupleOfChartMap U s))
  have h : Function.Bijective c.cofanTypes.fromSigma :=
    (chartMapsEquiv U n W.unop).bijective
  exact ((Cofan.nonempty_isColimit_iff_bijective_fromSigma c).2 h).some

private abbrev freePresheafFunctor : (X.Etaleᵒᵖ ⥤ Type u) ⥤ (X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (Functor.whiskeringRight X.Etaleᵒᵖ (Type u) AddCommGrpCat.{u}).obj AddCommGrpCat.free

private abbrev freeSheafFunctor : (X.Etaleᵒᵖ ⥤ Type u) ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  freePresheafFunctor (X := X) ⋙
    presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}

private abbrev presheafInclusion {n : ℕ} (s : U.Idx n) :=
  (freePresheafFunctor (X := X)).map (tupleInclusion U s)

/-- The inclusion of a represented summand in the ordered complex of sheaves. -/
def sheafInclusion {n : ℕ} (s : U.Idx n) :
    (PhilipponSheafCohomology.freeOn X.smallEtaleTopology).obj (chart U s) ⟶ sheafTerm U (n + 1) :=
  (freeSheafFunctor (X := X)).map (tupleInclusion U s)

/-- Each ordered Čech term is the coproduct of the free abelian sheaves on
its ordered intersections. -/
def sheafCofanIsColimit (n : ℕ) :
    IsColimit (Cofan.mk (sheafTerm U (n + 1)) (sheafInclusion U (n := n))) := by
  let H := (Functor.whiskeringRight X.Etaleᵒᵖ (Type u) AddCommGrpCat.{u}).obj AddCommGrpCat.free
  let : H.IsLeftAdjoint := ⟨_, ⟨AddCommGrpCat.adj.whiskerRight X.Etaleᵒᵖ⟩⟩
  let G := presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}
  exact isColimitCofanMkObjOfIsColimit (H ⋙ G) _ _ (tupleCofanIsColimit U n)

private theorem presheafInclusion_boundary {n : ℕ} (s : U.Idx (n + 1)) :
    presheafInclusion U s ≫ presheafD U (n + 1) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        ((freePresheafFunctor (X := X)).map (yoneda.map (chartFace U s i)) ≫
          presheafInclusion U (U.face s i)) := by
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro f
  let eval := AddCommGrpCat.homAddEquiv.toAddMonoidHom.comp
    (NatTrans.appHom (F := (freePresheafFunctor (X := X)).obj (yoneda.obj (chart U s)))
      (G := presheafTerm U (n + 1)) W)
  change eval (presheafInclusion U s ≫ presheafD U (n + 1)) (FreeAbelianGroup.of f) =
    eval (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
      ((freePresheafFunctor (X := X)).map (yoneda.map (chartFace U s i)) ≫
        presheafInclusion U (U.face s i))) (FreeAbelianGroup.of f)
  rw [map_sum]
  simp only [AddMonoidHom.finsetSum_apply, map_zsmul, AddMonoidHom.zsmul_apply]
  change boundary (Eligible U W.unop) (n + 1)
    (FreeAbelianGroup.map (tupleOfChartMap U s) (FreeAbelianGroup.of f)) = _
  rw [FreeAbelianGroup.map_of_apply, boundary_of]
  apply Finset.sum_congr rfl
  intro i _
  congr 1

/-- On each summand the sheaf boundary is the alternating sum of the
specified inclusions into ordered faces. -/
theorem sheafInclusion_boundary {n : ℕ} (s : U.Idx (n + 1)) :
    sheafInclusion U s ≫ sheafD U (n + 1) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        ((PhilipponSheafCohomology.freeOn X.smallEtaleTopology).map (chartFace U s i) ≫
          sheafInclusion U (U.face s i)) := by
  let G := presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}
  change G.map (presheafInclusion U s) ≫ G.map (presheafD U (n + 1)) = _
  rw [← G.map_comp, presheafInclusion_boundary, G.map_sum]
  simp only [Functor.map_zsmul, Functor.map_comp]
  rfl

/-- The identity of the base scheme as a terminal étale object. -/
abbrev terminalObject (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)

def terminalWitness (X : Scheme.{u}) : IsTerminal (terminalObject X) :=
  IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal

private def emptyTupleIso : tuplePresheaf U 0 ≅ yoneda.obj (terminalObject X) :=
  NatIso.ofComponents (fun W =>
    { hom := TypeCat.ofHom (fun _ => (terminalWitness X).from W.unop)
      inv := TypeCat.ofHom (fun _ => ⟨Fin.elim0, fun i => i.elim0⟩)
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro s
        exact Subtype.ext (funext fun i => i.elim0)
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro f
        exact (terminalWitness X).hom_ext _ _ }) (by
    intro W V f
    apply ConcreteCategory.hom_ext
    intro s
    exact (terminalWitness X).hom_ext _ _)

/-- The degree zero chain object is the free abelian sheaf on the terminal object. -/
def augmentationIso : sheafTerm U 0 ≅
    (PhilipponSheafCohomology.freeOn X.smallEtaleTopology).obj (terminalObject X) :=
  (freeSheafFunctor (X := X)).mapIso (emptyTupleIso U)

private theorem presheafInclusion_augmentation (s : U.Idx 0) :
    presheafInclusion U s ≫ presheafD U 0 ≫ (freePresheafFunctor (X := X)).map (emptyTupleIso U).hom =
      (freePresheafFunctor (X := X)).map (yoneda.map ((terminalWitness X).from (chart U s))) := by
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro f
  change FreeAbelianGroup.map (fun _ => (terminalWitness X).from W.unop)
    (boundary (Eligible U W.unop) 0
      (FreeAbelianGroup.map (tupleOfChartMap U s) (FreeAbelianGroup.of f))) =
    FreeAbelianGroup.map (fun a => a ≫ (terminalWitness X).from (chart U s)) (FreeAbelianGroup.of f)
  have hd : boundary (Eligible U W.unop) 0 (FreeAbelianGroup.of (tupleOfChartMap U s f)) =
      FreeAbelianGroup.of (face (tupleOfChartMap U s f) 0) := by
    rw [boundary_of]
    change (∑ i : Fin 1, ((-1 : ℤ) ^ (i : ℕ)) •
      FreeAbelianGroup.of (face (tupleOfChartMap U s f) i)) = _
    rw [Fin.sum_univ_one]
    simp
  rw [FreeAbelianGroup.map_of_apply, hd, FreeAbelianGroup.map_of_apply,
    FreeAbelianGroup.map_of_apply]
  rw [(terminalWitness X).hom_ext (f ≫ (terminalWitness X).from (chart U s))
    ((terminalWitness X).from W.unop)]

theorem sheafInclusion_augmentation (s : U.Idx 0) :
    sheafInclusion U s ≫ sheafD U 0 ≫ (augmentationIso U).hom =
      (PhilipponSheafCohomology.freeOn X.smallEtaleTopology).map ((terminalWitness X).from (chart U s)) := by
  let G := presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}
  change G.map (presheafInclusion U s) ≫ G.map (presheafD U 0) ≫
    G.map ((freePresheafFunctor (X := X)).map (emptyTupleIso U).hom) = _
  rw [← G.map_comp, ← G.map_comp, presheafInclusion_augmentation]
  rfl

private theorem vertices_cover : Sieve.ofArrows (fun s : U.Idx 0 => chart U s)
    (fun s => (terminalWitness X).from (chart U s)) ∈ X.smallEtaleTopology (terminalObject X) := by
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
  apply Set.eq_univ_of_forall
  intro x
  change X at x
  have hx : x ∈ ⨆ i, U.U i := by rw [U.iSup_eq_top]; trivial
  rw [TopologicalSpace.Opens.mem_iSup] at hx
  obtain ⟨i, hi⟩ := hx
  let s : U.Idx 0 := ⟨fun _ => i, fun a b hab => by
    have he : a = b := (Fin.fin_one_eq_zero a).trans (Fin.fin_one_eq_zero b).symm
    subst b
    exact (lt_irrefl _ hab).elim⟩
  have hs : x ∈ U.inter s := by
    change x ∈ (↑(⨅ j, U.U (s.val j)) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    exact fun _ => hi
  have hleft : ((terminalWitness X).from (chart U s)).left = (U.inter s).ι := by
    have hh := MorphismProperty.Over.w ((terminalWitness X).from (chart U s))
    change ((terminalWitness X).from (chart U s)).left ≫ 𝟙 X = (U.inter s).ι at hh
    exact (Category.comp_id _).symm.trans hh
  apply Set.mem_iUnion.mpr
  refine ⟨s, ?_⟩
  rw [hleft]
  exact ⟨⟨x, hs⟩, rfl⟩

/-- The augmentation is epimorphic because the original opens cover. -/
theorem augmentation_epi : Epi (sheafD U 0) := by
  have h : Epi (sheafD U 0 ≫ (augmentationIso U).hom) := by
    constructor
    intro F a b hab
    let J := X.smallEtaleTopology
    let T := terminalObject X
    apply (PhilipponSheafCohomology.representedSections J F T).injective
    have hs := Presheaf.isSheaf_comp_of_isSheaf J F.obj (forget AddCommGrpCat) F.property
    have hs' := (Presieve.isSheafFor_iff_generate (Presieve.ofArrows (fun s : U.Idx 0 => chart U s)
      (fun s => (terminalWitness X).from (chart U s)))).mpr
      ((isSheaf_iff_isSheaf_of_type _ _).mp hs _ (vertices_cover U))
    apply hs'.isSeparatedFor.ext
    rintro _ _ ⟨s⟩
    change F.obj.map ((terminalWitness X).from (chart U s)).op
      (PhilipponSheafCohomology.representedSections J F T a) =
      F.obj.map ((terminalWitness X).from (chart U s)).op
        (PhilipponSheafCohomology.representedSections J F T b)
    rw [← PhilipponSheafCohomology.representedSections_restrict,
      ← PhilipponSheafCohomology.representedSections_restrict]
    apply congrArg (PhilipponSheafCohomology.representedSections J F (chart U s))
    simpa only [← sheafInclusion_augmentation U s, Category.assoc] using
      congrArg (sheafInclusion U s ≫ ·) hab
  have he := epi_comp (sheafD U 0 ≫ (augmentationIso U).hom) (augmentationIso U).inv
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id] at he
  exact he

/-- The short exact sequences of cycles of the ordered étale Čech resolution. -/
def resolution : PhilipponCech.Resolution (C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) := by
  let : Epi (sheafD U 0) := augmentation_epi U
  exact PhilipponCech.Resolution.ofExact (sheafD U) (sheafD_squared U) (sheaf_exact U)

end PhilipponOrderedEtale

end

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

private instance : ((along f).op.lan : (Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
    X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}).PreservesMonomorphisms :=
  lan_preservesMonomorphisms (along f).op (along_op_shape f)

/-- Restriction of abelian étale sheaves to the open subscheme. -/
abbrev restrict : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  (along f).sheafPushforwardContinuous AddCommGrpCat Y.smallEtaleTopology X.smallEtaleTopology

/-- Restriction to an open subscheme preserves injective abelian sheaves. -/
instance restrict_preservesInjectiveObjects : (restrict f).PreservesInjectiveObjects := by
  let L := Functor.sheafPullbackConstruction.sheafPullback (along f) AddCommGrpCat
    Y.smallEtaleTopology X.smallEtaleTopology
  have : L.PreservesMonomorphisms := by
    unfold L Functor.sheafPullbackConstruction.sheafPullback
    infer_instance
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (along f) AddCommGrpCat
      Y.smallEtaleTopology X.smallEtaleTopology)

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

private theorem comparison_mk₀ {M : C} (x : Q ⟶ M) :
    comparison R p M 0 (Ext.mk₀ x) = Ext.mk₀ (p ≫ R.map x) := by
  change (Ext.mk₀ p).comp ((Ext.mk₀ x).mapExactFunctor R) (zero_add 0) = _
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

private theorem comparison_boundary {S : ShortComplex C} (hS : S.ShortExact)
    (n : ℕ) (x : Ext Q S.X₃ n) :
    comparison R p S.X₁ (n + 1) (x.comp hS.extClass rfl) =
      (comparison R p S.X₃ n x).comp (hS.map_of_exact R).extClass rfl := by
  rw [comparison_comp, Ext.mapExactFunctor_extClass]

private theorem comparison_post {M N : C} (a : M ⟶ N) (n : ℕ) (x : Ext Q M n) :
    comparison R p N n (x.comp (Ext.mk₀ a) (add_zero n)) =
      (comparison R p M n x).comp (Ext.mk₀ (R.map a)) (add_zero n) := by
  rw [comparison_comp, Ext.mapExactFunctor_mk₀]

/-- A Hom comparison extends to all Ext degrees when the exact functor
also preserves injectives. -/
theorem comparison_bijective [EnoughInjectives C] [R.PreservesInjectiveObjects]
    (h : ∀ M : C, Function.Bijective (fun a : Q ⟶ M => p ≫ R.map a))
    (n : ℕ) (M : C) : Function.Bijective (comparison R p M n) := by
  induction n generalizing M with
  | zero =>
      have hz : (comparison R p M 0 : Ext Q M 0 → Ext P (R.obj M) 0) =
          fun x => Ext.mk₀ (p ≫ R.map (Ext.addEquiv₀ x)) := by
        funext x
        obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective Q M).surjective x
        rw [show Ext.addEquiv₀ (Ext.mk₀ a) = a from Ext.addEquiv₀.apply_symm_apply a]
        exact comparison_mk₀ R p a
      rw [hz]
      exact (Ext.mk₀_bijective _ _).comp ((h M).comp Ext.addEquiv₀.bijective)
  | succ n ih =>
      let S := ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M))
        (cokernel.condition (Injective.ι M))
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι M) }
      have hSR := hS.map_of_exact R
      have : Injective S.X₂ := inferInstanceAs (Injective (Injective.under M))
      have : Injective (S.map R).X₂ := R.injective_obj_of_injective ‹Injective S.X₂›
      constructor
      · apply (AddMonoidHom.ker_eq_bot_iff _).mp
        rw [AddSubgroup.eq_bot_iff_forall]
        intro x hx
        have hx' : comparison R p S.X₁ (n + 1) x = 0 := hx
        obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ Q hS x
          (Ext.eq_zero_of_injective _) (n₀ := n) rfl
        have hzero : (comparison R p S.X₃ n y).comp hSR.extClass rfl = 0 := by
          rw [← comparison_boundary R p hS n y, hy]
          exact hx'
        obtain ⟨z', hz'⟩ := Ext.covariant_sequence_exact₃ P hSR _ rfl hzero
        obtain ⟨z, hz⟩ := (ih S.X₂).surjective z'
        have hyz : z.comp (Ext.mk₀ S.g) (add_zero n) = y := (ih S.X₃).injective (by
          rw [comparison_post, hz]
          exact hz')
        rw [← hy, ← hyz, Ext.comp_assoc_of_second_deg_zero,
          ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]
      · intro x'
        obtain ⟨y', hy'⟩ := Ext.covariant_sequence_exact₁ P hSR x'
          (Ext.eq_zero_of_injective _) (n₀ := n) rfl
        obtain ⟨y, hy⟩ := (ih S.X₃).surjective y'
        refine ⟨y.comp hS.extClass rfl, ?_⟩
        rw [comparison_boundary R p hS, hy]
        exact hy'

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

/-- Pullback of the global-functions sheaf to an open subscheme gives its
global-functions sheaf on the small étale site. -/
def restrictAdditiveIso : (restrict f).obj (SmallEtaleAdditive.sheaf X) ≅ SmallEtaleAdditive.sheaf Y :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B a
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl))

/-- The additive cohomology at an open object matches that on the open scheme. -/
def additiveOpenComparison (q : ℕ) :
    (SmallEtaleAdditive.sheaf X).H' q (V f) ≃+ (SmallEtaleAdditive.sheaf Y).H q :=
  (openComparison f (SmallEtaleAdditive.sheaf X) q).trans
    ((Sheaf.functorH Y.smallEtaleTopology q).mapIso (restrictAdditiveIso f)).addCommGroupIsoToAddEquiv

end PhilipponEtaleOpenCohomology

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits


namespace PhilipponCech

universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {S : ShortComplex C} (hS : S.ShortExact)

/-- When the two adjacent Ext groups of the middle object vanish, the
connecting map is an additive equivalence. -/
def connectingEquiv (F : C) (q : ℕ)
    [Subsingleton (Ext S.X₂ F q)] [Subsingleton (Ext S.X₂ F (q + 1))] :
    Ext S.X₁ F q ≃+ Ext S.X₃ F (q + 1) := by
  let hq : 1 + q = q + 1 := Nat.add_comm 1 q
  let δ := hS.extClass.precomp F hq
  refine AddEquiv.ofBijective δ ⟨?_, ?_⟩
  · apply (AddMonoidHom.ker_eq_bot_iff δ).mp
    rw [AddSubgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁ hS F x hq hx
    have : y = 0 := Subsingleton.elim _ _
    rw [this, Ext.comp_zero] at hy
    exact hy.symm
  · intro x
    have hx : (Ext.mk₀ S.g).comp x (zero_add (q + 1)) = 0 := Subsingleton.elim _ _
    exact Ext.contravariant_sequence_exact₃ hS F x hx hq

/-- The connecting equivalence commutes with maps on the coefficients. -/
theorem connectingEquiv_natural {F G : C} (f : F ⟶ G) (q : ℕ)
    [Subsingleton (Ext S.X₂ F q)] [Subsingleton (Ext S.X₂ F (q + 1))]
    [Subsingleton (Ext S.X₂ G q)] [Subsingleton (Ext S.X₂ G (q + 1))]
    (x : Ext S.X₁ F q) :
    connectingEquiv hS G q (x.comp (Ext.mk₀ f) (add_zero q)) =
      (connectingEquiv hS F q x).comp (Ext.mk₀ f) (add_zero (q + 1)) :=
  (Ext.comp_assoc_of_third_deg_zero hS.extClass x (Ext.mk₀ f) (Nat.add_comm 1 q)).symm

/-- The boundary from homomorphisms in the contravariant Ext sequence. -/
def homBoundary (F : C) : (S.X₁ ⟶ F) →+ Ext S.X₃ F 1 :=
  (hS.extClass.precomp F (rfl : 1 + 0 = 1)).comp Ext.addEquiv₀.symm.toAddMonoidHom

theorem homBoundary_exact (F : C) :
    Function.Exact (fun y : S.X₂ ⟶ F => S.f ≫ y) (homBoundary hS F) := by
  intro x
  constructor
  · intro hx
    change hS.extClass.comp (Ext.mk₀ x) (rfl : 1 + 0 = 1) = 0 at hx
    obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁ hS F (Ext.mk₀ x) rfl hx
    refine ⟨Ext.addEquiv₀ y, (Ext.mk₀_bijective _ _).injective ?_⟩
    rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]
    exact hy
  · rintro ⟨y, rfl⟩
    change hS.extClass.comp (Ext.mk₀ (S.f ≫ y)) (rfl : 1 + 0 = 1) = 0
    rw [← Ext.mk₀_comp_mk₀]
    exact hS.extClass_comp_assoc (Ext.mk₀ y)

theorem homBoundary_surjective (F : C) [Subsingleton (Ext S.X₂ F 1)] :
    Function.Surjective (homBoundary hS F) := by
  intro x
  have hx : (Ext.mk₀ S.g).comp x (zero_add 1) = 0 := Subsingleton.elim _ _
  obtain ⟨a, ha⟩ := Ext.contravariant_sequence_exact₃ hS F x hx (rfl : 1 + 0 = 1)
  refine ⟨Ext.addEquiv₀ a, ?_⟩
  change hS.extClass.comp (Ext.mk₀ (Ext.addEquiv₀ a)) (rfl : 1 + 0 = 1) = x
  rwa [Ext.mk₀_addEquiv₀_apply]

theorem homBoundary_natural {F G : C} (f : F ⟶ G) (x : S.X₁ ⟶ F) :
    homBoundary hS G (x ≫ f) = (homBoundary hS F x).comp (Ext.mk₀ f) (add_zero 1) := by
  change hS.extClass.comp (Ext.mk₀ (x ≫ f)) (rfl : 1 + 0 = 1) =
    (hS.extClass.comp (Ext.mk₀ x) (rfl : 1 + 0 = 1)).comp (Ext.mk₀ f) (add_zero 1)
  rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_third_deg_zero]

namespace Resolution

variable (R : Resolution (C := C))

/-- The section differential as a morphism of abelian groups. -/
def cochainHom (F : C) (n : ℕ) : (R.terms n ⟶ F) →+ (R.terms (n + 1) ⟶ F) where
  toFun := R.cochain F n
  map_zero' := by simp [cochain]
  map_add' x y := by simp [cochain, Preadditive.comp_add]

/-- A homomorphism from a cycle object pulls back to a cocycle. -/
def homToCocycle (F : C) (n : ℕ) :
    (R.cycles n ⟶ F) →+ (R.cochainHom F n).ker where
  toFun x := ⟨R.projection n ≫ x, by
    change R.cochain F n (R.projection n ≫ x) = 0
    unfold cochain
    rw [← Category.assoc (R.inclusion n), R.zero, zero_comp, comp_zero]⟩
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp only [AddSubgroup.coe_add, Preadditive.comp_add])

/-- A cocycle factors uniquely through the cycle object. -/
def homCocycleEquiv (F : C) (n : ℕ) :
    (R.cycles n ⟶ F) ≃+ (R.cochainHom F n).ker := by
  have : Epi (R.projection n) := (R.shortExact n).epi_g
  have : Epi (R.projection (n + 1)) := (R.shortExact (n + 1)).epi_g
  refine AddEquiv.ofBijective (R.homToCocycle F n) ⟨?_, ?_⟩
  · intro a b h
    exact (cancel_epi (R.projection n)).mp (congrArg Subtype.val h)
  · intro a
    have ha : R.inclusion n ≫ a.val = 0 := by
      apply (cancel_epi (R.projection (n + 1))).mp
      rw [comp_zero]
      exact a.property
    let T := CokernelCofork.ofπ a.val ha
    let hC := (R.shortExact n).gIsCokernel
    exact ⟨hC.desc T, Subtype.ext (hC.fac T WalkingParallelPair.one)⟩

omit [HasExt C] in
private theorem homCocycleEquiv_inclusion (F : C) (n : ℕ) (x : R.terms n ⟶ F) :
    (R.homCocycleEquiv F (n + 1) (R.inclusion n ≫ x)).val = R.cochain F n x := rfl

/-- The map from positive-degree cocycles to degree-one Ext on the
preceding cycle object. Its kernel consists of the coboundaries. -/
def cocycleBoundary (F : C) (n : ℕ) : (R.cochainHom F (n + 1)).ker →+ Ext (R.cycles n) F 1 :=
  (homBoundary (R.shortExact n) F).comp (R.homCocycleEquiv F (n + 1)).symm.toAddMonoidHom

theorem cocycleBoundary_eq_zero_iff (F : C) (n : ℕ)
    (x : (R.cochainHom F (n + 1)).ker) : R.cocycleBoundary F n x = 0 ↔
      ∃ y : R.terms n ⟶ F, R.cochain F n y = x.val := by
  let e := R.homCocycleEquiv F (n + 1)
  change homBoundary (R.shortExact n) F (e.symm x) = 0 ↔ _
  rw [homBoundary_exact (R.shortExact n) F (e.symm x)]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    have hy' : R.inclusion n ≫ y = e.symm x := hy
    rw [← R.homCocycleEquiv_inclusion F, hy']
    exact congrArg Subtype.val (e.apply_symm_apply x)
  · rintro ⟨y, hy⟩
    refine ⟨y, e.injective ?_⟩
    rw [AddEquiv.apply_symm_apply]
    exact Subtype.ext hy

theorem cocycleBoundary_surjective (F : C) (n : ℕ) [Subsingleton (Ext (R.terms n) F 1)] :
    Function.Surjective (R.cocycleBoundary F n) :=
  (homBoundary_surjective (R.shortExact n) F).comp (R.homCocycleEquiv F (n + 1)).symm.surjective

/-- A coefficient morphism takes a cocycle to a cocycle by postcomposition. -/
def cocyclePost {F G : C} (f : F ⟶ G) (n : ℕ) (x : (R.cochainHom F n).ker) :
    (R.cochainHom G n).ker := ⟨x.val ≫ f, by
  change R.cochain G n (x.val ≫ f) = 0
  have hx : R.cochain F n x.val = 0 := x.property
  rw [show R.cochain G n (x.val ≫ f) = R.cochain F n x.val ≫ f by
    simp only [cochain, Category.assoc], hx, zero_comp]⟩

private theorem homCocycleEquiv_symm_post {F G : C} (f : F ⟶ G) (n : ℕ)
    (x : (R.cochainHom F n).ker) :
    (R.homCocycleEquiv G n).symm (R.cocyclePost f n x) =
      (R.homCocycleEquiv F n).symm x ≫ f := by
  apply (R.homCocycleEquiv G n).injective
  rw [AddEquiv.apply_symm_apply]
  apply Subtype.ext
  change x.val ≫ f = R.projection n ≫ (R.homCocycleEquiv F n).symm x ≫ f
  rw [← Category.assoc]
  exact congrArg (· ≫ f) (congrArg Subtype.val ((R.homCocycleEquiv F n).apply_symm_apply x)).symm

/-- The map from cocycles to degree-one Ext is natural in the coefficients. -/
theorem cocycleBoundary_natural {F G : C} (f : F ⟶ G) (n : ℕ)
    (x : (R.cochainHom F (n + 1)).ker) :
    R.cocycleBoundary G n (R.cocyclePost f (n + 1) x) =
      (R.cocycleBoundary F n x).comp (Ext.mk₀ f) (add_zero 1) := by
  change homBoundary (R.shortExact n) G
    ((R.homCocycleEquiv G (n + 1)).symm (R.cocyclePost f (n + 1) x)) = _
  rw [R.homCocycleEquiv_symm_post, homBoundary_natural]
  rfl

private def reindexExt (F : C) {i j : ℕ} (h : i = j) :
    Ext (R.cycles i) F 1 ≃+ Ext (R.cycles j) F 1 := by
  subst j
  exact AddEquiv.refl _

private theorem reindexExt_natural {F G : C} (f : F ⟶ G) {i j : ℕ} (h : i = j)
    (x : Ext (R.cycles i) F 1) :
    R.reindexExt G h (x.comp (Ext.mk₀ f) (add_zero 1)) =
      (R.reindexExt F h x).comp (Ext.mk₀ f) (add_zero 1) := by
  subst j
  rfl

/-- Positive-degree cohomology is transported to an Ext group of degree one
by cutting a resolution whose terms are acyclic for the coefficients. -/
def degreeOneEquiv (F : C) (h : ∀ j q, Subsingleton (Ext (R.terms j) F (q + 1))) :
    ∀ n j : ℕ, Ext (R.cycles (j + n)) F 1 ≃+ Ext (R.cycles j) F (n + 1)
  | 0, _ => AddEquiv.refl _
  | n + 1, j => by
      let : Subsingleton (Ext (R.terms j) F (n + 1)) := h j n
      let : Subsingleton (Ext (R.terms j) F (n + 1 + 1)) := h j (n + 1)
      exact (R.reindexExt F (show j + (n + 1) = (j + 1) + n by omega)).trans
        ((degreeOneEquiv F h n (j + 1)).trans (connectingEquiv (R.shortExact j) F (n + 1)))

/-- The iterated connecting equivalence is natural in the coefficient object. -/
theorem degreeOneEquiv_natural {F G : C} (f : F ⟶ G)
    (hF : ∀ j q, Subsingleton (Ext (R.terms j) F (q + 1)))
    (hG : ∀ j q, Subsingleton (Ext (R.terms j) G (q + 1))) (n j : ℕ)
    (x : Ext (R.cycles (j + n)) F 1) :
    R.degreeOneEquiv G hG n j (x.comp (Ext.mk₀ f) (add_zero 1)) =
      (R.degreeOneEquiv F hF n j x).comp (Ext.mk₀ f) (add_zero (n + 1)) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
      simp only [degreeOneEquiv, AddEquiv.trans_apply]
      rw [reindexExt_natural, ih, connectingEquiv_natural]

/-- The edge map from positive-degree cocycles for an acyclic resolution
to the corresponding Ext group of the augmentation object. -/
def positiveCocycleBoundary (F : C) (h : ∀ j q, Subsingleton (Ext (R.terms j) F (q + 1)))
    (n : ℕ) : (R.cochainHom F (n + 1)).ker →+ Ext (R.cycles 0) F (n + 1) :=
  ((R.reindexExt F (Nat.zero_add n).symm).trans (R.degreeOneEquiv F h n 0)).toAddMonoidHom.comp
    (R.cocycleBoundary F n)

theorem positiveCocycleBoundary_surjective (F : C)
    (h : ∀ j q, Subsingleton (Ext (R.terms j) F (q + 1))) (n : ℕ) :
    Function.Surjective (R.positiveCocycleBoundary F h n) := by
  let : Subsingleton (Ext (R.terms n) F 1) := h n 0
  exact ((R.reindexExt F (Nat.zero_add n).symm).trans (R.degreeOneEquiv F h n 0)).surjective.comp
    (R.cocycleBoundary_surjective F n)

theorem positiveCocycleBoundary_eq_zero_iff (F : C)
    (h : ∀ j q, Subsingleton (Ext (R.terms j) F (q + 1))) (n : ℕ)
    (x : (R.cochainHom F (n + 1)).ker) : R.positiveCocycleBoundary F h n x = 0 ↔
      ∃ y : R.terms n ⟶ F, R.cochain F n y = x.val := by
  change (R.degreeOneEquiv F h n 0) (R.reindexExt F (Nat.zero_add n).symm
    (R.cocycleBoundary F n x)) = 0 ↔ _
  rw [AddEquiv.map_eq_zero_iff, AddEquiv.map_eq_zero_iff, R.cocycleBoundary_eq_zero_iff]

theorem positiveCocycleBoundary_natural {F G : C} (f : F ⟶ G)
    (hF : ∀ j q, Subsingleton (Ext (R.terms j) F (q + 1)))
    (hG : ∀ j q, Subsingleton (Ext (R.terms j) G (q + 1))) (n : ℕ)
    (x : (R.cochainHom F (n + 1)).ker) :
    R.positiveCocycleBoundary G hG n (R.cocyclePost f (n + 1) x) =
      (R.positiveCocycleBoundary F hF n x).comp (Ext.mk₀ f) (add_zero (n + 1)) := by
  change (R.degreeOneEquiv G hG n 0) (R.reindexExt G (Nat.zero_add n).symm
    (R.cocycleBoundary G n (R.cocyclePost f (n + 1) x))) = _
  rw [R.cocycleBoundary_natural, R.reindexExt_natural, R.degreeOneEquiv_natural]
  rfl

end Resolution

end PhilipponCech

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Abelian


namespace PhilipponCech.Resolution

universe u v w k p m
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable (R : Resolution (C := C)) (F : C)
variable {K : Type k} [Ring K] {P : ℕ → Type p}
variable [∀ n, AddCommGroup (P n)] [∀ n, Module K (P n)]
variable (d : ∀ n, P n →ₗ[K] P (n + 1))
variable (e : ∀ n, (R.terms n ⟶ F) ≃+ P n)
variable (he : ∀ n x, e (n + 1) (R.cochain F n x) = d n (e n x))

private def cocycleEquiv (n : ℕ) : (LinearMap.ker (d n)) ≃+ (R.cochainHom F n).ker := by
  refine
    { toFun := fun x => ⟨(e n).symm x.val, ?_⟩
      invFun := fun x => ⟨e n x.val, ?_⟩
      left_inv := fun x => Subtype.ext ((e n).apply_symm_apply x.val)
      right_inv := fun x => Subtype.ext ((e n).symm_apply_apply x.val)
      map_add' := fun x y => Subtype.ext (map_add (e n).symm x.val y.val) }
  · apply (e (n + 1)).injective
    change e (n + 1) (R.cochain F n ((e n).symm x.val)) = e (n + 1) 0
    rw [he, (e n).apply_symm_apply, map_zero]
    exact x.property
  · rw [LinearMap.mem_ker, ← he]
    exact (congrArg (e (n + 1)) x.property).trans (map_zero _)

variable (μ : K → (F ⟶ F))
variable (hμ : ∀ n (a : K) x, e n (x ≫ μ a) = a • e n x)

include hμ in
private theorem cocycleEquiv_scalar (n : ℕ) (a : K) (x : LinearMap.ker (d n)) :
    R.cocycleEquiv F d e he n (a • x) =
      R.cocyclePost (μ a) n (R.cocycleEquiv F d e he n x) := by
  apply Subtype.ext
  apply (e n).injective
  change e n ((e n).symm (a • x.val)) = e n ((e n).symm x.val ≫ μ a)
  rw [hμ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

variable {M : Type m} [AddCommGroup M] [Module K M]
variable (hF : ∀ n q, Subsingleton (Ext (R.terms n) F (q + 1)))
variable (q : ℕ) (a : Ext (R.cycles 0) F (q + 1) ≃+ M)
variable (ha : ∀ (b : K) x, a (x.comp (Ext.mk₀ (μ b)) (add_zero (q + 1))) = b • a x)

private def linearCocycleBoundary : LinearMap.ker (d (q + 1)) →ₗ[K] M := by
  let p := a.toAddMonoidHom.comp
    ((R.positiveCocycleBoundary F hF q).comp (R.cocycleEquiv F d e he (q + 1)).toAddMonoidHom)
  refine { p with map_smul' := ?_ }
  intro b x
  change a (R.positiveCocycleBoundary F hF q (R.cocycleEquiv F d e he _ (b • x))) =
    b • a (R.positiveCocycleBoundary F hF q (R.cocycleEquiv F d e he _ x))
  rw [R.cocycleEquiv_scalar F d e he μ hμ,
    R.positiveCocycleBoundary_natural (μ b) hF hF, ha]

include R F e he μ hμ hF a ha in
/-- A cochain model of an acyclic resolution computes its augmentation
cohomology as a linear equivalence when scalar multiplication is compatible. -/
theorem linearComparison :
    Nonempty (M ≃ₗ[K] ((LinearMap.ker (d (q + 1))) ⧸
      (LinearMap.range (d q)).comap (LinearMap.ker (d (q + 1))).subtype)) := by
  let ef := R.cocycleEquiv F d e he (q + 1)
  let δ := R.linearCocycleBoundary F d e he μ hμ hF q a ha
  have hs : Function.Surjective δ := a.surjective.comp
    ((R.positiveCocycleBoundary_surjective F hF q).comp ef.surjective)
  have hk : LinearMap.ker δ =
      (LinearMap.range (d q)).comap (LinearMap.ker (d (q + 1))).subtype := by
    ext x
    change a (R.positiveCocycleBoundary F hF q (ef x)) = 0 ↔ ∃ y, d q y = x.val
    rw [AddEquiv.map_eq_zero_iff, R.positiveCocycleBoundary_eq_zero_iff]
    have hx : e (q + 1) (ef x).val = x.val := (e (q + 1)).apply_symm_apply x.val
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨e q y, by rw [← he, hy, hx]⟩
    · rintro ⟨y, hy⟩
      refine ⟨(e q).symm y, (e (q + 1)).injective ?_⟩
      rw [he, AddEquiv.apply_symm_apply, hx, hy]
  exact ⟨(δ.quotKerEquivOfSurjective hs).symm.trans (Submodule.quotEquivOfEq _ _ hk)⟩

end PhilipponCech.Resolution

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open PhilipponOrderedEtale
open PhilipponSheafCohomology (freeOn representedSectionsAddEquiv representedSections_restrict
  representedSections_map freeTerminalIso)


namespace PhilipponEtaleCechComparison

private def cofanHomEquiv {D : Type*} [Category D] [Preadditive D]
    {ι : Type*} {J : ι → D} {c : Cofan J} (hc : IsColimit c) (B : D) :
    (c.pt ⟶ B) ≃+ (∀ i, J i ⟶ B) where
  toFun x i := c.inj i ≫ x
  invFun x := Cofan.IsColimit.desc hc x
  left_inv x := Cofan.IsColimit.hom_ext hc _ _ (Cofan.IsColimit.fac hc (fun i => c.inj i ≫ x))
  right_inv x := funext (Cofan.IsColimit.fac hc x)
  map_add' x y := by
    funext i
    simp only [Pi.add_apply, Preadditive.comp_add]

private def changeExtSource {D : Type*} [Category D] [Abelian D] [HasExt D]
    {P Q : D} (e : P ≅ Q) (B : D) (q : ℕ) : Ext P B q ≃+ Ext Q B q := by
  refine
    { toFun := fun x => (Ext.mk₀ e.inv).comp x (zero_add q)
      invFun := fun x => (Ext.mk₀ e.hom).comp x (zero_add q)
      map_add' := fun _ _ => Ext.comp_add _ _ _ _
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp x (zero_add q)) (zero_add q) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
  · intro x
    change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp x (zero_add q)) (zero_add q) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]

universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K))
variable (U : X.OrderedAffineCover)

private abbrev coefficients (X : Scheme.{u}) := SmallEtaleAdditive.sheaf X

private def summandSections {n : ℕ} (s : U.Idx n) :
    ((freeOn X.smallEtaleTopology).obj (chart U s) ⟶ coefficients X) ≃+
      (OModulePresheaf.unit π).obj (U.inter s) :=
  (representedSectionsAddEquiv X.smallEtaleTopology (coefficients X) (chart U s)).trans
    (U.inter s).topIso.commRingCatIsoToRingEquiv.toAddEquiv

/-- Evaluation on the represented summands identifies the cochain group
with sections on the corresponding ordered intersections. -/
private def cochainEquiv (n : ℕ) :
    ((resolution U).terms n ⟶ coefficients X) ≃+ (OModulePresheaf.unit π).cochain U n :=
  (cofanHomEquiv (sheafCofanIsColimit U n) (coefficients X)).trans
    (AddEquiv.piCongrRight (summandSections π U))

private theorem topIso_natural {V W : X.Opens} (h : V ≤ W) :
    W.topIso.hom ≫ X.presheaf.map (homOfLE h).op = (X.homOfLE h).appTop ≫ V.topIso.hom := by
  have h' : W.topIso.inv ≫ (X.homOfLE h).appTop =
      X.presheaf.map (homOfLE h).op ≫ V.topIso.inv := by
    rw [Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv, Scheme.Opens.topIso_inv,
      ← X.presheaf.map_comp, ← X.presheaf.map_comp]
    congr 1
  rw [← Iso.eq_inv_comp, ← Category.assoc, h', Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem summandSections_face {n : ℕ} (s : U.Idx (n + 1)) (i : Fin (n + 2))
    (a : (freeOn X.smallEtaleTopology).obj (chart U (U.face s i)) ⟶ coefficients X) :
    summandSections π U s ((freeOn X.smallEtaleTopology).map (chartFace U s i) ≫ a) =
      (OModulePresheaf.unit π).res (U.inter_le_inter_face s i)
        (summandSections π U (U.face s i) a) := by
  let h := U.inter_le_inter_face s i
  let e := PhilipponSheafCohomology.representedSections X.smallEtaleTopology (coefficients X)
  change (U.inter s).topIso.hom (e _ ((freeOn X.smallEtaleTopology).map (chartFace U s i) ≫ a)) =
    (X.presheaf.map (homOfLE h).op) ((U.inter (U.face s i)).topIso.hom (e _ a))
  rw [representedSections_restrict]
  exact (ConcreteCategory.congr_hom (topIso_natural h) (e _ a)).symm

private theorem cochainEquiv_d (n : ℕ) (a : (resolution U).terms n ⟶ coefficients X) :
    cochainEquiv π U (n + 1) ((resolution U).cochain (coefficients X) n a) =
      (OModulePresheaf.unit π).d U n (cochainEquiv π U n a) := by
  have hd : (resolution U).cochain (coefficients X) n a = sheafD U (n + 1) ≫ a := by
    rw [PhilipponCech.Resolution.cochain, ← Category.assoc]
    unfold resolution
    rw [PhilipponCech.Resolution.ofExact_differential]
  rw [hd]
  funext s
  rw [OModulePresheaf.d_apply]
  change summandSections π U s (sheafInclusion U s ≫ sheafD U (n + 1) ≫ a) =
    ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • (OModulePresheaf.unit π).res
      (U.inter_le_inter_face s i) (summandSections π U (U.face s i)
        (sheafInclusion U (U.face s i) ≫ a))
  rw [← Category.assoc, sheafInclusion_boundary, Preadditive.sum_comp, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Preadditive.zsmul_comp, map_zsmul, Category.assoc, summandSections_face]

private theorem scalar_topIso (V : X.Opens) (a : K) :
    V.topIso.hom (SmallEtaleAdditive.scalar π (openObject V) a) =
      (Scheme.TwoAffineOpenCover.algebraOfHom π V).algebraMap a := by
  have h : V.ι.appTop ≫ V.topIso.hom = X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
    congr 1
  have hm : SmallEtaleAdditive.scalar π (openObject V) ≫ V.topIso.hom =
      (Scheme.ΓSpecIso (.of K)).inv ≫ π.appLE ⊤ V le_top := by
    change ((Scheme.ΓSpecIso (.of K)).inv ≫ (V.ι ≫ π).appTop) ≫ V.topIso.hom = _
    rw [Scheme.Hom.comp_appTop, Category.assoc, Category.assoc, h]
    rfl
  exact ConcreteCategory.congr_hom hm a

private theorem cochainEquiv_scalar (n : ℕ) (a : K) (x : (resolution U).terms n ⟶ coefficients X) :
    cochainEquiv π U n (x ≫ SmallEtaleAdditive.mulScalar π a) = a • cochainEquiv π U n x := by
  funext s
  let e := PhilipponSheafCohomology.representedSections X.smallEtaleTopology (coefficients X)
  change (U.inter s).topIso.hom (e _ (sheafInclusion U s ≫ x ≫ SmallEtaleAdditive.mulScalar π a)) =
    a • (summandSections π U s (sheafInclusion U s ≫ x))
  rw [← Category.assoc, representedSections_map, SmallEtaleAdditive.mulScalar_app, map_mul,
    scalar_topIso, OModulePresheaf.unit_algebraMap_smul]
  rfl

private theorem termsAcyclic
    (hU : ∀ n (s : U.Idx n) q, Subsingleton ((SmallEtaleAdditive.sheaf (U.inter s : Scheme.{u})).H (q + 1))) :
    ∀ n q, Subsingleton (Ext ((resolution U).terms n) (coefficients X) (q + 1)) := by
  intro n q
  let e := Ext.biproductAddEquiv
    (biconeIsBilimitOfColimitCoconeOfIsColimit (sheafCofanIsColimit U n)) (coefficients X) (q + 1)
  refine ⟨fun x y => e.injective (funext fun s => ?_)⟩
  let d := PhilipponEtaleOpenCohomology.additiveOpenComparison (U.inter s).ι (q + 1)
  exact d.injective ((hU n s q).elim _ _)

private def augmentationComparison (q : ℕ) :
    Ext ((resolution U).cycles 0) (coefficients X) q ≃+ (coefficients X).H q :=
  changeExtSource ((augmentationIso U).trans (freeTerminalIso X.smallEtaleTopology (terminalWitness X)))
    (coefficients X) q

private theorem augmentationComparison_natural (q : ℕ) (a : K)
    (x : Ext ((resolution U).cycles 0) (coefficients X) q) :
    augmentationComparison U q (x.comp (Ext.mk₀ (SmallEtaleAdditive.mulScalar π a)) (add_zero q)) =
      Sheaf.H.map (SmallEtaleAdditive.mulScalar π a) q (augmentationComparison U q x) := by
  rw [Sheaf.H.map_apply]
  exact (Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add q)).symm

/-- Positive-degree étale cohomology of the additive sheaf is computed by
the specified ordered Čech complex when all its intersections are acyclic. -/
theorem comparison
    (hU : ∀ n (s : U.Idx n) q, Subsingleton ((SmallEtaleAdditive.sheaf (U.inter s : Scheme.{u})).H (q + 1)))
    (q : ℕ) : letI := SmallEtaleAdditive.cohomologyModule π (q + 1)
    Nonempty (((coefficients X).H (q + 1)) ≃ₗ[K] (OModulePresheaf.unit π).HSucc U q) := by
  letI := SmallEtaleAdditive.cohomologyModule π (q + 1)
  refine (resolution U).linearComparison (coefficients X)
    ((OModulePresheaf.unit π).d U) (cochainEquiv π U) (cochainEquiv_d π U)
    (SmallEtaleAdditive.mulScalar π) (cochainEquiv_scalar π U) (termsAcyclic U hU)
    q (augmentationComparison U (q + 1)) ?_
  exact augmentationComparison_natural π U (q + 1)

end PhilipponEtaleCechComparison

universe u

theorem solution (K : Type u) [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K))
    (U : X.OrderedAffineCover)
    (hU : ∀ (m : ℕ) (s : U.Idx m) (q : ℕ),
      Subsingleton ((SmallEtaleAdditive.sheaf (U.inter s : Scheme.{u})).H (q + 1))) :
    letI : ∀ q : ℕ, Module K ((SmallEtaleAdditive.sheaf X).H q) :=
      fun q => SmallEtaleAdditive.cohomologyModule π q
    ∀ q : ℕ, Nonempty (((SmallEtaleAdditive.sheaf X).H (q + 1)) ≃ₗ[K]
      (OModulePresheaf.unit π).HSucc U q) := by
  letI : ∀ q : ℕ, Module K ((SmallEtaleAdditive.sheaf X).H q) :=
    fun q => SmallEtaleAdditive.cohomologyModule π q
  intro q
  exact PhilipponEtaleCechComparison.comparison π U hU q

end
