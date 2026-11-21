-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleModeledCech
-- name    : AlgebraicGeometry_EtaleModeledCech
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-21T03:16:56.664656+00:00
-- url     : https://prove2.me/theorems/87320263-4474-40bc-a91a-fcd87443f4e3
-- title:
--   Čech complexes for finite-stage étale covers
-- statement:
--   Exactness of the Čech sections complex for a pulled-back injective sheaf on a descended covering arrow.

import Definitions.Def_AlgebraicGeometry_EtaleCechEvaluation

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

/-- Applying `Hom(-, F)` to the resolution is exact in positive degrees
when the coefficients are injective. -/
theorem cochain_exact_of_injective [Injective F] (j : ℕ) :
    Function.Exact (R.cochain F j) (R.cochain F (j + 1)) := by
  intro y
  constructor
  · intro hy
    let : Epi (R.projection (j + 2)) := (R.shortExact (j + 2)).epi_g
    have hz : R.inclusion (j + 1) ≫ y = 0 := by
      apply (cancel_epi (R.projection (j + 2))).mp
      rw [comp_zero]
      exact hy
    let T := CokernelCofork.ofπ y hz
    let h := (R.shortExact (j + 1)).gIsCokernel
    let z : R.cycles (j + 1) ⟶ F := h.desc T
    let : Mono (R.inclusion j) := (R.shortExact j).mono_f
    let x := Injective.factorThru z (R.inclusion j)
    refine ⟨x, ?_⟩
    change R.projection (j + 1) ≫ R.inclusion j ≫ Injective.factorThru z (R.inclusion j) = y
    rw [Injective.comp_factorThru]
    exact h.fac T WalkingParallelPair.one
  · rintro ⟨x, rfl⟩
    unfold cochain
    rw [← Category.assoc (R.inclusion (j + 1)), R.zero, zero_comp, comp_zero]

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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open scoped Simplicial


namespace PhilipponCech

universe u v w
variable {C : Type u} [Category.{v} C] [HasFiniteLimits C] {U V : C} (f : V ⟶ U)

private theorem evaluated_free_exact (W : C) (n : ℕ) :
    (augmentedSC ((SimplicialObject.Augmented.whiskeringObj C AddCommGrpCat.{v}
      (coyoneda.obj (op W) ⋙ AddCommGrpCat.free)).obj (Arrow.mk f).augmentedCechNerve) n).Exact := by
  let G := SimplicialObject.Augmented.whiskeringObj (Type v) AddCommGrpCat.{v} AddCommGrpCat.free
  let φ := G.map (evaluatedImageComparison f W)
  have : IsIso φ.left := by
    change IsIso (((SimplicialObject.whiskering (Type v) AddCommGrpCat.{v}).obj
      AddCommGrpCat.free).map (evaluatedImageComparison f W).left)
    infer_instance
  have : Mono φ.right := by
    change Mono (AddCommGrpCat.free.map (evaluatedImageComparison f W).right)
    infer_instance
  exact (augmented_exact_iff_of_iso_of_mono φ n).mp
    (augmented_exact_of_extraDegeneracy ((rangeExtraDegeneracy f W).map AddCommGrpCat.free) n)

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

private def representedFree : C ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{v} :=
  yoneda ⋙ (Functor.whiskeringRight Cᵒᵖ (Type v) AddCommGrpCat.{v}).obj AddCommGrpCat.free

private theorem represented_free_exact (n : ℕ) :
    (augmentedSC ((SimplicialObject.Augmented.whiskeringObj C (Cᵒᵖ ⥤ AddCommGrpCat.{v})
      (representedFree (C := C))).obj (Arrow.mk f).augmentedCechNerve) n).Exact := by
  let N := (Arrow.mk f).augmentedCechNerve
  let F := SimplicialObject.Augmented.whiskeringObj C (Cᵒᵖ ⥤ AddCommGrpCat.{v})
    (representedFree (C := C))
  apply exact_of_evaluation
  intro W
  exact (ShortComplex.exact_iff_of_iso
    (mapAugmentedSC ((evaluation Cᵒᵖ AddCommGrpCat.{v}).obj W) (F.obj N) n)).mpr
    (evaluated_free_exact f W.unop n)

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]

/-- The Čech nerve mapped to free abelian sheaves. -/
abbrev freeSheafNerve : SimplicialObject.Augmented (Sheaf J AddCommGrpCat.{v}) :=
  (SimplicialObject.Augmented.whiskeringObj C (Sheaf J AddCommGrpCat.{v})
    (PhilipponSheafCohomology.freeOn J)).obj (Arrow.mk f).augmentedCechNerve

/-- The augmented Čech nerve with free abelian sheaf coefficients is exact
at all the terms attached to simplices. -/
theorem free_sheaf_nerve_exact (n : ℕ) : (augmentedSC (freeSheafNerve f J) n).Exact := by
  let N := (Arrow.mk f).augmentedCechNerve
  let F := SimplicialObject.Augmented.whiskeringObj C (Cᵒᵖ ⥤ AddCommGrpCat.{v})
    (representedFree (C := C))
  let G := presheafToSheaf J AddCommGrpCat.{v}
  exact ShortComplex.exact_of_iso (mapAugmentedSC G (F.obj N) n)
    ((represented_free_exact f n).map G)

private theorem freeSheafNerve_aug_eq :
    augmentedD (freeSheafNerve f J) 0 =
      (PhilipponSheafCohomology.freeOn J).map (nerveZeroIso f).hom ≫
        (PhilipponSheafCohomology.freeOn J).map f := by
  rw [← Functor.map_comp, nerveZeroIso_hom_comp]
  simp [freeSheafNerve, augmentedD, SimplicialObject.Augmented.whiskeringObj]

variable [J.HasSheafCompose (forget AddCommGrpCat.{v})]

private theorem free_sheaf_augmentation_epi
    (h : Sieve.generate (Presieve.singleton f) ∈ J U) :
    Epi (augmentedD (freeSheafNerve f J) 0) := by
  have := PhilipponSheafCohomology.freeOn_map_epi_of_cover J f h
  rw [freeSheafNerve_aug_eq]
  infer_instance

/-- The sequence of short exact sequences of cycles in the free abelian
Čech resolution of a covering arrow. -/
def freeCechResolution (h : Sieve.generate (Presieve.singleton f) ∈ J U) :
    Resolution (C := Sheaf J AddCommGrpCat.{v}) := by
  let : Epi (augmentedD (freeSheafNerve f J) 0) := free_sheaf_augmentation_epi f J h
  exact Resolution.ofExact _ (augmentedD_comp _) (free_sheaf_nerve_exact f J)

/-- The usual alternating differential on sections over the Čech nerve. -/
def sectionCechD (F : Sheaf J AddCommGrpCat.{v}) (j : ℕ) :
    F.obj.obj (op ((Arrow.mk f).cechNerve.obj (op ⦋j⦌))) →+
      F.obj.obj (op ((Arrow.mk f).cechNerve.obj (op ⦋j + 1⦌))) :=
  ∑ i : Fin (j + 2), ((-1 : ℤ) ^ (i : ℕ)) •
    (F.obj.map ((Arrow.mk f).cechNerve.δ i).op).hom

private def cechSectionsEquiv (h : Sieve.generate (Presieve.singleton f) ∈ J U)
    (F : Sheaf J AddCommGrpCat.{v}) (j : ℕ) :
    ((freeCechResolution f J h).terms j ⟶ F) ≃+
      F.obj.obj (op ((Arrow.mk f).cechNerve.obj (op ⦋j⦌))) :=
  PhilipponSheafCohomology.representedSectionsAddEquiv J F _

private theorem cechSectionsEquiv_cochain (h : Sieve.generate (Presieve.singleton f) ∈ J U)
    (F : Sheaf J AddCommGrpCat.{v}) (j : ℕ) (s : (freeCechResolution f J h).terms j ⟶ F) :
    cechSectionsEquiv f J h F (j + 1) ((freeCechResolution f J h).cochain F j s) =
      sectionCechD f J F j (cechSectionsEquiv f J h F j s) := by
  have hd : (freeCechResolution f J h).projection (j + 1) ≫ (freeCechResolution f J h).inclusion j =
      ∑ i : Fin (j + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (PhilipponSheafCohomology.freeOn J).map ((Arrow.mk f).cechNerve.δ i) := by
    unfold freeCechResolution
    rw [Resolution.ofExact_differential, augmentedD,
      AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
    rfl
  rw [Resolution.cochain, ← Category.assoc, hd, sum_comp]
  simp only [zsmul_comp, map_sum, map_zsmul, sectionCechD, AddMonoidHom.finsetSum_apply,
    AddMonoidHom.zsmul_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact PhilipponSheafCohomology.representedSections_restrict J ((Arrow.mk f).cechNerve.δ i) s

private theorem cochain_exact_of_sections_exact (h : Sieve.generate (Presieve.singleton f) ∈ J U)
    (F : Sheaf J AddCommGrpCat.{v}) (j : ℕ)
    (he : Function.Exact (sectionCechD f J F j) (sectionCechD f J F (j + 1))) :
    Function.Exact ((freeCechResolution f J h).cochain F j)
      ((freeCechResolution f J h).cochain F (j + 1)) := by
  intro y
  constructor
  · intro hy
    have hy' : sectionCechD f J F (j + 1) (cechSectionsEquiv f J h F (j + 1) y) = 0 := by
      rw [← cechSectionsEquiv_cochain, hy, map_zero]
    obtain ⟨x, hx⟩ := (he _).mp hy'
    refine ⟨(cechSectionsEquiv f J h F j).symm x, (cechSectionsEquiv f J h F (j + 1)).injective ?_⟩
    rw [cechSectionsEquiv_cochain, AddEquiv.apply_symm_apply, hx]
  · rintro ⟨x, rfl⟩
    apply (cechSectionsEquiv f J h F (j + 2)).injective
    rw [cechSectionsEquiv_cochain, cechSectionsEquiv_cochain, map_zero]
    exact (he _).mpr ⟨_, rfl⟩

/-- Injective abelian sheaves have exact Čech cochains on every covering arrow. -/
theorem sectionCechD_exact_of_injective (h : Sieve.generate (Presieve.singleton f) ∈ J U)
    (F : Sheaf J AddCommGrpCat.{v}) [Injective F] (j : ℕ) :
    Function.Exact (sectionCechD f J F j) (sectionCechD f J F (j + 1)) := by
  let R := freeCechResolution f J h
  let e := cechSectionsEquiv f J h F
  let he := R.cochain_exact_of_injective F j
  intro y
  constructor
  · intro hy
    have hz : R.cochain F (j + 1) ((e (j + 1)).symm y) = 0 := by
      apply (e (j + 2)).injective
      rw [cechSectionsEquiv_cochain, AddEquiv.apply_symm_apply, map_zero, hy]
    obtain ⟨x, hx⟩ := (he _).mp hz
    refine ⟨e j x, ?_⟩
    rw [← cechSectionsEquiv_cochain, hx, AddEquiv.apply_symm_apply]
  · rintro ⟨x, rfl⟩
    have hz : R.cochain F (j + 1) (R.cochain F j ((e j).symm x)) = 0 :=
      (he _).mpr ⟨_, rfl⟩
    have hw := congrArg (e (j + 2)) hz
    rw [cechSectionsEquiv_cochain, cechSectionsEquiv_cochain, AddEquiv.apply_symm_apply, map_zero] at hw
    exact hw

/-- Exactness of Čech cochains and the vanishing of lower positive degrees
on the Čech terms imply that restriction along the cover is injective. -/
theorem class_eq_zero_of_cech_exact [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
    (h : Sieve.generate (Presieve.singleton f) ∈ J U)
    (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ)
    (hvanish : ∀ j q, 0 < q → q ≤ n →
      Subsingleton (F.H' q ((Arrow.mk f).cechNerve.obj (op ⦋j⦌))))
    (hcochain : ∀ j, Function.Exact (sectionCechD f J F j) (sectionCechD f J F (j + 1)))
    (x : F.H' (n + 1) U) (hx : (F.cohomologyPresheaf (n + 1)).map f.op x = 0) : x = 0 := by
  let R := freeCechResolution f J h
  apply R.eq_zero_of_restrict_zero F n 0 hvanish
    (fun j => cochain_exact_of_sections_exact f J h F j (hcochain j)) x
  change (Ext.mk₀ (augmentedD (freeSheafNerve f J) 0)).comp x (zero_add (n + 1)) = 0
  change (Ext.mk₀ ((PhilipponSheafCohomology.freeOn J).map f)).comp x (zero_add (n + 1)) = 0 at hx
  rw [freeSheafNerve_aug_eq, ← Ext.mk₀_comp_mk₀_assoc, hx, Ext.comp_zero]

end PhilipponCech

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open Opposite
open AlgebraicTopology
open scoped Simplicial


namespace PhilipponCech

universe u

/-- The two alternating coface differentials at a positive degree. -/
def cofaceShortComplex {A : Type*} [Category* A] [Preadditive A]
    (X : CosimplicialObject A) (n : ℕ) : ShortComplex A :=
  ShortComplex.mk (AlternatingCofaceMapComplex.objD X n)
    (AlternatingCofaceMapComplex.objD X (n + 1)) (AlternatingCofaceMapComplex.d_squared X n)

private theorem map_objD {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (G : A ⥤ B) [G.Additive] (X : CosimplicialObject A) (n : ℕ) :
    G.map (AlternatingCofaceMapComplex.objD X n) =
      AlternatingCofaceMapComplex.objD (X ⋙ G) n := by
  simp only [AlternatingCofaceMapComplex.objD, Functor.map_sum, Functor.map_zsmul]
  rfl

/-- Applying an additive functor commutes with the alternating coface
differentials. -/
def mapCofaceShortComplexIso {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (G : A ⥤ B) [G.Additive] (X : CosimplicialObject A) (n : ℕ) :
    (cofaceShortComplex X n).map G ≅ cofaceShortComplex (X ⋙ G) n :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      change 𝟙 _ ≫ AlternatingCofaceMapComplex.objD (X ⋙ G) n =
        G.map (AlternatingCofaceMapComplex.objD X n) ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id, map_objD])
    (by
      change 𝟙 _ ≫ AlternatingCofaceMapComplex.objD (X ⋙ G) (n + 1) =
        G.map (AlternatingCofaceMapComplex.objD X (n + 1)) ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id, map_objD])

private theorem objD_naturality {A : Type*} [Category* A] [Preadditive A]
    {X Y : CosimplicialObject A} (η : X ⟶ Y) (n : ℕ) :
    η.app ⦋n⦌ ≫ AlternatingCofaceMapComplex.objD Y n =
      AlternatingCofaceMapComplex.objD X n ≫ η.app ⦋n + 1⦌ := by
  simp only [AlternatingCofaceMapComplex.objD, comp_sum, sum_comp, comp_zsmul, zsmul_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg ((-1 : ℤ) ^ (i : ℕ) • ·) (η.naturality (SimplexCategory.δ i)).symm

/-- A natural isomorphism of cosimplicial objects gives an isomorphism of
the short complexes of alternating coface differentials. -/
def cofaceShortComplexIso {A : Type*} [Category* A] [Preadditive A]
    {X Y : CosimplicialObject A} (e : X ≅ Y) (n : ℕ) :
    cofaceShortComplex X n ≅ cofaceShortComplex Y n :=
  ShortComplex.isoMk (e.app ⦋n⦌) (e.app ⦋n + 1⦌) (e.app ⦋(n + 1) + 1⦌)
    (objD_naturality e.hom n) (objD_naturality e.hom (n + 1))

/-- Exactness of the Čech coface differentials at every stage implies
exactness after taking the filtered colimit. -/
theorem cofaceShortComplex_exact_colim {I : Type u} [Category.{u} I] [IsFiltered I]
    (X : CosimplicialObject (I ⥤ AddCommGrpCat.{u})) (n : ℕ)
    (h : ∀ i : I, (cofaceShortComplex (X ⋙ (evaluation _ _).obj i) n).Exact) :
    (cofaceShortComplex (X ⋙ colim) n).Exact := by
  have hs : (cofaceShortComplex X n).Exact := exact_of_evaluation _ fun i =>
    ShortComplex.exact_of_iso (mapCofaceShortComplexIso ((evaluation _ _).obj i) X n).symm (h i)
  exact ShortComplex.exact_of_iso (mapCofaceShortComplexIso colim X n) (hs.map colim)

/-- The cosimplicial section diagram of a Čech nerve. -/
abbrev cechSections {C A : Type*} [Category* C] [HasFiniteLimits C] [Category* A]
    {V U : C} (a : V ⟶ U) (P : Cᵒᵖ ⥤ A) : CosimplicialObject A :=
  (Arrow.mk a).cechNerve.rightOp ⋙ P

/-- Exactness of the short complex of Čech section groups is exactly
exactness of the alternating restriction homomorphisms. -/
theorem cofaceShortComplex_cech_exact_iff {C : Type*} [Category.{u} C] [HasFiniteLimits C]
    {V U : C} (a : V ⟶ U) (J : GrothendieckTopology C)
    (F : Sheaf J AddCommGrpCat.{u}) (n : ℕ) :
    (cofaceShortComplex (cechSections a F.obj) n).Exact ↔
      Function.Exact (sectionCechD a J F n) (sectionCechD a J F (n + 1)) := by
  rw [ShortComplex.ab_exact_iff_function_exact]
  have h (m : ℕ) : (AlternatingCofaceMapComplex.objD (cechSections a F.obj) m).hom =
      sectionCechD a J F m := by
    change (AddCommGrpCat.homAddEquiv (AlternatingCofaceMapComplex.objD (cechSections a F.obj) m)) = _
    simp only [AlternatingCofaceMapComplex.objD, sectionCechD, map_sum, map_zsmul]
    rfl
  change Function.Exact (AlternatingCofaceMapComplex.objD (cechSections a F.obj) n).hom
    (AlternatingCofaceMapComplex.objD (cechSections a F.obj) (n + 1)).hom ↔ _
  rw [h, h]
  rfl

end PhilipponCech

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleModeledGluing (qcqsCharts)
open PhilipponEtaleModeledSections


namespace PhilipponEtaleModeledCoverArrow

universe u

theorem singleton_cover_of_surjective {X : Scheme.{u}} {U V : X.Etale}
    (a : V ⟶ U) (ha : Function.Surjective a.left) :
    Sieve.generate (Presieve.singleton a) ∈ X.smallEtaleTopology U := by
  rw [← Presieve.ofArrows_pUnit.{0} a]
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff (fun _ : PUnit => a)).mpr
  exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨PUnit.unit, ha x⟩

variable {I : Type u} [Category.{u} I] {Y : Scheme.{u}} (E : I ⥤ Y.Etale)

private abbrev D := E ⋙ Scheme.Etale.forget Y ⋙ Over.forget Y

variable (c : Cone (D E))

private def chartLimitCofanIsColimit {i : I} {β : Type u} [Finite β]
    (W : β → ((D E).obj i).Etale) (A : ((D E).obj i).Etale) (κ : ∀ l, W l ⟶ A)
    (h : IsColimit (Cofan.mk A.left (fun l => (κ l).left))) :
    IsColimit (Cofan.mk ((chartLimitFunctor E c i).obj A).left
      (fun l => ((chartLimitFunctor E c i).map (κ l)).left)) := by
  let K := chartLimitFunctor E c i
  let r := c.π.app i
  let d : Cofan (fun l => (K.obj (W l)).left) :=
    Cofan.mk (K.obj A).left (fun l => (K.map (κ l)).left)
  let hU := FinitaryPreExtensive.isUniversal_finiteCoproducts h
  refine (hU.nonempty_isColimit_of_isPullback_left (fun l => (W l).hom) A.hom r
    (fun l => pullback.fst r (W l).hom) (fun l => pullback.snd r (W l).hom)
    (fun l => IsPullback.of_hasPullback r (W l).hom) (IsPullback.of_hasPullback r A.hom)
    d (Iso.refl _) (fun l => MorphismProperty.Over.w (κ l)) ?_ ?_).some
  · intro l
    change (K.map (κ l)).left ≫ 𝟙 _ ≫ pullback.fst r A.hom = pullback.fst r (W l).hom
    rw [Category.id_comp]
    exact pullback.lift_fst ..
  · intro l
    change (K.map (κ l)).left ≫ 𝟙 _ ≫ pullback.snd r A.hom =
      pullback.snd r (W l).hom ≫ (κ l).left
    rw [Category.id_comp]
    exact pullback.lift_snd ..

variable [IsCofiltered I] (hc : IsLimit c)
  [∀ {j k : I} (b : j ⟶ k), IsAffineHom ((D E).map b)]

include hc in
/-- A covering arrow over a modeled chart admits a refinement by a single
covering arrow from a stage, with affine source. -/
theorem exists_modeled_covering_arrow_refinement {i : I} {U : ((D E).obj i).Etale}
    (hU : qcqsCharts ((D E).obj i) U) {B : c.pt.Etale}
    (a : B ⟶ (chartLimitFunctor E c i).obj U) (ha : Function.Surjective a.left) :
    ∃ (j : I) (T V : ((D E).obj j).Etale)
      (e : (chartLimitFunctor E c i).obj U ≅ (chartLimitFunctor E c j).obj T)
      (b : V ⟶ T) (g : (chartLimitFunctor E c j).obj V ⟶ B),
      qcqsCharts ((D E).obj j) T ∧ IsAffine V.left ∧ Function.Surjective b.left ∧
      Sieve.generate (Presieve.singleton ((chartLimitFunctor E c j).map b)) ∈
        c.pt.smallEtaleTopology ((chartLimitFunctor E c j).obj T) ∧
      g ≫ a = (chartLimitFunctor E c j).map b ≫ e.inv := by
  classical
  let : CompactSpace U.left := hU.1
  let : QuasiSeparatedSpace U.left := hU.2
  obtain ⟨j, T, e, β, hβ, W, q, hT, hT', hW, hstage, hmem, hcover⟩ :=
    exists_modeled_cover_refinement E c hc (Sieve.generate (Presieve.singleton a))
      (singleton_cover_of_surjective a ha)
  let : Fintype β := hβ
  let X := (D E).obj j
  let K := chartLimitFunctor E c j
  let W₀ := fun l => (W l).left
  let (l : β) : IsAffine (W₀ l) := hW l
  let t : (∐ W₀) ⟶ X := Sigma.desc fun l => (W l).hom
  let : Etale t := by
    apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Etale) (sigmaOpenCover W₀)).mpr
    intro l
    change Etale (Sigma.ι W₀ l ≫ t)
    rw [Sigma.ι_desc]
    exact (W l).prop
  let V : X.Etale := Scheme.Etale.mk t
  let v : (∐ W₀) ⟶ T.left := Sigma.desc fun l => (q l).left
  let κ (l : β) : W l ⟶ V := MorphismProperty.Over.homMk (Sigma.ι W₀ l) (Sigma.ι_desc _ _) trivial
  let b : V ⟶ T := MorphismProperty.Over.homMk v (by
    apply Sigma.hom_ext
    intro l
    change Sigma.ι W₀ l ≫ v ≫ T.hom = Sigma.ι W₀ l ≫ t
    rw [← Category.assoc, Sigma.ι_desc, Sigma.ι_desc]
    exact MorphismProperty.Over.w (q l)) trivial
  have hb (l : β) : κ l ≫ b = q l := MorphismProperty.Over.Hom.ext (Sigma.ι_desc _ _)
  have hKb (l : β) : K.map (κ l) ≫ K.map b = K.map (q l) := by rw [← K.map_comp, hb]
  have hfact (l : β) : ∃ k : K.obj (W l) ⟶ B, k ≫ a = K.map (q l) ≫ e.inv := by
    obtain ⟨Z, d, z, hzs, hz⟩ := hmem l
    cases hzs
    exact ⟨d, hz⟩
  choose k hk using hfact
  let hC := chartLimitCofanIsColimit E c W V κ (coproductIsCoproduct W₀)
  let d : Cofan (fun l => (K.obj (W l)).left) := Cofan.mk B.left (fun l => (k l).left)
  let g₀ := hC.desc d
  have hg (l : β) : (K.map (κ l)).left ≫ g₀ = (k l).left := hC.fac d ⟨l⟩
  let g : K.obj V ⟶ B := MorphismProperty.Over.homMk g₀ (by
    apply Cofan.IsColimit.hom_ext hC
    intro l
    change (K.map (κ l)).left ≫ g₀ ≫ B.hom = (K.map (κ l)).left ≫ (K.obj V).hom
    rw [← Category.assoc, hg, MorphismProperty.Over.w, MorphismProperty.Over.w]) trivial
  refine ⟨j, T, V, e, b, g, ⟨hT, hT'⟩, inferInstanceAs (IsAffine (∐ W₀)), ?_, ?_, ?_⟩
  · intro x
    have hx := (Scheme.ofArrows_mem_smallEtaleTopology_iff q).mp hstage
    obtain ⟨l, y, hy⟩ := Set.mem_iUnion.mp (hx.symm ▸ Set.mem_univ x)
    exact ⟨Sigma.ι W₀ l y, (congrArg (fun m : W₀ l ⟶ T.left => m y) (Sigma.ι_desc _ _)).trans hy⟩
  · apply singleton_cover_of_surjective
    intro x
    have hx := (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mp hcover
    obtain ⟨l, y, hy⟩ := Set.mem_iUnion.mp (hx.symm ▸ Set.mem_univ (e.inv.left x))
    have h' : (K.map (q l)).left y = x := by
      let A := Scheme.Etale.forget c.pt ⋙ Over.forget c.pt
      let e' := A.mapIso e
      exact e'.inv.homeomorph.injective hy
    exact ⟨(K.map (κ l)).left y,
      (congrArg (fun m : K.obj (W l) ⟶ K.obj T => m.left y) (hKb l)).trans h'⟩
  · apply MorphismProperty.Over.Hom.ext
    apply Cofan.IsColimit.hom_ext hC
    intro l
    change (K.map (κ l)).left ≫ g₀ ≫ a.left =
      (K.map (κ l)).left ≫ (K.map b).left ≫ e.inv.left
    rw [← Category.assoc, hg, ← Category.assoc]
    exact (congrArg (fun m => m.left) (hk l)).trans
      (congrArg (fun m : K.obj (W l) ⟶ K.obj T => m.left ≫ e.inv.left) (hKb l).symm)

end PhilipponEtaleModeledCoverArrow

end

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

variable {i : I} {U V : ((D E).obj i).Etale} (a : V ⟶ U)
  (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})

private theorem stageCech_exact_at [Injective F] [Surjective a.left]
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
  let : Injective F' := (restrict b).injective_obj_of_injective inferInstance
  have h := (cofaceShortComplex_cech_exact_iff (B.map a) X.smallEtaleTopology F' n).mpr
    (sectionCechD_exact_of_injective (B.map a) X.smallEtaleTopology hcover F' n)
  exact ShortComplex.exact_of_iso (cofaceShortComplexIso eqSections n).symm h

variable [IsCofiltered I] (c : Cone (D E)) (hc : IsLimit c)
  [∀ {j k : I} (b : j ⟶ k), IsAffineHom ((D E).map b)]
  (p : c.pt ⟶ Y) (hp : ∀ j, c.π.app j ≫ (E.obj j).hom = p)

include hc hp in
/-- The inverse image of an injective étale sheaf has exact Čech cochains
for a covering arrow pulled back from a stage, with source and target qcqs. -/
theorem inverseImage_cech_exact_of_modeled_cover [Injective F] [Surjective a.left]
    (hU : qcqsCharts ((D E).obj i) U) (hV : qcqsCharts ((D E).obj i) V) (n : ℕ) :
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
    (fun j => stageCech_exact_at E a F j n)
  apply (cofaceShortComplex_cech_exact_iff (K.map a) c.pt.smallEtaleTopology ((pullbackSheaves p).obj F) n).mp
  exact ShortComplex.exact_of_iso (cofaceShortComplexIso isoSections n) hx

end PhilipponEtaleModeledCech

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000

open AlgebraicGeometry CategoryTheory


namespace AlgebraicGeometry.Scheme

universe u
variable {X : Scheme.{u}} {U : X.Etale}

private theorem contains_arrow_over_point (S : Sieve U)
    (hS : S ∈ X.smallEtaleTopology U) (x : U.left) :
    ∃ (V : X.Etale) (f : V ⟶ U), S f ∧ x ∈ Set.range f.left := by
  let ι := Σ V : X.Etale, {f : V ⟶ U // S f}
  let V : ι → X.Etale := fun i => i.1
  let f (i : ι) : V i ⟶ U := i.2.val
  have he : Sieve.ofArrows V f = S := by
    apply le_antisymm
    · apply (Sieve.generate_le_iff _ _).mpr
      rintro _ _ ⟨i⟩
      exact i.2.property
    · intro W g hg
      exact Sieve.ofArrows_mk V f (⟨W, ⟨g, hg⟩⟩ : ι)
  have hcover := (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mp (he.symm ▸ hS)
  have hx : x ∈ ⋃ i : ι, Set.range (f i).left := hcover.symm ▸ Set.mem_univ x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact ⟨V i, f i, i.2.property, hi⟩

private theorem contains_affine_arrow_over_point (S : Sieve U)
    (hS : S ∈ X.smallEtaleTopology U) (x : U.left) :
    ∃ (V : X.Etale) (f : V ⟶ U), S f ∧ IsAffine V.left ∧ x ∈ Set.range f.left := by
  obtain ⟨V, f, hf, y, rfl⟩ := contains_arrow_over_point S hS x
  obtain ⟨i, z, rfl⟩ := V.left.affineCover.exists_eq y
  let W : X.Etale := Scheme.Etale.mk ((V.left.affineCover.f i) ≫ V.hom)
  let g : W ⟶ V := MorphismProperty.Over.homMk (V.left.affineCover.f i) rfl trivial
  refine ⟨W, g ≫ f, S.downward_closed hf g, ?_, ⟨z, rfl⟩⟩
  change IsAffine (V.left.affineCover.X i)
  infer_instance

/-- A covering sieve on a quasi-compact object in the small étale site
has a finite refinement consisting of affine objects. -/
theorem exists_finite_affine_refinement [CompactSpace U.left] (S : Sieve U)
    (hS : S ∈ X.smallEtaleTopology U) :
    ∃ (ι : Type u) (_ : Fintype ι) (V : ι → X.Etale) (f : ∀ i, V i ⟶ U),
      (∀ i, S (f i)) ∧ (∀ i, IsAffine (V i).left) ∧
      Sieve.ofArrows V f ∈ X.smallEtaleTopology U := by
  classical
  choose V f hf ha hr using fun x : U.left => contains_affine_arrow_over_point S hS x
  have hopen (x : U.left) : IsOpen (Set.range (f x).left) :=
    (f x).left.isOpenMap.isOpen_range
  have hcover : (Set.univ : Set U.left) ⊆ ⋃ x : U.left, Set.range (f x).left :=
    fun x _ => Set.mem_iUnion.mpr ⟨x, hr x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover _ hopen hcover
  refine ⟨s, inferInstance, fun i => V i.val, fun i => f i.val,
    fun i => hf i.val, fun i => ha i.val, ?_⟩
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩

end AlgebraicGeometry.Scheme

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

universe u

/-- An individual higher étale cohomology class on a quasi-compact object is
killed by a finite family of affine étale charts. -/
theorem exists_finite_affine_cover_killing_class {X : Scheme.{u}} (U : X.Etale)
    [CompactSpace U.left] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ)
    (x : F.H' (q + 1) U) :
    ∃ (ι : Type u) (_ : Fintype ι) (V : ι → X.Etale) (f : ∀ i, V i ⟶ U),
      (∀ i, IsAffine (V i).left) ∧
      Sieve.ofArrows V f ∈ X.smallEtaleTopology U ∧
      ∀ i, (F.cohomologyPresheaf (q + 1)).map (f i).op x = 0 := by
  let S := Presheaf.equalizerSieve (F := F.cohomologyPresheaf (q + 1)) (X := op U) x 0
  have hS : S ∈ X.smallEtaleTopology U :=
    PhilipponSheafCohomology.cohomologyClass_locally_zero X.smallEtaleTopology q F U x
  obtain ⟨ι, hι, V, f, hf, hV, hcover⟩ := Scheme.exists_finite_affine_refinement S hS
  refine ⟨ι, hι, V, f, hV, hcover, fun i => ?_⟩
  have hi := hf i
  change (F.cohomologyPresheaf (q + 1)).map (f i).op x =
    (F.cohomologyPresheaf (q + 1)).map (f i).op 0 at hi
  simpa only [map_zero] using hi

/-- A higher cohomology class on a quasi-compact scheme restricts to zero on
the members of some finite affine étale covering of the scheme. -/
theorem exists_finite_affine_cover_killing_global_class (X : Scheme.{u}) [CompactSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ) (x : F.H (q + 1)) :
    let T := Scheme.Etale.mk (𝟙 X)
    let hT : IsTerminal T := IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _
      Over.mkIdTerminal
    ∃ (ι : Type u) (_ : Fintype ι) (V : ι → X.Etale) (f : ∀ i, V i ⟶ T),
      (∀ i, IsAffine (V i).left) ∧
      Sieve.ofArrows V f ∈ X.smallEtaleTopology T ∧
      ∀ i, (F.cohomologyPresheaf (q + 1)).map (f i).op
        (PhilipponSheafCohomology.terminalComparison X.smallEtaleTopology hT F (q + 1) x) = 0 := by
  intro T hT
  let : CompactSpace T.left := ‹CompactSpace X›
  exact Scheme.exists_finite_affine_cover_killing_class T F q
    (PhilipponSheafCohomology.terminalComparison X.smallEtaleTopology hT F (q + 1) x)

/-- The empty étale object has a unique section of any abelian sheaf. -/
theorem subsingleton_sections_of_isEmpty {X : Scheme.{u}} {W : X.Etale}
    (hW : IsEmpty W.left) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Subsingleton (F.obj.obj (op W)) := by
  let V : Empty → X.Etale := Empty.elim
  let p (i : Empty) : V i ⟶ W := Empty.elim i
  have hCover : Sieve.ofArrows V p ∈ X.smallEtaleTopology W :=
    (Scheme.ofArrows_mem_smallEtaleTopology_iff p).mpr (Set.ext fun x => (hW.false x).elim)
  have hBot : (⊥ : Sieve W) ∈ X.smallEtaleTopology W := by
    apply X.smallEtaleTopology.superset_covering _ hCover
    apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨i⟩
    exact Empty.elim i
  refine ⟨fun x y => ?_⟩
  have hs := Presheaf.isSheaf_comp_of_isSheaf X.smallEtaleTopology F.obj
    (CategoryTheory.forget AddCommGrpCat) F.property
  apply ((isSheaf_iff_isSheaf_of_type _ _).mp hs _ hBot).isSeparatedFor.ext
  intro _ _ h
  exact h.elim

/-- A single surjective affine étale morphism suffices to kill any given
higher cohomology class on a quasi-compact object of the small étale site. -/
theorem exists_surjective_affine_arrow_killing_class {X : Scheme.{u}} (U : X.Etale)
    [CompactSpace U.left] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ)
    (x : F.H' (q + 1) U) :
    ∃ (E : X.Etale) (g : E ⟶ U), IsAffine E.left ∧ Function.Surjective g.left ∧
      (F.cohomologyPresheaf (q + 1)).map g.op x = 0 := by
  obtain ⟨ι, hι, V, f, ha, hcover, hx⟩ := exists_finite_affine_cover_killing_class U F q x
  let : Fintype ι := hι
  let Y := fun i => (V i).left
  let : ∀ i, IsAffine (Y i) := ha
  let p : (∐ Y) ⟶ U.left := Sigma.desc (fun i => (f i).left)
  let t : (∐ Y) ⟶ X := Sigma.desc (fun i => (V i).hom)
  let : Etale t := by
    apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Etale) (sigmaOpenCover Y)).mpr
    intro i
    change Etale (Sigma.ι Y i ≫ t)
    rw [Sigma.ι_desc]
    exact (V i).prop
  let E : X.Etale := Scheme.Etale.mk t
  let g : E ⟶ U := MorphismProperty.Over.homMk p (by
    apply Sigma.hom_ext
    intro i
    change Sigma.ι Y i ≫ p ≫ U.hom = Sigma.ι Y i ≫ t
    rw [← Category.assoc]
    unfold p t
    rw [Sigma.ι_desc, Sigma.ι_desc]
    exact MorphismProperty.Over.w (f i)) trivial
  let j (i : ι) : V i ⟶ E :=
    MorphismProperty.Over.homMk (Sigma.ι Y i) (Sigma.ι_desc _ _) trivial
  have hj (i : ι) : j i ≫ g = f i := by
    apply MorphismProperty.Over.Hom.ext
    exact Sigma.ι_desc _ _
  refine ⟨E, g, inferInstanceAs (IsAffine (∐ Y)), ?_, ?_⟩
  · intro u
    have h := (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mp hcover
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp (h.symm ▸ (Set.mem_univ u))
    refine ⟨Sigma.ι Y i y, ?_⟩
    change (Sigma.ι Y i ≫ p) y = u
    rw [Sigma.ι_desc]
    exact hy
  · have hCover : Sieve.ofArrows V j ∈ X.smallEtaleTopology E := by
      apply (Scheme.ofArrows_mem_smallEtaleTopology_iff j).mpr
      ext y
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      let oc := sigmaOpenCover Y
      obtain ⟨z, hz⟩ := oc.covers y
      exact ⟨oc.idx y, z, hz⟩
    refine PhilipponSheafCohomology.class_eq_zero_of_disjoint_gluing X.smallEtaleTopology j
      ?_ F (q + 1) ((F.cohomologyPresheaf (q + 1)).map g.op x) ?_
    · intro G
      let P := G.obj ⋙ CategoryTheory.forget AddCommGrpCat
      have hP := Presheaf.isSheaf_comp_of_isSheaf X.smallEtaleTopology G.obj
        (CategoryTheory.forget AddCommGrpCat) G.property
      have hSheaf : Presieve.IsSheafFor P (.ofArrows V j) :=
        (Presieve.isSheafFor_iff_generate (.ofArrows V j)).mpr
          ((isSheaf_iff_isSheaf_of_type _ _).mp hP _ hCover)
      constructor
      · intro s s' h
        apply hSheaf.isSeparatedFor.ext
        rintro _ _ ⟨i⟩
        exact congrFun h i
      · intro s
        have hCompat : Presieve.Arrows.Compatible P j s := by
          intro i k W a b h
          have hh : a.left ≫ Sigma.ι Y i = b.left ≫ Sigma.ι Y k :=
            congrArg (fun t : W ⟶ E => t.left) h
          by_cases he : i = k
          · subst k
            have hSame : a = b := MorphismProperty.Over.Hom.ext
              ((cancel_mono (Sigma.ι Y i)).mp hh)
            rw [hSame]
          · exact (subsingleton_sections_of_isEmpty
              (isEmpty_of_commSq_sigmaι_of_ne ⟨hh⟩ he) G).elim _ _
        obtain ⟨s', hs', _⟩ :=
          (Presieve.isSheafFor_arrows_iff (π := j) (P := P)).mp hSheaf s hCompat
        exact ⟨s', funext hs'⟩
    · intro i
      let P := F.cohomologyPresheaf (q + 1)
      change P.map (j i).op (P.map g.op x) = 0
      rw [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp, hj]
      exact hx i

end AlgebraicGeometry.Scheme

end

end


