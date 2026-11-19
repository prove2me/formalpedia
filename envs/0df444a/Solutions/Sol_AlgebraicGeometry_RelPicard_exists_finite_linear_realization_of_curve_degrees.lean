-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_finite_linear_realization_of_curve_degrees
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-18T18:20:12.118093+00:00
-- url     : https://prove2.me/submissions/102a4bc3-9fe5-4218-982a-43bad248bcd7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_CurveDegreeTests
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Mathlib
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_finite_line_bundle_power_cosets_of_isProper
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eulerChar_sectionsOf_tensor_eq_add_sub
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso

universe u v

/- PhilipponIntegerProfileRank -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
noncomputable section

open Function

namespace PhilipponIntegerProfileRank

variable {M ι : Type*} [AddCommGroup M]

/-- The image of restriction to a finite set of coordinates. -/
def project (f : M →ₗ[ℤ] (ι → ℤ)) (s : Finset ι) : M →ₗ[ℤ] (s → ℤ) :=
  LinearMap.pi fun t => (LinearMap.proj t.val).comp f

abbrev multiple (n : ℤ) (M : Type*) [AddCommGroup M] : Submodule ℤ M :=
  LinearMap.range (n • LinearMap.id : M →ₗ[ℤ] M)

/-- A finite free image has rank bounded by the size of the quotient of the
source by multiplication by a nonunit integer. -/
theorem image_rank_le {N : Type*} [AddCommGroup N]
    (f : M →ₗ[ℤ] N) [Module.Free ℤ f.range] [Module.Finite ℤ f.range]
    (n : ℤ) (hn : ¬ IsUnit n) [Finite (M ⧸ multiple n M)] :
    Module.finrank ℤ f.range ≤ Nat.card (M ⧸ multiple n M) := by
  classical
  let b := Module.finBasis ℤ f.range
  let a (i : Fin (Module.finrank ℤ f.range)) := (f.surjective_rangeRestrict (b i)).choose
  have ha (i : Fin (Module.finrank ℤ f.range)) : f.rangeRestrict (a i) = b i :=
    (f.surjective_rangeRestrict (b i)).choose_spec
  let q (i : Fin (Module.finrank ℤ f.range)) := (multiple n M).mkQ (a i)
  rw [← Nat.card_fin (Module.finrank ℤ f.range)]
  apply Nat.card_le_card_of_injective q
  intro i j hij
  by_contra hne
  have hd : a i - a j ∈ multiple n M := (Submodule.Quotient.eq _).mp hij
  obtain ⟨x, hx⟩ := hd
  change n • x = a i - a j at hx
  have he := congrArg (fun y => b.repr (f.rangeRestrict y) i) hx
  have hone : n * b.repr (f.rangeRestrict x) i = 1 := by
    simpa [ha, Finsupp.single_apply, Ne.symm hne] using he
  exact hn (IsUnit.of_mul_eq_one _ hone)

/-- A surjection of equal finite rank between submodules of finite integer
products is injective. -/
theorem injective_of_rank_eq {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module.Finite ℤ A] [Module.Finite ℤ B] [Module.IsTorsionFree ℤ A]
    (g : A →ₗ[ℤ] B) (hg : Surjective g)
    (he : Module.finrank ℤ A = Module.finrank ℤ B) : Injective g := by
  have hk := g.lift_rank_eq_of_surjective hg
  have hr : Module.finrank ℤ A = Module.finrank ℤ B + Module.finrank ℤ g.ker := by
    rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank] at hk
    simp only [Cardinal.lift_natCast] at hk
    exact_mod_cast hk
  have hs : Subsingleton g.ker := (Module.finrank_eq_zero_iff_of_free ℤ g.ker).mp (by omega)
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.eq_bot_of_subsingleton

/-- With a finite quotient modulo a nonunit, a family of integer-valued
linear functionals has a finite set detecting simultaneous vanishing. -/
theorem exists_finite_detector (f : M →ₗ[ℤ] (ι → ℤ)) (n : ℤ) (hn : ¬ IsUnit n)
    [Finite (M ⧸ multiple n M)] :
    ∃ s : Finset ι, ∀ m, project f s m = 0 → f m = 0 := by
  classical
  let rank (s : Finset ι) := Module.finrank ℤ (project f s).range
  have hbound (s : Finset ι) : rank s ≤ Nat.card (M ⧸ multiple n M) :=
    image_rank_le (project f s) n hn
  have hb : BddAbove (Set.range rank) := ⟨_, by rintro _ ⟨s, rfl⟩; exact hbound s⟩
  obtain ⟨_, ⟨s, rfl⟩, hs⟩ := hb.exists_isGreatest_of_nonempty (Set.range_nonempty rank)
  refine ⟨s, fun m hm => ?_⟩
  funext t
  let w := insert t s
  let e : s → w := fun i => ⟨i.val, Finset.mem_insert_of_mem i.property⟩
  let g : (project f w).range →ₗ[ℤ] (project f s).range :=
    (LinearMap.pi fun i => (LinearMap.proj (e i)).comp (project f w).range.subtype).codRestrict
      _ (by
        rintro ⟨_, x, rfl⟩
        exact ⟨x, rfl⟩)
  have hg : Surjective g := by
    rintro ⟨_, x, rfl⟩
    exact ⟨(project f w).rangeRestrict x, rfl⟩
  have he : rank w = rank s := le_antisymm (hs (Set.mem_range_self w))
    (LinearMap.finrank_le_finrank_of_surjective hg)
  have hi := injective_of_rank_eq g hg he
  have hz : g ((project f w).rangeRestrict m) = g 0 := by
    rw [map_zero]
    exact Subtype.ext hm
  have hp := congrArg (fun x : (project f w).range => x.val ⟨t, Finset.mem_insert_self t s⟩)
    (hi hz)
  exact hp

/-- A finite detecting set embeds the image in a finite free integer module.
An integer basis of the image supplies a rational linear realization. -/
theorem exists_rational_realization (f : M →ₗ[ℤ] (ι → ℤ))
    (n : ℤ) (hn : ¬ IsUnit n) [Finite (M ⧸ multiple n M)] :
    ∃ (r : ℕ) (v : ι → Fin r → ℚ) (L : M → Module.Dual ℚ (Fin r → ℚ)),
      ∀ m t, (f m t : ℚ) = L m (v t) := by
  classical
  obtain ⟨s, hs⟩ := exists_finite_detector f n hn
  let e : f.range →ₗ[ℤ] (s → ℤ) :=
    LinearMap.pi fun i => (LinearMap.proj i.val).comp f.range.subtype
  have he : Injective e := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    rintro ⟨_, m, rfl⟩ hm
    exact Subtype.ext (hs m (show e (f.rangeRestrict m) = 0 from hm))
  letI : Module.Finite ℤ f.range := Module.Finite.of_injective e he
  let b := Module.finBasis ℤ f.range
  let L (m : M) : Module.Dual ℚ (Fin (Module.finrank ℤ f.range) → ℚ) :=
    ∑ i, (b.repr (f.rangeRestrict m) i : ℚ) • LinearMap.proj i
  refine ⟨_, fun t i => ((b i).val t : ℚ), L, fun m t => ?_⟩
  have h := congrArg (fun a : f.range => a.val t) (b.sum_repr (f.rangeRestrict m))
  have h' : ∑ i, b.repr (f.rangeRestrict m) i * (b i).val t = f m t := by
    rw [Submodule.coe_sum, Finset.sum_apply] at h
    exact h
  calc
    (f m t : ℚ) = ((∑ i, b.repr (f.rangeRestrict m) i * (b i).val t : ℤ) : ℚ) := by rw [h']
    _ = L m (fun i => ((b i).val t : ℚ)) := by simp [L]

end PhilipponIntegerProfileRank

end
end

/- PhilipponInvertibleClassLattice -/
section

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.InvertibleClassLattice
open AlgebraicGeometry CategoryTheory MonoidalCategory
open Scheme.Modules
variable {X : Scheme.{u}}

theorem isInvertible_of_iso {M N : X.Modules} (e : M ≅ N) (hM : IsInvertible M) :
    IsInvertible N := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hx, ⟨eU⟩⟩ := hM.exists_trivialization x
  exact ⟨U, hx, ⟨(pullback U.ι).mapIso e.symm ≪≫ eU⟩⟩

/-- An actual invertible sheaf determines a unit in the tensor monoid of
module isomorphism classes, using its already proved tensor inverse. -/
def unitClass (M : X.Modules) (hM : IsInvertible M) : (Skeleton X.Modules)ˣ := by
  let N := hM.exists_tensor_inverse_monoidalV2.choose
  let e := hM.exists_tensor_inverse_monoidalV2.choose_spec.2.some
  have he : toSkeleton M * toSkeleton N = 1 :=
    (Skeleton.toSkeleton_tensorObj M N).symm.trans (congr_toSkeleton_of_iso e)
  exact ⟨toSkeleton M, toSkeleton N, he, by rw [mul_comm]; exact he⟩

theorem unitClass_val (M : X.Modules) (hM : IsInvertible M) :
    (unitClass M hM).val = toSkeleton M := rfl


end PhilipponMultiplicity.InvertibleClassLattice
end
end

/- PhilipponSchemePicardGroup -/
section

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace AlgebraicGeometry.SchemePicard
open AlgebraicGeometry CategoryTheory MonoidalCategory
open PhilipponMultiplicity Scheme.Modules InvertibleClassLattice

/-- Units of the tensor-class monoid represented by actual invertible
sheaves. The representative condition uses the existing local definition. -/
def invertibleUnits (X : Scheme.{u}) : Subgroup (Skeleton X.Modules)ˣ where
  carrier := {a | ∃ M : X.Modules, IsInvertible M ∧ toSkeleton M = a.val}
  one_mem' := ⟨𝟙_ X.Modules, isInvertible_unit X, rfl⟩
  mul_mem' := by
    rintro a b ⟨M, hM, hm⟩ ⟨N, hN, hn⟩
    refine ⟨M ⊗ N, hM.tensor_monoidalV2 hN, ?_⟩
    rw [Skeleton.toSkeleton_tensorObj, hm, hn]
    rfl
  inv_mem' := by
    rintro a ⟨M, hM, hm⟩
    obtain ⟨N, hN, ⟨e⟩⟩ := hM.exists_tensor_inverse_monoidalV2
    refine ⟨N, hN, ?_⟩
    have he : a.val * toSkeleton N = 1 := by
      rw [← hm, ← Skeleton.toSkeleton_tensorObj]
      exact congr_toSkeleton_of_iso e
    change toSkeleton N = a.inv
    calc
      _ = a.inv * (a.val * toSkeleton N) := by rw [← mul_assoc, a.inv_val, one_mul]
      _ = a.inv := by rw [he, mul_one]

/-- The actual Picard group, written additively. Its objects are isomorphism
classes of invertible sheaves and addition is tensor product. -/
abbrev Group (X : Scheme.{u}) := Additive (invertibleUnits X)

variable {X : Scheme.{u}}

def value (a : Group X) : Skeleton X.Modules := a.toMul.val.val

theorem value_injective : Function.Injective (value (X := X)) := by
  intro a b h
  exact Subtype.ext (Units.ext h)

theorem value_zero : value (0 : Group X) = 1 := rfl

theorem value_add (a b : Group X) : value (a + b) = value a * value b := rfl

def classOf (M : X.Modules) (hM : IsInvertible M) : Group X :=
  Additive.ofMul ⟨unitClass M hM, M, hM, rfl⟩

theorem value_classOf (M : X.Modules) (hM : IsInvertible M) :
    value (classOf M hM) = toSkeleton M := rfl

theorem classOf_eq_iff (M N : X.Modules) (hM : IsInvertible M) (hN : IsInvertible N) :
    classOf M hM = classOf N hN ↔ Nonempty (M ≅ N) := by
  rw [← toSkeleton_eq_toSkeleton_iff]
  exact value_injective.eq_iff.symm

theorem classOf_tensor (M N : X.Modules) (hM : IsInvertible M) (hN : IsInvertible N) :
    classOf (M ⊗ N) (hM.tensor_monoidalV2 hN) = classOf M hM + classOf N hN := by
  apply value_injective
  exact Skeleton.toSkeleton_tensorObj M N

def representative (a : Group X) : X.Modules := a.toMul.property.choose

theorem representative_isInvertible (a : Group X) : IsInvertible (representative a) :=
  a.toMul.property.choose_spec.1

theorem representative_value (a : Group X) : toSkeleton (representative a) = value a :=
  a.toMul.property.choose_spec.2

theorem classOf_representative (a : Group X) :
    classOf (representative a) (representative_isInvertible a) = a :=
  value_injective (representative_value a)

def classHom (X : Scheme.{u}) : Multiplicative (Group X) →* Skeleton X.Modules where
  toFun := fun a => value a.toAdd
  map_one' := value_zero
  map_mul' := fun a b => value_add a.toAdd b.toAdd

theorem representative_class (a : Group X) :
    toSkeleton (representative a) = classHom X (Multiplicative.ofAdd a) :=
  representative_value a


end AlgebraicGeometry.SchemePicard
end
end

/- PhilipponSchemePicardClassification -/
section

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry.SchemePicard
open CategoryTheory MonoidalCategory
open PhilipponMultiplicity
variable {X : Scheme.{u}} {L : Type v} [AddCommGroup L] [Module ℤ L]
    (φ : Multiplicative L →* Skeleton X.Modules)
    (ℓ : L → X.Modules) (hℓ : ∀ l, Scheme.Modules.IsInvertible (ℓ l))
    (hclass : ∀ l, toSkeleton (ℓ l) = φ (Multiplicative.ofAdd l))

/-- An integer family with tensor-compatible classes gives its actual
class homomorphism to the Picard group. -/
def familyAddHom : L →+ Group X where
  toFun := fun l => classOf (ℓ l) (hℓ l)
  map_zero' := by
    apply value_injective
    change toSkeleton (ℓ 0) = 1
    rw [hclass, ofAdd_zero, map_one]
  map_add' := by
    intro l m
    apply value_injective
    change toSkeleton (ℓ (l + m)) = toSkeleton (ℓ l) * toSkeleton (ℓ m)
    rw [hclass, hclass, hclass, ofAdd_add, map_mul]

def familyLinearMap : L →ₗ[ℤ] Group X where
  toFun := familyAddHom φ ℓ hℓ hclass
  map_add' := (familyAddHom φ ℓ hℓ hclass).map_add
  map_smul' := fun n l =>
    (congrArg (familyAddHom φ ℓ hℓ hclass)
      (int_smul_eq_zsmul (inferInstance : Module ℤ L) n l)).trans
        (map_zsmul (familyAddHom φ ℓ hℓ hclass) n l)


end AlgebraicGeometry.SchemePicard
end
end

/- PhilipponCurveNeronSeveri -/
section

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry.SchemePicard
open CategoryTheory MonoidalCategory
variable {K : Type u} [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) (𝒱 : X.TwoAffineOpenCover)

/-- The actual two-chart Euler characteristic, with the existing section
modules and their existing kernel and cokernel. -/
def curveEuler (M : X.Modules) : ℤ :=
  (Module.finrank K (𝒱.sectionsOf π M).H0 : ℤ) -
    Module.finrank K (𝒱.sectionsOf π M).H1

theorem curveEuler_iso {M N : X.Modules} (e : M ≅ N) :
    curveEuler π 𝒱 M = curveEuler π 𝒱 N := by
  obtain ⟨𝒲, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso π π
      (Iso.refl X) (by simp) 𝒱 N M (e ≪≫ ((Scheme.Modules.pullbackId X).app N).symm)
  have h0' : 𝒲.U0 = 𝒱.U0 := by simpa using h0
  have h1' : 𝒲.U1 = 𝒱.U1 := by simpa using h1
  have hW : 𝒲 = 𝒱 := by
    cases 𝒲
    cases 𝒱
    simp_all
  subst 𝒲
  unfold curveEuler
  rw [e0.finrank_eq, e1.finrank_eq]

/-- Euler degree on genuine isomorphism classes of invertible sheaves. -/
def curveDegree (a : Group X) : ℤ :=
  curveEuler π 𝒱 (representative a) - curveEuler π 𝒱 (𝟙_ X.Modules)

theorem curveDegree_classOf (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    curveDegree π 𝒱 (classOf M hM) =
      curveEuler π 𝒱 M - curveEuler π 𝒱 (𝟙_ X.Modules) := by
  have h : toSkeleton (representative (classOf M hM)) = toSkeleton M :=
    representative_value _
  exact congrArg (fun t => t - curveEuler π 𝒱 (𝟙_ X.Modules))
    (curveEuler_iso π 𝒱 (toSkeleton_eq_toSkeleton_iff.mp h).some)

theorem curveDegree_zero : curveDegree π 𝒱 (0 : Group X) = 0 := by
  have h : toSkeleton (representative (0 : Group X)) = toSkeleton (𝟙_ X.Modules) :=
    representative_value _
  unfold curveDegree
  rw [curveEuler_iso π 𝒱 (toSkeleton_eq_toSkeleton_iff.mp h).some, sub_self]

variable [IsAlgClosed K] [IsIntegral X] [IsProper π] [SmoothOfRelativeDimension 1 π]

theorem curveDegree_add (a b : Group X) :
    curveDegree π 𝒱 (a + b) = curveDegree π 𝒱 a + curveDegree π 𝒱 b := by
  have h : toSkeleton (representative (a + b)) =
      toSkeleton (representative a ⊗ representative b) := by
    rw [Skeleton.toSkeleton_tensorObj, representative_value, representative_value,
      representative_value, value_add]
  have he := curveEuler_iso π 𝒱 (toSkeleton_eq_toSkeleton_iff.mp h).some
  have ht := Scheme.Modules.IsInvertible.eulerChar_sectionsOf_tensor_eq_add_sub K π
    (representative a) (representative b)
    (representative_isInvertible a) (representative_isInvertible b) 𝒱
  change curveEuler π 𝒱 (representative a ⊗ representative b) =
    curveEuler π 𝒱 (representative a) + curveEuler π 𝒱 (representative b) -
      curveEuler π 𝒱 (𝟙_ X.Modules) at ht
  unfold curveDegree
  rw [he, ht]
  omega

def curveDegreeHom : Group X →ₗ[ℤ] ℤ :=
  ({ toFun := curveDegree π 𝒱
     map_zero' := curveDegree_zero π 𝒱
     map_add' := curveDegree_add π 𝒱 } : Group X →+ ℤ).toIntLinearMap


end AlgebraicGeometry.SchemePicard
end
end

/- PhilipponSchemePicardPullback -/
section

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry.SchemePicard
open CategoryTheory MonoidalCategory
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Pullback of the actual Picard group, obtained by reusing the class map
of the tensor-compatible family of pulled-back representatives. -/
def pullback : Group Y →ₗ[ℤ] Group X :=
  familyLinearMap ((Skeleton.monoidHom (Scheme.Modules.pullback f)).comp (classHom Y))
    (fun a => (Scheme.Modules.pullback f).obj (representative a))
    (fun a => (representative_isInvertible a).pullback f)
    (fun a => by
      rw [← Functor.mapSkeleton_obj_toSkeleton, representative_class]
      rfl)

theorem pullback_classOf (M : Y.Modules) (hM : Scheme.Modules.IsInvertible M) :
    pullback f (classOf M hM) =
      classOf ((Scheme.Modules.pullback f).obj M) (hM.pullback f) := by
  apply value_injective
  change toSkeleton ((Scheme.Modules.pullback f).obj (representative (classOf M hM))) = _
  rw [← Functor.mapSkeleton_obj_toSkeleton, representative_value]
  exact Functor.mapSkeleton_obj_toSkeleton (Scheme.Modules.pullback f) M

theorem pullback_representative (a : Group Y) :
    pullback f a = classOf ((Scheme.Modules.pullback f).obj (representative a))
      ((representative_isInvertible a).pullback f) := rfl

end AlgebraicGeometry.SchemePicard
end
end

/- PhilipponCurveDegreePowerRealization -/
section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemePicard
open PhilipponIntegerProfileRank

namespace PhilipponCurveDegreePowerRealization

/-- The skeleton representatives of the power cosets surject onto the
quotient of the actual Picard group by integer multiplication. -/
theorem finite_picard_quotient {X : Scheme.{u}} (p r : ℕ)
    (M : Fin r → X.Modules) (hM : ∀ i, Scheme.Modules.IsInvertible (M i))
    (hcover : ∀ N : X.Modules, Scheme.Modules.IsInvertible N →
      ∃ (i : Fin r) (P : X.Modules), Scheme.Modules.IsInvertible P ∧
        toSkeleton N = toSkeleton (M i) * toSkeleton P ^ p) :
    Finite (SchemePicard.Group X ⧸ multiple (p : ℤ) (SchemePicard.Group X)) := by
  let Q := multiple (p : ℤ) (SchemePicard.Group X)
  apply Finite.of_surjective (fun i => Q.mkQ (classOf (M i) (hM i)))
  intro a
  obtain ⟨b, rfl⟩ := Q.mkQ_surjective a
  obtain ⟨i, P, hP, h⟩ := hcover (representative b) (representative_isInvertible b)
  have hpow : value (p • classOf P hP) = (toSkeleton P) ^ p :=
    (classHom X).map_pow (Multiplicative.ofAdd (classOf P hP)) p
  have hb : b = classOf (M i) (hM i) + p • classOf P hP := by
    apply value_injective
    rw [← representative_value, value_add, value_classOf, hpow]
    exact h
  refine ⟨i, ?_⟩
  rw [hb, map_add]
  have hzero : Q.mkQ (p • classOf P hP) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero Q).mpr
    exact ⟨classOf P hP, by simp⟩
  rw [hzero, add_zero]

/-- Collect the integer Euler-degree maps with exactly the input curve
charts and pullbacks used in the published degrees. -/
def profiles {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) :
    SchemePicard.Group X →ₗ[ℤ] (CurveDegreeTests.Probe π → ℤ) :=
  LinearMap.pi fun t =>
    (curveDegreeHom t.toBase t.cover).comp (SchemePicard.pullback t.toScheme)

theorem profiles_classOf {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) (t : CurveDegreeTests.Probe π)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    profiles π (classOf M hM) t = t.degree M := by
  change curveDegree t.toBase t.cover (SchemePicard.pullback t.toScheme (classOf M hM)) = _
  rw [pullback_classOf, curveDegree_classOf]
  rfl

theorem exists_realization_of_proper {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) [IsProper π] :
    ∃ (r : ℕ) (v : CurveDegreeTests.Probe π → Fin r → ℚ)
      (L : {M : X.Modules // Scheme.Modules.IsInvertible M} → Module.Dual ℚ (Fin r → ℚ)),
      ∀ M t, (t.degree M.val : ℚ) = L M (v t) := by
  obtain ⟨p, r, M, hp, hM, hcover⟩ :=
    AlgebraicGeometry.RelPicard.exists_finite_line_bundle_power_cosets_of_isProper K π
  letI := finite_picard_quotient p r M hM hcover
  have hnonunit : ¬ IsUnit (p : ℤ) := by
    simp only [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast]
    omega
  obtain ⟨d, v, L, hL⟩ := exists_rational_realization (profiles π) (p : ℤ) hnonunit
  refine ⟨d, v, fun M => L (classOf M.val M.property), fun M t => ?_⟩
  rw [← profiles_classOf π t M.val M.property]
  exact hL (classOf M.val M.property) t

end PhilipponCurveDegreePowerRealization

end
end

/- PhilipponCurveDegreePowerSolution -/
section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] [Smooth π]
    (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π) :
    ∃ (F : Type u) (_ : Field F) (_ : CharZero F) (r : ℕ)
      (v : CurveDegreeTests.Probe π → Fin r → F)
      (L : {M : X.Modules // Scheme.Modules.IsInvertible M} →
        Module.Dual F (Fin r → F)),
      ∀ M t, algebraMap ℚ F (t.degree M.val : ℚ) = L M (v t) := by
  obtain ⟨r, v, L, h⟩ := PhilipponCurveDegreePowerRealization.exists_realization_of_proper π
  let F := ULift.{u} ℚ
  letI : CharZero F := ⟨fun _ _ h => Nat.cast_injective (R := ℚ) (congrArg ULift.down h)⟩
  let L' (M : {M : X.Modules // Scheme.Modules.IsInvertible M}) : Module.Dual F (Fin r → F) :=
    { toFun := fun x => ULift.up (L M (fun j => (x j).down))
      map_add' := fun x y => congrArg ULift.up (map_add (L M) (fun j => (x j).down) (fun j => (y j).down))
      map_smul' := fun c x => congrArg ULift.up (map_smul (L M) c.down (fun j => (x j).down)) }
  refine ⟨F, inferInstance, inferInstance, r, fun t j => ULift.up (v t j), L', fun M t => ?_⟩
  apply ULift.ext
  change algebraMap ℚ ℚ (t.degree M.val : ℚ) = L M (v t)
  simpa using h M t


end

#print axioms PhilipponIntegerProfileRank.image_rank_le
#print axioms PhilipponIntegerProfileRank.injective_of_rank_eq
#print axioms PhilipponIntegerProfileRank.exists_finite_detector
#print axioms PhilipponIntegerProfileRank.exists_rational_realization
#print axioms PhilipponCurveDegreePowerRealization.finite_picard_quotient
#print axioms PhilipponCurveDegreePowerRealization.profiles_classOf
#print axioms PhilipponCurveDegreePowerRealization.exists_realization_of_proper
#print axioms solution
