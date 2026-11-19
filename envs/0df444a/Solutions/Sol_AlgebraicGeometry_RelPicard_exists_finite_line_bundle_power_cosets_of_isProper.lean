-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_finite_line_bundle_power_cosets_of_isProper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-18T19:15:05.40962+00:00
-- url     : https://prove2.me/submissions/39fb1c26-4658-4895-ab44-101780efc748
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_SmallEtaleUnits
import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_etale_units_H1_classes
import Theorems.Thm_AlgebraicGeometry_Scheme_finite_etale_roots_H2_of_isProper

universe u v

/- PhilipponKummerAffineCover -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

namespace PhilipponKummerAffineCover
variable {R : Type u} [CommRing R]

/-- The finite monic algebra adjoining a root of a unit. -/
def equation (n : ℕ) (a : Rˣ) : R[X] := X ^ n - C (a : R)

theorem root_pow (n : ℕ) (a : Rˣ) :
    AdjoinRoot.root (equation n a) ^ n = algebraMap R (AdjoinRoot (equation n a)) (a : R) := by
  apply sub_eq_zero.mp
  have h := AdjoinRoot.eval₂_root (equation n a)
  simp only [equation, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  exact h

/-- When `n` is a unit, the derivative is a unit in the entire monic
quotient. Hence the monic algebra is already standard étale. -/
theorem etale (n : ℕ) (hn : n ≠ 0) (hu : IsUnit (n : R)) (a : Rˣ) :
    Algebra.Etale R (AdjoinRoot (equation n a)) := by
  let f := equation n a
  let A := AdjoinRoot f
  let x : A := AdjoinRoot.root f
  have hx : IsUnit x := by
    apply isUnit_of_dvd_unit (dvd_pow_self x hn)
    rw [root_pow n a]
    exact a.isUnit.map (algebraMap R A)
  have hder : IsUnit (AdjoinRoot.mk f f.derivative) := by
    have hd : AdjoinRoot.mk f f.derivative = algebraMap R A (n : R) * x ^ (n - 1) := by
      change AdjoinRoot.mk f (derivative (X ^ n - C (a : R))) = _
      rw [derivative_sub, derivative_C, sub_zero, derivative_X_pow, map_mul, map_pow]
      rfl
    rw [hd]
    exact (hu.map (algebraMap R A)).mul (hx.pow _)
  let P : StandardEtalePair R := ⟨f, monic_X_pow_sub_C (a : R) hn, f.derivative, 1, 0, 1, by simp⟩
  let away : A ≃ₐ[R] Localization.Away (AdjoinRoot.mk P.f P.g) :=
    (IsLocalization.atUnit A (Localization.Away (AdjoinRoot.mk f f.derivative))
      (AdjoinRoot.mk f f.derivative) hder).restrictScalars R
  letI : Algebra.IsStandardEtale R A := Algebra.IsStandardEtale.of_equiv
    (P.equivAwayAdjoinRoot.trans away.symm)
  infer_instance

theorem algebraMap_injective [Nontrivial R] (n : ℕ) (hn : n ≠ 0) (a : Rˣ) :
    Function.Injective (algebraMap R (AdjoinRoot (equation n a))) := by
  let f := equation n a
  have hm : f.Monic := monic_X_pow_sub_C (a : R) hn
  have hleft : Function.LeftInverse (fun x => (AdjoinRoot.modByMonicHom hm x).coeff 0)
      (algebraMap R (AdjoinRoot f)) := by
    intro r
    change (AdjoinRoot.modByMonicHom hm (AdjoinRoot.mk f (C r))).coeff 0 = r
    have hdeg : (C r).degree < f.degree := by
      apply lt_of_le_of_lt degree_C_le
      rw [show f.degree = n from degree_X_pow_sub_C (Nat.pos_of_ne_zero hn) (a : R)]
      exact_mod_cast Nat.pos_of_ne_zero hn
    rw [AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff hm).mpr hdeg, coeff_C_zero]
  exact hleft.injective

/-- A finite étale surjection on which an invertible affine section has
an actual `n`-th root. -/
theorem exists_affine_cover [Nontrivial R] (n : ℕ) (hn : n ≠ 0) (hu : IsUnit (n : R)) (a : Rˣ) :
    ∃ (S : CommRingCat.{u}) (g : CommRingCat.of R ⟶ S) (b : (S : Type u)ˣ),
      IsFinite (Spec.map g) ∧ Etale (Spec.map g) ∧ Surjective (Spec.map g) ∧
      b ^ n = Units.map g.hom.toMonoidHom a := by
  let f := equation n a
  let A := AdjoinRoot f
  let g : CommRingCat.of R ⟶ CommRingCat.of A := CommRingCat.ofHom (algebraMap R A)
  have hm : f.Monic := monic_X_pow_sub_C (a : R) hn
  letI : Module.Finite R A := hm.finite_adjoinRoot
  letI : Algebra.Etale R A := etale n hn hu a
  have hfinite : (algebraMap R A).Finite := RingHom.finite_algebraMap.mpr inferInstance
  have hetale : (algebraMap R A).Etale := RingHom.etale_algebraMap.mpr inferInstance
  have hx : IsUnit (AdjoinRoot.root f) := by
    apply isUnit_of_dvd_unit (dvd_pow_self _ hn)
    rw [root_pow n a]
    exact a.isUnit.map (algebraMap R A)
  refine ⟨_, g, hx.unit, (IsFinite.SpecMap_iff g).mpr hfinite,
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hetale, ?_, ?_⟩
  · exact ⟨hfinite.to_isIntegral.comap_surjective (algebraMap_injective n hn a)⟩
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    exact root_pow n a

end PhilipponKummerAffineCover

end
end

/- PhilipponKummerLocalRoots -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory

namespace PhilipponKummerLocalRoots

abbrev UnitsOn (X : Scheme.{u}) := Γ(X, ⊤)ˣ

/-- Pullback on actual global units. -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) : UnitsOn Y →* UnitsOn X :=
  Units.map f.appTop.hom.toMonoidHom

theorem pull_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull (f ≫ g) = (pull f).comp (pull g) := by
  simp only [pull, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rfl

theorem exists_root_spec (R : CommRingCat.{u}) (n : ℕ) (hn : n ≠ 0)
    (hu : IsUnit (n : Γ(Spec R, ⊤))) (a : UnitsOn (Spec R)) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec R) (b : UnitsOn Y),
      IsFinite f ∧ Etale f ∧ Surjective f ∧ b ^ n = pull f a := by
  let e := Scheme.ΓSpecIso R
  rcases subsingleton_or_nontrivial R with h | h
  · letI : Subsingleton Γ(Spec R, ⊤) := e.commRingCatIsoToRingEquiv.injective.subsingleton
    exact ⟨_, 𝟙 _, 1, inferInstance, inferInstance, inferInstance, Subsingleton.elim _ _⟩
  · letI : Nontrivial R := h
    have hu' : IsUnit (n : R) := by simpa only [map_natCast] using hu.map e.hom.hom
    obtain ⟨S, g, b, hf, he, hs, hb⟩ :=
      PhilipponKummerAffineCover.exists_affine_cover n hn hu' (Units.map e.hom.hom.toMonoidHom a)
    refine ⟨_, Spec.map g, Units.map (Scheme.ΓSpecIso S).inv.hom.toMonoidHom b, hf, he, hs, ?_⟩
    rw [← map_pow, hb]
    change Units.map ((e.hom ≫ g ≫ (Scheme.ΓSpecIso S).inv).hom.toMonoidHom) a = _
    rw [Scheme.ΓSpecIso_inv_naturality, ← Category.assoc, e.hom_inv_id, Category.id_comp]

theorem exists_root_affine (X : Scheme.{u}) [IsAffine X] (n : ℕ) (hn : n ≠ 0)
    (hu : IsUnit (n : Γ(X, ⊤))) (a : UnitsOn X) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (b : UnitsOn Y),
      IsFinite f ∧ Etale f ∧ Surjective f ∧ b ^ n = pull f a := by
  let e := X.isoSpec
  have hu' : IsUnit (n : Γ(Spec Γ(X, ⊤), ⊤)) := by
    simpa only [map_natCast] using hu.map e.inv.appTop.hom
  obtain ⟨Y, f, b, hf, he, hs, hb⟩ := exists_root_spec _ n hn hu' (pull e.inv a)
  letI := hf
  letI := he
  letI := hs
  refine ⟨Y, f ≫ e.inv, b, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [pull_comp]
  exact hb

/-- Every point is covered by an étale chart on which the given unit
has an actual root. The root is a section of the chart's structure sheaf. -/
theorem exists_root_near (X : Scheme.{u}) (n : ℕ) (hn : n ≠ 0)
    (hu : IsUnit (n : Γ(X, ⊤))) (a : UnitsOn X) (x : X) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (y : Y) (b : UnitsOn Y),
      Etale f ∧ f y = x ∧ b ^ n = pull f a := by
  obtain ⟨i, z, rfl⟩ := X.affineCover.exists_eq x
  let g := X.affineCover.f i
  have hu' : IsUnit (n : Γ(X.affineCover.X i, ⊤)) := by
    simpa only [map_natCast] using hu.map g.appTop.hom
  obtain ⟨Y, f, b, _, he, hs, hb⟩ := exists_root_affine _ n hn hu' (pull g a)
  obtain ⟨y, rfl⟩ := hs.surj z
  letI := he
  refine ⟨Y, f ≫ g, y, b, inferInstance, rfl, ?_⟩
  rw [pull_comp]
  exact hb

end PhilipponKummerLocalRoots

end
end

/- PhilipponKummerSequence -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponKummerLocalRoots

namespace PhilipponKummerSequence

/-- Multiplication by `n` in the units sheaf is locally surjective for
the actual small étale topology when `n` is globally invertible. -/
theorem power_locally_surjective (X : Scheme.{u}) (n : ℕ) (hn : n ≠ 0)
    (hu : IsUnit (n : Γ(X, ⊤))) : Sheaf.IsLocallySurjective (power X n) := by
  constructor
  intro U a
  let a₀ : UnitsOn U.left := a
  have hu' : IsUnit (n : Γ(U.left, ⊤)) := by simpa only [map_natCast] using hu.map U.hom.appTop.hom
  choose Y f y b he hx hr using fun x : U.left => exists_root_near U.left n hn hu' a₀ x
  let W (x : U.left) : X.Etale := by
    letI := he x
    exact Scheme.Etale.mk (f x ≫ U.hom)
  let g (x : U.left) : W x ⟶ U := MorphismProperty.Over.homMk (f x) rfl trivial
  refine X.smallEtaleTopology.superset_covering (S := Sieve.ofArrows W g) ?_ ?_
  · apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨x⟩
    refine ⟨b x, ?_⟩
    change b x ^ n = pull (f x) a₀
    exact hr x
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff g).mpr
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨x, y x, hx x⟩

/-- The Kummer short exact sequence on the small étale site. -/
theorem short_exact (X : Scheme.{u}) (n : ℕ) (hn : n ≠ 0)
    (hu : IsUnit (n : Γ(X, ⊤))) : (sequence X n).ShortExact := by
  letI : Sheaf.IsLocallySurjective (power X n) := power_locally_surjective X n hn hu
  letI : Mono (sequence X n).f := inferInstanceAs (Mono (kernel.ι (power X n)))
  letI : Epi (sequence X n).g := inferInstanceAs (Epi (power X n))
  exact { exact := ShortComplex.exact_kernel (power X n) }

end PhilipponKummerSequence

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

/- PhilipponKummerPicardCosets -/
section

set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AlgebraicGeometry.SchemePicard PhilipponKummerSequence

namespace PhilipponKummerPicardCosets

/-- One of the primes two and three remains invertible in the global
sections of a scheme over a field. -/
theorem exists_invertible_prime {K : Type u} [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (CommRingCat.of K)) : ∃ p : ℕ, p.Prime ∧ IsUnit (p : Γ(X, ⊤)) := by
  suffices ∃ p : ℕ, p.Prime ∧ IsUnit (p : K) by
    obtain ⟨p, hp, hK⟩ := this
    let f := (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ π.appTop
    exact ⟨p, hp, by simpa only [map_natCast] using hK.map f.hom⟩
  by_cases hK : (2 : K) = 0
  · refine ⟨3, by decide, isUnit_iff_ne_zero.mpr ?_⟩
    rw [show ((3 : ℕ) : K) = (2 : K) + 1 by norm_num, hK, zero_add]
    exact one_ne_zero
  · exact ⟨2, by decide, isUnit_iff_ne_zero.mpr hK⟩

/-- The connecting map has equal values only on equal cosets modulo
the tensor power. This uses exactness at the actual `H¹` of units. -/
theorem exists_cosets_of_finite_H2 (X : Scheme.{u}) (n : ℕ) (hn : n ≠ 0)
    (hu : IsUnit (n : Γ(X, ⊤)))
    (e : SchemePicard.Group X ≃+ (units X).H 1)
    [Finite ((roots X n).H 2)] :
    ∃ (r : ℕ) (M : Fin r → X.Modules), (∀ i, Scheme.Modules.IsInvertible (M i)) ∧
      ∀ N : X.Modules, Scheme.Modules.IsInvertible N →
        ∃ (i : Fin r) (P : X.Modules), Scheme.Modules.IsInvertible P ∧
          toSkeleton N = toSkeleton (M i) * toSkeleton P ^ n := by
  classical
  let A := (constantSheaf X.smallEtaleTopology AddCommGrpCat).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let hS := short_exact X n hn hu
  let δ : (units X).H 1 →+ (roots X n).H 2 := hS.extClass.postcomp A (by decide)
  have hδ (x : (units X).H 1) (hx : δ x = 0) : ∃ y : (units X).H 1, x = n • y := by
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ A hS x (show 1 + 1 = 2 by decide) hx
    change (units X).H 1 at y
    have hy' : Sheaf.H.map (power X n) 1 y = x := hy
    refine ⟨y, hy'.symm.trans ?_⟩
    let F := Sheaf.functorH X.smallEtaleTopology 1
    have hmap : F.map (n • 𝟙 (units X)) = n • 𝟙 (F.obj (units X)) := by
      rw [Functor.map_nsmul]
      exact congrArg (fun f : F.obj (units X) ⟶ F.obj (units X) => n • f) (F.map_id _)
    exact congrArg (fun f : F.obj (units X) ⟶ F.obj (units X) => f y) hmap
  let c := δ.comp e.toAddMonoidHom
  let I := Set.range c
  letI : Fintype I := Fintype.ofFinite I
  let t := Fintype.equivFin I
  let a (i : Fin (Fintype.card I)) := ((t.symm i).property).choose
  have ha (i : Fin (Fintype.card I)) : c (a i) = (t.symm i).val := (t.symm i).property.choose_spec
  refine ⟨_, fun i => representative (a i), fun i => representative_isInvertible _, fun N hN => ?_⟩
  let b := classOf N hN
  let i := t ⟨c b, Set.mem_range_self b⟩
  have hi : c (a i) = c b := (ha i).trans (congrArg Subtype.val (t.symm_apply_apply _))
  have hz : δ (e (b - a i)) = 0 := by
    change c (b - a i) = 0
    rw [map_sub, hi, sub_self]
  obtain ⟨y, hy⟩ := hδ _ hz
  obtain ⟨w, rfl⟩ := e.surjective y
  have hba : b - a i = n • w := e.injective (hy.trans (map_nsmul e n w).symm)
  have hb : b = a i + n • w := by
    rw [add_comm, ← hba, sub_add_cancel]
  refine ⟨i, representative w, representative_isInvertible w, ?_⟩
  change value b = toSkeleton (representative (a i)) * toSkeleton (representative w) ^ n
  rw [hb, value_add, representative_value, representative_value]
  exact congrArg (value (a i) * ·) ((classHom X).map_pow (Multiplicative.ofAdd w) n)

end PhilipponKummerPicardCosets

end
end

/- PhilipponKummerPicardSolution -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemePicard PhilipponKummerSequence

namespace PhilipponKummerPicardSolution

/-- The representative formulation of the Picard comparison gives an
additive equivalence on the actual group of invertible classes. -/
theorem exists_picard_equiv (X : Scheme.{u}) :
    Nonempty (SchemePicard.Group X ≃+ (units X).H 1) := by
  obtain ⟨c, hsurj, hclass, hadd⟩ := X.exists_etale_units_H1_classes
  let f (a : SchemePicard.Group X) := c ⟨representative a, representative_isInvertible a⟩
  have hf (a b : SchemePicard.Group X) : f (a + b) = f a + f b := by
    apply hadd
    rw [representative_value, representative_value, representative_value, value_add]
  let F : SchemePicard.Group X →+ (units X).H 1 := AddMonoidHom.mk' f hf
  have hinj : Function.Injective F := by
    intro a b h
    have he := (hclass ⟨representative a, representative_isInvertible a⟩
      ⟨representative b, representative_isInvertible b⟩).mp h
    rw [representative_value, representative_value] at he
    exact value_injective he
  have hsur : Function.Surjective F := by
    intro b
    obtain ⟨M, rfl⟩ := hsurj b
    refine ⟨classOf M.val M.property, (hclass _ M).mpr ?_⟩
    rw [representative_value, value_classOf]
  exact ⟨AddEquiv.ofBijective F ⟨hinj, hsur⟩⟩

end PhilipponKummerPicardSolution

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] :
    ∃ (p r : ℕ) (M : Fin r → X.Modules),
      1 < p ∧ (∀ i, Scheme.Modules.IsInvertible (M i)) ∧
        ∀ N : X.Modules, Scheme.Modules.IsInvertible N →
          ∃ (i : Fin r) (P : X.Modules), Scheme.Modules.IsInvertible P ∧
            toSkeleton N = toSkeleton (M i) * toSkeleton P ^ p := by
  obtain ⟨p, hp, hu⟩ := PhilipponKummerPicardCosets.exists_invertible_prime π
  letI := X.finite_etale_roots_H2_of_isProper K π p hp.ne_zero hu
  obtain ⟨e⟩ := PhilipponKummerPicardSolution.exists_picard_equiv X
  obtain ⟨r, M, hM, hcover⟩ :=
    PhilipponKummerPicardCosets.exists_cosets_of_finite_H2 X p hp.ne_zero hu e
  exact ⟨p, r, M, hp.one_lt, hM, hcover⟩

end
end

#print axioms PhilipponKummerAffineCover.root_pow
#print axioms PhilipponKummerAffineCover.etale
#print axioms PhilipponKummerAffineCover.algebraMap_injective
#print axioms PhilipponKummerAffineCover.exists_affine_cover
#print axioms PhilipponKummerLocalRoots.pull_comp
#print axioms PhilipponKummerLocalRoots.exists_root_spec
#print axioms PhilipponKummerLocalRoots.exists_root_affine
#print axioms PhilipponKummerLocalRoots.exists_root_near
#print axioms PhilipponKummerSequence.power_locally_surjective
#print axioms PhilipponKummerSequence.short_exact
#print axioms PhilipponKummerPicardCosets.exists_invertible_prime
#print axioms PhilipponKummerPicardCosets.exists_cosets_of_finite_H2
#print axioms PhilipponKummerPicardSolution.exists_picard_equiv
#print axioms solution
