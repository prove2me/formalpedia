-- Prove2me | Definitions.Def_MazurTransfer_Order13MixedOriginalRecoveredReciprocalAndSingleSectionPolynomialBasesData20261019
-- name    : MazurTransfer_Order13MixedOriginalRecoveredReciprocalAndSingleSectionPolynomialBasesData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T05:50:47.253923+00:00
-- url     : https://prove2.me/theorems/f14b3291-c506-4ba9-911f-1fc36ef355d0
-- title:
--   Original recovered reciprocal maps and ordinary single-section polynomial basis
-- statement:
--   The original localization maps, recovered reciprocal-coordinate morphisms, actual ordinary parameter subalgebra, its explicit polynomial basis and original finite free coefficient level sets. Eleven further original modules retain their headers, whole constructor values and complete original types; prior parameter constructors are separately checked as context. Named downstream consumer: the actual single-section affine atlas and original degree-three FiniteMapData.
-- source:
--   MazurTheorem original mixed single-section parameter algebras and reciprocal recovery, by Vas and contributors; exact official Anthropic FLT quotient/base-change bridge at pin 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0. Original per-file attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the exact original recovered reciprocal coordinates,
localization maps, and the ordinary single-section polynomial basis and
finite free level sets for the same mixed quadratic curve.
Named downstream consumer: the actual single-section affine atlas and
original degree-three FiniteMapData. Original per-file headers are retained.
-/
import Mathlib
import Theorems.Thm_MazurTransfer_mixed_inverse_parameter_reciprocal_recovery
import Definitions.Def_MazurTransfer_Order13MixedOriginalParameterRingsAndInverseParameterPolynomialBasesDataExplicitPublicPowerProfileV320261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual inverse-parameter finite algebra coordinates and
the unit-ideal cover by s and 1-s-b, valid over every commutative base.
Named downstream consumer: identifying the two principal charts of the
SECOND mixed FiniteMapData affine open. No curve-open identification is
asserted by this algebraic cover.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open Polynomial Order13MixedInverseParameterPolynomialIdentities
variable (R : Type u) [CommRing R]

def aElement : candidateAlgebra R := ⟨a R,Algebra.subset_adjoin (by simp)⟩
def bElement : candidateAlgebra R := ⟨b R,Algebra.subset_adjoin (by simp)⟩
def denominatorElement : candidateAlgebra R := 1 - parameterElement R - bElement R

theorem parameterElement_coe : (parameterElement R : ordinaryParameterLocalization R) = s R := by
  change aeval (s R) X = s R
  exact aeval_X _

theorem a_mul_b : aElement R * bElement R = parameterElement R * denominatorElement R := by
  apply Subtype.val_injective
  change a R * b R = (parameterElement R : ordinaryParameterLocalization R) *
    (1 - (parameterElement R : ordinaryParameterLocalization R) - b R)
  rw [parameterElement_coe]
  have h := (actual_inverse_parameter_multiplication_table R).2.1
  linear_combination h

theorem b_squared : bElement R ^ 2 =
    (1 - parameterElement R) * (aElement R - parameterElement R * denominatorElement R) := by
  apply Subtype.val_injective
  change b R ^ 2 = (1 - (parameterElement R : ordinaryParameterLocalization R)) *
    (a R - (parameterElement R : ordinaryParameterLocalization R) *
      (1 - (parameterElement R : ordinaryParameterLocalization R) - b R))
  rw [parameterElement_coe]
  have h := (actual_inverse_parameter_multiplication_table R).2.2
  linear_combination h

theorem two_generator_unit_ideal : Ideal.span
    ({parameterElement R,denominatorElement R} : Set (candidateAlgebra R)) = ⊤ := by
  let I : Ideal (candidateAlgebra R) := Ideal.span {parameterElement R,denominatorElement R}
  have hs : parameterElement R ∈ I := Ideal.subset_span (by simp)
  have hd : denominatorElement R ∈ I := Ideal.subset_span (by simp)
  have hb : 1 - bElement R ∈ I := by
    have h := I.add_mem hd hs
    convert h using 1 <;> dsimp only [denominatorElement] <;> ring
  have ha : aElement R ∈ I := by
    have hab : aElement R * bElement R ∈ I := by rw [a_mul_b];exact I.mul_mem_left _ hd
    have h := I.add_mem hab (I.mul_mem_left (aElement R) hb)
    convert h using 1 <;> ring
  have hb2 : bElement R ^ 2 ∈ I := by
    rw [b_squared]
    exact I.mul_mem_left _ (I.sub_mem ha (I.mul_mem_left _ hd))
  have hone : (1 : candidateAlgebra R) ∈ I := by
    have h := I.add_mem hb2 (I.mul_mem_right (1 + bElement R) hb)
    convert h using 1 <;> ring
  exact I.eq_top_of_isUnit_mem hone isUnit_one

theorem two_principal_open_cover : PrimeSpectrum.basicOpen (parameterElement R) ⊔
    PrimeSpectrum.basicOpen (denominatorElement R) = ⊤ := by
  have h := PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr (two_generator_unit_ideal R)
  simpa only [iSup_insert,iSup_singleton] using h

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.a_mul_b
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.b_squared
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.two_principal_open_cover

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual ordinary mixed quadratic ring maps to any
R-algebra carrying a pair satisfying its literal equation.
Named downstream consumer: inverse maps of the mixed single-section
parameter and adjusted principal-localization equivalences.
-/

noncomputable section
namespace MazurTransfer.Order13MixedQuadraticOrdinarySolutions
open Polynomial MixedQuadraticCoordinateJacobian Order13MixedQuadraticJacobianCertificates
open Order13MixedQuadraticPolynomialEvaluations Order13DyadicMixedQuadraticCharts
open Order13MixedQuadraticOverlapCoordinates
universe u v
variable (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
variable (x y : A) (h : y ^ 2 + (x ^ 3 + x ^ 2 + 1) * y - x * (x + 1) = 0)

def solutionToAlgHom : ordinaryCoordinateRing R →ₐ[R] A :=
  AdjoinRoot.liftAlgHom (equation R (ordinaryH R) (ordinaryF R)) (aeval x) y (by
    change eval₂ (aeval x).toRingHom y
      (X ^ 2 + C (ordinaryH R) * X - C (ordinaryF R)) = 0
    simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
    rw [map_ordinaryH R _,map_ordinaryF R _]
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
    exact h)

theorem solutionToAlgHom_x : solutionToAlgHom R A x y h (xCoordinate R) = x := by
  simp only [solutionToAlgHom, xCoordinate, AdjoinRoot.liftAlgHom_of, aeval_X]
theorem solutionToAlgHom_y : solutionToAlgHom R A x y h (yCoordinate R) = y :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

end MazurTransfer.Order13MixedQuadraticOrdinarySolutions
#print axioms MazurTransfer.Order13MixedQuadraticOrdinarySolutions.solutionToAlgHom

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal inverse-parameter algebra localized at s=1/t
is isomorphic to the actual ordinary t-localization, with the inclusion and
coefficient maps retained. Named downstream consumer: the ordinary chart of
the second finite curve chart in single-section FiniteMapData.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticOrdinarySolutions
open Order13MixedInverseParameterPolynomialIdentities
open Order13MixedSingleSectionPolynomialIdentities (t p)

variable (R : Type u) [CommRing R]

abbrev sElement := parameterElement R
abbrev parameterLocalization := Localization.Away (sElement R)

def inclusion : candidateAlgebra R →ₐ[R] ordinaryParameterLocalization R where
  __ := (candidateAlgebra R).val.toRingHom
  commutes' r := by change aeval (s R) (C r) = _; exact aeval_C _ _

theorem inclusion_sElement : inclusion R (sElement R) = s R := by
  change aeval (s R) X = s R
  exact aeval_X _

theorem s_isUnit : IsUnit (s R) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (t R),?_⟩
  rw [mul_comm]
  exact IsLocalization.Away.mul_invSelf (t R)

def localizedInclusion : parameterLocalization R →ₐ[R] ordinaryParameterLocalization R :=
  IsLocalization.Away.liftAlgHom (sElement R) (f := inclusion R)
    (by rw [inclusion_sElement]; exact s_isUnit R)

theorem localizedInclusion_algebraMap (c : candidateAlgebra R) :
    localizedInclusion R (algebraMap (candidateAlgebra R) (parameterLocalization R) c) =
      (c : ordinaryParameterLocalization R) := by
  simp [localizedInclusion, IsLocalization.Away.liftAlgHom, IsLocalization.Away.lift_eq,
    inclusion]

theorem localizedInclusion_injective : Function.Injective (localizedInclusion R) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (sElement R))
    (localizedInclusion R).toRingHom).mpr
  intro x y
  change algebraMap (candidateAlgebra R) (parameterLocalization R) x =
    algebraMap (candidateAlgebra R) (parameterLocalization R) y ↔
    localizedInclusion R (algebraMap (candidateAlgebra R) (parameterLocalization R) x) =
    localizedInclusion R (algebraMap (candidateAlgebra R) (parameterLocalization R) y)
  rw [localizedInclusion_algebraMap,localizedInclusion_algebraMap]
  constructor
  · intro h
    have H := congrArg (localizedInclusion R) h
    simpa only [localizedInclusion_algebraMap] using H
  · intro h
    exact congrArg (algebraMap (candidateAlgebra R) (parameterLocalization R)) (Subtype.ext h)

theorem localizedInclusion_invSelf :
    localizedInclusion R (IsLocalization.Away.invSelf (sElement R)) =
      algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (t R) := by
  apply (s_isUnit R).mul_right_inj.mp
  calc
    _ = localizedInclusion R (algebraMap (candidateAlgebra R) (parameterLocalization R)
      (sElement R) * IsLocalization.Away.invSelf (sElement R)) := by
      rw [map_mul, localizedInclusion_algebraMap]
      change s R * _ = aeval (s R) X * _
      rw [aeval_X]
    _ = 1 := by rw [IsLocalization.Away.mul_invSelf,map_one]
    _ = _ := by rw [mul_comm]; exact (IsLocalization.Away.mul_invSelf (t R)).symm

def recoveredX : parameterLocalization R :=
  algebraMap (candidateAlgebra R) (parameterLocalization R) (aElement R) *
    IsLocalization.Away.invSelf (sElement R)
def recoveredY : parameterLocalization R := IsLocalization.Away.invSelf (sElement R) -
  recoveredX R ^ 3 - recoveredX R ^ 2 - 1

theorem localizedInclusion_recoveredX : localizedInclusion R (recoveredX R) =
    algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (xCoordinate R) := by
  rw [recoveredX,map_mul,localizedInclusion_algebraMap,localizedInclusion_invSelf]
  change a R * algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (t R) = _
  have ht := IsLocalization.Away.mul_invSelf (t R) (S := ordinaryParameterLocalization R)
  dsimp [a,p,s]
  rw [map_mul]
  calc
    _ = algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (xCoordinate R) *
      (algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (t R) *
        IsLocalization.Away.invSelf (t R)) ^ 2 := by ring
    _ = _ := by rw [ht]; simp

theorem localizedInclusion_recoveredY : localizedInclusion R (recoveredY R) =
    algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (yCoordinate R) := by
  rw [recoveredY,map_sub,map_sub,map_sub,map_pow,map_pow,map_one,
    localizedInclusion_invSelf,localizedInclusion_recoveredX]
  simp only [t,map_add,map_pow,map_one]
  ring

theorem recovered_equation : recoveredY R ^ 2 +
    (recoveredX R ^ 3 + recoveredX R ^ 2 + 1) * recoveredY R -
    recoveredX R * (recoveredX R + 1) = 0 := by
  apply localizedInclusion_injective R
  simp only [map_add,map_sub,map_mul,map_pow,map_one,map_zero,
    localizedInclusion_recoveredX,localizedInclusion_recoveredY]
  have h := congrArg (algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R))
    (ordinary_relation R)
  simp only [map_add,map_sub,map_mul,map_pow,map_one,map_zero] at h
  exact h

def inverseOnOrdinary : ordinaryCoordinateRing R →ₐ[R] parameterLocalization R :=
  solutionToAlgHom R (parameterLocalization R) (recoveredX R) (recoveredY R) (recovered_equation R)

theorem inverseOnOrdinary_x : inverseOnOrdinary R (xCoordinate R) = recoveredX R :=
  solutionToAlgHom_x R _ _ _ _
theorem inverseOnOrdinary_y : inverseOnOrdinary R (yCoordinate R) = recoveredY R :=
  solutionToAlgHom_y R _ _ _ _
theorem inverseOnOrdinary_t : inverseOnOrdinary R (t R) =
    IsLocalization.Away.invSelf (sElement R) := by
  simp only [t,map_add,map_pow,map_one,
    inverseOnOrdinary_x,inverseOnOrdinary_y]
  rw [recoveredY]
  ring

def inverseLocalizedInclusion : ordinaryParameterLocalization R →ₐ[R] parameterLocalization R :=
  IsLocalization.Away.liftAlgHom (t R) (f := inverseOnOrdinary R) (by
    rw [inverseOnOrdinary_t]
    apply isUnit_iff_exists_inv.mpr
    refine ⟨algebraMap (candidateAlgebra R) (parameterLocalization R) (sElement R),?_⟩
    rw [mul_comm]
    exact IsLocalization.Away.mul_invSelf (sElement R))

theorem inverseLocalizedInclusion_algebraMap (z : ordinaryCoordinateRing R) :
    inverseLocalizedInclusion R (algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) z) =
      inverseOnOrdinary R z := by
  simp [inverseLocalizedInclusion,IsLocalization.Away.liftAlgHom,IsLocalization.Away.lift_eq]

theorem localizedInclusion_comp_inverseOnOrdinary :
    (localizedInclusion R).comp (inverseOnOrdinary R) =
      IsScalarTower.toAlgHom R (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change localizedInclusion R (inverseOnOrdinary R (xCoordinate R)) = _
    rw [inverseOnOrdinary_x,localizedInclusion_recoveredX]
    rfl
  · change localizedInclusion R (inverseOnOrdinary R (yCoordinate R)) = _
    rw [inverseOnOrdinary_y,localizedInclusion_recoveredY]
    rfl

theorem localizedInclusion_inverseLocalizedInclusion :
    (localizedInclusion R).comp (inverseLocalizedInclusion R) =
      AlgHom.id R (ordinaryParameterLocalization R) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (t R))
  apply RingHom.ext
  intro z
  change localizedInclusion R (inverseLocalizedInclusion R
    (algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) z)) = _
  rw [inverseLocalizedInclusion_algebraMap]
  exact DFunLike.congr_fun (localizedInclusion_comp_inverseOnOrdinary R) z

theorem inverseLocalizedInclusion_localizedInclusion :
    (inverseLocalizedInclusion R).comp (localizedInclusion R) =
      AlgHom.id R (parameterLocalization R) := by
  apply AlgHom.ext
  intro z
  apply localizedInclusion_injective R
  exact DFunLike.congr_fun (localizedInclusion_inverseLocalizedInclusion R) (localizedInclusion R z)

def parameterLocalizationEquiv : parameterLocalization R ≃ₐ[R] ordinaryParameterLocalization R :=
  AlgEquiv.ofAlgHom (localizedInclusion R) (inverseLocalizedInclusion R)
    (localizedInclusion_inverseLocalizedInclusion R) (inverseLocalizedInclusion_localizedInclusion R)

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.parameterLocalizationEquiv

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual polynomial identities and a two-principal-open cover
of the inverse finite coordinate algebra. Named downstream consumer: recover
reciprocal coordinates on the positive-infinity chart of FiniteMapData.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open AlgebraicGeometry Polynomial
open Order13MixedInverseParameterPolynomialIdentities
variable (R : Type u) [CommRing R]

def infinityLinearElement : candidateAlgebra R := 1 - sElement R - bElement R
def infinityRootElement : candidateAlgebra R := infinityLinearElement R - aElement R ^ 2
def infinityPatchElement : candidateAlgebra R := infinityRootElement R * infinityLinearElement R

theorem candidate_multiplication_table :
    aElement R ^ 2 = sElement R * bElement R - sElement R ^ 2 * aElement R ∧
    aElement R * bElement R = sElement R - sElement R ^ 2 - sElement R * bElement R ∧
    bElement R ^ 2 = (1 - sElement R) * aElement R +
      (sElement R - sElement R ^ 2) * bElement R +
      (2 * sElement R ^ 2 - sElement R ^ 3 - sElement R) := by
  have h := actual_inverse_parameter_multiplication_table R
  refine ⟨?_,?_,?_⟩ <;> apply Subtype.val_injective
  · change a R ^ 2 = aeval (s R) X * b R - aeval (s R) X ^ 2 * a R
    simpa only [aeval_X] using h.1
  · change a R * b R = aeval (s R) X - aeval (s R) X ^ 2 - aeval (s R) X * b R
    simpa only [aeval_X] using h.2.1
  · change b R ^ 2 = (1 - aeval (s R) X) * a R +
      (aeval (s R) X - aeval (s R) X ^ 2) * b R +
      (2 * aeval (s R) X ^ 2 - aeval (s R) X ^ 3 - aeval (s R) X)
    simp only [aeval_X]
    linear_combination h.2.2

theorem a_mul_b_linear : aElement R * bElement R = sElement R * infinityLinearElement R := by
  have h := (candidate_multiplication_table R).2.1
  dsimp [infinityLinearElement]
  linear_combination h

theorem b_squared_linear : bElement R ^ 2 =
    (aElement R + sElement R ^ 2) * infinityLinearElement R := by
  have h2 := (candidate_multiplication_table R).2.1
  have h3 := (candidate_multiplication_table R).2.2
  dsimp [infinityLinearElement]
  linear_combination h3 + h2

theorem s_squared_mul_root : sElement R ^ 2 * infinityRootElement R = aElement R ^ 3 := by
  have h1 := (candidate_multiplication_table R).1
  have h2 := (candidate_multiplication_table R).2.1
  dsimp [infinityRootElement,infinityLinearElement]
  linear_combination -(aElement R) * h1 - sElement R * h2

theorem b_squared_mul_root : bElement R ^ 2 * infinityRootElement R =
    aElement R * infinityLinearElement R ^ 2 := by
  have h1 := b_squared_linear R
  have h2 := s_squared_mul_root R
  dsimp [infinityRootElement] at h2 ⊢
  linear_combination (infinityLinearElement R - aElement R ^ 2) * h1 +
    infinityLinearElement R * h2

theorem s_mem_prime_forces_a_b 
    (p : PrimeSpectrum (candidateAlgebra R)) (hs : sElement R ∈ p.asIdeal) :
    aElement R ∈ p.asIdeal ∧ bElement R ∈ p.asIdeal := by
  have ha2 : aElement R ^ 2 ∈ p.asIdeal := by
    rw [(candidate_multiplication_table R).1]
    exact p.asIdeal.sub_mem (p.asIdeal.mul_mem_right _ hs)
      (p.asIdeal.mul_mem_right _ (p.asIdeal.pow_mem_of_mem hs 2 (by decide)))
  have ha := p.isPrime.mem_of_pow_mem 2 ha2
  have hb2 : bElement R ^ 2 ∈ p.asIdeal := by
    rw [b_squared_linear]
    exact p.asIdeal.mul_mem_right _ (p.asIdeal.add_mem ha
      (p.asIdeal.pow_mem_of_mem hs 2 (by decide)))
  exact ⟨ha, p.isPrime.mem_of_pow_mem 2 hb2⟩

theorem s_mem_prime_forces_patch_nonmem 
    (p : PrimeSpectrum (candidateAlgebra R)) (hs : sElement R ∈ p.asIdeal) :
    infinityPatchElement R ∉ p.asIdeal := by
  obtain ⟨ha,hb⟩ := s_mem_prime_forces_a_b R p hs
  have hc : sElement R + bElement R ∈ p.asIdeal :=
    p.asIdeal.add_mem hs hb
  have hl : infinityLinearElement R ∉ p.asIdeal := by
    intro h
    have h1 := p.asIdeal.add_mem h hc
    have he : infinityLinearElement R + (sElement R + bElement R) = 1 := by
      dsimp [infinityLinearElement]; ring
    rw [he] at h1
    exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem h1 isUnit_one)
  have hr : infinityRootElement R ∉ p.asIdeal := by
    intro h
    have h1 := p.asIdeal.add_mem h (p.asIdeal.pow_mem_of_mem ha 2 (by decide))
    change infinityLinearElement R - aElement R ^ 2 + aElement R ^ 2 ∈ p.asIdeal at h1
    rw [sub_add_cancel] at h1
    exact hl h1
  intro h
  exact (p.isPrime.mem_or_mem h).elim hr hl

theorem inverse_candidate_two_principal_open_cover  :
    PrimeSpectrum.basicOpen (sElement R) ⊔ PrimeSpectrum.basicOpen (infinityPatchElement R) = ⊤ := by
  apply SetLike.ext
  intro p
  change (sElement R ∉ p.asIdeal ∨ infinityPatchElement R ∉ p.asIdeal) ↔ True
  constructor
  · intro _; trivial
  · intro _
    by_cases hs : sElement R ∈ p.asIdeal
    · exact Or.inr (s_mem_prime_forces_patch_nonmem R p hs)
    · exact Or.inl hs

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.b_squared_mul_root
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.inverse_candidate_two_principal_open_cover

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual regular inverse-parameter coordinates on a literal
reciprocal principal-open neighborhood of the positive infinity section.
Named downstream consumer: the positive-infinity chart isomorphism of the
second finite chart in single-section FiniteMapData. No isomorphism is assumed.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterPositiveReciprocalPatch
open Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticInfinitySections
variable (R : Type u) [CommRing R]

def f : reciprocalCoordinateRing R := wCoordinate R + (1 + zCoordinate R + zCoordinate R ^ 3)
def g : reciprocalCoordinateRing R := f R + zCoordinate R ^ 4
abbrev PatchRing := Localization.Away (f R * g R)
def z : PatchRing R := algebraMap (reciprocalCoordinateRing R) (PatchRing R) (zCoordinate R)
def w : PatchRing R := algebraMap (reciprocalCoordinateRing R) (PatchRing R) (wCoordinate R)
def F : PatchRing R := algebraMap (reciprocalCoordinateRing R) (PatchRing R) (f R)
def G : PatchRing R := algebraMap (reciprocalCoordinateRing R) (PatchRing R) (g R)
def r : PatchRing R := G R * IsLocalization.Away.invSelf (f R * g R)

theorem F_mul_r : F R * r R = 1 := by
  rw [r,← mul_assoc]
  change algebraMap (reciprocalCoordinateRing R) (PatchRing R) (f R) *
    algebraMap (reciprocalCoordinateRing R) (PatchRing R) (g R) * _ = 1
  rw [← map_mul,IsLocalization.Away.mul_invSelf]

theorem r_isUnit : IsUnit (r R) := by
  apply isUnit_iff_exists_inv.mpr
  exact ⟨F R,by rw [mul_comm];exact F_mul_r R⟩

theorem F_mul_G_isUnit : IsUnit (F R * G R) := by
  change IsUnit (algebraMap (reciprocalCoordinateRing R) (PatchRing R) (f R) *
    algebraMap (reciprocalCoordinateRing R) (PatchRing R) (g R))
  rw [← map_mul]
  exact IsLocalization.Away.algebraMap_isUnit (f R * g R)

theorem G_isUnit : IsUnit (G R) := isUnit_of_mul_isUnit_right (F_mul_G_isUnit R)

theorem F_equation : F R ^ 2 - (1 + z R + z R ^ 3) * F R -
    z R ^ 4 * (1 + z R) = 0 := by
  have h := congrArg (algebraMap (reciprocalCoordinateRing R) (PatchRing R)) (reciprocal_relation R)
  simp only [map_mul,map_add,map_sub,map_pow,map_one,map_zero] at h
  have he : F R = w R + (1 + z R + z R ^ 3) := by
    simp only [F,f,w,z,map_add,map_pow,map_one]
  rw [he]
  change w R ^ 2 + (1 + z R + z R ^ 3) * w R - (z R ^ 4 + z R ^ 5) = 0 at h
  linear_combination h

theorem inverse_profile : 1 = (1 + z R + z R ^ 3) * r R +
    z R ^ 4 * (1 + z R) * r R ^ 2 := by
  have hF := F_equation R
  have hFr := F_mul_r R
  linear_combination r R ^ 2 * hF -
    (F R * r R + 1 - (1 + z R + z R ^ 3) * r R) * hFr

def s : PatchRing R := z R ^ 3 * r R
def a : PatchRing R := z R ^ 2 * r R
def b : PatchRing R := z R * r R + z R ^ 5 * r R ^ 2

theorem root_profile : 1 - s R - b R - a R ^ 2 = r R := by
  have h := inverse_profile R
  dsimp [s,a,b]
  linear_combination h

theorem linear_profile : 1 - s R - b R = r R ^ 2 * G R := by
  have h := root_profile R
  have hFr := F_mul_r R
  have hG : G R = F R + z R ^ 4 := by
    simp only [G,g,map_add,map_mul,map_pow,_root_.map_ofNat]
    rfl
  rw [hG]
  dsimp [a] at h
  linear_combination h - r R * hFr

theorem root_times_linear_isUnit :
    IsUnit ((1 - s R - b R - a R ^ 2) * (1 - s R - b R)) := by
  rw [root_profile,linear_profile]
  exact (r_isUnit R).mul (((r_isUnit R).pow 2).mul (G_isUnit R))

theorem inverse_parameter_multiplication_table :
    a R ^ 2 = s R * b R - s R ^ 2 * a R ∧
    a R * b R = s R - s R ^ 2 - s R * b R ∧
    b R ^ 2 = (1 - s R) * a R + (s R - s R ^ 2) * b R +
      (2 * s R ^ 2 - s R ^ 3 - s R) := by
  have hab : a R * b R = s R - s R ^ 2 - s R * b R := by
    have h := inverse_profile R
    dsimp [s,a,b]
    linear_combination -(z R ^ 3 * r R) * h
  have hb : b R ^ 2 = (a R + s R ^ 2) * (1 - s R - b R) := by
    have h := root_profile R
    have he : 1 - s R - b R = r R + a R ^ 2 := by linear_combination h
    rw [he]
    dsimp [s,a,b]
    ring
  refine ⟨?_,hab,?_⟩
  · dsimp [s,a,b];ring
  · linear_combination hb - hab

theorem positive_infinity_denominator : infinityPointZero R (f R * g R) = 1 := by
  have hz : infinityPointZero R (zCoordinate R) = 0 := by
    simp only [infinityPointZero,zCoordinate,AdjoinRoot.liftAlgHom_of,aeval_X]
  have hw : infinityPointZero R (wCoordinate R) = 0 := AdjoinRoot.liftAlgHom_root _ _ _ _
  simp only [f,g,map_mul,map_add,map_one,map_pow,hz,hw]
  ring

theorem negative_infinity_denominator : infinityPointNegOne R (f R * g R) = 0 := by
  have hz : infinityPointNegOne R (zCoordinate R) = 0 := by
    simp only [infinityPointNegOne,zCoordinate,AdjoinRoot.liftAlgHom_of,aeval_X]
  have hw : infinityPointNegOne R (wCoordinate R) = -1 := AdjoinRoot.liftAlgHom_root _ _ _ _
  simp only [f,g,map_mul,map_add,map_one,map_pow,hz,hw]
  ring

end MazurTransfer.Order13MixedInverseParameterPositiveReciprocalPatch
#print axioms MazurTransfer.Order13MixedInverseParameterPositiveReciprocalPatch.inverse_parameter_multiplication_table
#print axioms MazurTransfer.Order13MixedInverseParameterPositiveReciprocalPatch.root_times_linear_isUnit
#print axioms MazurTransfer.Order13MixedInverseParameterPositiveReciprocalPatch.positive_infinity_denominator

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: recover literal reciprocal z,w on the positive-infinity
localization of the actual inverse finite algebra and construct its actual
reciprocal-patch map. Named downstream consumer: the second chart comparison
for single-section FiniteMapData. Bijectivity is a separate obligation.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open MixedQuadraticCoordinateJacobian Order13MixedQuadraticJacobianCertificates
open Order13MixedQuadraticPolynomialEvaluations
variable (R : Type u) [CommRing R]

abbrev infinityLocalization := Localization.Away (infinityPatchElement R)
def infinityS : infinityLocalization R := algebraMap (candidateAlgebra R) (infinityLocalization R) (sElement R)
def infinityA : infinityLocalization R := algebraMap (candidateAlgebra R) (infinityLocalization R) (aElement R)
def infinityB : infinityLocalization R := algebraMap (candidateAlgebra R) (infinityLocalization R) (bElement R)
def infinityH : infinityLocalization R := algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityRootElement R)
def infinityL : infinityLocalization R := algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityLinearElement R)
def infinityHInverse : infinityLocalization R := infinityL R * IsLocalization.Away.invSelf (infinityPatchElement R)
def infinityLInverse : infinityLocalization R := infinityH R * IsLocalization.Away.invSelf (infinityPatchElement R)

theorem infinityH_mul_inverse : infinityH R * infinityHInverse R = 1 := by
  rw [infinityHInverse,← mul_assoc]
  change algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityRootElement R) *
    algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityLinearElement R) * _ = 1
  rw [← map_mul]
  exact IsLocalization.Away.mul_invSelf (infinityPatchElement R)

theorem infinityL_mul_inverse : infinityL R * infinityLInverse R = 1 := by
  rw [infinityLInverse,← mul_assoc,mul_comm (infinityL R) (infinityH R)]
  change algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityRootElement R) *
    algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityLinearElement R) * _ = 1
  rw [← map_mul]
  exact IsLocalization.Away.mul_invSelf (infinityPatchElement R)

theorem infinityH_isUnit : IsUnit (infinityH R) :=
  isUnit_iff_exists_inv.mpr ⟨infinityHInverse R,infinityH_mul_inverse R⟩
theorem infinityL_isUnit : IsUnit (infinityL R) :=
  isUnit_iff_exists_inv.mpr ⟨infinityLInverse R,infinityL_mul_inverse R⟩

theorem infinity_H_eq_L_sub : infinityH R = infinityL R - infinityA R ^ 2 := by
  simp only [infinityH,infinityRootElement,map_sub,map_mul,map_pow,_root_.map_ofNat,infinityL,infinityA]

theorem infinity_L_profile : infinityL R = 1 - infinityS R - infinityB R := by
  simp only [infinityL,infinityLinearElement,map_sub,map_mul,map_one,_root_.map_ofNat,infinityS,infinityB]

theorem infinity_A_B : infinityA R * infinityB R = infinityS R * infinityL R := by
  simpa only [map_mul,_root_.map_ofNat,infinityA,infinityB,infinityS,infinityL] using
    congrArg (algebraMap (candidateAlgebra R) (infinityLocalization R)) (a_mul_b_linear R)

theorem infinity_B_squared_H : infinityB R ^ 2 * infinityH R = infinityA R * infinityL R ^ 2 := by
  simpa only [map_mul,map_pow,_root_.map_ofNat,infinityA,infinityB,infinityH,infinityL] using
    congrArg (algebraMap (candidateAlgebra R) (infinityLocalization R)) (b_squared_mul_root R)

def infinityRecoveredZ : infinityLocalization R := infinityB R * infinityLInverse R
def infinityRecoveredF : infinityLocalization R := infinityHInverse R
def infinityRecoveredW : infinityLocalization R := infinityRecoveredF R -
  (1 + infinityRecoveredZ R + infinityRecoveredZ R ^ 3)

theorem recoveredZ_mul_L : infinityRecoveredZ R * infinityL R = infinityB R := by
  have h := infinityL_mul_inverse R
  dsimp [infinityRecoveredZ]
  linear_combination (infinityB R) * h

theorem H_mul_recoveredF : infinityH R * infinityRecoveredF R = 1 := by
  rw [infinityRecoveredF]
  linear_combination infinityH_mul_inverse R

theorem recoveredZ_mul_A : infinityRecoveredZ R * infinityA R = infinityS R := by
  apply (infinityL_isUnit R).mul_right_inj.mp
  have hz := recoveredZ_mul_L R
  have hab := infinity_A_B R
  linear_combination infinityA R * hz + hab

theorem recoveredZ_squared_H : infinityRecoveredZ R ^ 2 * infinityH R = infinityA R := by
  apply ((infinityL_isUnit R).pow 2).mul_right_inj.mp
  have hz := recoveredZ_mul_L R
  have h := infinity_B_squared_H R
  linear_combination h +
    infinityH R * (infinityRecoveredZ R * infinityL R + infinityB R) * hz

theorem recoveredZ_cubed_H : infinityRecoveredZ R ^ 3 * infinityH R = infinityS R := by
  have h2 := recoveredZ_squared_H R
  have ha := recoveredZ_mul_A R
  linear_combination infinityRecoveredZ R * h2 + ha

theorem recoveredZ_fourth_H_squared : infinityRecoveredZ R ^ 4 * infinityH R ^ 2 = infinityA R ^ 2 := by
  have h := recoveredZ_squared_H R
  linear_combination (infinityRecoveredZ R ^ 2 * infinityH R + infinityA R) * h

theorem recovered_inverse_profile :
    (1 + infinityRecoveredZ R + infinityRecoveredZ R ^ 3) * infinityH R +
      infinityRecoveredZ R ^ 4 * (1 + infinityRecoveredZ R) * infinityH R ^ 2 = 1 := by
  have hz := recoveredZ_mul_L R
  have h3 := recoveredZ_cubed_H R
  have h4 := recoveredZ_fourth_H_squared R
  have hh := infinity_H_eq_L_sub R
  have hl := infinity_L_profile R
  linear_combination hz + h3 + (1 + infinityRecoveredZ R) * h4 +
    (1 + infinityRecoveredZ R) * hh + hl

theorem recoveredF_equation : infinityRecoveredF R ^ 2 -
    (1 + infinityRecoveredZ R + infinityRecoveredZ R ^ 3) * infinityRecoveredF R -
      infinityRecoveredZ R ^ 4 * (1 + infinityRecoveredZ R) = 0 := by
  have h := MazurTransfer.mixed_inverse_parameter_reciprocal_recovery
    (infinityS R) (infinityA R) (infinityB R) (infinityH R) (infinityL R)
    (infinityHInverse R) (infinityLInverse R)
    (infinity_H_eq_L_sub R) (infinity_L_profile R) (infinity_A_B R) (infinity_B_squared_H R)
    (infinityH_mul_inverse R) (infinityL_mul_inverse R)
  simpa only [infinityRecoveredZ,infinityRecoveredF] using h.2.2.2.1

theorem recovered_reciprocal_equation : infinityRecoveredW R ^ 2 +
    (1 + infinityRecoveredZ R + infinityRecoveredZ R ^ 3) * infinityRecoveredW R -
    (infinityRecoveredZ R ^ 4 + infinityRecoveredZ R ^ 5) = 0 := by
  have h := MazurTransfer.mixed_inverse_parameter_reciprocal_recovery
    (infinityS R) (infinityA R) (infinityB R) (infinityH R) (infinityL R)
    (infinityHInverse R) (infinityLInverse R)
    (infinity_H_eq_L_sub R) (infinity_L_profile R) (infinity_A_B R) (infinity_B_squared_H R)
    (infinityH_mul_inverse R) (infinityL_mul_inverse R)
  simpa only [infinityRecoveredW,infinityRecoveredZ,infinityRecoveredF] using h.2.2.2.2

def recoveredReciprocalBase : reciprocalCoordinateRing R →ₐ[R] infinityLocalization R :=
  AdjoinRoot.liftAlgHom (equation R (reciprocalH R) (reciprocalF R))
    (aeval (infinityRecoveredZ R)) (infinityRecoveredW R) (by
      change eval₂ (aeval (infinityRecoveredZ R)).toRingHom (infinityRecoveredW R)
        (X ^ 2 + C (reciprocalH R) * X - C (reciprocalF R)) = 0
      simp only [eval₂_sub,eval₂_add,eval₂_mul,eval₂_pow,eval₂_X,eval₂_C]
      rw [map_reciprocalH R _,map_reciprocalF R _]
      simp only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,aeval_X]
      exact recovered_reciprocal_equation R)

theorem recoveredReciprocalBase_z : recoveredReciprocalBase R (zCoordinate R) = infinityRecoveredZ R := by
  simp only [recoveredReciprocalBase,zCoordinate,AdjoinRoot.liftAlgHom_of,aeval_X]
theorem recoveredReciprocalBase_w : recoveredReciprocalBase R (wCoordinate R) = infinityRecoveredW R := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

theorem recoveredReciprocalBase_f :
    recoveredReciprocalBase R (Order13MixedInverseParameterPositiveReciprocalPatch.f R) = infinityRecoveredF R := by
  simp only [Order13MixedInverseParameterPositiveReciprocalPatch.f,map_add,map_pow,map_one,
    recoveredReciprocalBase_w,recoveredReciprocalBase_z,infinityRecoveredW]
  ring

theorem recoveredReciprocalBase_g_H_squared :
    recoveredReciprocalBase R (Order13MixedInverseParameterPositiveReciprocalPatch.g R) * infinityH R ^ 2 =
      infinityL R := by
  rw [Order13MixedInverseParameterPositiveReciprocalPatch.g,map_add,
    map_pow,recoveredReciprocalBase_f,recoveredReciprocalBase_z]
  have hf := H_mul_recoveredF R
  have hz := recoveredZ_fourth_H_squared R
  have hh := infinity_H_eq_L_sub R
  linear_combination infinityH R * hf + hz + hh

theorem recoveredReciprocalBase_denominator_isUnit :
    IsUnit (recoveredReciprocalBase R
      (Order13MixedInverseParameterPositiveReciprocalPatch.f R * Order13MixedInverseParameterPositiveReciprocalPatch.g R)) := by
  have hf : IsUnit (infinityRecoveredF R) := by
    have hh : IsUnit (infinityH R * infinityRecoveredF R) := by rw [H_mul_recoveredF];exact isUnit_one
    exact isUnit_of_mul_isUnit_right hh
  have hg : IsUnit (recoveredReciprocalBase R (Order13MixedInverseParameterPositiveReciprocalPatch.g R)) := by
    have hh : IsUnit (recoveredReciprocalBase R (Order13MixedInverseParameterPositiveReciprocalPatch.g R) * infinityH R ^ 2) := by
      rw [recoveredReciprocalBase_g_H_squared]
      exact infinityL_isUnit R
    exact isUnit_of_mul_isUnit_left hh
  rw [map_mul,recoveredReciprocalBase_f]
  exact hf.mul hg

def recoveredReciprocalPatch  :
    Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R →ₐ[R] infinityLocalization R :=
  IsLocalization.Away.liftAlgHom
    (Order13MixedInverseParameterPositiveReciprocalPatch.f R * Order13MixedInverseParameterPositiveReciprocalPatch.g R)
    (f := recoveredReciprocalBase R) (recoveredReciprocalBase_denominator_isUnit R)

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.recoveredReciprocalPatch
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.recovered_reciprocal_equation

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: exact regular inverse-parameter images under the actual
positive reciprocal-patch map into the inverse finite coordinate algebra.
Named downstream consumer: surjectivity and the second-chart isomorphism
for single-section FiniteMapData. Injectivity remains separate.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedInverseParameterPositiveReciprocalPatch
variable (R : Type u) [CommRing R]

theorem recoveredReciprocalPatch_algebraMap  (q : reciprocalCoordinateRing R) :
    recoveredReciprocalPatch R (algebraMap (reciprocalCoordinateRing R) (PatchRing R) q) =
      recoveredReciprocalBase R q := by
  simp [recoveredReciprocalPatch,IsLocalization.Away.liftAlgHom,IsLocalization.Away.lift_eq]

theorem recoveredReciprocalPatch_z  :
    recoveredReciprocalPatch R (z R) = infinityRecoveredZ R :=
  (recoveredReciprocalPatch_algebraMap R _).trans (recoveredReciprocalBase_z R)
theorem recoveredReciprocalPatch_F  :
    recoveredReciprocalPatch R (F R) = infinityRecoveredF R :=
  (recoveredReciprocalPatch_algebraMap R _).trans (recoveredReciprocalBase_f R)

theorem recoveredReciprocalPatch_r  :
    recoveredReciprocalPatch R (r R) = infinityH R := by
  have hu : IsUnit (infinityRecoveredF R) := by
    have h := (isUnit_of_mul_isUnit_left (F_mul_G_isUnit R)).map (recoveredReciprocalPatch R)
    rwa [recoveredReciprocalPatch_F] at h
  apply hu.mul_right_inj.mp
  have h := congrArg (recoveredReciprocalPatch R) (F_mul_r R)
  rw [map_mul,map_one,recoveredReciprocalPatch_F] at h
  linear_combination h - H_mul_recoveredF R

theorem recoveredReciprocalPatch_s  :
    recoveredReciprocalPatch R (s R) = infinityS R := by
  rw [s,map_mul,map_pow,recoveredReciprocalPatch_z]
  have hr := recoveredReciprocalPatch_r R
  have hz := recoveredZ_cubed_H R
  linear_combination infinityRecoveredZ R ^ 3 * hr + hz

theorem recoveredReciprocalPatch_a  :
    recoveredReciprocalPatch R (a R) = infinityA R := by
  rw [a,map_mul,map_pow,recoveredReciprocalPatch_z]
  have hr := recoveredReciprocalPatch_r R
  have hz := recoveredZ_squared_H R
  linear_combination infinityRecoveredZ R ^ 2 * hr + hz

theorem recoveredReciprocalPatch_b  :
    recoveredReciprocalPatch R (b R) = infinityB R := by
  rw [b,map_add,map_mul,map_mul,map_pow,map_pow,recoveredReciprocalPatch_z]
  have hr := recoveredReciprocalPatch_r R
  have hz := recoveredZ_mul_L R
  have h4 := recoveredZ_fourth_H_squared R
  have hh := infinity_H_eq_L_sub R
  linear_combination infinityRecoveredZ R * hr +
    infinityRecoveredZ R ^ 5 * (recoveredReciprocalPatch R (r R) + infinityH R) * hr +
      hz + infinityRecoveredZ R * hh + infinityRecoveredZ R * h4

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.recoveredReciprocalPatch_s
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.recoveredReciprocalPatch_a
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.recoveredReciprocalPatch_b

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: surjectivity of the actual recovered reciprocal-patch map.
Named downstream consumer: the inverse-parameter positive-infinity chart isomorphism.
No injectivity or curve-complement identification is assumed or asserted.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open Polynomial
variable (R : Type u) [CommRing R]

theorem recoveredReciprocalPatch_polynomial_scalars  (F : Polynomial R) :
    recoveredReciprocalPatch R (aeval (Order13MixedInverseParameterPositiveReciprocalPatch.s R) F) =
      algebraMap (candidateAlgebra R) (infinityLocalization R) (algebraMap (Polynomial R) (candidateAlgebra R) F) := by
  have h : (recoveredReciprocalPatch R).comp (aeval (Order13MixedInverseParameterPositiveReciprocalPatch.s R)) =
      (IsScalarTower.toAlgHom R (candidateAlgebra R) (infinityLocalization R)).comp
        (IsScalarTower.toAlgHom R (Polynomial R) (candidateAlgebra R)) := by
    apply Polynomial.algHom_ext
    change recoveredReciprocalPatch R (aeval (Order13MixedInverseParameterPositiveReciprocalPatch.s R) X) =
      infinityS R
    rw [aeval_X,recoveredReciprocalPatch_s]
  exact DFunLike.congr_fun h F

theorem recoveredReciprocalPatch_contains_candidate  (b : candidateAlgebra R) :
    ∃ c : Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R,
      recoveredReciprocalPatch R c = algebraMap (candidateAlgebra R) (infinityLocalization R) b := by
  rcases b with ⟨b,hb⟩
  refine Algebra.adjoin_induction (R := Polynomial R)
    (p := fun x hx => ∃ c : Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R,
      recoveredReciprocalPatch R c =
        algebraMap (candidateAlgebra R) (infinityLocalization R) ⟨x,hx⟩) ?_ ?_ ?_ ?_ hb
  · intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨Order13MixedInverseParameterPositiveReciprocalPatch.a R,recoveredReciprocalPatch_a R⟩
    · exact ⟨Order13MixedInverseParameterPositiveReciprocalPatch.b R,recoveredReciprocalPatch_b R⟩
  · intro F
    exact ⟨aeval (Order13MixedInverseParameterPositiveReciprocalPatch.s R) F,
      recoveredReciprocalPatch_polynomial_scalars R F⟩
  · intro x y hx hy hcx hcy
    rcases hcx with ⟨c,hc⟩;rcases hcy with ⟨d,hd⟩
    refine ⟨c+d,?_⟩
    rw [map_add,hc,hd,← map_add]
    rfl
  · intro x y hx hy hcx hcy
    rcases hcx with ⟨c,hc⟩;rcases hcy with ⟨d,hd⟩
    refine ⟨c*d,?_⟩
    rw [map_mul,hc,hd,← map_mul]
    rfl

theorem recoveredReciprocalPatch_infinityPatchElement  :
    recoveredReciprocalPatch R
      ((1 - Order13MixedInverseParameterPositiveReciprocalPatch.s R -
        Order13MixedInverseParameterPositiveReciprocalPatch.b R -
        Order13MixedInverseParameterPositiveReciprocalPatch.a R ^ 2) *
        (1 - Order13MixedInverseParameterPositiveReciprocalPatch.s R -
          Order13MixedInverseParameterPositiveReciprocalPatch.b R)) =
      algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityPatchElement R) := by
  simp only [map_mul,map_sub,map_one,_root_.map_ofNat,map_pow,
    recoveredReciprocalPatch_s,recoveredReciprocalPatch_a,recoveredReciprocalPatch_b]
  change (1 - infinityS R - infinityB R - infinityA R ^ 2) *
    (1 - infinityS R - infinityB R) = _
  rw [← infinity_L_profile,← infinity_H_eq_L_sub]
  change algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityRootElement R) *
    algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityLinearElement R) = _
  rw [← map_mul]
  rfl

theorem recoveredReciprocalPatch_surjective  :
    Function.Surjective (recoveredReciprocalPatch R) := by
  let v : Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R :=
    ((1 - Order13MixedInverseParameterPositiveReciprocalPatch.s R -
        Order13MixedInverseParameterPositiveReciprocalPatch.b R -
        Order13MixedInverseParameterPositiveReciprocalPatch.a R ^ 2) *
        (1 - Order13MixedInverseParameterPositiveReciprocalPatch.s R -
          Order13MixedInverseParameterPositiveReciprocalPatch.b R))
  have hv : IsUnit v := Order13MixedInverseParameterPositiveReciprocalPatch.root_times_linear_isUnit R
  let vi : Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R := ↑(hv.unit⁻¹)
  have hiv : recoveredReciprocalPatch R vi *
      algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityPatchElement R) = 1 := by
    calc
      _ = recoveredReciprocalPatch R (vi * v) := by
        rw [map_mul,recoveredReciprocalPatch_infinityPatchElement]
      _ = 1 := by
        have h : vi * v = 1 := by rw [← hv.unit_spec];exact Units.inv_mul hv.unit
        rw [h,map_one]
  intro a
  obtain ⟨b,s,hs⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (infinityPatchElement R)) a
  obtain ⟨n,hn⟩ := (Submonoid.mem_powers_iff (s : candidateAlgebra R) (infinityPatchElement R)).mp s.property
  obtain ⟨c,hc⟩ := recoveredReciprocalPatch_contains_candidate R b
  refine ⟨c * vi ^ n,?_⟩
  rw [← hs]
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  rw [map_mul,map_pow,hc,← hn,map_pow]
  calc
    _ = algebraMap (candidateAlgebra R) (infinityLocalization R) b *
      (recoveredReciprocalPatch R vi *
        algebraMap (candidateAlgebra R) (infinityLocalization R) (infinityPatchElement R)) ^ n := by ring
    _ = _ := by rw [hiv,one_pow,mul_one]

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.recoveredReciprocalPatch_surjective

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the ACTUAL R[T]-subalgebra generated by p=x*t and
q=x*(p+1), with T acting by t=y+x^3+x^2+1, is finite over every commutative
coefficient ring. Named downstream consumer: the first affine chart of
single-section finite-map data for the mixed dyadic family.
Adapts the complete checked span/adjoin proof of Order13SingleSectionFiniteAlgebra,
using the integral mixed multiplication table with no invertibility of two.
Freeness and the actual complement scheme identification are separate.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open Polynomial Submodule
open Order13DyadicMixedQuadraticCharts
open Order13MixedSingleSectionPolynomialIdentities
variable (R : Type u) [CommRing R]

noncomputable def parameterMap : Polynomial R →+* ordinaryCoordinateRing R := (aeval (t R)).toRingHom
scoped instance parameterAlgebra : Algebra (Polynomial R) (ordinaryCoordinateRing R) :=
  (parameterMap R).toAlgebra
scoped instance parameterSMul : SMul (Polynomial R) (ordinaryCoordinateRing R) :=
  (parameterAlgebra R).toSMul
scoped instance parameterModule : Module (Polynomial R) (ordinaryCoordinateRing R) :=
  @Algebra.toModule (Polynomial R) (ordinaryCoordinateRing R) _ _ (parameterAlgebra R)

theorem parameter_algebraMap (s : Polynomial R) :
    algebraMap (Polynomial R) (ordinaryCoordinateRing R) s = aeval (t R) s := rfl

def generators : Set (ordinaryCoordinateRing R) := {1, p R, q R}
def spanningModule : Submodule (Polynomial R) (ordinaryCoordinateRing R) :=
  Submodule.span (Polynomial R) (generators R)
noncomputable def candidateAlgebra : Subalgebra (Polynomial R) (ordinaryCoordinateRing R) :=
  Algebra.adjoin (Polynomial R) ({p R, q R} : Set (ordinaryCoordinateRing R))

private theorem one_mem_span : (1 : ordinaryCoordinateRing R) ∈ spanningModule R :=
  Submodule.subset_span (by simp [generators])
private theorem p_mem_span : p R ∈ spanningModule R :=
  Submodule.subset_span (by simp [generators])
private theorem q_mem_span : q R ∈ spanningModule R :=
  Submodule.subset_span (by simp [generators])

private theorem p_mul_p_mem : p R * p R ∈ spanningModule R := by
  rw [← pow_two, p_squared]
  have ht : t R * q R = (X : Polynomial R) • q R := by
    simp [Algebra.smul_def, parameter_algebraMap, _root_.map_ofNat]
  rw [ht]
  exact (spanningModule R).sub_mem ((spanningModule R).smul_mem _ (q_mem_span R)) (p_mem_span R)

private theorem p_mul_q_mem : p R * q R ∈ spanningModule R := by
  rw [p_mul_q]
  have h1 : t R ^ 3 - t R ^ 2 = (X ^ 3 - X ^ 2 : Polynomial R) • (1 : ordinaryCoordinateRing R) := by
    simp [Algebra.smul_def, parameter_algebraMap, _root_.map_ofNat]
  have hq : t R * q R = (X : Polynomial R) • q R := by
    simp [Algebra.smul_def, parameter_algebraMap, _root_.map_ofNat]
  rw [h1,hq]
  exact (spanningModule R).sub_mem ((spanningModule R).smul_mem _ (one_mem_span R))
    ((spanningModule R).smul_mem _ (q_mem_span R))

private theorem q_mul_q_mem : q R * q R ∈ spanningModule R := by
  rw [← pow_two, q_squared]
  have hp : (t R ^ 2 - t R) * p R = (X ^ 2 - X : Polynomial R) • p R := by
    simp [Algebra.smul_def, parameter_algebraMap, _root_.map_ofNat]
  have hq : (t R - 1) * q R = (X - 1 : Polynomial R) • q R := by
    simp [Algebra.smul_def, parameter_algebraMap, _root_.map_ofNat]
  have hc : (2 - t R) * t R ^ 2 - t R =
      ((2-X)*X^2-X : Polynomial R) • (1 : ordinaryCoordinateRing R) := by
    simp [Algebra.smul_def, parameter_algebraMap, _root_.map_ofNat]
  rw [hp,hq,add_sub_assoc,hc]
  exact (spanningModule R).add_mem
    ((spanningModule R).add_mem ((spanningModule R).smul_mem _ (p_mem_span R))
      ((spanningModule R).smul_mem _ (q_mem_span R)))
    ((spanningModule R).smul_mem _ (one_mem_span R))

theorem spanningModule_mul_closed 
    (v w : ordinaryCoordinateRing R) (hv : v ∈ spanningModule R) (hw : w ∈ spanningModule R) :
    v * w ∈ spanningModule R := by
  have hle : spanningModule R * spanningModule R ≤ spanningModule R := by
    change span (Polynomial R) (generators R) * span (Polynomial R) (generators R) ≤ _
    rw [Submodule.span_mul_span]
    apply Submodule.span_le.mpr
    rintro z ⟨v, hv, w, hw, rfl⟩
    simp only [generators, Set.mem_insert_iff, Set.mem_singleton_iff] at hv hw
    rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
    · simpa using one_mem_span R
    · simpa using p_mem_span R
    · simpa using q_mem_span R
    · simpa using p_mem_span R
    · exact p_mul_p_mem R
    · exact p_mul_q_mem R
    · simpa using q_mem_span R
    · change q R * p R ∈ spanningModule R
      rw [mul_comm]
      exact p_mul_q_mem R
    · exact q_mul_q_mem R
  exact hle (Submodule.mul_mem_mul hv hw)

theorem candidateAlgebra_eq_span  :
    (candidateAlgebra R).toSubmodule = spanningModule R := by
  let S : Subalgebra (Polynomial R) (ordinaryCoordinateRing R) :=
    (spanningModule R).toSubalgebra (one_mem_span R) (spanningModule_mul_closed R)
  have hBS : candidateAlgebra R ≤ S := by
    apply Algebra.adjoin_le
    intro z hz
    rcases hz with rfl | rfl
    · exact p_mem_span R
    · exact q_mem_span R
  apply le_antisymm
  · exact fun _ hz => hBS hz
  · apply Submodule.span_le.mpr
    intro z hz
    simp only [generators, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact (candidateAlgebra R).one_mem
    · exact Algebra.subset_adjoin (by simp)
    · exact Algebra.subset_adjoin (by simp)

theorem candidateAlgebra_finite  :
    Module.Finite (Polynomial R) (candidateAlgebra R) := by
  change Module.Finite (Polynomial R) (candidateAlgebra R).toSubmodule
  apply Module.Finite.of_fg
  rw [candidateAlgebra_eq_span R]
  exact Submodule.fg_span (by simp [generators])

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.candidateAlgebra_eq_span
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.candidateAlgebra_finite

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual finite subalgebra has the explicit R[T]-basis
1,p,q over an integral base in every characteristic. Named downstream consumer:
finite free level sets in single-section FiniteMapData.
The parameter T acts by t. The exact affine-open identification remains separate.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open Polynomial Module
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedSingleSectionPolynomialIdentities
open Order13MixedSingleSectionPolynomialCombinationIndependence
variable (R : Type u) [CommRing R] [IsDomain R]

theorem generator_linearIndependent :
    LinearIndependent (Polynomial R) (generator R) := by
  apply Fintype.linearIndependent_iff.mpr
  intro F hF
  apply polynomial_combination_kernel R F
  simpa only [Algebra.smul_def,parameter_algebraMap] using hF

omit [IsDomain R] in
theorem generator_range : Set.range (generator R) = generators R := by
  ext z
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp [generator,generators]
  · intro hz
    simp only [generators,Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨0,by simp [generator]⟩
    · exact ⟨1,by simp [generator]⟩
    · exact ⟨2,by simp [generator]⟩

noncomputable def candidateBasis :
    Basis (Fin 3) (Polynomial R) (candidateAlgebra R) := by
  change Basis (Fin 3) (Polynomial R) (candidateAlgebra R).toSubmodule
  exact (Basis.span (generator_linearIndependent R)).map
    (LinearEquiv.ofEq _ _ (by
      rw [generator_range]
      exact (candidateAlgebra_eq_span R).symm))

theorem candidateBasis_value (i : Fin 3) :
    (candidateBasis R i : ordinaryCoordinateRing R) = generator R i := by
  simp [candidateBasis]

theorem candidateAlgebra_free :
    Module.Free (Polynomial R) (candidateAlgebra R) := Module.Free.of_basis (candidateBasis R)

theorem candidateAlgebra_finrank :
    Module.finrank (Polynomial R) (candidateAlgebra R) = 3 := by
  simpa using Module.finrank_eq_card_basis (candidateBasis R)

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.generator_linearIndependent
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.candidateBasis_value
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.candidateAlgebra_free
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.candidateAlgebra_finrank

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Reuses the complete checked quotient/base-change identification from official
Anthropic FLT, pin 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: actual algebraic level sets of the parameter in B, with
finite freeness and rank three. Named downstream consumer: full single-section
FiniteMapData after the still-separate actual affine-open identification.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open Polynomial Module
open scoped TensorProduct
variable (R : Type u) [CommRing R] [IsDomain R]

scoped instance candidateBaseAlgebra : Algebra R (candidateAlgebra R) :=
  ((algebraMap (Polynomial R) (candidateAlgebra R)).comp (Polynomial.C)).toAlgebra

scoped instance candidateBaseTower : IsScalarTower R (Polynomial R) (candidateAlgebra R) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem candidate_base_algebraMap_coe (r : R) :
    (algebraMap R (candidateAlgebra R) r : Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing R) =
      algebraMap R (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing R) r := by
  change aeval (Order13MixedSingleSectionPolynomialIdentities.t R) (C r) = _
  exact aeval_C _ _

def parameterElement : candidateAlgebra R :=
  algebraMap (Polynomial R) (candidateAlgebra R) X

variable (S : Type u) [CommRing S] [Algebra R S]

abbrev levelSet (s : S) :=
  S ⊗[R] candidateAlgebra R ⧸
    Ideal.span {(1 : S) ⊗ₜ[R] parameterElement R - s ⊗ₜ[R] (1 : candidateAlgebra R)}

noncomputable def levelSetBasis (s : S) :
    Basis (Fin 3) S (levelSet R S s) := by
  letI : Algebra (Polynomial R) S := (aeval s).toRingHom.toAlgebra
  letI : IsScalarTower R (Polynomial R) S := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R S r = aeval s (C r)
    rw [aeval_C]
  let e := P2MW.S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial.U4b.levelSetEquiv
    R (candidateAlgebra R) S (parameterElement R) s (by rfl) (by
      change aeval s X = s
      exact aeval_X s)
  exact ((candidateBasis R).baseChange S).map e.symm.toLinearEquiv

theorem levelSet_finite_free_finrank [Nontrivial S] (s : S) :
    Module.Finite S (levelSet R S s) ∧ Module.Free S (levelSet R S s) ∧
      Module.finrank S (levelSet R S s) = 3 := by
  let b := levelSetBasis R S s
  exact ⟨Module.Finite.of_basis b, Module.Free.of_basis b, by
    simpa using Module.finrank_eq_card_basis b⟩

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.levelSetBasis
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.levelSet_finite_free_finrank

end


