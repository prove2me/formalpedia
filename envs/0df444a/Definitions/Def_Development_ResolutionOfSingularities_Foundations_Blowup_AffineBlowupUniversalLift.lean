-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupUniversalLift
-- name    : Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupUniversalLift
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T12:40:13.156133+00:00
-- url     : https://prove2.me/theorems/974069c7-132b-4d49-9205-330c8adcd5e3
-- title:
--   Affine Blowup Universal Lift
-- statement:
--   Definitions and structural lemmas for Affine Blowup Universal Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupUniversalLift.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Theorems.Thm_FunctorialResolution_Blowup_reesDegreeZeroEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.Blowup.reesDegreeZeroEquiv_apply


set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.Blowup
universe u v
section
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
def polynomialEvalInvSelf (φ : R →+* S) (s : S) : Polynomial R →+* Localization.Away s :=
  Polynomial.eval₂RingHom
    (((algebraMap S (Localization.Away s)) : S →+* Localization.Away s).comp φ)
    (Localization.Away.invSelf s)
theorem polynomialEvalInvSelf_monomial (φ : R →+* S) (s : S) (n : ℕ) (r : R) :
    polynomialEvalInvSelf φ s (Polynomial.monomial n r) =
      algebraMap S (Localization.Away s) (φ r) * Localization.Away.invSelf s ^ n := by
  simp [polynomialEvalInvSelf]
theorem exists_mul_pow_of_mem_pow (I : Ideal R) (φ : R →+* S) (s : S)
    (hI : Ideal.map φ I = Ideal.span {s}) (n : ℕ) (r : R) (hr : r ∈ I ^ n) :
    ∃ c : S, φ r = c * s ^ n := by
  have hmem : φ r ∈ Ideal.span {s ^ n} := by
    have h1 : φ r ∈ Ideal.map φ (I ^ n) := Ideal.mem_map_of_mem φ hr
    rwa [Ideal.map_pow, hI, Ideal.span_singleton_pow] at h1
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmem
  exact ⟨c, by rw [hc, mul_comm]⟩
theorem algebraMap_mul_invSelf {T : Type v} [CommRing T] (t : T) :
    algebraMap T (Localization.Away t) t * Localization.Away.invSelf t = 1 := by
  have h : Localization.Away.invSelf t
      = Localization.mk 1 ⟨t, Submonoid.mem_powers t⟩ := rfl
  rw [h, Localization.mk_eq_mk', mul_comm, IsLocalization.mk'_spec, map_one]
theorem exists_algebraMap_eq_polynomialEvalInvSelf (I : Ideal R) (φ : R →+* S) (s : S)
    (hI : Ideal.map φ I = Ideal.span {s}) (p : ↥(reesAlgebra I)) :
    ∃ c : S, algebraMap S (Localization.Away s) c = polynomialEvalInvSelf φ s (p : Polynomial R) := by
  have hmem : ∀ i : ℕ, (p : Polynomial R).coeff i ∈ I ^ i := by
    have hp := p.2
    rw [mem_reesAlgebra_iff] at hp
    exact hp
  have key : ∀ i : ℕ, ∃ c : S, φ ((p : Polynomial R).coeff i) = c * s ^ i := fun i =>
    exists_mul_pow_of_mem_pow I φ s hI i ((p : Polynomial R).coeff i) (hmem i)
  choose c hc using key
  refine ⟨∑ i ∈ Finset.range ((p : Polynomial R).natDegree + 1), c i, ?_⟩
  have hEval : polynomialEvalInvSelf φ s (p : Polynomial R) =
      Polynomial.eval₂
        (((algebraMap S (Localization.Away s)) : S →+* Localization.Away s).comp φ)
        (Localization.Away.invSelf s) (p : Polynomial R) := rfl
  rw [map_sum, hEval, Polynomial.eval₂_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.comp_apply, hc i, map_mul, map_pow, mul_assoc, ← mul_pow,
    algebraMap_mul_invSelf s, one_pow, mul_one]
def reesAlgebraLiftFun (I : Ideal R) (φ : R →+* S) (s : S)
    (hI : Ideal.map φ I = Ideal.span {s}) (_hs : s ∈ nonZeroDivisors S)
    (p : ↥(reesAlgebra I)) : S :=
  (exists_algebraMap_eq_polynomialEvalInvSelf I φ s hI p).choose
theorem algebraMap_reesAlgebraLiftFun (I : Ideal R) (φ : R →+* S) (s : S)
    (hI : Ideal.map φ I = Ideal.span {s}) (hs : s ∈ nonZeroDivisors S)
    (p : ↥(reesAlgebra I)) :
    algebraMap S (Localization.Away s) (reesAlgebraLiftFun I φ s hI hs p) =
      polynomialEvalInvSelf φ s (p : Polynomial R) :=
  (exists_algebraMap_eq_polynomialEvalInvSelf I φ s hI p).choose_spec
theorem reesAlgebraLiftFun_one (I : Ideal R) (φ : R →+* S) (s : S)
    (hI : Ideal.map φ I = Ideal.span {s}) (hs : s ∈ nonZeroDivisors S) :
    reesAlgebraLiftFun I φ s hI hs 1 = 1 := by
  have hinj : Function.Injective (algebraMap S (Localization.Away s)) :=
    IsLocalization.injective (Localization.Away s) (Submonoid.powers_le.mpr hs)
  apply hinj
  rw [algebraMap_reesAlgebraLiftFun I φ s hI hs 1]
  simp
theorem reesAlgebraLiftFun_mul (I : Ideal R) (φ : R →+* S) (s : S)
    (hI : Ideal.map φ I = Ideal.span {s}) (hs : s ∈ nonZeroDivisors S)
    (p q : ↥(reesAlgebra I)) :
    reesAlgebraLiftFun I φ s hI hs (p * q) = reesAlgebraLiftFun I φ s hI hs p * reesAlgebraLiftFun I φ s hI hs q := by
  have hM : Submonoid.powers s ≤ nonZeroDivisors S := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact pow_mem hs n
  have hinj : Function.Injective (algebraMap S (Localization.Away s)) :=
    IsLocalization.injective (S := Localization.Away s) (M := Submonoid.powers s) hM
  apply hinj
  have hcoe : ((p * q : ↥(reesAlgebra I)) : Polynomial R)
      = (p : Polynomial R) * (q : Polynomial R) := rfl
  rw [map_mul, algebraMap_reesAlgebraLiftFun, algebraMap_reesAlgebraLiftFun, algebraMap_reesAlgebraLiftFun, hcoe, map_mul]
theorem reesAlgebraLiftFun_zero (I : Ideal R) (φ : R →+* S) (s : S)
    (hI : Ideal.map φ I = Ideal.span {s}) (hs : s ∈ nonZeroDivisors S) :
    reesAlgebraLiftFun I φ s hI hs 0 = 0 := by
  have hinj : Function.Injective (algebraMap S (Localization.Away s)) :=
    IsLocalization.injective (Localization.Away s) (Submonoid.powers_le.mpr hs)
  apply hinj
  rw [algebraMap_reesAlgebraLiftFun I φ s hI hs 0]
  simp
theorem reesAlgebraLiftFun_add (I : Ideal R) (φ : R →+* S) (s : S)
    (hI : Ideal.map φ I = Ideal.span {s}) (hs : s ∈ nonZeroDivisors S)
    (p q : ↥(reesAlgebra I)) :
    reesAlgebraLiftFun I φ s hI hs (p + q) = reesAlgebraLiftFun I φ s hI hs p + reesAlgebraLiftFun I φ s hI hs q := by
  have hM : Submonoid.powers s ≤ nonZeroDivisors S := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact pow_mem hs n
  have hinj : Function.Injective (algebraMap S (Localization.Away s)) :=
    IsLocalization.injective (S := Localization.Away s) (M := Submonoid.powers s) hM
  apply hinj
  have hcoe : ((p + q : ↥(reesAlgebra I)) : Polynomial R)
      = (p : Polynomial R) + (q : Polynomial R) := rfl
  rw [map_add, algebraMap_reesAlgebraLiftFun, algebraMap_reesAlgebraLiftFun, algebraMap_reesAlgebraLiftFun, hcoe, map_add]
def reesAlgebraLift (I : Ideal R) (φ : R →+* S) (s : S)
    (hI : Ideal.map φ I = Ideal.span {s}) (hs : s ∈ nonZeroDivisors S) :
    ↥(reesAlgebra I) →+* S where
  toFun := reesAlgebraLiftFun I φ s hI hs
  map_one' := reesAlgebraLiftFun_one I φ s hI hs
  map_mul' := reesAlgebraLiftFun_mul I φ s hI hs
  map_zero' := reesAlgebraLiftFun_zero I φ s hI hs
  map_add' := reesAlgebraLiftFun_add I φ s hI hs
theorem reesAlgebraLift_apply (I : Ideal R) (φ : R →+* S) (s : S)
    (hI : Ideal.map φ I = Ideal.span {s}) (hs : s ∈ nonZeroDivisors S)
    (p : ↥(reesAlgebra I)) :
    reesAlgebraLift I φ s hI hs p = reesAlgebraLiftFun I φ s hI hs p := rfl
theorem reesAlgebraLift_reesGenerator (I : Ideal R) (φ : R →+* S) (s : S)
    (hI : Ideal.map φ I = Ideal.span {s}) (hs : s ∈ nonZeroDivisors S)
    (a : ↥I) (ha : φ (a : R) = s) :
    reesAlgebraLift I φ s hI hs (reesGenerator I a) = 1 := by
  have hinj : Function.Injective (algebraMap S (Localization.Away s)) :=
    IsLocalization.injective (Localization.Away s) (Submonoid.powers_le.mpr hs)
  apply hinj
  rw [reesAlgebraLift_apply, algebraMap_reesAlgebraLiftFun I φ s hI hs, reesGenerator_coe, polynomialEvalInvSelf_monomial, ha,
    pow_one, algebraMap_mul_invSelf,
    map_one (algebraMap S (Localization.Away s))]
end
section
variable {R : Type u} [CommRing R]
def globalSectionsRingHom {W : Scheme.{u}} (g : W ⟶ Spec (CommRingCat.of R)) : R →+* Γ(W, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom
def homogeneousLocalizationAwayVal {B : Type u} [CommRing B] (J : Ideal B) (a : ↥J) :
    HomogeneousLocalization.Away (reesGrading J) (reesGenerator J a) →+*
      Localization.Away (reesGenerator J a) where
  toFun := HomogeneousLocalization.val
  map_one' := by simp
  map_mul' := fun p q => by simp
  map_zero' := by simp
  map_add' := fun p q => by simp
theorem isUnit_reesAlgebraLift_powers {B : Type u} [CommRing B] (J : Ideal B)
    {T : Type v} [CommRing T] (φ : B →+* T) (a : ↥J)
    (hgen : Ideal.map φ J = Ideal.span {φ (a : B)})
    (hnzd : φ (a : B) ∈ nonZeroDivisors T) :
    ∀ y : Submonoid.powers (reesGenerator J a),
      IsUnit (reesAlgebraLift J φ (φ (a : B)) hgen hnzd (y : ↥(reesAlgebra J))) := by
  intro y
  obtain ⟨n, hn⟩ := y.2
  have hy : (y : ↥(reesAlgebra J)) = reesGenerator J a ^ n := hn.symm
  rw [hy, map_pow, reesAlgebraLift_reesGenerator J φ (φ (a : B)) hgen hnzd a rfl, one_pow]
  exact isUnit_one
def homogeneousAwayLift {B : Type u} [CommRing B] (J : Ideal B)
    {T : Type v} [CommRing T] (φ : B →+* T) (a : ↥J)
    (hgen : Ideal.map φ J = Ideal.span {φ (a : B)})
    (hnzd : φ (a : B) ∈ nonZeroDivisors T) :
    HomogeneousLocalization.Away (reesGrading J) (reesGenerator J a) →+* T :=
  RingHom.comp
    (IsLocalization.lift (S := Localization.Away (reesGenerator J a))
      (g := reesAlgebraLift J φ (φ (a : B)) hgen hnzd) (isUnit_reesAlgebraLift_powers J φ a hgen hnzd))
    (homogeneousLocalizationAwayVal J a)
end
end FunctorialResolution.Blowup


