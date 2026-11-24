-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
-- name    : Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:32.549933+00:00
-- url     : https://prove2.me/theorems/cab39f74-c03a-45a6-9f4b-e96d3e4a8e4b
-- title:
--   Rees Grading
-- statement:
--   Definitions and structural lemmas for Rees Grading, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/ReesGrading.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
namespace FunctorialResolution.Blowup
variable {R : Type*} [CommRing R]
theorem mem_pow_one (I : Ideal R) {a : R} (ha : a ∈ I) : a ∈ I ^ 1 := by
  rwa [pow_one]
theorem mem_pow_zero (I : Ideal R) (r : R) : r ∈ I ^ 0 := by
  rw [pow_zero, Ideal.one_eq_top]
  exact Submodule.mem_top
noncomputable def reesGrading (I : Ideal R) (n : ℕ) : Submodule R ↥(reesAlgebra I) :=
  Submodule.comap (reesAlgebra I).val.toLinearMap
    (LinearMap.range (Polynomial.monomial (R := R) n))
theorem mem_reesGrading_iff_monomial (I : Ideal R) (n : ℕ) (p : ↥(reesAlgebra I)) :
    p ∈ reesGrading I n ↔ ∃ r ∈ I ^ n, (p : R[X]) = Polynomial.monomial n r := by
  have hmem : p ∈ reesGrading I n ↔ ∃ r : R, Polynomial.monomial n r = (p : R[X]) := Iff.rfl
  rw [hmem]
  constructor
  · rintro ⟨r, hr⟩
    have hp : (p : R[X]).coeff n ∈ I ^ n := (mem_reesAlgebra_iff I _).mp p.2 n
    have hcoef : (Polynomial.monomial n r : R[X]).coeff n = r := by simp
    rw [← hr, hcoef] at hp
    exact ⟨r, hp, hr.symm⟩
  · rintro ⟨r, -, hpr⟩
    exact ⟨r, hpr.symm⟩
theorem mem_reesGrading_iff_coeff (I : Ideal R) (n : ℕ) (p : ↥(reesAlgebra I)) :
    p ∈ reesGrading I n ↔ ∀ i, i ≠ n → (p : R[X]).coeff i = 0 := by
  have key : p ∈ reesGrading I n ↔ ∃ r : R, Polynomial.monomial n r = (p : R[X]) := Iff.rfl
  rw [key]
  constructor
  · rintro ⟨r, hr⟩ i hi
    rw [← hr, Polynomial.coeff_monomial, if_neg (Ne.symm hi)]
  · intro h
    refine ⟨(p : R[X]).coeff n, ?_⟩
    ext i
    rcases eq_or_ne i n with rfl | hi
    · simp
    · simp [Polynomial.coeff_monomial, Ne.symm hi, h i hi]
theorem reesGrading_one_mem (I : Ideal R) : (1 : ↥(reesAlgebra I)) ∈ reesGrading I 0 := by
  show ((1 : ↥(reesAlgebra I)) : R[X]) ∈ LinearMap.range (Polynomial.monomial (R := R) 0)
  refine LinearMap.mem_range.2 ⟨1, ?_⟩
  simp
theorem reesGrading_mul_mem (I : Ideal R) {m n : ℕ} {p q : ↥(reesAlgebra I)}
    (hp : p ∈ reesGrading I m) (hq : q ∈ reesGrading I n) :
    p * q ∈ reesGrading I (m + n) := by
  have key : ∀ (k : ℕ) (x : ↥(reesAlgebra I)),
      x ∈ reesGrading I k ↔ ∃ r : R, Polynomial.monomial k r = (x : R[X]) :=
    fun _ _ => Iff.rfl
  obtain ⟨a, ha⟩ := (key m p).1 hp
  obtain ⟨b, hb⟩ := (key n q).1 hq
  refine (key (m + n) (p * q)).2 ⟨a * b, ?_⟩
  have hpq : ((p * q : ↥(reesAlgebra I)) : R[X]) = (p : R[X]) * (q : R[X]) := rfl
  rw [hpq, ← ha, ← hb, Polynomial.monomial_mul_monomial]
instance instGradedMonoidReesGrading (I : Ideal R) : SetLike.GradedMonoid (reesGrading I) where
  one_mem := reesGrading_one_mem I
  mul_mem := @fun _ _ _ _ hp hq => reesGrading_mul_mem I hp hq
theorem reesGrading_iSupIndep (I : Ideal R) : iSupIndep (reesGrading I) := by
  intro n
  rw [Submodule.disjoint_def]
  intro p hp hp'
  have hcoeff : ∀ i, i ≠ n → (p : R[X]).coeff i = 0 :=
    (mem_reesGrading_iff_coeff I n p).1 hp
  have hker : (⨆ (j : ℕ) (_ : j ≠ n), reesGrading I j) ≤
      LinearMap.ker ((Polynomial.lcoeff R n).comp ((reesAlgebra I).val.toLinearMap)) := by
    refine iSup_le fun j => iSup_le fun hj => ?_
    intro x hx
    have hx' := (mem_reesGrading_iff_coeff I j x).1 hx n (Ne.symm hj)
    simpa [LinearMap.mem_ker, Polynomial.lcoeff_apply] using hx'
  have hpn : (p : R[X]).coeff n = 0 := by
    have h := hker hp'
    simpa [LinearMap.mem_ker, Polynomial.lcoeff_apply] using h
  have hp0 : (p : R[X]) = 0 := by
    ext i
    rcases eq_or_ne i n with rfl | hi
    · simpa using hpn
    · simpa using hcoeff i hi
  exact Subtype.ext (by simpa using hp0)
theorem coeff_mem_pow (I : Ideal R) (p : ↥(reesAlgebra I)) (i : ℕ) :
    ((p : R[X])).coeff i ∈ I ^ i := p.2 i
theorem monomial_mem_reesGrading (I : Ideal R) {n : ℕ} {r : R} (hr : r ∈ I ^ n) :
    (⟨Polynomial.monomial n r, reesAlgebra.monomial_mem.mpr hr⟩ : ↥(reesAlgebra I))
      ∈ reesGrading I n := by
  refine (mem_reesGrading_iff_coeff I n _).2 fun i hi => ?_
  show (Polynomial.monomial n r : R[X]).coeff i = 0
  rw [Polynomial.coeff_monomial, if_neg (Ne.symm hi)]
theorem reesGrading_iSup_eq_top (I : Ideal R) : (⨆ n : ℕ, reesGrading I n) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun p => ?_
  have hval : ∀ x y : ↥(reesAlgebra I),
      (reesAlgebra I).val x = (reesAlgebra I).val y → x = y := fun _ _ h => Subtype.ext h
  have hsum : p = ∑ i ∈ (p : R[X]).support,
      (⟨Polynomial.monomial i ((p : R[X]).coeff i),
        reesAlgebra.monomial_mem.mpr (coeff_mem_pow I p i)⟩ : ↥(reesAlgebra I)) :=
    hval _ _ (by rw [map_sum]; exact Polynomial.as_sum_support _)
  rw [hsum]
  exact sum_mem fun i _ => Submodule.mem_iSup_of_mem i
    (monomial_mem_reesGrading I (coeff_mem_pow I p i))
theorem reesGrading_isInternal (I : Ideal R) : DirectSum.IsInternal (reesGrading I) := by
  exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top (reesGrading I)).2
    ⟨reesGrading_iSupIndep I, reesGrading_iSup_eq_top I⟩
noncomputable def directSumReesGradingEquiv (I : Ideal R) :
    DirectSum ℕ (fun n => ↥(reesGrading I n)) ≃ ↥(reesAlgebra I) :=
  Equiv.ofBijective (DirectSum.coeAddMonoidHom (reesGrading I)) (reesGrading_isInternal I)
theorem leftInverse_coeAddMonoidHom_reesGrading (I : Ideal R) :
    Function.LeftInverse (DirectSum.coeAddMonoidHom (reesGrading I))
      ⇑(directSumReesGradingEquiv I).symm :=
  fun x => (directSumReesGradingEquiv I).apply_symm_apply x
theorem rightInverse_coeAddMonoidHom_reesGrading (I : Ideal R) :
    Function.RightInverse (DirectSum.coeAddMonoidHom (reesGrading I))
      ⇑(directSumReesGradingEquiv I).symm :=
  fun x => (directSumReesGradingEquiv I).symm_apply_apply x
noncomputable instance instGradedAlgebraReesGrading (I : Ideal R) :
    GradedAlgebra (reesGrading I) where
  __ := instGradedMonoidReesGrading I
  decompose' := ⇑(directSumReesGradingEquiv I).symm
  left_inv := leftInverse_coeAddMonoidHom_reesGrading I
  right_inv := rightInverse_coeAddMonoidHom_reesGrading I
noncomputable def reesMonomial (I : Ideal R) (n : ℕ) (r : R) (hr : r ∈ I ^ n) :
    ↥(reesAlgebra I) :=
  ⟨Polynomial.monomial n r, reesAlgebra.monomial_mem.mpr hr⟩
@[simp] theorem reesMonomial_coe (I : Ideal R) (n : ℕ) (r : R) (hr : r ∈ I ^ n) :
    ((reesMonomial I n r hr : ↥(reesAlgebra I)) : R[X]) = Polynomial.monomial n r := rfl
theorem reesMonomial_mem_reesGrading (I : Ideal R) {n : ℕ} {r : R} (hr : r ∈ I ^ n) :
    reesMonomial I n r hr ∈ reesGrading I n := by
  rw [mem_reesGrading_iff_monomial]
  exact ⟨r, hr, reesMonomial_coe I n r hr⟩
noncomputable def reesDegreeOneMonomial (I : Ideal R) (a : R) (ha : a ∈ I) : ↥(reesAlgebra I) :=
  reesMonomial I 1 a (mem_pow_one I ha)
@[simp] theorem reesDegreeOneMonomial_coe (I : Ideal R) (a : R) (ha : a ∈ I) :
    ((reesDegreeOneMonomial I a ha : ↥(reesAlgebra I)) : R[X]) = Polynomial.monomial 1 a := rfl
noncomputable def reesGenerator (I : Ideal R) (a : ↥I) : ↥(reesAlgebra I) :=
  reesDegreeOneMonomial I (a : R) a.2
@[simp] theorem reesGenerator_coe (I : Ideal R) (a : ↥I) :
    ((reesGenerator I a : ↥(reesAlgebra I)) : R[X]) = Polynomial.monomial 1 (a : R) := rfl
noncomputable def reesMonomialOfCoeff (I : Ideal R) (p : ↥(reesAlgebra I)) (i : ℕ) :
    ↥(reesAlgebra I) :=
  reesMonomial I i ((p : R[X]).coeff i) (coeff_mem_pow I p i)
noncomputable def reesDegreeZeroMonomial (I : Ideal R) (r : R) : ↥(reesGrading I 0) :=
  ⟨reesMonomial I 0 r (mem_pow_zero I r),
    reesMonomial_mem_reesGrading I (mem_pow_zero I r)⟩
theorem reesDegreeZeroMonomial_one (I : Ideal R) : reesDegreeZeroMonomial I 1 = 1 := by
  refine Subtype.ext (Subtype.ext ?_)
  show (Polynomial.monomial 0 (1 : R) : R[X]) = _
  exact Polynomial.monomial_zero_one
theorem reesDegreeZeroMonomial_mul (I : Ideal R) (r s : R) :
    reesDegreeZeroMonomial I (r * s) = reesDegreeZeroMonomial I r * reesDegreeZeroMonomial I s := by
  refine Subtype.ext (Subtype.ext ?_)
  show (Polynomial.monomial 0 (r * s) : R[X])
      = (Polynomial.monomial 0 r : R[X]) * (Polynomial.monomial 0 s : R[X])
  exact (Polynomial.monomial_mul_monomial 0 0 r s).symm
theorem reesDegreeZeroMonomial_zero (I : Ideal R) : reesDegreeZeroMonomial I 0 = 0 := by
  refine Subtype.ext (Subtype.ext ?_)
  show (Polynomial.monomial 0 (0 : R) : R[X]) = 0
  rw [map_zero]
theorem reesDegreeZeroMonomial_add (I : Ideal R) (r s : R) :
    reesDegreeZeroMonomial I (r + s) = reesDegreeZeroMonomial I r + reesDegreeZeroMonomial I s := by
  refine Subtype.ext (Subtype.ext ?_)
  show (Polynomial.monomial 0 (r + s) : R[X])
      = (Polynomial.monomial 0 r : R[X]) + (Polynomial.monomial 0 s : R[X])
  exact map_add (Polynomial.monomial (R := R) 0) r s
noncomputable def reesDegreeZeroRingHom (I : Ideal R) : R →+* ↥(reesGrading I 0) where
  toFun := reesDegreeZeroMonomial I
  map_one' := reesDegreeZeroMonomial_one I
  map_mul' := reesDegreeZeroMonomial_mul I
  map_zero' := reesDegreeZeroMonomial_zero I
  map_add' := reesDegreeZeroMonomial_add I
@[simp] theorem reesDegreeZeroRingHom_coe_coe (I : Ideal R) (r : R) :
    ((reesDegreeZeroRingHom I r : ↥(reesAlgebra I)) : R[X]) = Polynomial.C r := by
  show (Polynomial.monomial 0 r : R[X]) = Polynomial.C r
  simp
theorem reesDegreeZeroRingHom_injective (I : Ideal R) :
    Function.Injective (reesDegreeZeroRingHom I) := by
  intro r s h
  have h1 := congrArg (fun x : ↥(reesGrading I 0) => ((x : ↥(reesAlgebra I)) : R[X])) h
  have h2 : (Polynomial.monomial 0 r : R[X]) = Polynomial.monomial 0 s := h1
  have h3 : (Polynomial.monomial 0 r : R[X]).coeff 0 = (Polynomial.monomial 0 s : R[X]).coeff 0 :=
    congrArg (fun p : R[X] => p.coeff 0) h2
  simpa using h3
theorem reesDegreeZeroRingHom_surjective (I : Ideal R) :
    Function.Surjective (reesDegreeZeroRingHom I) := by
  rintro ⟨x, hx⟩
  have hco : ∀ i, i ≠ 0 → ((x : ↥(reesAlgebra I)) : R[X]).coeff i = 0 :=
    (mem_reesGrading_iff_coeff I 0 x).1 hx
  refine ⟨((x : ↥(reesAlgebra I)) : R[X]).coeff 0, Subtype.ext (Subtype.ext ?_)⟩
  show (Polynomial.monomial 0 (((x : ↥(reesAlgebra I)) : R[X]).coeff 0) : R[X])
      = ((x : ↥(reesAlgebra I)) : R[X])
  ext i
  rcases eq_or_ne i 0 with rfl | hi
  · simp
  · rw [Polynomial.coeff_monomial, if_neg (Ne.symm hi)]
    exact (hco i hi).symm
theorem reesDegreeZeroRingHom_bijective (I : Ideal R) :
    Function.Bijective (reesDegreeZeroRingHom I) :=
  ⟨reesDegreeZeroRingHom_injective I, reesDegreeZeroRingHom_surjective I⟩
noncomputable def reesDegreeZeroEquiv (I : Ideal R) : R ≃+* ↥(reesGrading I 0) :=
  RingEquiv.ofBijective (reesDegreeZeroRingHom I) (reesDegreeZeroRingHom_bijective I)
end FunctorialResolution.Blowup


