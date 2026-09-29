-- Prove2me | solution 1 for Algebra.finrank_quotient_span_sub_eq_of_isLocalization_away_of_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/dd64d7e2-b610-5187-9c7b-7fe9e2b3d7a8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_finrank_quotient_span_sub_eq_of_isLocalization_away_of_mul_eq_one

set_option autoImplicit false

universe u

open Polynomial
open scoped TensorProduct

namespace GLUE

section Identification

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  [Algebra R[X] A] [IsScalarTower R R[X] A]
  (S : Type u) [CommRing S] [Algebra R S] [Algebra R[X] S] [IsScalarTower R R[X] S]
  (f : A) (s : S) (hf : algebraMap R[X] A X = f) (hs : algebraMap R[X] S X = s)

abbrev lsIdeal : Ideal (S ⊗[R] A) := Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}

noncomputable def fwd : S ⊗[R] A →ₐ[S] S ⊗[R[X]] A :=
  AlgHom.liftEquiv R S A (S ⊗[R[X]] A)
    ((Algebra.TensorProduct.includeRight (R := R[X]) (A := S) (B := A)).restrictScalars R)

@[scoped simp] theorem fwd_tmul (x : S) (a : A) : fwd R A S (x ⊗ₜ[R] a) = x ⊗ₜ[R[X]] a := by
  rw [fwd, AlgHom.liftEquiv_tmul, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.includeRight_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

include hf hs in
theorem fwd_rel : fwd R A S ((1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)) = 0 := by
  rw [map_sub, fwd_tmul, fwd_tmul, ← hf, ← hs, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, sub_self]

noncomputable def fwdQ : (S ⊗[R] A ⧸ lsIdeal R A S f s) →ₐ[S] S ⊗[R[X]] A :=
  Ideal.Quotient.liftₐ (lsIdeal R A S f s) (fwd R A S) (by
    intro a ha
    rw [← RingHom.mem_ker]
    refine (Ideal.span_le.mpr ?_) ha
    rintro _ rfl
    exact fwd_rel R A S f s hf hs)

@[scoped simp] theorem fwdQ_mk (t : S ⊗[R] A) :
    fwdQ R A S f s hf hs (Ideal.Quotient.mk _ t) = fwd R A S t := rfl

noncomputable def bwdA₀ : A →ₐ[R] (S ⊗[R] A ⧸ lsIdeal R A S f s) :=
  (Ideal.Quotient.mkₐ R (lsIdeal R A S f s)).comp
    (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A))

@[scoped simp] theorem bwdA₀_apply (a : A) :
    bwdA₀ R A S f s a = Ideal.Quotient.mk _ ((1 : S) ⊗ₜ[R] a) := rfl

include hf hs in

theorem bwdA₀_comp :
    (bwdA₀ R A S f s).comp (IsScalarTower.toAlgHom R R[X] A) =
      IsScalarTower.toAlgHom R R[X] (S ⊗[R] A ⧸ lsIdeal R A S f s) := by
  refine Polynomial.algHom_ext ?_
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', bwdA₀_apply, hf]
  rw [IsScalarTower.algebraMap_apply R[X] (S ⊗[R] A) (S ⊗[R] A ⧸ lsIdeal R A S f s),
    Ideal.Quotient.algebraMap_eq, Algebra.TensorProduct.algebraMap_apply, hs,
    Ideal.Quotient.eq]
  exact Ideal.subset_span rfl

noncomputable def bwdA : A →ₐ[R[X]] (S ⊗[R] A ⧸ lsIdeal R A S f s) :=
  { bwdA₀ R A S f s with
    commutes' := fun p => by
      have := congrArg (fun φ : R[X] →ₐ[R] _ => φ p) (bwdA₀_comp R A S f s hf hs)
      simpa using this }

@[scoped simp] theorem bwdA_apply (a : A) :
    bwdA R A S f s hf hs a = Ideal.Quotient.mk _ ((1 : S) ⊗ₜ[R] a) := rfl

noncomputable def bwd : S ⊗[R[X]] A →ₐ[S] (S ⊗[R] A ⧸ lsIdeal R A S f s) :=
  AlgHom.liftEquiv R[X] S A _ (bwdA R A S f s hf hs)

@[scoped simp] theorem bwd_tmul (x : S) (a : A) :
    bwd R A S f s hf hs (x ⊗ₜ[R[X]] a) = Ideal.Quotient.mk _ (x ⊗ₜ[R] a) := by
  rw [bwd, AlgHom.liftEquiv_tmul, bwdA_apply]
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply S (S ⊗[R] A) (S ⊗[R] A ⧸ lsIdeal R A S f s),
    Ideal.Quotient.algebraMap_eq, ← map_mul, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rfl

noncomputable def levelSetEquiv : (S ⊗[R] A ⧸ lsIdeal R A S f s) ≃ₐ[S] S ⊗[R[X]] A :=
  AlgEquiv.ofAlgHom (fwdQ R A S f s hf hs) (bwd R A S f s hf hs)
    (by
      refine Algebra.TensorProduct.ext' fun x a => ?_
      simp)
    (by
      refine Ideal.Quotient.algHom_ext _ (Algebra.TensorProduct.ext' fun x a => ?_)
      simp)

end Identification

section FibreDim

variable (K : Type u) [Field K] (D : Type u) [CommRing D] [Algebra K D] [Algebra K[X] D] [IsScalarTower K K[X] D]

theorem finrank_quotient_span_sub [Module.Finite K[X] D] [Module.Free K[X] D] (x : K) :
    Module.finrank K (D ⧸ Ideal.span {algebraMap K[X] D X - algebraMap K D x}) = Module.finrank K[X] D := by

  letI algKX : Algebra K[X] K := (Polynomial.aeval x : K[X] →ₐ[K] K).toRingHom.toAlgebra
  haveI : IsScalarTower K K[X] K := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap K K r = (Polynomial.aeval x : K[X] →ₐ[K] K) (algebraMap K K[X] r)
    rw [AlgHom.commutes]
  have hs : algebraMap K[X] K X = x := Polynomial.aeval_X x

  let e := levelSetEquiv K D K (algebraMap K[X] D X) x rfl hs

  let lid : K ⊗[K] D ≃ₐ[K] D := Algebra.TensorProduct.lid K D
  have hmap : Ideal.map lid (lsIdeal K D K (algebraMap K[X] D X) x) =
      Ideal.span {algebraMap K[X] D X - algebraMap K D x} := by
    rw [lsIdeal, Ideal.map_span, Set.image_singleton]
    congr 1
    simp [lid, Algebra.TensorProduct.lid_tmul, Algebra.smul_def]
  let q : (K ⊗[K] D ⧸ lsIdeal K D K (algebraMap K[X] D X) x) ≃ₐ[K]
      (D ⧸ Ideal.span {algebraMap K[X] D X - algebraMap K D x}) :=
    Ideal.quotientEquivAlg _ _ lid hmap.symm
  rw [← q.toLinearEquiv.finrank_eq, e.toLinearEquiv.finrank_eq]
  exact Module.finrank_baseChange

end FibreDim

end GLUE
p2m_reactivate "P2MW.S_Algebra_finrank_quotient_span_sub_eq_of_isLocalization_away_of_mul_eq_one.GLUE"

namespace GLUE

section Glued

variable {K : Type u} [Field K] {D E O : Type u} [CommRing D] [CommRing E] [CommRing O]
  [IsDomain D] [IsDomain E] [Algebra K D] [Algebra K E] [Algebra K O]
  (φ : D →ₐ[K] O) (ψ : E →ₐ[K] O) (a : D) (b : E)

theorem injective_aeval_of_glued (hφinj : Function.Injective φ) (hab : φ a * ψ b = 1)
    (hinj : Function.Injective (Polynomial.aeval a : K[X] →ₐ[K] D)) :
    Function.Injective (Polynomial.aeval b : K[X] →ₐ[K] E) := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  haveI : Invertible (ψ b) := ⟨φ a, hab, by rw [mul_comm]; exact hab⟩
  have h1 : Polynomial.eval₂ (algebraMap K O) (ψ b) P = 0 := by
    rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, hP, map_zero]
  have h2 : Polynomial.eval₂ (algebraMap K O) (⅟ (ψ b)) P.reverse = 0 :=
    (Polynomial.eval₂_reverse_eq_zero_iff (algebraMap K O) (ψ b) P).mpr h1
  have hinv : ⅟ (ψ b) = φ a := invOf_eq_right_inv (by rw [mul_comm]; exact hab)
  have h3 : φ (Polynomial.aeval a P.reverse) = 0 := by
    rw [← Polynomial.aeval_algHom_apply, Polynomial.aeval_def, ← hinv]
    exact h2
  rw [← map_zero φ] at h3
  have h4 : P.reverse = 0 := by
    rw [← map_zero (Polynomial.aeval a : K[X] →ₐ[K] D)] at h3
    exact hinj (hφinj h3)
  exact Polynomial.reverse_eq_zero.mp h4

end Glued
p2m_reactivate "P2MW.S_Algebra_finrank_quotient_span_sub_eq_of_isLocalization_away_of_mul_eq_one.GLUE"

section Laurent

open LaurentPolynomial

variable {K : Type u} [Field K] {D O : Type u} [CommRing D] [CommRing O] [Algebra K D] [Algebra K O]
  [Algebra K[X] D] [IsScalarTower K K[X] D]

theorem finrank_laurent_eq [Module.Free K[X] D] (φ : D →ₐ[K] O)
    (hloc : letI := φ.toRingHom.toAlgebra; IsLocalization.Away (algebraMap K[X] D X) O)
    (hunit : IsUnit ((φ.toRingHom.comp (algebraMap K[X] D)) X)) :
    letI : Algebra K[T;T⁻¹] O := (IsLocalization.Away.lift (X : K[X]) hunit).toAlgebra
    Module.finrank K[T;T⁻¹] O = Module.finrank K[X] D := by
  letI algDO : Algebra D O := φ.toRingHom.toAlgebra
  letI algXO : Algebra K[X] O := (φ.toRingHom.comp (algebraMap K[X] D)).toAlgebra
  haveI : IsScalarTower K[X] D O := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI algTO : Algebra K[T;T⁻¹] O := (IsLocalization.Away.lift (X : K[X]) hunit).toAlgebra
  haveI : IsScalarTower K[X] K[T;T⁻¹] O := IsScalarTower.of_algebraMap_eq fun p =>
    (IsLocalization.Away.lift_eq (X : K[X]) hunit p).symm
  have hM : Algebra.algebraMapSubmonoid D (Submonoid.powers (X : K[X])) =
      Submonoid.powers (algebraMap K[X] D X) := by
    show Submonoid.map _ _ = _
    rw [Submonoid.map_powers]
  haveI : IsLocalization (Algebra.algebraMapSubmonoid D (Submonoid.powers (X : K[X]))) O := by
    rw [hM]; exact hloc
  haveI : IsLocalizedModule (Submonoid.powers (X : K[X])) (IsScalarTower.toAlgHom K[X] D O).toLinearMap :=
    inferInstance
  have hBC := IsLocalizedModule.isBaseChange (Submonoid.powers (X : K[X])) K[T;T⁻¹]
    (IsScalarTower.toAlgHom K[X] D O).toLinearMap
  rw [← hBC.equiv.finrank_eq]
  exact Module.finrank_baseChange

end Laurent
p2m_reactivate "P2MW.S_Algebra_finrank_quotient_span_sub_eq_of_isLocalization_away_of_mul_eq_one.GLUE"

theorem main {K : Type u} [Field K] {D E O : Type u} [CommRing D] [CommRing E] [CommRing O]
    [IsDomain D] [IsDomain E] [Algebra K D] [Algebra K E] [Algebra K O]
    (φ : D →ₐ[K] O) (ψ : E →ₐ[K] O) (a : D) (b : E)
    (hφ : letI := φ.toRingHom.toAlgebra; IsLocalization.Away a O)
    (hψ : letI := ψ.toRingHom.toAlgebra; IsLocalization.Away b O)
    (hab : φ a * ψ b = 1)
    (hfinD : (Polynomial.aeval a : K[X] →ₐ[K] D).toRingHom.Finite)
    (hfinE : (Polynomial.aeval b : K[X] →ₐ[K] E).toRingHom.Finite)
    (hinj : Function.Injective (Polynomial.aeval a : K[X] →ₐ[K] D))
    (x : K) :
    Module.finrank K (D ⧸ Ideal.span {a - algebraMap K D x}) =
      Module.finrank K (E ⧸ Ideal.span {b}) := by

  have ha0 : a ≠ 0 := by
    intro h
    have : (Polynomial.aeval a : K[X] →ₐ[K] D) X = (Polynomial.aeval a : K[X] →ₐ[K] D) 0 := by
      rw [Polynomial.aeval_X, map_zero, h]
    exact Polynomial.X_ne_zero (hinj this)
  have hφinj : Function.Injective φ := by
    letI := φ.toRingHom.toAlgebra
    exact IsLocalization.injective (M := Submonoid.powers a) O
      (powers_le_nonZeroDivisors_of_noZeroDivisors ha0)
  have hinjE := injective_aeval_of_glued φ ψ a b hφinj hab hinj

  letI algXD : Algebra K[X] D := (Polynomial.aeval a : K[X] →ₐ[K] D).toRingHom.toAlgebra
  letI algXE : Algebra K[X] E := (Polynomial.aeval b : K[X] →ₐ[K] E).toRingHom.toAlgebra
  haveI : IsScalarTower K K[X] D := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap K D r = (Polynomial.aeval a : K[X] →ₐ[K] D) (algebraMap K K[X] r)
    rw [AlgHom.commutes]
  haveI : IsScalarTower K K[X] E := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap K E r = (Polynomial.aeval b : K[X] →ₐ[K] E) (algebraMap K K[X] r)
    rw [AlgHom.commutes]
  haveI : Module.Finite K[X] D := hfinD
  haveI : Module.Finite K[X] E := hfinE
  haveI : Module.IsTorsionFree K[X] D := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  haveI : Module.IsTorsionFree K[X] E := Module.isTorsionFree_iff_algebraMap_injective.mpr hinjE
  have haX : algebraMap K[X] D X = a := Polynomial.aeval_X a
  have hbX : algebraMap K[X] E X = b := Polynomial.aeval_X b

  have hD : Module.finrank K (D ⧸ Ideal.span {a - algebraMap K D x}) = Module.finrank K[X] D := by
    rw [← haX]; exact finrank_quotient_span_sub K D x
  have hE : Module.finrank K (E ⧸ Ideal.span {b}) = Module.finrank K[X] E := by
    have := finrank_quotient_span_sub K E 0
    rwa [map_zero, sub_zero, hbX] at this
  rw [hD, hE]

  have hua : IsUnit (φ a) := ⟨⟨φ a, ψ b, hab, by rw [mul_comm]; exact hab⟩, rfl⟩
  have hub : IsUnit (ψ b) := ⟨⟨ψ b, φ a, by rw [mul_comm]; exact hab, hab⟩, rfl⟩
  have hunitD : IsUnit ((φ.toRingHom.comp (algebraMap K[X] D)) X) := by
    show IsUnit (φ (algebraMap K[X] D X)); rw [haX]; exact hua
  have hunitE : IsUnit ((ψ.toRingHom.comp (algebraMap K[X] E)) X) := by
    show IsUnit (ψ (algebraMap K[X] E X)); rw [hbX]; exact hub
  have h1 := finrank_laurent_eq φ (by rw [haX]; exact hφ) hunitD
  have h2 := finrank_laurent_eq ψ (by rw [hbX]; exact hψ) hunitE
  rw [← h1, ← h2]

  let α₁ : LaurentPolynomial K →+* O := IsLocalization.Away.lift (X : K[X]) hunitD
  let α₂ : LaurentPolynomial K →+* O := IsLocalization.Away.lift (X : K[X]) hunitE
  have hc : α₂.comp (LaurentPolynomial.invert (R := K)).toRingEquiv.toRingHom =
      (RingEquiv.refl O).toRingHom.comp α₁ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (X : K[X]))
    refine Polynomial.ringHom_ext (fun k => ?_) ?_
    ·
      have e1 : algebraMap K[X] (LaurentPolynomial K) (Polynomial.C k) = LaurentPolynomial.C k := by
        rw [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_C]
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        AlgEquiv.coe_ringEquiv, e1, LaurentPolynomial.invert_C,
        RingEquiv.refl_apply]
      rw [← e1, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq]
      show ψ ((Polynomial.aeval b : K[X] →ₐ[K] E) (Polynomial.C k)) =
        φ ((Polynomial.aeval a : K[X] →ₐ[K] D) (Polynomial.C k))
      rw [Polynomial.aeval_C, Polynomial.aeval_C, AlgHom.commutes, AlgHom.commutes]
    ·
      have eX : algebraMap K[X] (LaurentPolynomial K) Polynomial.X = LaurentPolynomial.T 1 := by
        rw [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_X]
      have hα₂X : α₂ (LaurentPolynomial.T 1) = ψ b := by
        rw [← eX]; show IsLocalization.Away.lift _ hunitE _ = _
        rw [IsLocalization.Away.lift_eq]; show ψ (algebraMap K[X] E X) = ψ b; rw [hbX]
      have hα₁X : α₁ (LaurentPolynomial.T 1) = φ a := by
        rw [← eX]; show IsLocalization.Away.lift _ hunitD _ = _
        rw [IsLocalization.Away.lift_eq]; show φ (algebraMap K[X] D X) = φ a; rw [haX]
      have hα₂inv : α₂ (LaurentPolynomial.T (-1)) = φ a := by
        have hprod : α₂ (LaurentPolynomial.T (-1)) * ψ b = 1 := by
          rw [← hα₂X, ← map_mul, ← LaurentPolynomial.T_add]; simp
        calc α₂ (LaurentPolynomial.T (-1)) = α₂ (LaurentPolynomial.T (-1)) * (ψ b * φ a) := by
              rw [mul_comm (ψ b), hab, mul_one]
          _ = φ a := by rw [← mul_assoc, hprod, one_mul]
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        AlgEquiv.coe_ringEquiv, eX, LaurentPolynomial.invert_T,
        RingEquiv.refl_apply]
      rw [hα₂inv, hα₁X]
  exact @Algebra.finrank_eq_of_equiv_equiv (LaurentPolynomial K) O _ _ α₁.toAlgebra
    (LaurentPolynomial K) O _ _ α₂.toAlgebra (LaurentPolynomial.invert (R := K)).toRingEquiv
    (RingEquiv.refl O) hc

end GLUE
p2m_reactivate "P2MW.S_Algebra_finrank_quotient_span_sub_eq_of_isLocalization_away_of_mul_eq_one.GLUE"

open Polynomial in
theorem solution
    {K : Type u} [Field K] {D E O : Type u} [CommRing D] [CommRing E] [CommRing O]
    [IsDomain D] [IsDomain E] [Algebra K D] [Algebra K E] [Algebra K O]
    (φ : D →ₐ[K] O) (ψ : E →ₐ[K] O) (a : D) (b : E)
    (hφ : letI := φ.toRingHom.toAlgebra; IsLocalization.Away a O)
    (hψ : letI := ψ.toRingHom.toAlgebra; IsLocalization.Away b O)
    (hab : φ a * ψ b = 1)
    (hfinD : (Polynomial.aeval a : K[X] →ₐ[K] D).toRingHom.Finite)
    (hfinE : (Polynomial.aeval b : K[X] →ₐ[K] E).toRingHom.Finite)
    (hinj : Function.Injective (Polynomial.aeval a : K[X] →ₐ[K] D))
    (x : K) :
    Module.finrank K (D ⧸ Ideal.span {a - algebraMap K D x}) =
      Module.finrank K (E ⧸ Ideal.span {b}) :=
  GLUE.main φ ψ a b hφ hψ hab hfinD hfinE hinj x

end S_Algebra_finrank_quotient_span_sub_eq_of_isLocalization_away_of_mul_eq_one
end P2MW
export P2MW.S_Algebra_finrank_quotient_span_sub_eq_of_isLocalization_away_of_mul_eq_one (solution)
