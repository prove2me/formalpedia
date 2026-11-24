-- Prove2me | solution 1 for AdicCompletion.exists_etale_aeval_eq_zero_of_aeval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-24T05:33:12.363969+00:00
-- url     : https://prove2.me/submissions/a5ac7ec7-d876-4a22-b414-110e0d682ac1

import Mathlib
import Definitions.Def_RPLib_FX_ArtinApprox_04

set_option autoImplicit false

theorem solution
    (K : Type) [Field K] [PerfectField K] (A : Type) [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    (χ : A →ₐ[K] K) (n m : ℕ) (f : Fin m → MvPolynomial (Fin n) A)
    (ŷ : Fin n → AdicCompletion (RingHom.ker χ) A) (hŷ : ∀ j, MvPolynomial.aeval ŷ (f j) = 0) :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra A R') (_ : Algebra.Etale A R') (χ' : R' →+* K)
      (y : Fin n → R'), (∀ a : A, χ' (algebraMap A R' a) = χ a) ∧ (∀ j, MvPolynomial.aeval y (f j) = 0) ∧
      ∀ i, ∃ a : A, χ' (y i) = χ a ∧ AdicCompletion.evalₐ (RingHom.ker χ) 1 (ŷ i) = Ideal.Quotient.mk _ a := by
  exact RamanujanPetersson.EtPBC.Cov.artinApproxAt χ n m f ŷ hŷ
