-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:59.684217+00:00
-- url     : https://prove2.me/theorems/ebe0acc4-672a-465b-9ffe-db15cb60c63f
-- title:
--   Sub Const Mem Orig
-- statement:
--   Definitions and structural lemmas for Sub Const Mem Orig, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/SubConstMemOrig.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
open MvPolynomial
variable (R : Type) [CommRing R] (ι : Type) (m : ℕ)
def orig : Ideal (MvPolynomial ι R) := Ideal.span (Set.range X)
abbrev Jet : Type := MvPolynomial ι R ⧸ orig R ι ^ (m + 1)
variable {R ι m}
theorem map_orig_pow {B : Type} [CommRing B] (f : MvPolynomial ι R →+* B) (k : ℕ) :
    Ideal.map f (orig R ι ^ k) = Ideal.span (Set.range fun i => f (X i)) ^ k := by
  rw [orig, Ideal.map_pow, Ideal.map_span, ← Set.range_comp]
  rfl
def liftJet {B : Type} [CommRing B] [Algebra R B] (f : MvPolynomial ι R →ₐ[R] B)
    (h : Ideal.span (Set.range fun i => f (X i)) ^ (m + 1) = ⊥) : Jet R ι m →ₐ[R] B :=
  Ideal.Quotient.liftₐ _ f fun a ha => by
    have : f a ∈ Ideal.map (f : MvPolynomial ι R →+* B) (orig R ι ^ (m + 1)) :=
      Ideal.mem_map_of_mem _ ha
    have h' : Ideal.span (Set.range fun i => (f : MvPolynomial ι R →+* B) (X i)) ^ (m + 1) = ⊥ := h
    rw [map_orig_pow, h'] at this
    exact (Submodule.mem_bot _).1 this
def jetMap {ι' : Type} (φ : ι → MvPolynomial ι' R) (hφ : ∀ i, φ i ∈ orig R ι') :
    Jet R ι m →ₐ[R] Jet R ι' m :=
  liftJet ((Ideal.Quotient.mkₐ R (orig R ι' ^ (m + 1))).comp (aeval φ)) (by
    apply le_bot_iff.1
    have h1 : Ideal.span (Set.range fun i =>
        ((Ideal.Quotient.mkₐ R (orig R ι' ^ (m + 1))).comp (aeval φ)) (X i)) =
        Ideal.map (Ideal.Quotient.mk (orig R ι' ^ (m + 1))) (Ideal.span (Set.range φ)) := by
      rw [Ideal.map_span, ← Set.range_comp]
      congr 1
      ext x
      simp
    rw [h1, ← Ideal.map_pow]
    have h2 : Ideal.span (Set.range φ) ^ (m + 1) ≤ orig R ι' ^ (m + 1) :=
      Ideal.pow_right_mono (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hφ i)) _
    refine (Ideal.map_mono h2).trans ?_
    rw [Ideal.map_quotient_self])
theorem X_mem_orig {ι' : Type} (i : ι') : (X i : MvPolynomial ι' R) ∈ orig R ι' :=
  Ideal.subset_span ⟨i, rfl⟩
def jetIn {K : Type} (k : K) : Jet R ι m →ₐ[R] Jet R (K × ι) m :=
  jetMap (fun i => X (k, i)) fun i => X_mem_orig (k, i)
def jetSum {K : Type} (I : Finset K) : Jet R ι m →ₐ[R] Jet R (K × ι) m :=
  jetMap (fun i => ∑ k ∈ I, X (k, i)) fun i => Ideal.sum_mem _ fun k _ => X_mem_orig (k, i)
def jetScale (c : ι → R) : Jet R ι m →ₐ[R] Jet R ι m :=
  jetMap (fun i => C (c i) * X i) fun i => Ideal.mul_mem_left _ _ (X_mem_orig i)
def jetAug : Jet R ι m →ₐ[R] R :=
  liftJet (aeval fun _ => (0 : R)) (by
    have : Ideal.span (Set.range fun i => (aeval fun _ => (0 : R)) (X i : MvPolynomial ι R)) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro _ ⟨i, rfl⟩
      simp
    rw [this, Ideal.bot_pow (Nat.succ_ne_zero m)])
def jetTan [DecidableEq ι] (ℓ : ι) : Jet R ι (m + 1) →ₐ[R] DualNumber R :=
  liftJet (aeval fun i => if i = ℓ then (DualNumber.eps : DualNumber R) else 0) (by
    apply le_bot_iff.1
    have h1 : Ideal.span (Set.range fun i =>
        (aeval fun i => if i = ℓ then (DualNumber.eps : DualNumber R) else 0) (X i : MvPolynomial ι R))
        ≤ Ideal.span {(DualNumber.eps : DualNumber R)} := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      by_cases h : i = ℓ
      · simp [h]
      · simp [h]
    refine (Ideal.pow_right_mono h1 _).trans ?_
    refine (Ideal.pow_le_pow_right (show 2 ≤ m + 1 + 1 by omega)).trans ?_
    rw [Ideal.span_singleton_pow]
    simp)
theorem sub_const_mem_orig (P : MvPolynomial ι R) :
    P - C (MvPolynomial.constantCoeff P) ∈ orig R ι := by
  induction P using MvPolynomial.induction_on
  next a =>
    simp
  next p q hp hq =>
    have h : p + q - C (MvPolynomial.constantCoeff (p + q)) =
        (p - C (MvPolynomial.constantCoeff p)) + (q - C (MvPolynomial.constantCoeff q)) := by
      simp only [map_add]
      ring
    rw [h]
    exact Ideal.add_mem _ hp hq
  next p n _ =>
    simp only [map_mul, constantCoeff_X, mul_zero, map_zero, sub_zero]
    exact Ideal.mul_mem_left _ _ (X_mem_orig n)
def degLE [Fintype ι] [DecidableEq ι] (m : ℕ) : Finset (ι →₀ ℕ) :=
  ((Finset.univ : Finset (ι → Fin (m + 1))).image fun v =>
    Finsupp.equivFunOnFinite.symm fun i => (v i : ℕ)).filter fun e => (e.sum fun _ k => k) ≤ m
def psTrunc [Fintype ι] [DecidableEq ι] (m : ℕ) (f : MvPowerSeries ι R) : MvPolynomial ι R :=
  ∑ e ∈ degLE m, monomial e (MvPowerSeries.coeff e f)
def psJet [Fintype ι] [DecidableEq ι] (m : ℕ) (f : MvPowerSeries ι R) : Jet R ι m :=
  Ideal.Quotient.mk _ (psTrunc m f)
def jetSubstPS {ι' : Type} [Fintype ι'] [DecidableEq ι'] (φ : ι → MvPowerSeries ι' R) : Jet R ι m →ₐ[R] Jet R ι' m :=
  jetMap (fun i => psTrunc m (φ i) - C (MvPolynomial.constantCoeff (psTrunc m (φ i))))
    fun i => sub_const_mem_orig _
def jetTrunc : Jet R ι (m + 1) →ₐ[R] Jet R ι m :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega))
end Formalism.L2.Pj


