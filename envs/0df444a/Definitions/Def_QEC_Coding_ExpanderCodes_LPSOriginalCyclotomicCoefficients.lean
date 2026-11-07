-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:30:26.704608+00:00
-- url     : https://prove2.me/theorems/27490f5f-036a-45a9-b006-6483c8e9cab5
-- title:
--   LPSOriginal Cyclotomic Coefficients
-- statement:
--   Definitions and structural lemmas for LPSOriginal Cyclotomic Coefficients, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCyclotomicCoefficients.lean

import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Finite.Basic
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
abbrev lpsOriginalCyclotomicCoefficientRing (p : ℕ) : Type :=
  AdjoinRoot (Polynomial.cyclotomic p ℤ)
def lpsOriginalCyclotomicComplexRoot (p : ℕ) : ℂ :=
  Complex.exp (2*Real.pi*Complex.I/p)
lemma lpsOriginalCyclotomicComplexRoot_primitive (p : ℕ) [Fact p.Prime] :
    IsPrimitiveRoot (lpsOriginalCyclotomicComplexRoot p) p :=
  Complex.isPrimitiveRoot_exp p (Fact.out : p.Prime).ne_zero
lemma lpsOriginalCyclotomicComplexRoot_annihilates (p : ℕ) [Fact p.Prime] :
    (Polynomial.cyclotomic p ℤ).eval₂ (Int.castRingHom ℂ)
      (lpsOriginalCyclotomicComplexRoot p)=0 := by
  have h := (lpsOriginalCyclotomicComplexRoot_primitive p).isRoot_cyclotomic
    (Fact.out : p.Prime).pos
  rw [Polynomial.eval₂_eq_eval_map,Polynomial.map_cyclotomic_int]
  exact h
def lpsOriginalCyclotomicComplexEmbedding (p : ℕ) [Fact p.Prime] :
    lpsOriginalCyclotomicCoefficientRing p →+* ℂ :=
  AdjoinRoot.lift (Int.castRingHom ℂ) (lpsOriginalCyclotomicComplexRoot p)
    (lpsOriginalCyclotomicComplexRoot_annihilates p)
lemma lpsOriginalCyclotomic_mod_root (p : ℕ) [Fact p.Prime] :
    (Polynomial.cyclotomic p ℤ).eval₂ (Int.castRingHom (ZMod p)) 1=0 := by
  rw [Polynomial.eval₂_eq_eval_map,Polynomial.map_cyclotomic_int,
    Polynomial.cyclotomic_prime]
  simp
def lpsOriginalCyclotomicReduction (p : ℕ) [Fact p.Prime] :
    lpsOriginalCyclotomicCoefficientRing p →+* ZMod p :=
  AdjoinRoot.lift (Int.castRingHom (ZMod p)) 1 (lpsOriginalCyclotomic_mod_root p)
end
end QEC.Coding.TannerLiftedProduct


