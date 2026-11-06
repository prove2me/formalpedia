-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncPlaceClassification
-- name    : QEC_Coding_AlgebraicGeometry_Places_RatFuncPlaceClassification
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:19:17.001204+00:00
-- url     : https://prove2.me/theorems/f4125826-3bde-4939-89b8-cf30e50508d2
-- title:
--   Rat Func Place Classification
-- statement:
--   Definitions and structural lemmas for Rat Func Place Classification, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RatFuncPlaceClassification.lean

import Mathlib.NumberTheory.RatFunc.Ostrowski
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_trivialOnConstants
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_normalizedValuation_eq_of_isEquiv

set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open MonoidWithZeroHom
namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace
variable {k : Type*} [Field k] [Finite k]
noncomputable def rationalAdic
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) : GlobalPlace k (RatFunc k) :=
  { valuation := p.valuation (RatFunc k)
    normalized := p.valuation_surjective (RatFunc k) }
noncomputable def rationalPlaceOfOption :
    Option (IsDedekindDomain.HeightOneSpectrum k[X]) → GlobalPlace k (RatFunc k)
  | none => rationalInfinity k
  | some p => rationalAdic p
theorem globalPlace_eq_of_valuation_eq
    {P Q : GlobalPlace k (RatFunc k)} (hvaluation : P.valuation = Q.valuation) : P = Q := by
  cases P
  cases Q
  cases hvaluation
  rfl
theorem globalPlace_valuation_isNontrivial
    (P : GlobalPlace k (RatFunc k)) : P.valuation.IsNontrivial := by
  rw [Valuation.isNontrivial_iff_exists_lt_one]
  refine ⟨P.uniformizer, ?_, ?_⟩
  · apply P.valuation.ne_zero_iff.mp
    rw [P.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  · rw [P.valuation_uniformizer, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
theorem rationalPlaceOfOption_injective :
    Function.Injective (rationalPlaceOfOption (k := k)) := by
  classical
  intro P Q hPQ
  cases P with
  | none =>
      cases Q with
      | none => rfl
      | some q =>
          exfalso
          apply RatFunc.adicValuation_ne_inftyValuation q
          exact (congrArg
            (fun R : GlobalPlace k (RatFunc k) => R.valuation) hPQ).symm
  | some p =>
      cases Q with
      | none =>
          exfalso
          apply RatFunc.adicValuation_ne_inftyValuation p
          exact congrArg (fun R : GlobalPlace k (RatFunc k) => R.valuation) hPQ
      | some q =>
          congr 1
          apply IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation
            (K := RatFunc k)
          exact Valuation.IsEquiv.of_eq
            (congrArg (fun R : GlobalPlace k (RatFunc k) => R.valuation) hPQ)
theorem rationalPlaceOfOption_surjective :
    Function.Surjective (rationalPlaceOfOption (k := k)) := by
  classical
  intro P
  letI : P.valuation.IsNontrivial := globalPlace_valuation_isNontrivial P
  letI : IsCyclic (valueGroup (MonoidWithZeroHom.ofClass P.valuation)) := inferInstance
  letI : Nontrivial (valueGroup (MonoidWithZeroHom.ofClass P.valuation)) := inferInstance
  letI : P.valuation.IsRankOneDiscrete :=
    Valuation.IsRankOneDiscrete.mk' P.valuation
  letI : P.valuation.IsTrivialOn k := P.trivialOnConstants
  rcases RatFunc.valuation_isEquiv_infty_or_adic (v := P.valuation) with
    ⟨hInfinity, _⟩ | ⟨hadic, _⟩
  · refine ⟨none, ?_⟩
    apply globalPlace_eq_of_valuation_eq
    exact (normalizedValuation_eq_of_isEquiv
      P.valuation
      (RatFunc.inftyValuation k)
      P.normalized
      (rationalInfinity_surjective k)
      hInfinity).symm
  · obtain ⟨p, hp, _⟩ := hadic
    refine ⟨some p, ?_⟩
    apply globalPlace_eq_of_valuation_eq
    exact (normalizedValuation_eq_of_isEquiv
      P.valuation
      (p.valuation (RatFunc k))
      P.normalized
      (p.valuation_surjective (RatFunc k))
      hp).symm
noncomputable def rationalPlaceEquiv :
    Option (IsDedekindDomain.HeightOneSpectrum k[X]) ≃ GlobalPlace k (RatFunc k) :=
  Equiv.ofBijective (rationalPlaceOfOption (k := k))
    ⟨rationalPlaceOfOption_injective, rationalPlaceOfOption_surjective⟩
end GlobalPlace
end QEC.Coding.AlgebraicGeometry


