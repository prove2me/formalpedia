-- Prove2me | Definitions.Def_TauCeti_NumberTheory_NumberField_Global_Approximation_Weak
-- name    : TauCeti_NumberTheory_NumberField_Global_Approximation_Weak
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:10:18.816735+00:00
-- url     : https://prove2.me/theorems/420a6e41-5e2f-4a72-b67b-2fbe75887efb
-- title:
--   Weak approximation at finite and infinite places
-- statement:
--   For a number field $K$, prescribe targets and nonzero radii at finitely many finite places, and a sign at every real place. There exists $x\in K^\times$ simultaneously approximating all finite targets within their radii and realizing every prescribed sign. This combines finite-place approximation with archimedean sign conditions.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/Approximation/Weak.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/Approximation/Weak.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Algebra_Order_Ring_Units
import Definitions.Def_TauCeti_NumberTheory_NumberField_SignApproximation
import Definitions.Def_TauCeti_NumberTheory_NumberField_Units_Signature_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Units_Signature_Integer
import Definitions.Def_TauCeti_RingTheory_Valuation_AbsoluteValue
import Definitions.Def_TauCeti_RingTheory_Valuation_Approximation
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic.Group

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Weak approximation at finite and infinite places

This file proves Artin--Whaples weak approximation for a number field in a finite product that
contains both nonarchimedean and archimedean completions.  The finite factors are Mathlib's
`HeightOneSpectrum.adicCompletion`, and the infinite factors are
`NumberField.InfinitePlace.Completion`.

The proof first applies Mathlib's weak approximation theorem for inequivalent real absolute
values to the disjoint union of the chosen places.  At a finite place, the normalized discrete
valuation is viewed as a real absolute value through `Valuation.toRealAbsoluteValue`.  Distinct
finite places are inequivalent, distinct infinite places are inequivalent, and a finite place is
inequivalent to an infinite one because every algebraic integer has finite absolute value at most
one whereas every infinite place sends `2` to `2`.

The resulting approximation inside the number field is then promoted to the actual completions.
Density of the field in each individual completion supplies nearby field-valued targets, and a
second simultaneous approximation remains inside the prescribed product neighbourhood.

Two consequences for a *unit* of `K` are derived from it.  Prescribing an approximation target at
each of finitely many finite places and a sign at each real place is one open condition on the
product, so one element of `Kˣ` meets all of them at once; specializing the finite targets to
elements of prescribed valuation gives independent valuations instead.  The archimedean half of the
prescription is not redone here: the target family and the estimate that reads a sign off an
approximation of it are
`NumberField.exists_forall_apply_eq_one_and_embedding_of_isReal_eq` and
`NumberField.mul_pos_of_infinitePlace_sub_lt`, shared with the purely archimedean statement
`NumberField.exists_ne_zero_forall_isReal_pos`.

The conclusions use `Kˣ` to package the required nonvanishing and make `signHom` applicable.  A
`K`-valued formulation would instead need an explicit `x ≠ 0` condition and sign predicates stated
directly in terms of the real embeddings.

## Main results

* `GlobalNumberFields.weakApproximation_denseRange`: the diagonal image of a number field is dense
  in every finite product of finite and infinite completions.
* `GlobalNumberFields.denseRange_algebraMap_embedding_of_isReal`: the same with each real
  completion read as `ℝ` through the embedding of its real place.
* `GlobalNumberFields.exists_fieldUnit_valuation_sub_lt_and_signHom_eq`: one field unit of `K`
  approximates
  independently prescribed targets at finitely many finite places while realizing a prescribed
  sign at every real place.
* `GlobalNumberFields.exists_fieldUnit_valuation_eq_and_signHom_eq`: the same with prescribed
  valuations in place of the approximation targets.

## References

The weak approximation theorem is due to E. Artin and G. Whaples, *Axiomatic characterization of
fields by the product formula for valuations*, Bull. Amer. Math. Soc. **51** (1945).  The mixed
number-field formulation also appears in J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number
Theory*, Chapter II.
-/

 section

open Filter IsDedekindDomain NumberField NumberField.InfinitePlace Set Topology
open scoped NNReal Topology WithZero

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

 abbrev FinitePlace (K : Type*) [Field K]
    (S : Finset (HeightOneSpectrum (RingOfIntegers K))) :=
  {v : HeightOneSpectrum (RingOfIntegers K) // v ∈ S}

 noncomputable def mixedAbsoluteValue
    {Sₑ : Finset (HeightOneSpectrum (RingOfIntegers K))} {Sinf : Finset (InfinitePlace K)} :
    FinitePlace K Sₑ ⊕ {w : InfinitePlace K // w ∈ Sinf} → AbsoluteValue K ℝ
  | .inl v => (v.1.valuation K).toRealAbsoluteValue
  | .inr w => w.1.1

 theorem mixedAbsoluteValue_isNontrivial
    {Sₑ : Finset (HeightOneSpectrum (RingOfIntegers K))} {Sinf : Finset (InfinitePlace K)}
    (v : FinitePlace K Sₑ ⊕ {w : InfinitePlace K // w ∈ Sinf}) :
    (mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) v).IsNontrivial := by
  cases v with
  | inl v =>
      exact (Valuation.toRealAbsoluteValue_isNontrivial_iff (v.1.valuation K)).mpr inferInstance
  | inr w =>
      exact w.1.isNontrivial

 theorem finite_mixedAbsoluteValue_not_isEquiv_infinite
    {Sₑ : Finset (HeightOneSpectrum (RingOfIntegers K))} {Sinf : Finset (InfinitePlace K)}
    (v : FinitePlace K Sₑ) (w : {w : InfinitePlace K // w ∈ Sinf}) :
    ¬(mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) (Sum.inl v)).IsEquiv
      (mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) (Sum.inr w)) := by
  intro h
  have hfinite : mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) (Sum.inl v) (2 : K) ≤
      mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) (Sum.inl v) 1 := by
    rw [mixedAbsoluteValue, Valuation.toRealAbsoluteValue_le_iff, map_one,
      ← map_ofNat (algebraMap (RingOfIntegers K) K) 2]
    exact v.1.valuation_le_one (K := K) 2
  have hinfinite : ¬mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) (Sum.inr w) (2 : K) ≤
      mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) (Sum.inr w) 1 := by
    have hw : (1 : ℝ) < w.1.1 (2 : K) := by
      rw [← InfinitePlace.coe_apply, ← Nat.cast_ofNat (R := K) (n := 2),
        InfinitePlace.map_natCast]
      norm_num
    simpa only [mixedAbsoluteValue, map_one, not_le] using hw
  exact hinfinite ((h (2 : K) 1).mp hfinite)

 theorem mixedAbsoluteValue_pairwise_not_isEquiv
    {Sₑ : Finset (HeightOneSpectrum (RingOfIntegers K))} {Sinf : Finset (InfinitePlace K)} :
    Pairwise fun v w : FinitePlace K Sₑ ⊕ {w : InfinitePlace K // w ∈ Sinf} =>
      ¬(mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) v).IsEquiv
        (mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) w) := by
  intro v w hvw
  cases v with
  | inl v =>
      cases w with
      | inl w =>
          intro h
          apply hvw
          apply congrArg Sum.inl
          apply Subtype.ext
          exact HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := K)
            ((Valuation.toRealAbsoluteValue_isEquiv_iff _ _).mp h)
      | inr w =>
          exact finite_mixedAbsoluteValue_not_isEquiv_infinite v w
  | inr v =>
      cases w with
      | inl w =>
          exact fun h => finite_mixedAbsoluteValue_not_isEquiv_infinite w v h.symm
      | inr w =>
          intro h
          apply hvw
          apply congrArg Sum.inr
          apply Subtype.ext
          exact (InfinitePlace.eq_iff_isEquiv (K := K)).mpr h

 theorem exists_mixed_approximation
    {Sₑ : Finset (HeightOneSpectrum (RingOfIntegers K))} {Sinf : Finset (InfinitePlace K)}
    (aₑ : FinitePlace K Sₑ → K) (ainf : {w : InfinitePlace K // w ∈ Sinf} → K)
    (εₑ : FinitePlace K Sₑ → ℤᵐ⁰) (hεₑ : ∀ v, εₑ v ≠ 0)
    (einf : {w : InfinitePlace K // w ∈ Sinf} → ℝ) (heinf : ∀ w, 0 < einf w) :
    ∃ x : K, (∀ v, v.1.valuation K (x - aₑ v) < εₑ v) ∧
      ∀ w, w.1 (x - ainf w) < einf w := by
  classical
  choose p hp using fun (v : FinitePlace K Sₑ) => v.1.valuation_surjective K (εₑ v)
  let a : FinitePlace K Sₑ ⊕ {w : InfinitePlace K // w ∈ Sinf} → K
    | .inl v => aₑ v
    | .inr w => ainf w
  let ρ : FinitePlace K Sₑ ⊕ {w : InfinitePlace K // w ∈ Sinf} → ℝ
    | .inl v => mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) (Sum.inl v) (p v)
    | .inr w => einf w
  have hρ : ∀ i, 0 < ρ i := by
    rintro (v | w)
    · exact (mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) (Sum.inl v)).pos_iff.mpr
        ((v.1.valuation K).ne_zero_iff.mp (hp v ▸ hεₑ v))
    · exact heinf w
  cases @isEmpty_or_nonempty (FinitePlace K Sₑ ⊕ {w : InfinitePlace K // w ∈ Sinf}) with
  | inl h =>
      refine ⟨0,
        fun v => (h.false (Sum.inl (β := {w : InfinitePlace K // w ∈ Sinf}) v)).elim,
        fun w => (h.false (Sum.inr (α := FinitePlace K Sₑ) w)).elim⟩
  | inr h =>
      let _ := Fintype.ofFinite (FinitePlace K Sₑ ⊕ {w : InfinitePlace K // w ∈ Sinf})
      let r := Finset.univ.inf' Finset.univ_nonempty ρ
      have hr : 0 < r := (Finset.lt_inf'_iff _).mpr fun i _ => hρ i
      obtain ⟨x, hx⟩ := (AbsoluteValue.denseRange_algebraMap_pi
          (v := fun i : FinitePlace K Sₑ ⊕ {w : InfinitePlace K // w ∈ Sinf} =>
            mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) i)
          (fun i => mixedAbsoluteValue_isNontrivial i)
          mixedAbsoluteValue_pairwise_not_isEquiv).exists_dist_lt
        (fun i => WithAbs.toAbs
          (mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) i) (a i)) (ε := r) hr
      refine ⟨x, fun v => ?_, fun w => ?_⟩
      · have hv := (dist_pi_lt_iff hr).mp hx (Sum.inl v)
        rw [dist_comm, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub] at hv
        simp only [a] at hv
        have hvρ : mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) (Sum.inl v)
            (x - aₑ v) < ρ (Sum.inl v) :=
          hv.trans_le (Finset.inf'_le ρ (Finset.mem_univ (Sum.inl v)))
        simp only [ρ] at hvρ
        rw [← hp v]
        exact lt_of_not_ge fun h => not_le.mpr hvρ
          ((Valuation.toRealAbsoluteValue_le_iff _).mpr h)
      · have hw := (dist_pi_lt_iff hr).mp hx (Sum.inr w)
        rw [dist_comm, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub] at hw
        simp only [a, mixedAbsoluteValue] at hw
        exact hw.trans_le (Finset.inf'_le ρ (Finset.mem_univ (Sum.inr w)))





/-! ### Simultaneous approximation in `Kˣ`

The two statements below use `Kˣ` to package the required nonvanishing and make `signHom`
applicable.  A `K`-valued version would need an explicit `x ≠ 0` condition and would state the sign
requirements directly as predicates on the real embeddings.
-/

/-- **Simultaneous approximation with prescribed signs.**  Given a finite set `S` of finite
places, a target `a v` and a nonzero radius `γ v` at each place of `S`, and a prescribed sign at
*every* real place, one and the same field unit of `K` approximates each finite target to within
its own radius and has each prescribed sign.

The finite conditions are independent of one another and of the archimedean ones; this is the
`Kˣ`-valued form of `weakApproximation_denseRange`, and it is what a congruence-and-positivity
statement for a modulus is built from. -/
theorem exists_fieldUnit_valuation_sub_lt_and_signHom_eq
    {S : Finset (HeightOneSpectrum (RingOfIntegers K))}
    (a : HeightOneSpectrum (RingOfIntegers K) → K)
    (γ : HeightOneSpectrum (RingOfIntegers K) → ℤᵐ⁰) (hγ : ∀ v ∈ S, γ v ≠ 0)
    (s : {w : InfinitePlace K // w.IsReal} → ℤˣ) :
    ∃ x : Kˣ, (∀ v ∈ S, v.valuation K ((x : K) - a v) < γ v) ∧ signHom x = s := by
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
  -- The archimedean targets: absolute value one everywhere, with the prescribed signs.
  obtain ⟨b, hbabs, hbsign⟩ :=
    NumberField.exists_forall_apply_eq_one_and_embedding_of_isReal_eq (K := K) s
  obtain ⟨x, hxf, hxi⟩ := exists_mixed_approximation (Sₑ := S) (Sinf := Finset.univ)
    (fun v => a v.1) (fun w => b w.1) (fun v => γ v.1) (fun v => hγ v.1 v.2)
    (fun _ => 1) (fun _ => one_pos)
  have hxi' : ∀ w : InfinitePlace K, w (x - b w) < 1 := fun w => hxi ⟨w, Finset.mem_univ w⟩
  have hx0 := NumberField.ne_zero_of_infinitePlace_sub_lt (hbabs w₀) (hxi' w₀)
  refine ⟨Units.mk0 x hx0, fun v hv => by simpa using hxf ⟨v, hv⟩, ?_⟩
  funext w
  have h := NumberField.mul_pos_of_infinitePlace_sub_lt w.2 (hbabs w.1) (hxi' w.1)
  rw [hbsign w] at h
  rcases Int.units_eq_one_or (s w) with hs | hs <;> rw [hs] at h ⊢
  · rw [signHom_apply_eq_one_iff, Units.val_mk0]
    simpa using h
  · rw [signHom_apply_eq_neg_one_iff, Units.val_mk0]
    simpa using h





end TauCeti.GlobalNumberFields

end
end


