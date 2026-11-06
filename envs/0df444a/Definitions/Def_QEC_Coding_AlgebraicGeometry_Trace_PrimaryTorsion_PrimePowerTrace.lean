-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PrimePowerTrace
-- name    : QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PrimePowerTrace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:33:30.639396+00:00
-- url     : https://prove2.me/theorems/874f9e17-8d30-4288-9fb6-b0d9b3272d79
-- title:
--   Prime Power Trace
-- statement:
--   Definitions and structural lemmas for Prime Power Trace, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/PrimePowerTrace.lean

import Mathlib.Algebra.Module.PID
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R]
noncomputable def primePowerQuotientMul (q : R) (e : ℕ) (r : R) :
    (R ⧸ Ideal.span {q ^ e}) →ₗ[R] (R ⧸ Ideal.span {q ^ e}) :=
  Algebra.lmul R (R ⧸ Ideal.span {q ^ e})
    (Ideal.Quotient.mk (Ideal.span {q ^ e}) r)
theorem primaryTorsionLayer_primePowerQuotient (q : R) (hq : q ≠ 0)
    (e i : ℕ) (hi : i ≤ e) :
    primaryTorsionLayer (Ideal.span {q})
        (R ⧸ Ideal.span {q ^ e}) i =
      R ∙ Ideal.Quotient.mk (Ideal.span {q ^ e}) (q ^ (e - i)) := by
  have hpow : q ^ i * q ^ (e - i) = q ^ e := by
    rw [← pow_add, Nat.add_sub_of_le hi]
  rw [← hpow, primaryTorsionLayer, Ideal.span_singleton_pow,
    Submodule.torsionBySet_ideal_span_singleton_eq]
  exact Ideal.Quotient.torsionBy_eq_span_singleton
    (q ^ i) (q ^ (e - i))
      (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero i hq))
def primePowerGradeGenerator (q : R) (hq : q ≠ 0)
    (e i : ℕ) (hi : i < e) :
    primaryTorsionLayer (Ideal.span {q})
      (R ⧸ Ideal.span {q ^ e}) (i + 1) :=
  ⟨Ideal.Quotient.mk (Ideal.span {q ^ e}) (q ^ (e - (i + 1))), by
    rw [primaryTorsionLayer_primePowerQuotient q hq e (i + 1) hi]
    exact Submodule.mem_span_singleton_self _⟩
def primePowerGradeMap (q : R) (hq : q ≠ 0)
    (e i : ℕ) (hi : i < e) :
    R →ₗ[R] primaryTorsionGrade (Ideal.span {q})
      (R ⧸ Ideal.span {q ^ e}) i :=
  LinearMap.toSpanSingleton R _
    (Submodule.Quotient.mk (primePowerGradeGenerator q hq e i hi))
theorem primePowerGradeMap_surjective (q : R) (hq : q ≠ 0)
    (e i : ℕ) (hi : i < e) :
    Function.Surjective (primePowerGradeMap q hq e i hi) := by
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ x =>
      have hx : (x : R ⧸ Ideal.span {q ^ e}) ∈
          R ∙ Ideal.Quotient.mk (Ideal.span {q ^ e})
            (q ^ (e - (i + 1))) := by
        rw [← primaryTorsionLayer_primePowerQuotient q hq e (i + 1) hi]
        exact x.property
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hx
      refine ⟨r, ?_⟩
      change r • (Submodule.Quotient.mk
          (primePowerGradeGenerator q hq e i hi) :
            primaryTorsionGrade (Ideal.span {q})
              (R ⧸ Ideal.span {q ^ e}) i) =
        (Submodule.Quotient.mk x :
          primaryTorsionGrade (Ideal.span {q})
            (R ⧸ Ideal.span {q ^ e}) i)
      rw [← Submodule.Quotient.mk_smul]
      congr 2
      apply Subtype.ext
      exact hr
theorem primePowerGradeMap_ker (q : R) (hq : q ≠ 0)
    (e i : ℕ) (hi : i < e) :
    LinearMap.ker (primePowerGradeMap q hq e i hi) = Ideal.span {q} := by
  ext r
  constructor
  · intro hr
    rw [LinearMap.mem_ker] at hr
    change r • (Submodule.Quotient.mk
        (primePowerGradeGenerator q hq e i hi) :
          primaryTorsionGrade (Ideal.span {q})
            (R ⧸ Ideal.span {q ^ e}) i) = 0 at hr
    rw [← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at hr
    change r • (primePowerGradeGenerator q hq e i hi :
      R ⧸ Ideal.span {q ^ e}) ∈
        primaryTorsionLayer (Ideal.span {q})
          (R ⧸ Ideal.span {q ^ e}) i at hr
    rw [primaryTorsionLayer_primePowerQuotient q hq e i hi.le,
      Submodule.mem_span_singleton] at hr
    obtain ⟨c, hc⟩ := hr
    change Ideal.Quotient.mk (Ideal.span {q ^ e})
        (c * q ^ (e - i)) =
      Ideal.Quotient.mk (Ideal.span {q ^ e})
        (r * q ^ (e - (i + 1))) at hc
    rw [Ideal.Quotient.eq] at hc
    have hpow_le : Ideal.span {q ^ e} ≤ Ideal.span {q ^ (e - i)} := by
      rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
      exact Ideal.pow_le_pow_right (Nat.sub_le e i)
    have hcq : c * q ^ (e - i) ∈ Ideal.span {q ^ (e - i)} :=
      Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    have hrq : r * q ^ (e - (i + 1)) ∈ Ideal.span {q ^ (e - i)} := by
      have := (Ideal.span {q ^ (e - i)}).sub_mem hcq (hpow_le hc)
      simpa only [sub_sub_cancel] using this
    have hsub : e - i = (e - (i + 1)) + 1 := by omega
    rw [hsub, pow_succ, Ideal.mem_span_singleton] at hrq
    obtain ⟨d, hd⟩ := hrq
    rw [mul_comm r (q ^ (e - (i + 1))), mul_assoc] at hd
    have hd' : r = q * d :=
      mul_left_cancel₀ (pow_ne_zero (e - (i + 1)) hq) hd
    rw [Ideal.mem_span_singleton]
    exact ⟨d, hd'⟩
  · intro hr
    rw [LinearMap.mem_ker]
    change r • (Submodule.Quotient.mk
        (primePowerGradeGenerator q hq e i hi) :
          primaryTorsionGrade (Ideal.span {q})
            (R ⧸ Ideal.span {q ^ e}) i) = 0
    have hann := primaryTorsionGrade_annihilated
      (R := R) (M := R ⧸ Ideal.span {q ^ e}) (Ideal.span {q}) i
    exact @hann
      (Submodule.Quotient.mk (primePowerGradeGenerator q hq e i hi)) ⟨r, hr⟩
noncomputable def primaryTorsionGradeEquivPrimePowerQuotientR
    (q : R) (hq : q ≠ 0) (e i : ℕ) (hi : i < e) :
    (R ⧸ Ideal.span {q}) ≃ₗ[R]
      primaryTorsionGrade (Ideal.span {q})
        (R ⧸ Ideal.span {q ^ e}) i :=
  (Submodule.quotEquivOfEq (Ideal.span {q})
      (LinearMap.ker (primePowerGradeMap q hq e i hi))
      (primePowerGradeMap_ker q hq e i hi).symm).trans
    ((primePowerGradeMap q hq e i hi).quotKerEquivOfSurjective
      (primePowerGradeMap_surjective q hq e i hi))
noncomputable def primaryTorsionGradeEquivPrimePowerQuotient
    (q : R) (hq : q ≠ 0) (e i : ℕ) (hi : i < e) :
    letI := primaryTorsionGradeModule
      (M := R ⧸ Ideal.span {q ^ e}) (Ideal.span {q}) i
    (R ⧸ Ideal.span {q}) ≃ₗ[R ⧸ Ideal.span {q}]
      primaryTorsionGrade (Ideal.span {q})
        (R ⧸ Ideal.span {q ^ e}) i := by
  let h := primaryTorsionGrade_annihilated
    (R := R) (M := R ⧸ Ideal.span {q ^ e}) (Ideal.span {q}) i
  letI : Module (R ⧸ Ideal.span {q})
      (primaryTorsionGrade (Ideal.span {q})
        (R ⧸ Ideal.span {q ^ e}) i) := h.module
  let E := primaryTorsionGradeEquivPrimePowerQuotientR q hq e i hi
  exact
    { toEquiv := E.toEquiv
      map_add' := E.map_add
      map_smul' := by
        intro c x
        induction c using Quotient.inductionOn' with
        | _ r =>
            change E (Ideal.Quotient.mk (Ideal.span {q}) r • x) =
              Ideal.Quotient.mk (Ideal.span {q}) r • E x
            rw [Module.IsTorsionBySet.mk_smul h]
            exact E.map_smul r x }
end QEC.Coding.AlgebraicGeometry


