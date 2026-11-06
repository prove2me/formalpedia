-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicFactorTrace
-- name    : QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicFactorTrace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:35:30.26319+00:00
-- url     : https://prove2.me/theorems/db7f9d8f-1497-44c9-8992-3820f3fd41f4
-- title:
--   Cyclic Factor Trace
-- statement:
--   Definitions and structural lemmas for Cyclic Factor Trace, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/CyclicFactorTrace.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PrimePowerTrace
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R]
noncomputable def cyclicPowerFactorQuotientMul
    (q : R) (e : ℕ) (b r : R) :
    (R ⧸ Ideal.span {q ^ e * b}) →ₗ[R]
      (R ⧸ Ideal.span {q ^ e * b}) :=
  Algebra.lmul R (R ⧸ Ideal.span {q ^ e * b})
    (Ideal.Quotient.mk (Ideal.span {q ^ e * b}) r)
theorem primaryTorsionLayer_cyclicPowerFactorQuotient
    (q : R) (hq : q ≠ 0) (e : ℕ) (b : R) (i : ℕ) (hi : i ≤ e) :
    primaryTorsionLayer (Ideal.span {q})
        (R ⧸ Ideal.span {q ^ e * b}) i =
      R ∙ Ideal.Quotient.mk (Ideal.span {q ^ e * b})
        (q ^ (e - i) * b) := by
  have hfactor : q ^ i * (q ^ (e - i) * b) = q ^ e * b := by
    rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hi]
  rw [← hfactor, primaryTorsionLayer, Ideal.span_singleton_pow,
    Submodule.torsionBySet_ideal_span_singleton_eq]
  exact Ideal.Quotient.torsionBy_eq_span_singleton
    (q ^ i) (q ^ (e - i) * b)
      (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero i hq))
def cyclicPowerFactorGradeGenerator
    (q : R) (hq : q ≠ 0) (e : ℕ) (b : R)
    (i : ℕ) (hi : i < e) :
    primaryTorsionLayer (Ideal.span {q})
      (R ⧸ Ideal.span {q ^ e * b}) (i + 1) :=
  ⟨Ideal.Quotient.mk (Ideal.span {q ^ e * b})
      (q ^ (e - (i + 1)) * b), by
    rw [primaryTorsionLayer_cyclicPowerFactorQuotient
      q hq e b (i + 1) hi]
    exact Submodule.mem_span_singleton_self _⟩
def cyclicPowerFactorGradeMap
    (q : R) (hq : q ≠ 0) (e : ℕ) (b : R)
    (i : ℕ) (hi : i < e) :
    R →ₗ[R] primaryTorsionGrade (Ideal.span {q})
      (R ⧸ Ideal.span {q ^ e * b}) i :=
  LinearMap.toSpanSingleton R _
    (Submodule.Quotient.mk
      (cyclicPowerFactorGradeGenerator q hq e b i hi))
theorem cyclicPowerFactorGradeMap_surjective
    (q : R) (hq : q ≠ 0) (e : ℕ) (b : R)
    (i : ℕ) (hi : i < e) :
    Function.Surjective (cyclicPowerFactorGradeMap q hq e b i hi) := by
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ x =>
      have hx : (x : R ⧸ Ideal.span {q ^ e * b}) ∈
          R ∙ Ideal.Quotient.mk (Ideal.span {q ^ e * b})
            (q ^ (e - (i + 1)) * b) := by
        rw [← primaryTorsionLayer_cyclicPowerFactorQuotient
          q hq e b (i + 1) hi]
        exact x.property
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hx
      refine ⟨r, ?_⟩
      change r • (Submodule.Quotient.mk
          (cyclicPowerFactorGradeGenerator q hq e b i hi) :
            primaryTorsionGrade (Ideal.span {q})
              (R ⧸ Ideal.span {q ^ e * b}) i) =
        (Submodule.Quotient.mk x :
          primaryTorsionGrade (Ideal.span {q})
            (R ⧸ Ideal.span {q ^ e * b}) i)
      rw [← Submodule.Quotient.mk_smul]
      congr 2
      apply Subtype.ext
      exact hr
theorem cyclicPowerFactorGradeMap_ker
    (q : R) (hq : q ≠ 0) (e : ℕ) (b : R) (hb : b ≠ 0)
    (i : ℕ) (hi : i < e) :
    LinearMap.ker (cyclicPowerFactorGradeMap q hq e b i hi) =
      Ideal.span {q} := by
  ext r
  constructor
  · intro hr
    rw [LinearMap.mem_ker] at hr
    change r • (Submodule.Quotient.mk
        (cyclicPowerFactorGradeGenerator q hq e b i hi) :
          primaryTorsionGrade (Ideal.span {q})
            (R ⧸ Ideal.span {q ^ e * b}) i) = 0 at hr
    rw [← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at hr
    change r • (cyclicPowerFactorGradeGenerator q hq e b i hi :
      R ⧸ Ideal.span {q ^ e * b}) ∈
        primaryTorsionLayer (Ideal.span {q})
          (R ⧸ Ideal.span {q ^ e * b}) i at hr
    rw [primaryTorsionLayer_cyclicPowerFactorQuotient
      q hq e b i hi.le, Submodule.mem_span_singleton] at hr
    obtain ⟨c, hc⟩ := hr
    change Ideal.Quotient.mk (Ideal.span {q ^ e * b})
        (c * (q ^ (e - i) * b)) =
      Ideal.Quotient.mk (Ideal.span {q ^ e * b})
        (r * (q ^ (e - (i + 1)) * b)) at hc
    rw [Ideal.Quotient.eq] at hc
    have hfactor : q ^ i * (q ^ (e - i) * b) = q ^ e * b := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hi.le]
    have hpow_le : Ideal.span {q ^ e * b} ≤
        Ideal.span {q ^ (e - i) * b} := by
      rw [Ideal.span_le, Set.singleton_subset_iff, ← hfactor]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    have hcq : c * (q ^ (e - i) * b) ∈
        Ideal.span {q ^ (e - i) * b} :=
      Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    have hrq : r * (q ^ (e - (i + 1)) * b) ∈
        Ideal.span {q ^ (e - i) * b} := by
      have := (Ideal.span {q ^ (e - i) * b}).sub_mem hcq (hpow_le hc)
      simpa only [sub_sub_cancel] using this
    have hsub : e - i = (e - (i + 1)) + 1 := by omega
    rw [Ideal.mem_span_singleton] at hrq
    obtain ⟨d, hd⟩ := hrq
    have hgenerator : q ^ (e - i) * b =
        (q ^ (e - (i + 1)) * b) * q := by
      rw [hsub, pow_succ]
      ring
    rw [hgenerator, mul_comm r (q ^ (e - (i + 1)) * b),
      mul_assoc] at hd
    have hnonzero : q ^ (e - (i + 1)) * b ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hq) hb
    have hd_cancel : (q ^ (e - (i + 1)) * b) * r =
        (q ^ (e - (i + 1)) * b) * (q * d) := by
      simpa only [mul_assoc] using hd
    have hd' : r = q * d := mul_left_cancel₀ hnonzero hd_cancel
    rw [Ideal.mem_span_singleton]
    exact ⟨d, hd'⟩
  · intro hr
    rw [LinearMap.mem_ker]
    change r • (Submodule.Quotient.mk
        (cyclicPowerFactorGradeGenerator q hq e b i hi) :
          primaryTorsionGrade (Ideal.span {q})
            (R ⧸ Ideal.span {q ^ e * b}) i) = 0
    have hann := primaryTorsionGrade_annihilated
      (R := R) (M := R ⧸ Ideal.span {q ^ e * b})
        (Ideal.span {q}) i
    exact @hann
      (Submodule.Quotient.mk
        (cyclicPowerFactorGradeGenerator q hq e b i hi)) ⟨r, hr⟩
noncomputable def primaryTorsionGradeEquivCyclicPowerFactorQuotientR
    (q : R) (hq : q ≠ 0) (e : ℕ) (b : R) (hb : b ≠ 0)
    (i : ℕ) (hi : i < e) :
    (R ⧸ Ideal.span {q}) ≃ₗ[R]
      primaryTorsionGrade (Ideal.span {q})
        (R ⧸ Ideal.span {q ^ e * b}) i :=
  (Submodule.quotEquivOfEq (Ideal.span {q})
      (LinearMap.ker (cyclicPowerFactorGradeMap q hq e b i hi))
      (cyclicPowerFactorGradeMap_ker q hq e b hb i hi).symm).trans
    ((cyclicPowerFactorGradeMap q hq e b i hi).quotKerEquivOfSurjective
      (cyclicPowerFactorGradeMap_surjective q hq e b i hi))
noncomputable def primaryTorsionGradeEquivCyclicPowerFactorQuotient
    (q : R) (hq : q ≠ 0) (e : ℕ) (b : R) (hb : b ≠ 0)
    (i : ℕ) (hi : i < e) :
    letI := primaryTorsionGradeModule
      (M := R ⧸ Ideal.span {q ^ e * b}) (Ideal.span {q}) i
    (R ⧸ Ideal.span {q}) ≃ₗ[R ⧸ Ideal.span {q}]
      primaryTorsionGrade (Ideal.span {q})
        (R ⧸ Ideal.span {q ^ e * b}) i := by
  let h := primaryTorsionGrade_annihilated
    (R := R) (M := R ⧸ Ideal.span {q ^ e * b})
      (Ideal.span {q}) i
  letI : Module (R ⧸ Ideal.span {q})
      (primaryTorsionGrade (Ideal.span {q})
        (R ⧸ Ideal.span {q ^ e * b}) i) := h.module
  let E := primaryTorsionGradeEquivCyclicPowerFactorQuotientR
    q hq e b hb i hi
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


