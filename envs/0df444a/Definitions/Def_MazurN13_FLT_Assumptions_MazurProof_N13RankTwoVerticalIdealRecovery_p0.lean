-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RankTwoVerticalIdealRecovery_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13RankTwoVerticalIdealRecovery_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:45:59.890444+00:00
-- url     : https://prove2.me/theorems/b68c91f2-9f93-4c13-82f1-e16081597c1b
-- title:
--   FLT.Assumptions.MazurProof.N13RankTwoVerticalIdealRecovery source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13RankTwoVerticalIdealRecovery

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13RankTwoVerticalIdealRecovery
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RankTwoIdealRecovery_p0
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option autoImplicit false




open Polynomial

/-!
# Recovering a vertical graph from a rank-two quotient

If a quotient has basis `{1,y}`, multiplication by `y` supplies its monic
quadratic relation, while `x` is linear in `y`.  This file gives the
ideal-correspondence argument recovering the ambient ideal as
`(m(y), x-s(y))`.
-/

namespace MazurProof.N13RankTwoVerticalIdealRecovery

noncomputable section

universe uR uA

variable {R : Type uR} {A : Type uA}
variable [CommRing R] [CommRing A] [Algebra R A]

def HasVerticalPolynomialNormalForm
    (y x : A) (s : R[X]) : Prop :=
  ∀ z : A, ∃ p : R[X], ∃ q : A,
    z = aeval y p + q * (x - aeval y s)

theorem verticalNormalForm_of_rankTwoPolynomialNormalForm
    (x y : A)
    (hnormal :
      N13RankTwoIdealRecovery.HasRankTwoPolynomialNormalForm
        (R := R) x y)
    (s : R[X]) :
    HasVerticalPolynomialNormalForm (R := R) y x s := by
  intro z
  obtain ⟨p, q, hz⟩ := hnormal z
  obtain ⟨cp, hcp⟩ :=
    sub_dvd_eval_sub x (aeval y s)
      (p.map (algebraMap R A))
  obtain ⟨cq, hcq⟩ :=
    sub_dvd_eval_sub x (aeval y s)
      (q.map (algebraMap R A))
  refine
    ⟨p.comp s + (q.comp s) * X,
      cp + cq * y, ?_⟩
  have hp :
      aeval x p - aeval y (p.comp s) =
        (x - aeval y s) * cp := by
    simpa [aeval_def, aeval_comp] using hcp
  have hq :
      aeval x q - aeval y (q.comp s) =
        (x - aeval y s) * cq := by
    simpa [aeval_def, aeval_comp] using hcq
  calc
    z =
        aeval x p + aeval x q * y := hz
    _ =
        aeval y (p.comp s + (q.comp s) * X) +
          (cp + cq * y) * (x - aeval y s) := by
      simp only [map_add, map_mul, aeval_X]
      linear_combination hp + hq * y

theorem ideal_eq_span_vertical
    (y x : A)
    (I : Ideal A)
    (m s : R[X])
    (hnormal :
      HasVerticalPolynomialNormalForm (R := R) y x s)
    (hker :
      RingHom.ker
          ((aeval (Ideal.Quotient.mk I y) :
              R[X] →ₐ[R] A ⧸ I).toRingHom) =
        Ideal.span ({m} : Set R[X]))
    (hx :
      Ideal.Quotient.mk I x =
        aeval (Ideal.Quotient.mk I y) s) :
    I =
      Ideal.span
        ({aeval y m, x - aeval y s} : Set A) := by
  let π : A →ₐ[R] A ⧸ I := Ideal.Quotient.mkₐ R I
  have hker' :
      RingHom.ker
          ((aeval (π y) : R[X] →ₐ[R] A ⧸ I).toRingHom) =
        Ideal.span ({m} : Set R[X]) := by
    simpa [π] using hker
  have hx' : π x = aeval (π y) s := by
    simpa [π] using hx
  have hgraphZero :
      π (x - aeval y s) = 0 := by
    calc
      π (x - aeval y s) =
          π x - π (aeval y s) := map_sub π _ _
      _ = π x - aeval (π y) s := by
        rw [← Polynomial.aeval_algHom_apply π y s]
      _ = 0 := by rw [hx', sub_self]
  apply le_antisymm
  · intro z hz
    obtain ⟨p, q, hform⟩ := hnormal z
    have hz0 : π z = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
    have hp0 : aeval (π y) p = 0 := by
      calc
        aeval (π y) p =
            π (aeval y p) := by
          rw [Polynomial.aeval_algHom_apply]
        _ =
            π (aeval y p) +
              π q * π (x - aeval y s) := by
          rw [hgraphZero, mul_zero, add_zero]
        _ =
            π (aeval y p +
              q * (x - aeval y s)) := by
          rw [map_add, map_mul]
        _ = π z := by rw [← hform]
        _ = 0 := hz0
    have hpSpan :
        p ∈ Ideal.span ({m} : Set R[X]) := by
      rw [← hker']
      exact RingHom.mem_ker.mpr hp0
    obtain ⟨w, hw⟩ :=
      Ideal.mem_span_singleton.mp hpSpan
    refine
      (Ideal.mem_span_pair).2
        ⟨aeval y w, q, ?_⟩
    calc
      aeval y w * aeval y m +
          q * (x - aeval y s) =
        aeval y (m * w) +
          q * (x - aeval y s) := by
        simp only [map_mul]
        ring
      _ =
        aeval y p +
          q * (x - aeval y s) := by rw [← hw]
      _ = z := hform.symm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have hmKer :
          m ∈
            RingHom.ker
              ((aeval (π y) :
                  R[X] →ₐ[R] A ⧸ I).toRingHom) := by
        rw [hker']
        exact Ideal.mem_span_singleton_self m
      have hzero : π (aeval y m) = 0 := by
        calc
          π (aeval y m) =
              aeval (π y) m :=
            (Polynomial.aeval_algHom_apply π y m).symm
          _ = 0 := RingHom.mem_ker.mp hmKer
      exact Ideal.Quotient.eq_zero_iff_mem.mp
        (by simpa [π] using hzero)
    · exact Ideal.Quotient.eq_zero_iff_mem.mp
        (by simpa [π] using hgraphZero)

end

end MazurProof.N13RankTwoVerticalIdealRecovery


