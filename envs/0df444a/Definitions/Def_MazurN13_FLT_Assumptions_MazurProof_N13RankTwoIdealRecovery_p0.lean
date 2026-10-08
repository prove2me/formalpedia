-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RankTwoIdealRecovery_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13RankTwoIdealRecovery_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:44:29.562338+00:00
-- url     : https://prove2.me/theorems/78f23d0b-153d-44d9-9ec1-b7187d446451
-- title:
--   FLT.Assumptions.MazurProof.N13RankTwoIdealRecovery source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13RankTwoIdealRecovery

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13RankTwoIdealRecovery
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RankTwoQuotientAlgebra_p0
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option autoImplicit false




/-!
# Recovering the literal graph ideal from a rank-two quotient

Once a quotient has basis `{1,x̄}`, the characteristic polynomial `u` of
multiplication by `x̄` generates the evaluation kernel.  Expressing `ȳ` as
`v(x̄)` then recovers the original ambient ideal literally as

`(u(x), y-v(x))`.

This is an ideal-correspondence argument.  It does not assume that the
original ideal was already given in Mumford graph form.
-/

open Polynomial

namespace MazurProof.N13RankTwoIdealRecovery

noncomputable section

universe uR uA

variable {R : Type uR} {A : Type uA}
variable [CommRing R] [CommRing A] [Algebra R A]

/-- Polynomial normal form of degree at most one in the second coordinate. -/
def HasRankTwoPolynomialNormalForm (x y : A) : Prop :=
  ∀ a : A, ∃ p q : R[X],
    a = aeval x p + aeval x q * y

/--
If evaluation at `x̄` has kernel `(u)` and `ȳ=v(x̄)`, then the ambient
ideal is exactly `(u(x),y-v(x))`.
-/
theorem ideal_eq_span_aeval_y_sub
    (x y : A)
    (I : Ideal A)
    (u v : R[X])
    (hnormal : HasRankTwoPolynomialNormalForm (R := R) x y)
    (hker :
      RingHom.ker
          ((aeval (Ideal.Quotient.mk I x) :
              R[X] →ₐ[R] A ⧸ I).toRingHom) =
        Ideal.span ({u} : Set R[X]))
    (hy :
      Ideal.Quotient.mk I y =
        aeval (Ideal.Quotient.mk I x) v) :
    I =
      Ideal.span
        ({aeval x u, y - aeval x v} : Set A) := by
  let π : A →ₐ[R] A ⧸ I := Ideal.Quotient.mkₐ R I
  have hker' :
      RingHom.ker
          ((aeval (π x) : R[X] →ₐ[R] A ⧸ I).toRingHom) =
        Ideal.span ({u} : Set R[X]) := by
    simpa [π] using hker
  have hy' : π y = aeval (π x) v := by
    simpa [π] using hy
  apply le_antisymm
  · intro a ha
    obtain ⟨p, q, hform⟩ := hnormal a
    have ha0 : π a = 0 := by
      simpa [π] using
        (Ideal.Quotient.eq_zero_iff_mem.mpr ha)
    have hpoly0 :
        aeval (π x) (p + q * v) = 0 := by
      calc
        aeval (π x) (p + q * v) =
            aeval (π x) p +
              aeval (π x) q * aeval (π x) v := by
          simp only [map_add, map_mul]
        _ =
            aeval (π x) p +
              aeval (π x) q * π y := by
          rw [← hy']
        _ =
            π (aeval x p) +
              π (aeval x q) * π y := by
          rw [Polynomial.aeval_algHom_apply π x p,
            Polynomial.aeval_algHom_apply π x q]
        _ = π (aeval x p + aeval x q * y) := by
          rw [map_add, map_mul]
        _ = π a := by rw [← hform]
        _ = 0 := ha0
    have hpqSpan :
        p + q * v ∈ Ideal.span ({u} : Set R[X]) := by
      rw [← hker']
      exact RingHom.mem_ker.mpr hpoly0
    obtain ⟨w, hw⟩ :=
      Ideal.mem_span_singleton.mp hpqSpan
    refine
      (Ideal.mem_span_pair).2
        ⟨aeval x w, aeval x q, ?_⟩
    calc
      aeval x w * aeval x u +
          aeval x q * (y - aeval x v) =
        aeval x (u * w) +
          aeval x q * y -
          aeval x (q * v) := by
        simp only [map_mul]
        ring
      _ =
        aeval x (p + q * v) +
          aeval x q * y -
          aeval x (q * v) := by
        rw [← hw]
      _ = aeval x p + aeval x q * y := by
        simp only [map_add, map_mul]
        ring
      _ = a := hform.symm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have huKer :
          u ∈
            RingHom.ker
              ((aeval (π x) :
                  R[X] →ₐ[R] A ⧸ I).toRingHom) := by
        rw [hker']
        exact Ideal.mem_span_singleton_self u
      have hzero : π (aeval x u) = 0 := by
        calc
          π (aeval x u) = aeval (π x) u :=
            (Polynomial.aeval_algHom_apply π x u).symm
          _ = 0 := RingHom.mem_ker.mp huKer
      exact
        Ideal.Quotient.eq_zero_iff_mem.mp
          (by simpa [π] using hzero)
    · have hzero : π (y - aeval x v) = 0 := by
        calc
          π (y - aeval x v) =
              π y - π (aeval x v) := by
            exact map_sub π y (aeval x v)
          _ = π y - aeval (π x) v := by
            rw [← Polynomial.aeval_algHom_apply π x v]
          _ = 0 := by rw [hy', sub_self]
      exact
        Ideal.Quotient.eq_zero_iff_mem.mp
          (by simpa [π] using hzero)

end

end MazurProof.N13RankTwoIdealRecovery


