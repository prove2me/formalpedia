-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialQuadraticGraphRegularity_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialQuadraticGraphRegularity_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:23:18.481729+00:00
-- url     : https://prove2.me/theorems/0298e8f2-fe83-404e-bb11-6f8d727f341a
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialQuadraticGraphRegularity source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialQuadraticGraphRegularity

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialQuadraticGraphRegularity
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GeneralizedMumfordReduction_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialGraphDivisorCharts_p0

set_option autoImplicit false




/-!
# Automatic regularity of quadratic special N13 graphs

The coefficient `h=1+X²+X³` of the special affine curve is an irreducible
cubic over `F₂`.  It is therefore coprime to every monic quadratic.  This
supplies the Bézout field required by the special Mumford API for any monic
quadratic semigraph, without an additional smoothness hypothesis.

Consequently every integral monic quadratic semigraph reduces directly to
the special graph data whose canonical root divisor has the same affine
ideal.
-/

open Polynomial

namespace MazurProof.N13SpecialQuadraticGraphRegularity

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The cubic coefficient of the special affine curve is irreducible over
`F₂`: it has no root in `F₂`. -/
theorem hPoly_irreducible :
    Irreducible N13GoodCoordinateRingTwo.hPoly := by
  apply
    (N13GoodCoordinateRingTwo.hPoly_monic.irreducible_iff_roots_eq_zero_of_degree_le_three
        (by rw [N13GoodCoordinateRingTwo.hPoly_natDegree]; norm_num)
        (by rw [N13GoodCoordinateRingTwo.hPoly_natDegree])).mpr
  apply Multiset.eq_zero_of_forall_notMem
  intro a ha
  have hroot :
      N13GoodCoordinateRingTwo.hPoly.eval a = 0 :=
    (Polynomial.mem_roots
      N13GoodCoordinateRingTwo.hPoly_monic.ne_zero).mp ha
  have hone :
      N13GoodCoordinateRingTwo.hPoly.eval a = 1 := by
    simp only [N13GoodCoordinateRingTwo.hPoly,
      eval_add, eval_one, eval_pow, eval_X]
    fin_cases a <;> decide
  rw [hone] at hroot
  exact one_ne_zero hroot

/-- Every monic quadratic over the special field is coprime to the cubic
curve coefficient. -/
theorem quadratic_isCoprime_hPoly
    (u : N13GoodCoordinateRingTwo.K[X])
    (hu : u.Monic)
    (hdeg : u.natDegree = 2) :
    IsCoprime u N13GoodCoordinateRingTwo.hPoly := by
  apply IsCoprime.symm
  apply (hPoly_irreducible.isCoprime_or_dvd u).resolve_right
  intro hdvd
  have hle :=
    Polynomial.natDegree_le_of_dvd hdvd hu.ne_zero
  rw [N13GoodCoordinateRingTwo.hPoly_natDegree, hdeg] at hle
  omega

/-- A monic quadratic special semigraph automatically satisfies the
Mumford Bézout regularity condition. -/
theorem quadratic_graph_bezout
    (u v w : N13GoodCoordinateRingTwo.K[X])
    (hu : u.Monic)
    (hdeg : u.natDegree = 2) :
    ∃ a b c : N13GoodCoordinateRingTwo.K[X],
      a * u +
          b * (2 * v + N13GoodCoordinateRingTwo.hPoly) +
          c * w =
        1 := by
  obtain ⟨a, b, hab⟩ :=
    quadratic_isCoprime_hPoly u hu hdeg
  refine ⟨a, b, 0, ?_⟩
  have htwo :
      (2 : N13GoodCoordinateRingTwo.K[X]) = 0 :=
    CharP.cast_eq_zero N13GoodCoordinateRingTwo.K[X] 2
  rw [htwo, zero_mul, zero_add, zero_mul, add_zero]
  exact hab

/-- Coefficientwise reduction turns an integral monic quadratic semigraph
into regular special Mumford data. -/
def reduceSemiMumford
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (hdeg : D.u.natDegree = 2) :
    N13GoodCoordinateRingTwo.SemiMumford where
  u := N13GeneralizedMumfordReduction.reducePoly D.u
  v := N13GeneralizedMumfordReduction.reducePoly D.v
  w := N13GeneralizedMumfordReduction.reducePoly D.w
  u_monic :=
    D.u_monic.map N13GeneralizedMumfordReduction.reduceBase
  curve_eq := by
    have h :=
      congrArg N13GeneralizedMumfordReduction.reducePoly D.curve_eq
    simpa only [map_add, map_sub, map_mul, map_pow,
      N13GeneralizedMumfordReduction.reduce_hPoly,
      N13GeneralizedMumfordReduction.reduce_rhsPoly] using h
  bezout :=
    quadratic_graph_bezout
      (N13GeneralizedMumfordReduction.reducePoly D.u)
      (N13GeneralizedMumfordReduction.reducePoly D.v)
      (N13GeneralizedMumfordReduction.reducePoly D.w)
      (D.u_monic.map N13GeneralizedMumfordReduction.reduceBase)
      (by
        rw [N13GeneralizedMumfordReduction.reducePoly_apply,
          D.u_monic.natDegree_map, hdeg])

/-- The reduced horizontal polynomial retains degree two. -/
theorem reduceSemiMumford_u_natDegree
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (hdeg : D.u.natDegree = 2) :
    (reduceSemiMumford D hdeg).u.natDegree = 2 := by
  change
    (N13GeneralizedMumfordReduction.reducePoly D.u).natDegree = 2
  rw [N13GeneralizedMumfordReduction.reducePoly_apply,
    D.u_monic.natDegree_map, hdeg]

/-- Reducing an integral monic quadratic graph ideal gives the affine ideal
of the canonical divisor of its special root graph. -/
theorem map_mumfordIdeal_eq_graphDivisor_affineIdeal
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (hdeg : D.u.natDegree = 2) :
    Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := N13GeneralizedMumfordReduction.R₂) D.u D.v) =
      (N13SpecialDivisorCharts.ofDivisor
        (N13SpecialGraphDivisor.graphDivisor
          (reduceSemiMumford D hdeg)
          (reduceSemiMumford_u_natDegree D hdeg))).affineIdeal := by
  rw [N13GeneralizedMumfordReduction.map_mumfordIdeal,
    N13SpecialGraphDivisorCharts.ofDivisor_graphDivisor_affineIdeal]
  rfl

end

end MazurProof.N13SpecialQuadraticGraphRegularity


