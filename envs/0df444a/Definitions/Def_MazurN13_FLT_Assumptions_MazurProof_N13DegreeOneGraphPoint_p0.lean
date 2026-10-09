-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13DegreeOneGraphPoint_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13DegreeOneGraphPoint_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T20:10:28.125874+00:00
-- url     : https://prove2.me/theorems/6a30662a-b602-4571-85b4-dd7b8dbbc59a
-- title:
--   FLT.Assumptions.MazurProof.N13DegreeOneGraphPoint source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13DegreeOneGraphPoint

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13DegreeOneGraphPoint
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ConstructedHalfIntegralSpread_p0

set_option autoImplicit false




/-!
# Degree-one N13 graphs are proper curve points

A balanced Mumford graph with monic linear `u` and zero infinity
coordinate is not a genuinely new divisor: it is the graph of one affine
point of the smooth projective curve.  This identifies the degree-one
branch of the selected Padé root with the already constructed proper
two-chart point reduction.

The argument is structural.  Monicity determines `u = X - x`, reducedness
makes `v` constant, and the Mumford divisibility relation is exactly the
curve equation at `x`.
-/

open Polynomial

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (M : Model K)

/-- A degree-one balanced graph with no infinity contribution is exactly
the Mumford representative of an affine curve point. -/
theorem exists_affinePoint_of_natDegree_eq_one
    (D : Mumford M)
    (hdeg : D.u.natDegree = 1)
    (hnInf : D.nInf = 0) :
    ∃ x y : K, ∃ hcurve : y ^ 2 = M.f.eval x,
      D = affinePointMumford M x y hcurve := by
  let x : K := -D.u.coeff 0
  let y : K := D.v.coeff 0
  have hu :
      D.u = X - C x := by
    rw [D.u_monic.eq_X_add_C hdeg]
    simp [x]
  have huDegree :
      D.u.degree = (1 : WithBot ℕ) := by
    rw [degree_eq_natDegree D.u_monic.ne_zero, hdeg]
    norm_num
  have hvDegree :
      D.v.degree < D.u.degree :=
    (mod_eq_self_iff D.u_monic.ne_zero).mp D.v_reduced
  have hvNatDegree :
      D.v.natDegree = 0 := by
    by_cases hv0 : D.v = 0
    · simp [hv0]
    · have hvlt : D.v.natDegree < 1 := by
        rw [natDegree_lt_iff_degree_lt hv0]
        simpa [huDegree] using hvDegree
      omega
  have hv :
      D.v = C y := by
    exact eq_C_of_natDegree_eq_zero hvNatDegree
  have hzero :
      (M.f - D.v ^ 2).eval x = 0 := by
    obtain ⟨q, hq⟩ := D.curve_dvd
    rw [hq, eval_mul, hu]
    simp
  have hcurve :
      y ^ 2 = M.f.eval x := by
    have hzero' :
        M.f.eval x - y ^ 2 = 0 := by
      simpa [hv] using hzero
    exact (sub_eq_zero.mp hzero').symm
  refine ⟨x, y, hcurve, ?_⟩
  cases D with
  | mk u v n u_monic deg_u v_reduced curve_dvd infinity_bound =>
      dsimp at hu hv hnInf ⊢
      congr

end

end MazurProof.SexticMumford

namespace MazurProof.N13DegreeOneGraphPoint

noncomputable section

abbrev G : Type :=
  N13ConstructedHalfIntegralSpread.G

abbrev ModelQ : SexticMumford.Model ℚ :=
  N13Mumford.model ℚ

/-- Normalization preserves the degree of the retained nonzero graph
polynomial. -/
theorem normalizedGraphMumford_u_natDegree
    (P : G) :
    (N13ConstructedHalfIntegralSpread.normalizedGraphMumford P).u.natDegree =
      (N13ConstructedHalfIntegralSpread.graphU P).natDegree := by
  change
    (normalize
      (N13ConstructedHalfIntegralSpread.graphU P)).natDegree =
        (N13ConstructedHalfIntegralSpread.graphU P).natDegree
  exact Polynomial.natDegree_eq_of_degree_eq
    (Polynomial.degree_eq_degree_of_associated
      (associated_normalize
        (N13ConstructedHalfIntegralSpread.graphU P)).symm)

/-- In the degree-one branch, the selected normalized Padé graph is
literally the balanced graph of a rational affine curve point. -/
theorem exists_rationalAffinePoint_of_graphU_natDegree_eq_one
    (P : G)
    (hdeg :
      (N13ConstructedHalfIntegralSpread.graphU P).natDegree = 1) :
    ∃ x y : ℚ, ∃ hcurve : y ^ 2 = ModelQ.f.eval x,
      N13ConstructedHalfIntegralSpread.normalizedGraphMumford P =
        SexticMumford.affinePointMumford ModelQ x y hcurve := by
  have hnormalized :
      (N13ConstructedHalfIntegralSpread.normalizedGraphMumford P).u.natDegree =
        1 := by
    rw [normalizedGraphMumford_u_natDegree, hdeg]
  obtain ⟨x, y, hcurve, hpoint⟩ :=
    SexticMumford.exists_affinePoint_of_natDegree_eq_one
      ModelQ
      (N13ConstructedHalfIntegralSpread.normalizedGraphMumford P)
      hnormalized rfl
  exact ⟨x, y, hcurve, hpoint⟩

/-- Curve-point form of the same degree-one identification. -/
theorem exists_rationalCurvePoint_of_graphU_natDegree_eq_one
    (P : G)
    (hdeg :
      (N13ConstructedHalfIntegralSpread.graphU P).natDegree = 1) :
    ∃ Q : SexticMumford.CurvePoint ModelQ,
      N13ConstructedHalfIntegralSpread.normalizedGraphMumford P =
        SexticMumford.pointMumford ModelQ Q := by
  obtain ⟨x, y, hcurve, hpoint⟩ :=
    exists_rationalAffinePoint_of_graphU_natDegree_eq_one P hdeg
  exact ⟨.affine x y hcurve, hpoint⟩

end

end MazurProof.N13DegreeOneGraphPoint


