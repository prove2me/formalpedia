-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianCandidateDlog_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GaussianCandidateDlog_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T23:18:39.67298+00:00
-- url     : https://prove2.me/theorems/52e1ec01-f970-46f7-861d-d1cc08251c2a
-- title:
--   FLT.Assumptions.MazurProof.N13GaussianCandidateDlog source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GaussianCandidateDlog

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GaussianCandidateDlog
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CandidateCollapse_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianLocalization_p0

set_option autoImplicit false




/-!
# Integral first jets of the N13 global candidates

The global candidate generators specialize to short integral elements of
the fixed Gaussian order.  Their reduction is therefore computed by the
exact quotient map of `N13GaussianOrderTwo`, rather than by assigning jets
formally.

This file proves that the first logarithm of that genuine integral reduction
is exactly `N13LocalDlogTwo.candidateDlog`.
-/

namespace MazurProof.N13GaussianCandidateDlog

noncomputable section

open N13LocalDlogTwo
open N13GaussianOrderTwo
open N13GaussianLocalization

abbrev Order : Type :=
  N13GaussianOrderTwo.Order

abbrev F8 : Type :=
  N13LocalDlogTwo.F8

/-- The integral order element represented by a global candidate. -/
def candidateOrder (a b c d : ZMod 2) : Order :=
  i ^ a.val * e1Order ^ b.val * e2Order ^ c.val *
    (primeAOrder * primeQOrder) ^ d.val

/-- The unit in the exact first-jet quotient obtained from the same four
short integral generators. -/
def candidateJet (a b c d : ZMod 2) :
    (DualNumber F8)ˣ :=
  zetaJet ^ a.val * e1Jet ^ b.val * e2Jet ^ c.val *
    (aJet * qJet) ^ d.val

theorem reduction_i_eq_zetaJet :
    reduction i = (zetaJet : DualNumber F8) := by
  rw [reduction_i]
  ext <;>
    simp [N13LocalDlogRegimes.gaussianIDual, zetaJet,
      RamifiedDlog.unitOf_val]

/-- The exact order reduction of a candidate is the advertised product of
the four first jets. -/
theorem reduction_candidateOrder (a b c d : ZMod 2) :
    reduction (candidateOrder a b c d) =
      (candidateJet a b c d : DualNumber F8) := by
  simp only [candidateOrder, candidateJet, map_mul, map_pow,
    reduction_i_eq_zetaJet, reduction_e1Order,
    reduction_e2Order, reduction_primeAOrder,
    reduction_primeQOrder, Units.val_mul, Units.val_pow_eq_pow_val]

/-- The global candidate unit and the integral candidate order element have
the same image after inverting `2`. -/
theorem globalCandidate_specializes_to_order
    (a b c d : ZMod 2) :
    sexticToLocalOrder
        (N13CandidateCollapse.candidateUnit a b c d :
          N13SexticSquareclass.SexticAlgebra) =
      algebraMap Order LocalOrder (candidateOrder a b c d) := by
  simp only [N13CandidateCollapse.candidateUnit,
    Units.val_mul, Units.val_pow_eq_pow_val,
    N13CandidateCollapse.zetaUnit_val,
    N13CandidateCollapse.e1Unit_val,
    N13CandidateCollapse.e2Unit_val,
    N13CandidateCollapse.primeAUnit_val,
    N13CandidateCollapse.primeQUnit_val,
    map_mul, map_pow, sexticToLocalOrder_zeta,
    sexticToLocalOrder_e1, sexticToLocalOrder_e2,
    sexticToLocalOrder_primeA, sexticToLocalOrder_primeQ,
    candidateOrder, localI]

theorem dlog_pow_nat (z : (DualNumber F8)ˣ) :
    ∀ n : ℕ,
      RamifiedDlog.dlog (z ^ n) =
        (n : F8) * RamifiedDlog.dlog z
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ, RamifiedDlog.dlog_mul, dlog_pow_nat z n]
      push_cast
      ring

/-- The finite formula is the actual logarithm of the integral candidate
reduction. -/
theorem dlog_candidateJet (a b c d : ZMod 2) :
    RamifiedDlog.dlog (candidateJet a b c d) =
      candidateDlog a b c d := by
  have ha :
      (a.val : F8) = algebraMap (ZMod 2) F8 a := by
    simpa only [map_natCast] using
      congrArg (algebraMap (ZMod 2) F8)
        (ZMod.natCast_zmod_val a)
  have hb :
      (b.val : F8) = algebraMap (ZMod 2) F8 b := by
    simpa only [map_natCast] using
      congrArg (algebraMap (ZMod 2) F8)
        (ZMod.natCast_zmod_val b)
  have hc :
      (c.val : F8) = algebraMap (ZMod 2) F8 c := by
    simpa only [map_natCast] using
      congrArg (algebraMap (ZMod 2) F8)
        (ZMod.natCast_zmod_val c)
  have hd :
      (d.val : F8) = algebraMap (ZMod 2) F8 d := by
    simpa only [map_natCast] using
      congrArg (algebraMap (ZMod 2) F8)
        (ZMod.natCast_zmod_val d)
  rw [candidateJet, RamifiedDlog.dlog_mul,
    RamifiedDlog.dlog_mul, RamifiedDlog.dlog_mul,
    dlog_pow_nat, dlog_pow_nat, dlog_pow_nat, dlog_pow_nat,
    ha, hb, hc, hd]
  exact (candidateDlog_eq_generator_sum a b c d).symm

/-- Consequently, vanishing of the candidate formula is literally
vanishing of the logarithm of its exact order reduction. -/
theorem candidateDlog_eq_zero_iff_orderJet
    (a b c d : ZMod 2) :
    candidateDlog a b c d = 0 ↔
      RamifiedDlog.dlog (candidateJet a b c d) = 0 := by
  rw [dlog_candidateJet]

end

end MazurProof.N13GaussianCandidateDlog


