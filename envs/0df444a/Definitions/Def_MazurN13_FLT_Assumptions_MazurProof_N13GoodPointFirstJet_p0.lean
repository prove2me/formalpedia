-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GoodPointFirstJet_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GoodPointFirstJet_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:35:50.591172+00:00
-- url     : https://prove2.me/theorems/6747040a-00b5-4b64-bcec-179c9eb63203
-- title:
--   FLT.Assumptions.MazurProof.N13GoodPointFirstJet source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GoodPointFirstJet

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GoodPointFirstJet
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GeneralizedMumfordIntegral_p0
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.Polynomial.Derivative

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

An actual point and implicit tangent on the good quadratic curve define a
ring map to dual numbers. Squared graph-ideal membership therefore forces
both the value and first derivative of a regular function to vanish.
Only this direction is needed for the principal/Hermite matching step.
-/

namespace MazurProof.N13GoodPointFirstJet

set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Polynomial MulOpposite
universe u
variable {K : Type u} [Field K]

abbrev Dual (K : Type u) [Field K] := TrivSqZeroExt K K
abbrev Good (K : Type u) [Field K] := N13GeneralizedMumfordIntegral.CoordinateRing (R := K)

def polynomialJet (x : K) : K[X] →+* Dual K where
  toFun p := (p.eval x, p.derivative.eval x)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' p q := by apply TrivSqZeroExt.ext <;> simp
  map_mul' p q := by
    apply TrivSqZeroExt.ext
    · simp
    · simp [derivative_mul, smul_eq_mul, op_smul_eq_smul]
      ring

private theorem polynomialJet_apply (x : K) (p : K[X]) :
    polynomialJet x p = (p.eval x, p.derivative.eval x) := rfl

private theorem root_jet
    (x y s : K)
    (hc : y ^ 2 + (x ^ 3 + x + 1) * y - (x ^ 5 + x ^ 4) = 0)
    (hd : (2 * y + (x ^ 3 + x + 1)) * s +
      (3 * x ^ 2 + 1) * y - (5 * x ^ 4 + 4 * x ^ 3) = 0) :
    (N13GeneralizedMumfordIntegral.curvePoly (R := K)).eval₂
      (polynomialJet x) (y, s) = 0 := by
  apply TrivSqZeroExt.ext
  · simp only [N13GeneralizedMumfordIntegral.curvePoly,
      N13GeneralizedMumfordIntegral.hPoly, N13GeneralizedMumfordIntegral.rhsPoly,
      eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X, eval₂_one,
      polynomialJet_apply, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_mul,
      TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_one, TrivSqZeroExt.fst_zero,
      eval_X, eval_add, eval_pow, eval_one, eval_C, TrivSqZeroExt.fst_mk]
    linear_combination hc
  · simp only [N13GeneralizedMumfordIntegral.curvePoly,
      N13GeneralizedMumfordIntegral.hPoly, N13GeneralizedMumfordIntegral.rhsPoly,
      eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X, eval₂_one,
      polynomialJet_apply]
    simp [derivative_mul, derivative_pow, smul_eq_mul, op_smul_eq_smul, nsmul_eq_mul,
      TrivSqZeroExt.snd_pow]
    linear_combination hd

def pointJet (x y s : K)
    (hc : y ^ 2 + (x ^ 3 + x + 1) * y - (x ^ 5 + x ^ 4) = 0)
    (hd : (2 * y + (x ^ 3 + x + 1)) * s +
      (3 * x ^ 2 + 1) * y - (5 * x ^ 4 + 4 * x ^ 3) = 0) : Good K →+* Dual K :=
  AdjoinRoot.lift (polynomialJet x) (y, s) (root_jet x y s hc hd)

section
variable (x y s : K)
variable (hc : y ^ 2 + (x ^ 3 + x + 1) * y - (x ^ 5 + x ^ 4) = 0)
variable (hd : (2 * y + (x ^ 3 + x + 1)) * s +
  (3 * x ^ 2 + 1) * y - (5 * x ^ 4 + 4 * x ^ 3) = 0)

@[simp] theorem pointJet_xClass (p : K[X]) :
    pointJet x y s hc hd (N13GeneralizedMumfordIntegral.xClass p) =
      (p.eval x, p.derivative.eval x) := AdjoinRoot.lift_of _

@[simp] theorem pointJet_yClass :
    pointJet x y s hc hd N13GeneralizedMumfordIntegral.yClass = (y, s) :=
  AdjoinRoot.lift_root _

theorem square_graph_maps_to_zero (u v : K[X])
    (hu : u.eval x = 0) (hv : v.eval x = y)
    (n : Good K) (hn : n ∈ N13GeneralizedMumfordIntegral.mumfordIdeal u v ^ 2) :
    pointJet x y s hc hd n = 0 := by
  let f : Good K →+* K :=
    (TrivSqZeroExt.fstHom K K K).toRingHom.comp (pointJet x y s hc hd)
  have hI : N13GeneralizedMumfordIntegral.mumfordIdeal u v ≤ RingHom.ker f := by
    rw [N13GeneralizedMumfordIntegral.mumfordIdeal, Ideal.span_le]
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · change (pointJet x y s hc hd (N13GeneralizedMumfordIntegral.xClass u)).fst = 0
      simpa using hu
    · change (pointJet x y s hc hd (N13GeneralizedMumfordIntegral.ySubClass v)).fst = 0
      simp [N13GeneralizedMumfordIntegral.ySubClass, hv]
  have hsquare : N13GeneralizedMumfordIntegral.mumfordIdeal u v ^ 2 ≤
      RingHom.ker (pointJet x y s hc hd) := by
    rw [pow_two]
    apply Ideal.mul_le.mpr
    intro a ha b hb
    have hfa : (pointJet x y s hc hd a).fst = 0 := hI ha
    have hfb : (pointJet x y s hc hd b).fst = 0 := hI hb
    change pointJet x y s hc hd (a * b) = 0
    rw [map_mul]
    apply TrivSqZeroExt.ext <;>
      simp [hfa, hfb, smul_eq_mul, op_smul_eq_smul]
  exact hsquare hn

include hc hd in
theorem value_derivative_of_square_graph
    (u v p q : K[X]) (hu : u.eval x = 0) (hv : v.eval x = y)
    (hn : N13GeneralizedMumfordIntegral.xClass p +
        N13GeneralizedMumfordIntegral.xClass q * N13GeneralizedMumfordIntegral.yClass ∈
      N13GeneralizedMumfordIntegral.mumfordIdeal u v ^ 2) :
    p.eval x + q.eval x * y = 0 ∧
      p.derivative.eval x + q.derivative.eval x * y + q.eval x * s = 0 := by
  have hj := square_graph_maps_to_zero x y s hc hd u v hu hv _ hn
  constructor
  · simpa using congrArg TrivSqZeroExt.fst hj
  · have hs := congrArg TrivSqZeroExt.snd hj
    simp [smul_eq_mul, op_smul_eq_smul] at hs
    convert hs using 1 <;> ring

end
end
end MazurProof.N13GoodPointFirstJet


