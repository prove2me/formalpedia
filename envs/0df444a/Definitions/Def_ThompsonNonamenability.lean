-- Prove2me | Definitions.Def_ThompsonNonamenability
-- name    : ThompsonNonamenability
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:29.703555+00:00
-- url     : https://prove2.me/theorems/0a5c0211-fd0a-4aab-a764-a8e496335dac
-- statement:
--   The unit interval UnitInterval is the closed real interval [0,1] with endpoints unitIntervalZero and unitIntervalOne, and IntervalHomeomorph is a structure wrapping a self-homeomorphism of [0,1], usable as a function. IsDyadic(x) means x=k/2^n for some integer k and natural number n. A DyadicPLWitness for such an f consists of a positive piece count m and strictly increasing knots t_0<...<t_m in [0,1] with t_0=0, t_m=1 and every knot dyadic, such that every x in [0,1] lies in some interval [t_i,t_{i+1}], together with an integer exponent e_i for each piece such that on that interval f(x)=f(t_i)+2^{e_i}(x−t_i). HasDyadicPLPieces(f) says such a witness exists, and F is the type of those interval homeomorphisms that are strictly monotone and have dyadic piecewise-linear pieces, with no group structure on F itself being defined here. For a type G with a group structure, BoundedReal(G) is the space ℓ^∞(G) of bounded real-valued functions on G, and leftPull(h) is the real-linear map on it sending f to g↦f(hg), whose boundedness is checked. An InvariantMean on G is a real-linear functional on ℓ^∞(G) that is nonnegative on every function that is pointwise nonnegative, sends the constant function 1 to 1, and satisfies m(leftPull(h) f)=m(f) for all h in G and bounded f. The block only defines these notions and states no theorem about amenability or nonamenability of F.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ThompsonNonamenability.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ThompsonNonamenability.lean; bytes 177..2424
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Basic

namespace OAI

noncomputable section

open scoped ENNReal

universe uG

namespace ThompsonNonamenability

abbrev UnitInterval := Set.Icc (0 : ℝ) 1

def unitIntervalZero : UnitInterval := ⟨0, le_rfl, zero_le_one⟩
def unitIntervalOne : UnitInterval := ⟨1, zero_le_one, le_rfl⟩

structure IntervalHomeomorph where
  toHomeomorph : UnitInterval ≃ₜ UnitInterval

namespace IntervalHomeomorph

instance : CoeFun IntervalHomeomorph (fun _ => UnitInterval → UnitInterval) :=
  ⟨fun f => f.toHomeomorph⟩

end IntervalHomeomorph

def IsDyadic (x : ℝ) : Prop :=
  ∃ (k : ℤ) (n : ℕ), x = (k : ℝ) / (2 : ℝ) ^ n

structure DyadicPLWitness (f : IntervalHomeomorph) where
  pieceCount : ℕ
  positive : 0 < pieceCount
  knots : Fin (pieceCount + 1) → UnitInterval
  strictMono_knots : StrictMono knots
  first : knots 0 = unitIntervalZero
  last : knots (Fin.last pieceCount) = unitIntervalOne
  dyadic : ∀ i, IsDyadic (knots i : ℝ)
  cover : ∀ x : UnitInterval, ∃ i : Fin pieceCount,
    knots i.castSucc ≤ x ∧ x ≤ knots i.succ
  exponent : Fin pieceCount → ℤ
  affine : ∀ (i : Fin pieceCount) (x : UnitInterval),
    knots i.castSucc ≤ x → x ≤ knots i.succ →
    (f x : ℝ) = (f (knots i.castSucc) : ℝ) +
      (2 : ℝ) ^ exponent i * ((x : ℝ) - (knots i.castSucc : ℝ))

def HasDyadicPLPieces (f : IntervalHomeomorph) : Prop := Nonempty (DyadicPLWitness f)

def F := {f : IntervalHomeomorph // StrictMono f ∧ HasDyadicPLPieces f}

abbrev BoundedReal (G : Type uG) := lp (fun _ : G => ℝ) ∞

variable {G : Type uG} [Group G]

def leftPull (h : G) : BoundedReal G →ₗ[ℝ] BoundedReal G where
  toFun f := ⟨fun g => f (h * g), memℓp_infty ⟨‖f‖, by
    rintro y ⟨g, rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero f (h * g)⟩⟩
  map_add' f g := by
    apply lp.ext
    funext x
    rfl
  map_smul' r f := by
    apply lp.ext
    funext x
    rfl

structure InvariantMean (G : Type uG) [Group G] where
  toLinearMap : BoundedReal G →ₗ[ℝ] ℝ
  positive : ∀ f : BoundedReal G, (∀ g, 0 ≤ f g) → 0 ≤ toLinearMap f
  normalized : toLinearMap 1 = 1
  left_invariant : ∀ (h : G) (f : BoundedReal G),
    toLinearMap (leftPull h f) = toLinearMap f



end ThompsonNonamenability
end
end OAI


