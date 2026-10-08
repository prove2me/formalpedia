-- Prove2me | Definitions.Def_KLInvariance
-- name    : KLInvariance
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:16.029203+00:00
-- url     : https://prove2.me/theorems/0864f624-2404-4846-a545-a8bb9d32ba13
-- statement:
--   For a Coxeter system cs with group W and Coxeter matrix M, BruhatStep(x,y) holds when y is strictly longer than x and y = t·x for some reflection t, giving the upward edges of the strong Bruhat graph with left reflections. BruhatLE is the reflexive transitive closure of these steps, so it is the strong Bruhat order rather than the weak order. Interval(u,b) is the subtype of elements x with u ≤ x ≤ b, endpoints included, and it is given a partial order by restricting BruhatLE; antisymmetry is proved using monotonicity of length along Bruhat relations. rankDifference(x,y) is the natural-number subtraction ℓ(y) − ℓ(x) of lengths. A pair of families R and P of integer-polynomial-valued functions on W×W satisfies the predicate NormalizedKL when: R(x,x)=1 and R(x,y)=0 unless x ≤ y; for each simple generator s_i with ℓ(s_i y) < ℓ(y), R(x,y) equals R(s_i x, s_i y) if ℓ(s_i x) < ℓ(x), and otherwise (X−1)R(x,s_i y) + X R(s_i x, s_i y); P(x,x)=1 and P(x,y)=0 unless x ≤ y; for x < y, twice the degree of P(x,y) is less than rankDifference(x,y); and for x ≤ y, the reflection q^d P(x,y)(q⁻¹), with d the rank difference, equals the finite sum over z in the interval [x,y] of R(x,z)P(z,y). The pair of families klFamilies is chosen by Classical.epsilon among pairs satisfying NormalizedKL, so it is specified only through this normalization with no uniqueness or existence proved here, and klPolynomial(x,y) is the second component, the Kazhdan–Lusztig polynomial P(x,y). The finite sum is taken as a finsum over the interval.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/KLInvariance.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/KLInvariance.lean; bytes 16..3453
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}

/-- An upward edge in the *strong* Bruhat graph, with left reflection labels. -/
def BruhatStep (cs : CoxeterSystem M W) (x y : W) : Prop :=
  cs.length x < cs.length y ∧ ∃ t : W, cs.IsReflection t ∧ y = t * x

/-- The actual strong Bruhat order, not the weak order. -/
def BruhatLE (cs : CoxeterSystem M W) : W → W → Prop :=
  Relation.ReflTransGen (BruhatStep cs)

/-- The unlabelled interval, including both endpoints. -/
def Interval (cs : CoxeterSystem M W) (u b : W) :=
  {x : W // BruhatLE cs u x ∧ BruhatLE cs x b}

instance intervalOrder (cs : CoxeterSystem M W) (u b : W) :
    PartialOrder (Interval cs u b) where
  le left right := BruhatLE cs left.val right.val
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ forward backward := forward.trans backward
  le_antisymm left right forward backward := by
    apply Subtype.ext
    have length_mono : ∀ {lower upper : W}, BruhatLE cs lower upper →
        cs.length lower ≤ cs.length upper := by
      intro lower upper relation
      induction relation using Relation.ReflTransGen.head_induction_on with
      | refl => exact le_rfl
      | head step _ rest => exact le_trans step.1.le rest
    by_contra distinct
    rcases forward.cases_head with same | ⟨middle, step, rest⟩
    · exact distinct same
    · exact (not_lt_of_ge (length_mono backward))
        (lt_of_lt_of_le step.1 (length_mono rest))

/-- `d(x,y)` in the manuscript, used only for comparable endpoints. -/
noncomputable def rankDifference (cs : CoxeterSystem M W) (x y : W) : ℕ :=
  cs.length y - cs.length x

abbrev PolynomialFamilies (W : Type v) := (W → W → ℤ[X]) × (W → W → ℤ[X])

/-- Exact equal-parameter normalization in the introduction.
The first family is R and the second is P.  `reflect d p` is `q^d p(q⁻¹)`
when `p.natDegree ≤ d`, which follows here from the degree bound (or the
diagonal normalization). The sum is over the real Bruhat interval;
its finiteness is a separate theorem, not a different definition of order. -/
structure NormalizedKL (cs : CoxeterSystem M W) (RP : PolynomialFamilies W) : Prop where
  R_diagonal : ∀ x, RP.1 x x = 1
  R_zero : ∀ x y, ¬ BruhatLE cs x y → RP.1 x y = 0
  R_recursion : ∀ x y i, cs.length (cs.simple i * y) < cs.length y →
    RP.1 x y =
      if cs.length (cs.simple i * x) < cs.length x then
        RP.1 (cs.simple i * x) (cs.simple i * y)
      else
        (X - 1) * RP.1 x (cs.simple i * y) +
          X * RP.1 (cs.simple i * x) (cs.simple i * y)
  P_diagonal : ∀ x, RP.2 x x = 1
  P_zero : ∀ x y, ¬ BruhatLE cs x y → RP.2 x y = 0
  P_degree : ∀ x y, BruhatLE cs x y → x ≠ y →
    2 * (RP.2 x y).natDegree < rankDifference cs x y
  reciprocity : ∀ x y, BruhatLE cs x y →
    reflect (rankDifference cs x y) (RP.2 x y) =
      ∑ᶠ z : Interval cs x y, RP.1 x z.val * RP.2 z.val y

/-- The polynomial families selected by their equal-parameter normalization. -/
noncomputable def klFamilies (cs : CoxeterSystem M W) : PolynomialFamilies W :=
  Classical.epsilon (NormalizedKL cs)

noncomputable def klPolynomial (cs : CoxeterSystem M W) (x y : W) : ℤ[X] :=
  (klFamilies cs).2 x y

end KLInvariance

namespace KLInvariance

universe u v u' v'

variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}



end KLInvariance
end OAI


