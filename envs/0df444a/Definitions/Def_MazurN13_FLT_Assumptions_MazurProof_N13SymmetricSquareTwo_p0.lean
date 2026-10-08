-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SymmetricSquareTwo_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SymmetricSquareTwo_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:53:16.699868+00:00
-- url     : https://prove2.me/theorems/ee408ff7-eded-46af-91b1-09d2c86e658c
-- title:
--   FLT.Assumptions.MazurProof.N13SymmetricSquareTwo source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SymmetricSquareTwo

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SymmetricSquareTwo
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GoodModelTwo_p0
import Mathlib.Data.Sym.NatCard

set_option autoImplicit false




/-!
# The symmetric-square route to `#J(F₂)=19`

For a genus-two curve, the Abel map `Sym²(C) → J` is an isomorphism away
from the canonical divisor class.  Its exceptional fibre is the canonical
linear system `P¹`.  Over `F₂` this replaces three points by one.

The good N13 model has six `F₂`-points, so its ordinary symmetric square has
`6 multichoose 2 = 21` points.  This file proves the finite fibre-counting
argument that turns the geometric Abel-fibre statement into
`#J(F₂)=21-2=19`.  It deliberately isolates the remaining geometric input
as a structure, rather than assuming a general zeta-function API or
enumerating Jacobian representatives.
-/

namespace MazurProof.N13SymmetricSquareTwo

noncomputable section

open scoped BigOperators

abbrev CurvePoint :=
  N13GoodModelTwo.CompletedPoint N13GoodModelTwo.F2

/-- Unordered effective divisors of degree two on the special fibre. -/
abbrev EffectiveDivisorTwo :=
  Sym2 CurvePoint

/-- Six curve points give twenty-one unordered degree-two divisors. -/
theorem effectiveDivisorTwo_card :
    Nat.card EffectiveDivisorTwo = 21 := by
  rw [Sym2.natCard, N13GoodModelTwo.completed_points_f2_card]
  norm_num [Nat.choose]

section FiberCounting

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

/-- A fibre of a function, as a finite type. -/
abbrev Fiber (f : A → B) (b : B) :=
  {a : A // f a = b}

/-- A finite type is the disjoint union of the fibres of any map out of it. -/
def sigmaFiberEquiv (f : A → B) :
    A ≃ Σ b : B, Fiber f b where
  toFun a := ⟨f a, ⟨a, rfl⟩⟩
  invFun a := a.2.1
  left_inv _ := rfl
  right_inv a := by
    rcases a with ⟨b, a, ha⟩
    subst b
    rfl

theorem card_eq_sum_fibers (f : A → B) :
    Fintype.card A = ∑ b : B, Fintype.card (Fiber f b) := by
  classical
  rw [Fintype.card_congr (sigmaFiberEquiv f), Fintype.card_sigma]

/-- If one fibre has three elements and every other fibre is a singleton,
the source has two more elements than the target. -/
theorem card_source_eq_card_target_add_two
    (f : A → B) (exceptional : B)
    (hexceptional : Fintype.card (Fiber f exceptional) = 3)
    (hregular : ∀ b : B, b ≠ exceptional →
      Fintype.card (Fiber f b) = 1) :
    Fintype.card A = Fintype.card B + 2 := by
  classical
  rw [card_eq_sum_fibers f]
  calc
    (∑ b : B, Fintype.card (Fiber f b)) =
        ∑ b : B, if b = exceptional then 3 else 1 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : b = exceptional
      · subst b
        simp [hexceptional]
      · simp [hb, hregular b hb]
    _ = Fintype.card B + 2 := by
      have hsplit (b : B) :
          (if b = exceptional then 3 else 1) =
            1 + if b = exceptional then 2 else 0 := by
        by_cases hb : b = exceptional <;> simp [hb]
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib]
      simp

end FiberCounting

/-- Exact geometric data needed from the genus-two Abel map.  Constructing
this package is the remaining algebraic-geometry seam; all cardinal
arithmetic after it is formalized here. -/
structure AbelFiberData (J : Type*) [Finite J] where
  abel : EffectiveDivisorTwo → J
  canonicalClass : J
  canonical_fiber :
    Nat.card {D : EffectiveDivisorTwo // abel D = canonicalClass} = 3
  regular_fiber :
    ∀ c : J, c ≠ canonicalClass →
      Nat.card {D : EffectiveDivisorTwo // abel D = c} = 1

/-- The genus-two Abel-fibre theorem and the six curve points imply
`#J(F₂)=19`. -/
theorem jacobian_card_eq_nineteen
    {J : Type*} [Finite J] (D : AbelFiberData J) :
    Nat.card J = 19 := by
  classical
  letI : Fintype J := Fintype.ofFinite J
  letI : Fintype CurvePoint := Fintype.ofFinite CurvePoint
  letI : Fintype EffectiveDivisorTwo := Fintype.ofFinite EffectiveDivisorTwo
  have hsource : Fintype.card EffectiveDivisorTwo = 21 := by
    rw [← Nat.card_eq_fintype_card]
    exact effectiveDivisorTwo_card
  have hexceptional :
      Fintype.card (Fiber D.abel D.canonicalClass) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact D.canonical_fiber
  have hregular :
      ∀ c : J, c ≠ D.canonicalClass →
        Fintype.card (Fiber D.abel c) = 1 := by
    intro c hc
    rw [← Nat.card_eq_fintype_card]
    exact D.regular_fiber c hc
  have hcount := card_source_eq_card_target_add_two
    D.abel D.canonicalClass hexceptional hregular
  rw [hsource] at hcount
  rw [Nat.card_eq_fintype_card]
  omega

/-- Consequently the finite additive Jacobian is annihilated by nineteen. -/
theorem jacobian_exponent_nineteen
    {J : Type*} [AddCommGroup J] [Finite J] (D : AbelFiberData J) :
    ∀ P : J, 19 • P = 0 := by
  classical
  letI : Fintype J := Fintype.ofFinite J
  have hcard : Fintype.card J = 19 := by
    rw [← Nat.card_eq_fintype_card]
    exact jacobian_card_eq_nineteen D
  intro P
  rw [← hcard]
  exact card_nsmul_eq_zero

end

end MazurProof.N13SymmetricSquareTwo


