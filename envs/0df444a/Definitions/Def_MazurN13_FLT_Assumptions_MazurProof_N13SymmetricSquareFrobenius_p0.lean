-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SymmetricSquareFrobenius_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SymmetricSquareFrobenius_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:33:19.945975+00:00
-- url     : https://prove2.me/theorems/5beadf2c-26a7-4db8-9fdb-eb682c3d4be3
-- title:
--   FLT.Assumptions.MazurProof.N13SymmetricSquareFrobenius source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SymmetricSquareFrobenius

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SymmetricSquareFrobenius
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SymmetricSquareTwo_p0

set_option autoImplicit false




/-!
# Frobenius-fixed degree-two divisors on the N13 special fibre

An `𝔽₂`-rational point of a geometric symmetric square can in general be a
nonsplit Frobenius pair of `𝔽₄`-points.  For the N13 good model this does
not occur: the structural point classification already proves that every
`𝔽₄` curve point has both coordinates fixed by Frobenius.

This file makes that source-type correction explicit.  Base change gives an
equivalence between the six `𝔽₂` points and the six `𝔽₄` points, geometric
Frobenius is pointwise the identity on the latter, and consequently its
fixed unordered degree-two divisors are exactly `Sym2(C(𝔽₂))`.
-/

namespace MazurProof.N13SymmetricSquareFrobenius

noncomputable section

open N13GoodModelTwo

abbrev F2 := N13GoodModelTwo.F2
abbrev F4 := N13GoodModelTwo.F4

abbrev Point2 := CompletedPoint F2
abbrev Point4 := CompletedPoint F4

def residueEmbedding : F2 →+* F4 :=
  algebraMap F2 F4

def affineBaseChange : AffinePoint F2 → AffinePoint F4 :=
  fun P =>
    ⟨(residueEmbedding P.1.1, residueEmbedding P.1.2), by
      have hmap := congrArg residueEmbedding P.2
      have hy :
          residueEmbedding P.1.2 ^ 2 = residueEmbedding P.1.2 := by
        rw [← map_pow, ZMod.pow_card]
      simpa [AffineEquation, h, rhs, hy, map_add, map_mul, map_pow] using hmap⟩

def infinityBaseChange : InfinityPoint F2 → InfinityPoint F4 :=
  fun P =>
    ⟨residueEmbedding P.1, by
      have hmap := congrArg residueEmbedding P.2
      have hv :
          residueEmbedding P.1 ^ 2 = residueEmbedding P.1 := by
        rw [← map_pow, ZMod.pow_card]
      simpa [InfinityChartEquation, hv, map_add, map_mul, map_pow] using hmap⟩

def pointBaseChange : Point2 → Point4
  | Sum.inl P => Sum.inl (affineBaseChange P)
  | Sum.inr P => Sum.inr (infinityBaseChange P)

theorem affineBaseChange_injective :
    Function.Injective affineBaseChange := by
  intro P Q hPQ
  apply Subtype.ext
  have hval := congrArg Subtype.val hPQ
  apply Prod.ext
  · exact residueEmbedding.injective (congrArg Prod.fst hval)
  · exact residueEmbedding.injective (congrArg Prod.snd hval)

theorem infinityBaseChange_injective :
    Function.Injective infinityBaseChange := by
  intro P Q hPQ
  apply Subtype.ext
  exact residueEmbedding.injective (congrArg Subtype.val hPQ)

theorem pointBaseChange_injective :
    Function.Injective pointBaseChange := by
  intro P Q hPQ
  rcases P with P | P <;> rcases Q with Q | Q
  · exact congrArg Sum.inl (affineBaseChange_injective (Sum.inl.inj hPQ))
  · cases hPQ
  · cases hPQ
  · exact congrArg Sum.inr (infinityBaseChange_injective (Sum.inr.inj hPQ))

theorem pointBaseChange_bijective :
    Function.Bijective pointBaseChange := by
  apply (Nat.bijective_iff_injective_and_card pointBaseChange).mpr
  exact
    ⟨pointBaseChange_injective,
      completed_points_f2_card.trans completed_points_f4_card.symm⟩

def pointBaseChangeEquiv : Point2 ≃ Point4 :=
  Equiv.ofBijective pointBaseChange pointBaseChange_bijective

def affineFrobenius : AffinePoint F4 → AffinePoint F4 :=
  fun P =>
    ⟨(P.1.1 ^ 2, P.1.2 ^ 2), by
      have hfixed :=
        (affineEquation_iff_fixed f4_fourth_eq P.1.1 P.1.2).mp P.2
      simpa [hfixed.1, hfixed.2] using P.2⟩

def infinityFrobenius : InfinityPoint F4 → InfinityPoint F4 :=
  fun P =>
    ⟨P.1 ^ 2, by
      have hfixed :=
        (infinityChartEquation_zero_iff_fixed P.1).mp P.2
      simpa [hfixed] using P.2⟩

def pointFrobenius : Point4 → Point4
  | Sum.inl P => Sum.inl (affineFrobenius P)
  | Sum.inr P => Sum.inr (infinityFrobenius P)

theorem affineFrobenius_eq (P : AffinePoint F4) :
    affineFrobenius P = P := by
  apply Subtype.ext
  exact Prod.ext
    ((affineEquation_iff_fixed f4_fourth_eq P.1.1 P.1.2).mp P.2).1
    ((affineEquation_iff_fixed f4_fourth_eq P.1.1 P.1.2).mp P.2).2

theorem infinityFrobenius_eq (P : InfinityPoint F4) :
    infinityFrobenius P = P := by
  apply Subtype.ext
  exact (infinityChartEquation_zero_iff_fixed P.1).mp P.2

theorem pointFrobenius_eq (P : Point4) :
    pointFrobenius P = P := by
  rcases P with P | P
  · exact congrArg Sum.inl (affineFrobenius_eq P)
  · exact congrArg Sum.inr (infinityFrobenius_eq P)

def divisorFrobenius : Sym2 Point4 → Sym2 Point4 :=
  Sym2.map pointFrobenius

theorem divisorFrobenius_eq (D : Sym2 Point4) :
    divisorFrobenius D = D := by
  induction D using Sym2.ind with
  | _ P Q =>
      simp [divisorFrobenius, pointFrobenius_eq]

abbrev FrobeniusFixedDivisor : Type :=
  {D : Sym2 Point4 // divisorFrobenius D = D}

def fixedDivisorEquiv : FrobeniusFixedDivisor ≃ Sym2 Point4 where
  toFun D := D.1
  invFun D := ⟨D, divisorFrobenius_eq D⟩
  left_inv D := by
    apply Subtype.ext
    rfl
  right_inv _ := rfl

def sym2MapEquiv {A B : Type*} (e : A ≃ B) : Sym2 A ≃ Sym2 B where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv D := by
    induction D using Sym2.ind with
    | _ P Q => simp
  right_inv D := by
    induction D using Sym2.ind with
    | _ P Q => simp

/-- There are no nonsplit Frobenius pairs: every fixed degree-two divisor
over `𝔽₄` comes uniquely by base change from `Sym2(C(𝔽₂))`. -/
def effectiveDivisorTwoEquivFrobeniusFixed :
    Sym2 Point2 ≃ FrobeniusFixedDivisor :=
  (sym2MapEquiv pointBaseChangeEquiv).trans fixedDivisorEquiv.symm

theorem frobeniusFixedDivisor_card :
    Nat.card FrobeniusFixedDivisor = 21 := by
  rw [← Nat.card_congr effectiveDivisorTwoEquivFrobeniusFixed]
  exact N13SymmetricSquareTwo.effectiveDivisorTwo_card

end

end MazurProof.N13SymmetricSquareFrobenius


