-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinitySpecialPointClass_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13InfinitySpecialPointClass_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T19:42:28.153285+00:00
-- url     : https://prove2.me/theorems/325950d2-fb16-446e-a950-d94927ec0fd9
-- title:
--   FLT.Assumptions.MazurProof.N13InfinitySpecialPointClass source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13InfinitySpecialPointClass

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13InfinitySpecialPointClass
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ProperCurveReduction_p0

set_option autoImplicit false




/-!
# Anchored Abel classes at the two N13 infinity points

The set-valued special Abel class adjoins the positive infinity point as a
fixed anchor.  Therefore the negative infinity point gives the canonical
hyperelliptic fibre, while two copies of the positive point do not.  These
calculations retain the sheet coordinate that a bare affine ideal loses.
-/

namespace MazurProof.N13InfinitySpecialPointClass

noncomputable section

open scoped Sym2

/-- The residue field `F₂`, used for the two sheets of the special curve. -/
abbrev K : Type :=
  N13AbelFiberTwoModel.K

/-- The two-adic field in which the proper affine/infinity chart split is made. -/
abbrev Q₂ : Type :=
  N13ProperCurveReduction.Q₂

/-- The fixed anchor is the sheet-zero point over the infinity base point. -/
@[simp] theorem curvePointEquiv_specialAnchor :
    N13AbelFiberTwoModel.curvePointEquiv
        N13RationalPointEndgame.specialAnchor =
      (N13AbelFiberTwoModel.baseAtInfinity, (0 : K)) := by
  simp [N13RationalPointEndgame.specialAnchor,
    N13AbelFiberTwoModel.baseAtInfinity,
    N13SpecialCuspReduction.cuspCoordinate]

/-- The negative infinity cusp is the sheet-one point over the same base. -/
@[simp] theorem curvePointEquiv_specialInfinityMinus :
    N13AbelFiberTwoModel.curvePointEquiv
        (N13SpecialCuspReduction.specialCuspEquiv
          N13Mumford.Cusp13.infinityMinus) =
      (N13AbelFiberTwoModel.baseAtInfinity, (1 : K)) := by
  simp [N13AbelFiberTwoModel.baseAtInfinity,
    N13SpecialCuspReduction.cuspCoordinate]

/-- The negative infinity point together with the positive anchor is the
canonical degree-two divisor over the infinity base point. -/
theorem infinityPair_isCanonical :
    N13AbelFiberTwoModel.IsCanonical
      s(N13SpecialCuspReduction.specialCuspEquiv
          N13Mumford.Cusp13.infinityMinus,
        N13RationalPointEndgame.specialAnchor) := by
  refine
    ⟨N13AbelFiberTwoModel.baseAtInfinity, ?_⟩
  change
    s(N13AbelFiberTwoModel.curvePointEquiv.symm
        (N13AbelFiberTwoModel.baseAtInfinity, 0),
      N13AbelFiberTwoModel.curvePointEquiv.symm
        (N13AbelFiberTwoModel.baseAtInfinity, 1)) =
      s(N13SpecialCuspReduction.specialCuspEquiv
          N13Mumford.Cusp13.infinityMinus,
        N13RationalPointEndgame.specialAnchor)
  rw [Sym2.eq_iff]
  refine Or.inr ⟨?_, ?_⟩
  · apply N13AbelFiberTwoModel.curvePointEquiv.injective
    simp
  · apply N13AbelFiberTwoModel.curvePointEquiv.injective
    simp [N13AbelFiberTwoModel.baseAtInfinity,
      N13SpecialCuspReduction.cuspCoordinate]

/-- The anchored special class of negative infinity is the canonical class. -/
@[simp] theorem specialPointClass_infinityMinus_eq_canonicalClass :
    N13RationalPointEndgame.specialPointClass
        (N13SpecialCuspReduction.specialCuspEquiv
          N13Mumford.Cusp13.infinityMinus) =
      N13AbelFiberTwoModel.canonicalClass := by
  exact
    (N13AbelFiberTwoModel.abel_eq_canonicalClass_iff _).2
      infinityPair_isCanonical

/-- Two copies of the positive infinity point cannot be a hyperelliptic
fibre because a canonical fibre contains one point on each sheet. -/
theorem anchorPair_not_canonical :
    ¬ N13AbelFiberTwoModel.IsCanonical
      s(N13RationalPointEndgame.specialAnchor,
        N13RationalPointEndgame.specialAnchor) := by
  rintro ⟨b, hb⟩
  change
    s(N13AbelFiberTwoModel.curvePointEquiv.symm (b, 0),
      N13AbelFiberTwoModel.curvePointEquiv.symm (b, 1)) =
      s(N13RationalPointEndgame.specialAnchor,
        N13RationalPointEndgame.specialAnchor) at hb
  rw [Sym2.eq_iff] at hb
  rcases hb with hb | hb
  · have hsheet :=
      congrArg
        (fun P => (N13AbelFiberTwoModel.curvePointEquiv P).2)
        hb.2
    simp at hsheet
  · have hsheet :=
      congrArg
        (fun P => (N13AbelFiberTwoModel.curvePointEquiv P).2)
        hb.2
    simp at hsheet

/-- Hence the anchored class of positive infinity is a regular class, not
the canonical class obtained from the opposite sheet. -/
theorem specialPointClass_specialAnchor_ne_canonicalClass :
    N13RationalPointEndgame.specialPointClass
        N13RationalPointEndgame.specialAnchor ≠
      N13AbelFiberTwoModel.canonicalClass := by
  intro h
  exact
    anchorPair_not_canonical
      ((N13AbelFiberTwoModel.abel_eq_canonicalClass_iff _).1 h)

/-!
## Injectivity of the anchored special Abel map

Outside the canonical pencil an Abel class has a unique effective divisor of
degree two.  Inside the pencil, the fixed positive-infinity anchor determines
the base point and therefore forces the other point to be negative infinity.
Thus adjoining the fixed anchor loses no information about a special curve
point.
-/

/-- Two special curve points with the same anchored Abel class are equal.
The only exceptional Abel fibre is the canonical pencil, and only its
infinity fibre contains the fixed anchor. -/
theorem specialPointClass_injective :
    Function.Injective
      N13RationalPointEndgame.specialPointClass := by
  intro P Q hPQ
  change
    N13AbelFiberTwoModel.abel
          s(P, N13RationalPointEndgame.specialAnchor) =
      N13AbelFiberTwoModel.abel
          s(Q, N13RationalPointEndgame.specialAnchor) at hPQ
  rw [N13AbelFiberTwoModel.abel_eq_iff] at hPQ
  rcases hPQ with hdivisor | ⟨hcanonicalP, hcanonicalQ⟩
  · -- Equality of unordered pairs either fixes both entries or swaps the
    -- moving point with the common anchor; both alternatives give `P = Q`.
    rw [Sym2.eq_iff] at hdivisor
    rcases hdivisor with hstraight | hswap
    · exact hstraight.1
    · exact hswap.1.trans hswap.2
  · -- A canonical divisor containing the sheet-zero infinity anchor must
    -- have the sheet-one infinity point as its other member.
    have eq_infinityMinus_of_canonical
        (T : N13RationalPointEndgame.SpecialCurvePoint)
        (hcanonical :
          N13AbelFiberTwoModel.IsCanonical
            s(T, N13RationalPointEndgame.specialAnchor)) :
        T =
          N13SpecialCuspReduction.specialCuspEquiv
            N13Mumford.Cusp13.infinityMinus := by
      obtain ⟨b, hb⟩ := hcanonical
      change
        s(N13AbelFiberTwoModel.curvePointEquiv.symm (b, 0),
            N13AbelFiberTwoModel.curvePointEquiv.symm (b, 1)) =
          s(T, N13RationalPointEndgame.specialAnchor) at hb
      rw [Sym2.eq_iff] at hb
      rcases hb with hstraight | hswap
      · have hsheet :=
          congrArg
            (fun Z => (N13AbelFiberTwoModel.curvePointEquiv Z).2)
            hstraight.2
        simp at hsheet
      · have hbbase :
            b = N13AbelFiberTwoModel.baseAtInfinity := by
          have hcoord :=
            congrArg N13AbelFiberTwoModel.curvePointEquiv hswap.1
          simpa using congrArg Prod.fst hcoord
        apply N13AbelFiberTwoModel.curvePointEquiv.injective
        calc
          N13AbelFiberTwoModel.curvePointEquiv T = (b, 1) := by
            simpa using
              congrArg N13AbelFiberTwoModel.curvePointEquiv hswap.2.symm
          _ =
              (N13AbelFiberTwoModel.baseAtInfinity, 1) := by
            rw [hbbase]
          _ =
              N13AbelFiberTwoModel.curvePointEquiv
                (N13SpecialCuspReduction.specialCuspEquiv
                  N13Mumford.Cusp13.infinityMinus) := by
            simp [N13AbelFiberTwoModel.baseAtInfinity,
              N13SpecialCuspReduction.cuspCoordinate]
    exact
      (eq_infinityMinus_of_canonical P hcanonicalP).trans
        (eq_infinityMinus_of_canonical Q hcanonicalQ).symm

/-! ## Proper reduction of an escaping affine point -/

/-- Proper reduction of a nonintegral affine point records the residue of
the ordinate of its integral infinity-chart lift, over the infinity base
point.  This is the same lift used by the explicit proper point line. -/
@[simp] theorem curvePointEquiv_reduceNonintegralAffine
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13AbelFiberTwoModel.curvePointEquiv
        (N13ProperCurveReduction.reduceNonintegralAffine
          x y hx hxy) =
      (N13AbelFiberTwoModel.baseAtInfinity,
        PadicInt.toZMod
          (N13ProperCurveReduction.nonintegralInfinityLift
            x y hx hxy).1.2) := by
  rfl

/-- An escaping affine point reduces to exactly one of the two infinity
sheets: the fixed positive anchor or the named negative infinity cusp. -/
theorem reduceNonintegralAffine_eq_specialAnchor_or_infinityMinus
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13ProperCurveReduction.reduceNonintegralAffine x y hx hxy =
        N13RationalPointEndgame.specialAnchor ∨
      N13ProperCurveReduction.reduceNonintegralAffine x y hx hxy =
        N13SpecialCuspReduction.specialCuspEquiv
          N13Mumford.Cusp13.infinityMinus := by
  let s : K :=
    PadicInt.toZMod
      (N13ProperCurveReduction.nonintegralInfinityLift
        x y hx hxy).1.2
  have hs : s = 0 ∨ s = 1 :=
    N13GoodModelTwo.fixedTwo_eq_zero_or_one
      s (ZMod.pow_card s)
  rcases hs with hs | hs
  · left
    apply N13AbelFiberTwoModel.curvePointEquiv.injective
    rw [curvePointEquiv_reduceNonintegralAffine,
      curvePointEquiv_specialAnchor]
    simp [s, hs]
  · right
    apply N13AbelFiberTwoModel.curvePointEquiv.injective
    rw [curvePointEquiv_reduceNonintegralAffine,
      curvePointEquiv_specialInfinityMinus]
    simp [s, hs]

/-- Consequently the anchored special target of an escaping point is
completely determined: it is either the anchor-double class or the
canonical class. -/
theorem specialPointClass_reduceNonintegralAffine_dichotomy
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13RationalPointEndgame.specialPointClass
          (N13ProperCurveReduction.reduceNonintegralAffine
            x y hx hxy) =
        N13RationalPointEndgame.specialPointClass
          N13RationalPointEndgame.specialAnchor ∨
      N13RationalPointEndgame.specialPointClass
          (N13ProperCurveReduction.reduceNonintegralAffine
            x y hx hxy) =
        N13AbelFiberTwoModel.canonicalClass := by
  rcases
      reduceNonintegralAffine_eq_specialAnchor_or_infinityMinus
        x y hx hxy with hplus | hminus
  · exact Or.inl (congrArg
      N13RationalPointEndgame.specialPointClass hplus)
  · exact Or.inr (by
      rw [hminus,
        specialPointClass_infinityMinus_eq_canonicalClass])

end

end MazurProof.N13InfinitySpecialPointClass


