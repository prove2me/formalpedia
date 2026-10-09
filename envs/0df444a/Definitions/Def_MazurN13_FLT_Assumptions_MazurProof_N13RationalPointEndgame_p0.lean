-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RationalPointEndgame_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13RationalPointEndgame_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T18:19:34.165998+00:00
-- url     : https://prove2.me/theorems/85b6df60-90b9-47ed-9524-159ef5f49482
-- title:
--   FLT.Assumptions.MazurProof.N13RationalPointEndgame source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13RationalPointEndgame

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13RationalPointEndgame
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordAbelJacobi_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ReductionClassifier_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialCuspReduction_p0

set_option autoImplicit false




/-!
# The structural N13 rational-point endgame

This file isolates the exact proper-reduction input still needed after the
N13 two-descent and formal-kernel arguments.

A compatible reduction consists of the existing exact set-valued Picard
classifier, a reduction of rational curve points to the good special fibre,
and compatibility with the Abel map and the six rational cusps.  Since the
six cusps cover the special curve, every rational curve point has the same
reduced Abel class as a cusp.  Separatedness makes Picard reduction
injective, and the already-proved Abel--Jacobi embedding then identifies the
two curve points.

No group law on the nineteen-element set and no finite table are used.
-/

namespace MazurProof.N13RationalPointEndgame

noncomputable section

open scoped Sym2

abbrev G : Type :=
  N13ReductionClassifier.G

abbrev SpecialSet : Type :=
  N13ReductionClassifier.SpecialSet

abbrev RationalCurvePoint : Type :=
  SexticMumford.CurvePoint (N13Mumford.model ℚ)

abbrev SpecialCurvePoint : Type :=
  N13SpecialCuspReduction.SpecialCurvePoint

abbrev Cusp13 : Type :=
  N13Mumford.Cusp13

def rationalAbel : RationalCurvePoint → G :=
  N13MumfordAbelJacobi.abelJacobi ℚ

/-- A fixed special point used to place degree-one Abel classes in the
degree-two set model.  Its choice is immaterial when comparing two points
with the same reduction. -/
def specialAnchor : SpecialCurvePoint :=
  N13SpecialCuspReduction.specialCuspEquiv .infinityPlus

/-- The set-valued special Abel class of a curve point, represented by
adjoining one fixed anchor point. -/
def specialPointClass (P : SpecialCurvePoint) : SpecialSet :=
  N13AbelFiberTwoModel.abel (s(P, specialAnchor))

/-- Proper curve reduction together with its compatibility with the exact
Picard classifier and with the six named rational cusps. -/
structure CompatibleReduction where
  classifier : N13ReductionClassifier.Data G SpecialSet
  reduceCurve : RationalCurvePoint → SpecialCurvePoint
  classify_abel :
    ∀ P : RationalCurvePoint,
      classifier.classify (rationalAbel P) =
        specialPointClass (reduceCurve P)
  reduce_cusp :
    ∀ c : Cusp13,
      reduceCurve (N13Mumford.cuspPoint c) =
        N13SpecialCuspReduction.specialCuspEquiv c

namespace CompatibleReduction

variable (D : CompatibleReduction)

/-- Every rational curve point and some rational cusp have the same
set-valued special Picard class. -/
theorem exists_cusp_classify_eq
    (P : RationalCurvePoint) :
    ∃ c : Cusp13,
      D.classifier.classify (rationalAbel P) =
        D.classifier.classify
          (N13MumfordAbelJacobi.cuspAbelJacobi c) := by
  obtain ⟨c, hc⟩ :=
    N13SpecialCuspReduction.specialCuspEquiv_surjective
      (D.reduceCurve P)
  refine ⟨c, ?_⟩
  calc
    D.classifier.classify (rationalAbel P) =
        specialPointClass (D.reduceCurve P) :=
      D.classify_abel P
    _ =
        specialPointClass
          (N13SpecialCuspReduction.specialCuspEquiv c) := by
      rw [hc]
    _ =
        specialPointClass
          (D.reduceCurve (N13Mumford.cuspPoint c)) := by
      rw [D.reduce_cusp c]
    _ =
        D.classifier.classify
          (N13MumfordAbelJacobi.cuspAbelJacobi c) := by
      exact (D.classify_abel (N13Mumford.cuspPoint c)).symm

/-- A separated exact classifier makes every rational point of the
projective N13 curve equal to one of the six rational cusps. -/
theorem curvePoint_eq_cusp
    (separated :
      N18RouteC.Separated.NSeparated
        D.classifier.red.ker 2)
    (P : RationalCurvePoint) :
    ∃ c : Cusp13, P = N13Mumford.cuspPoint c := by
  obtain ⟨c, hclass⟩ :=
    D.exists_cusp_classify_eq P
  have hred :
      D.classifier.red (rationalAbel P) =
        D.classifier.red
          (N13MumfordAbelJacobi.cuspAbelJacobi c) := by
    apply D.classifier.quotientClassify_injective
    simpa only [
      N13ReductionClassifier.Data.quotientClassify_red]
      using hclass
  have hPic :
      rationalAbel P =
        N13MumfordAbelJacobi.cuspAbelJacobi c :=
    (N13ReductionClassifier.n13_reduction_injective
      D.classifier separated) hred
  refine ⟨c, ?_⟩
  exact N13MumfordAbelJacobi.abelJacobi_injective ℚ hPic

private def affineX? :
    RationalCurvePoint → Option ℚ
  | .infinityPlus => none
  | .infinityMinus => none
  | .affine x _ _ => some x

/-- The exact affine statement consumed by `CyclicExclusion13` follows from
the compatible proper reduction and formal-kernel separatedness. -/
theorem affine_x_is_cuspidal
    (separated :
      N18RouteC.Separated.NSeparated
        D.classifier.red.ker 2) :
    ∀ X Y : ℚ, N13CurveModel.C13SexticEq X Y →
      X = 0 ∨ X = -1 := by
  intro X Y hcurve
  let P : RationalCurvePoint :=
    N13Mumford.affineCurvePoint X Y hcurve
  obtain ⟨c, hPc⟩ :=
    D.curvePoint_eq_cusp separated P
  have hx := congrArg affineX? hPc
  cases c with
  | infinityPlus =>
      simp [P, affineX?, N13Mumford.affineCurvePoint,
        N13Mumford.cuspPoint] at hx
  | infinityMinus =>
      simp [P, affineX?, N13Mumford.affineCurvePoint,
        N13Mumford.cuspPoint] at hx
  | zeroPlus =>
      exact Or.inl (by
        simpa [P, affineX?, N13Mumford.affineCurvePoint,
          N13Mumford.cuspPoint] using hx)
  | zeroMinus =>
      exact Or.inl (by
        simpa [P, affineX?, N13Mumford.affineCurvePoint,
          N13Mumford.cuspPoint] using hx)
  | negOnePlus =>
      exact Or.inr (by
        simpa [P, affineX?, N13Mumford.affineCurvePoint,
          N13Mumford.cuspPoint] using hx)
  | negOneMinus =>
      exact Or.inr (by
        simpa [P, affineX?, N13Mumford.affineCurvePoint,
          N13Mumford.cuspPoint] using hx)

end CompatibleReduction

end

end MazurProof.N13RationalPointEndgame


