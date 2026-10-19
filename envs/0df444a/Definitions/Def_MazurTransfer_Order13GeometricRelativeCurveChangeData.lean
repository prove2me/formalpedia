-- Prove2me | Definitions.Def_MazurTransfer_Order13GeometricRelativeCurveChangeData
-- name    : MazurTransfer_Order13GeometricRelativeCurveChangeData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T18:04:40.616003+00:00
-- url     : https://prove2.me/theorems/ee19a3ba-5eee-4071-9bb6-22219085df86
-- title:
--   The literal extension-field curve is the actual relative curve fibre
-- statement:
--   The original embedding identifies the literal curve over a characteristic-zero field with the pullback of the actual rational curve. Its first and second projections, reassociation lemmas, IsIso proof-instance type, and compatibility with every commuting pair of curve endomorphisms are retained. Seven complete original types and the actual embedding constructor value are compared. Named downstream consumer: geometric Picard line-bundle pullback and the actual arithmetic class dictionary.
-- source:
--   Complete original MazurTheorem Order13GeometricRelativeCurveChange using the accepted actual whole-curve Cartesian-square theorem and published re-rigidified curve pullback data. Official Anthropic FLT relative Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the literal extension-field curve with the actual
relative curve fibre, compatibly with every commuting curve endomorphism.
Named downstream consumer: line-bundle pullback for geometric points of
the existing rational Picard diamond action.
-/
import Theorems.Thm_MazurTransfer_Order13ActualCurveBaseChange_wholeCurve_isPullback
import Definitions.Def_MazurTransfer_Order13PublicFunctionFieldInvariants
import Definitions.Def_MazurTransfer_PicardReRigidifiedCurvePullbackData

noncomputable section
namespace MazurTransfer.Order13GeometricRelativeCurveChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualCurveBaseChange
variable (K : Type) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

def geometricCurveEmbedding : curveScheme K ⟶
    pullback (curveToBase ℚ) (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) :=
  (wholeCurve_isPullback ℚ K).isoPullback.hom

instance : IsIso (geometricCurveEmbedding K) := by
  unfold geometricCurveEmbedding
  infer_instance

@[reassoc]
theorem geometricCurveEmbedding_fst :
    geometricCurveEmbedding K ≫ pullback.fst _ _ = curveMap ℚ K :=
  (wholeCurve_isPullback ℚ K).isoPullback_hom_fst

@[reassoc]
theorem geometricCurveEmbedding_snd :
    geometricCurveEmbedding K ≫ pullback.snd _ _ = curveToBase K :=
  (wholeCurve_isPullback ℚ K).isoPullback_hom_snd

theorem geometricCurveEmbedding_curveChange
    (f : curveScheme ℚ ⟶ curveScheme ℚ) (hf : f ≫ curveToBase ℚ = curveToBase ℚ)
    (g : curveScheme K ⟶ curveScheme K) (hg : g ≫ curveToBase K = curveToBase K)
    (hcomm : g ≫ curveMap ℚ K = curveMap ℚ K ≫ f) :
    geometricCurveEmbedding K ≫ curveChange f hf (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) =
      g ≫ geometricCurveEmbedding K := by
  apply pullback.hom_ext
  · simp only [curveChange, Category.assoc, pullback.map, pullback.lift_fst,
      Category.comp_id]
    rw [geometricCurveEmbedding_fst_assoc, geometricCurveEmbedding_fst]
    exact hcomm.symm
  · simp only [curveChange, Category.assoc, pullback.map, pullback.lift_snd,
      Category.comp_id]
    rw [geometricCurveEmbedding_snd]
    exact hg.symm

end MazurTransfer.Order13GeometricRelativeCurveChange
#print axioms MazurTransfer.Order13GeometricRelativeCurveChange.geometricCurveEmbedding_curveChange


