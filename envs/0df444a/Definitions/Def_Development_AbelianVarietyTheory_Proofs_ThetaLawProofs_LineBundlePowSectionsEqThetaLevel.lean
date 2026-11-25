-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LineBundlePowSectionsEqThetaLevel
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LineBundlePowSectionsEqThetaLevel
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T17:18:36.984498+00:00
-- url     : https://prove2.me/theorems/e596801b-fb47-4bc2-af7d-ec2881539f5b
-- title:
--   Line Bundle Pow Sections Eq Theta Level
-- statement:
--   Definitions and structural lemmas for Line Bundle Pow Sections Eq Theta Level, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/LineBundlePowSectionsEqThetaLevel.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_LevBasis
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_UnimodularAndTangentOfIsAH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LevelThreeSeparatesTangentVectors
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply


set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
noncomputable section
namespace GlobalTheory.LevelDict
section Charts
variable {X : Scheme.{0}} (L : LB X) (n : ℕ)
theorem sec_ext {M : LB X} {s t : M.Sec} (h : ∀ i, s.f i = t.f i) : s = t := by
  obtain ⟨f, hf⟩ := s
  obtain ⟨f', hf'⟩ := t
  obtain rfl : f = f' := funext h
  rfl
theorem powChart_le (j : (lbPow L n).ι) : (lbPow L n).U j ≤ L.U (j PUnit.unit) :=
  fun _ hy => Set.mem_iInter.1 hy PUnit.unit
theorem le_powChart (j : (lbPow L n).ι) : L.U (j PUnit.unit) ≤ (lbPow L n).U j :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy
theorem lbPow_g (j j' : (lbPow L n).ι) : ((lbPow L n).g j j').val =
    rs X (inf_le_inf (powChart_le L n j) (powChart_le L n j'))
      (L.g (j PUnit.unit) (j' PUnit.unit) ^ (n : ℤ)).val := by
  have h : (lbPow L n).g j j' = res (inf_le_inf (powChart_le L n j) (powChart_le L n j'))
      (L.g (j PUnit.unit) (j' PUnit.unit) ^ (n : ℤ)) := by
    rw [map_zpow]
    unfold lbPow LB.LinComb
    dsimp only
    rw [Fintype.prod_unique]
    rfl
  rw [h]
  rfl
def powSecEquiv : (lbPow L n).Sec ≃ (pw L (n : ℤ)).Sec where
  toFun s := ⟨fun i => rs X (le_powChart L n fun _ => i) (s.f fun _ => i), fun i k => by
    have h := congrArg (rs X (inf_le_inf (le_powChart L n fun _ => i) (le_powChart L n fun _ => k)))
      (s.compat (fun _ => i) (fun _ => k))
    refine (rs_rs _ _ _).trans ((rs_rs _ _ _).symm.trans (h.trans ((map_mul _ _ _).trans ?_)))
    exact congrArg₂ (· * ·) ((congrArg _ (lbPow_g L n _ _)).trans ((rs_rs _ _ _).trans (rs_self _ _)))
      ((rs_rs _ _ _).trans (rs_rs _ _ _).symm)⟩
  invFun s := ⟨fun j => rs X (powChart_le L n j) (s.f (j PUnit.unit)), fun j k => by
    have h := congrArg (rs X (inf_le_inf (powChart_le L n j) (powChart_le L n k)))
      (s.compat (j PUnit.unit) (k PUnit.unit))
    rw [lbPow_g]
    refine (rs_rs _ _ _).trans ((rs_rs _ _ _).symm.trans (h.trans ((map_mul _ _ _).trans ?_)))
    exact congrArg _ ((rs_rs _ _ _).trans (rs_rs _ _ _).symm)⟩
  left_inv s := sec_ext fun _ => (rs_rs _ _ _).trans (rs_self _ _)
  right_inv s := sec_ext fun _ => (rs_rs _ _ _).trans (rs_self _ _)
end Charts
section Frames
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}
end Frames
end GlobalTheory.LevelDict


