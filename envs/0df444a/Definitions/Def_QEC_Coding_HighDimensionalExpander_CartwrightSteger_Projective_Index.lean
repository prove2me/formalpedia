-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:35:18.526915+00:00
-- url     : https://prove2.me/theorems/b5639dce-f297-4cf1-a82c-6e143974e08e
-- title:
--   Index
-- statement:
--   Definitions and structural lemmas for Index, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Index.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueRepresentation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_two_le_matrixRank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace ProjectiveIndex
variable (n K : Type*) [Fintype n] [DecidableEq n]
  [Nonempty n] [Field K] [Fintype K]
abbrev DetPowerClass :=
  Kˣ ⧸ (powMonoidHom (Fintype.card n) : Kˣ →* Kˣ).range
noncomputable def projectiveDetClass :
    PGL(n, K) →* DetPowerClass n K :=
  Matrix.ProjGenLinGroup.lift
    ((QuotientGroup.mk'
      (powMonoidHom (Fintype.card n) : Kˣ →* Kˣ).range).comp
        Matrix.GeneralLinearGroup.det) <| by
    ext u
    change QuotientGroup.mk' _
      (Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.scalar n u)) = 1
    rw [Matrix.GeneralLinearGroup.det_scalar]
    apply (QuotientGroup.eq_one_iff _).2
    exact ⟨u, rfl⟩
noncomputable def projectiveSpecialLinear :
    Subgroup PGL(n, K) :=
  (Matrix.ProjGenLinGroup.mk.comp Matrix.SpecialLinearGroup.toGL).range
end ProjectiveIndex
instance rankMatrixIndexNonempty (r : Rank) : Nonempty (Fin r.matrixRank) :=
  ⟨⟨0, lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)⟩⟩
noncomputable def residueProjectiveDetClass
    (P : BasePrime) (r : Rank) (level : Nat) :
    PGL P r level →* ResiduePowerClass P r level :=
  by
    simpa only [PGL, ResiduePowerClass, IndexSelection.PowerClass,
      IndexSelection.dthPowerUnits, ProjectiveIndex.DetPowerClass,
      Fintype.card_fin] using
      (ProjectiveIndex.projectiveDetClass
        (Fin r.matrixRank) (ResidueField P r level))
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


