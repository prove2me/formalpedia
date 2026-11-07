-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_FiniteImage
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_FiniteImage
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:37:50.214067+00:00
-- url     : https://prove2.me/theorems/cb65418e-dcb8-4743-a6d8-1b2158faa741
-- title:
--   Finite Image
-- statement:
--   Definitions and structural lemmas for Finite Image, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/FiniteImage.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_ProjectiveIndex_generalLinear_det_surjective

set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace ProjectiveIndex
variable {G Q : Type*} [Group G] [Group Q]
variable (n K : Type*) [Fintype n] [DecidableEq n]
  [Nonempty n] [Field K] [Fintype K]
noncomputable def generatedProjectiveImage (b : PGL(n, K)) :
    Subgroup PGL(n, K) :=
  projectiveSpecialLinear n K ⊔ Subgroup.zpowers b
end ProjectiveIndex
noncomputable def indexWitnessGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ResidueField P r level) :=
  Classical.choose
    (ProjectiveIndex.generalLinear_det_surjective
      (Fin r.matrixRank) (ResidueField P r level)
      (indexRatioUnit P r level))
noncomputable def indexWitness
    (P : BasePrime) (r : Rank) (level : Nat) : PGL P r level :=
  Matrix.ProjGenLinGroup.mk (indexWitnessGL P r level)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


