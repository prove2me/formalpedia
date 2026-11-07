-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveLinearSize
-- name    : QEC_Coding_ExpanderCodes_ProjectiveLinearSize
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:45:13.665405+00:00
-- url     : https://prove2.me/theorems/311531d0-ad1d-4f80-ac76-a8a005bad9aa
-- title:
--   Projective Linear Size
-- statement:
--   Definitions and structural lemmas for Projective Linear Size, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProjectiveLinearSize.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldQuadraticSplitting
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
set_option autoImplicit false
namespace QEC.Coding.ExpanderCodes.ProjectiveLinearSize
open Matrix
variable {K : Type*} [Field K]
def upperUnipotent (t : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩
def projectiveUpper (t : K) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
  QuotientGroup.mk (upperUnipotent t)
end QEC.Coding.ExpanderCodes.ProjectiveLinearSize


