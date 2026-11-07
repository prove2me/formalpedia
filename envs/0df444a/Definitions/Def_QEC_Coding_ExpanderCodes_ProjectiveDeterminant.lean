-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveDeterminant
-- name    : QEC_Coding_ExpanderCodes_ProjectiveDeterminant
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:43:57.931414+00:00
-- url     : https://prove2.me/theorems/8bbb33cf-9ea5-43d0-8f34-13748423268a
-- title:
--   Projective Determinant
-- statement:
--   Definitions and structural lemmas for Projective Determinant, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProjectiveDeterminant.lean

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
set_option autoImplicit false
namespace QEC.Coding.ExpanderCodes.ProjectiveDeterminant
open Matrix
variable {K : Type*} [Field K]
def specialProjectiveSubgroup : Subgroup (Matrix.ProjGenLinGroup (Fin 2) K) :=
  Matrix.SpecialLinearGroup.toPGL.range
theorem specialProjectiveSubgroup_eq_psl_range :
    specialProjectiveSubgroup (K := K) =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  ext g
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨QuotientGroup.mk s, rfl⟩
  · rintro ⟨s, rfl⟩
    induction s using Quotient.inductionOn with
    | h s => exact ⟨s, rfl⟩
noncomputable def liftToPSL (g : Matrix.ProjGenLinGroup (Fin 2) K)
    (hg : g ∈ specialProjectiveSubgroup) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
  (MonoidHom.ofInjective Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).symm
    ⟨g, by rwa [← specialProjectiveSubgroup_eq_psl_range]⟩
end QEC.Coding.ExpanderCodes.ProjectiveDeterminant


