-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWIntermediate
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWIntermediate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:24:47.028216+00:00
-- url     : https://prove2.me/theorems/850265ff-67ee-4832-b6d5-50b1b0b7dd5f
-- title:
--   Source Galois WIntermediate
-- statement:
--   Definitions and structural lemmas for Source Galois WIntermediate, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWIntermediate.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisFunctionField
import Mathlib.FieldTheory.Relrank
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open IntermediateField Polynomial
theorem galoisBaseField_le_sourceGaloisWField :
    (F256⟮galoisBaseZ⟯ : IntermediateField F256 (RatFunc F256)) ≤
      F256⟮galoisBaseW⟯ := by
  rw [IntermediateField.adjoin_simple_le_iff]
  change galoisBaseW ^ 15 ∈ F256⟮galoisBaseW⟯
  exact (F256⟮galoisBaseW⟯).pow_mem
    (IntermediateField.subset_adjoin F256 {galoisBaseW}
      (Set.mem_singleton galoisBaseW)) 15
abbrev SourceGaloisWField : Type :=
  IntermediateField.extendScalars galoisBaseField_le_sourceGaloisWField
noncomputable def sourceGaloisSeedRatFuncToClosure (m : ℕ) :
    RatFunc F256 →ₐ[GaloisBaseField] SourceGaloisClosureField m :=
  (sourceGaloisSeedToClosure m).comp
    (IsScalarTower.toAlgHom GaloisBaseField (RatFunc F256) (SourceField m))
noncomputable def sourceGaloisWFieldToClosure (m : ℕ) :
    SourceGaloisWField →ₐ[GaloisBaseField] SourceGaloisClosureField m :=
  (sourceGaloisSeedRatFuncToClosure m).comp
    (IntermediateField.extendScalars
      galoisBaseField_le_sourceGaloisWField).val
abbrev SourceGaloisWClosureField (m : ℕ) :
    IntermediateField GaloisBaseField (SourceGaloisClosureField m) :=
  (sourceGaloisWFieldToClosure m).fieldRange
noncomputable instance (priority := 3000) sourceGaloisWClosureFieldAlgebra (m : ℕ) :
    Algebra GaloisBaseField (SourceGaloisWClosureField m) :=
  (SourceGaloisWClosureField m).toSubalgebra.algebra'
noncomputable instance (priority := 3000) sourceGaloisWClosureFieldSMul (m : ℕ) :
    SMul GaloisBaseField (SourceGaloisWClosureField m) :=
  (sourceGaloisWClosureFieldAlgebra m).toSMul
noncomputable instance (priority := 3000) sourceGaloisWClosureFieldModule (m : ℕ) :
    Module GaloisBaseField (SourceGaloisWClosureField m) :=
  @Algebra.toModule GaloisBaseField (SourceGaloisWClosureField m) _ _
    (sourceGaloisWClosureFieldAlgebra m)
noncomputable def sourceGaloisWIntermediate_sourceGaloisWFieldGenerator : SourceGaloisWField :=
  ⟨galoisBaseW, by
    change galoisBaseW ∈ F256⟮galoisBaseW⟯
    exact IntermediateField.subset_adjoin F256 {galoisBaseW}
      (Set.mem_singleton galoisBaseW)⟩
noncomputable def sourceGaloisWClosureGenerator (m : ℕ) :
    SourceGaloisWClosureField m :=
  ⟨sourceGaloisWFieldToClosure m sourceGaloisWIntermediate_sourceGaloisWFieldGenerator,
    ⟨sourceGaloisWIntermediate_sourceGaloisWFieldGenerator, rfl⟩⟩
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


