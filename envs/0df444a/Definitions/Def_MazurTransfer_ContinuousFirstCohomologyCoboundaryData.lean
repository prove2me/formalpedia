-- Prove2me | Definitions.Def_MazurTransfer_ContinuousFirstCohomologyCoboundaryData
-- name    : MazurTransfer_ContinuousFirstCohomologyCoboundaryData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T02:06:46.132527+00:00
-- url     : https://prove2.me/theorems/111069ec-b252-46d4-b374-52e42a1341d9
-- title:
--   Original continuous coboundaries and their zero H1 classes
-- statement:
--   For a topological commutative coefficient group with its original continuous group action, retain the explicit continuous coboundary of m, with value g*m/m, and its original evaluation and zero-class laws in the existing continuous H1 presentation. All three original types and the single nonproof constructor value are compared. Named downstream consumer: adjusting a cocycle to lift it through the kernel map in continuous H1 exactness.
-- source:
--   Original MazurTheorem ContinuousFirstCohomologyCoboundary, Apache-2.0. All original declaration bodies are retained; only imports are replaced by checked public dependencies.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: explicit continuous coboundaries represent zero in the
existing continuous-cocycle H1 presentation. Named downstream consumer:
continuous H1 exactness for the actual norm-character sequences.
-/
import Definitions.Def_MazurTransfer_ContinuousFirstCohomologyPresentationData
import Theorems.Thm_MazurTransfer_ContinuousFirstCohomologyPresentation_coboundaries_continuous

noncomputable section
namespace MazurTransfer.ContinuousFirstCohomologyCoboundary
open ContinuousFirstCohomologyPresentation
variable (G M : Type) [Group G] [CommGroup M] [MulDistribMulAction G M]
  [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M] [ContinuousSMul G M]

def coboundary (m : M) : continuousCocycles G M :=
  ⟨groupCohomology.coboundariesToCocycles₁ (rep G M)
      (groupCohomology.coboundariesOfIsMulCoboundary₁ (f := fun g : G => g • m / m)
        ⟨m, fun _ => rfl⟩),
    coboundaries_continuous G M _
      (groupCohomology.coboundariesOfIsMulCoboundary₁ (f := fun g : G => g • m / m)
        ⟨m, fun _ => rfl⟩).property⟩

theorem coboundary_apply (m : M) (g : G) :
    (Additive.toMul ((coboundary G M m).val g) : M) = g • m / m := rfl

theorem class_coboundary (m : M) : classMap G M (coboundary G M m) = 0 := by
  apply (classMap_eq_zero_iff G M _).mpr
  exact (groupCohomology.coboundariesOfIsMulCoboundary₁ (f := fun g : G => g • m / m)
    ⟨m, fun _ => rfl⟩).property

end MazurTransfer.ContinuousFirstCohomologyCoboundary
#print axioms MazurTransfer.ContinuousFirstCohomologyCoboundary.class_coboundary


