-- Prove2me | Definitions.Def_QAlgorithms_Defs_MitigationMeasurements
-- name    : QAlgorithms_Defs_MitigationMeasurements
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:17:29.04898+00:00
-- url     : https://prove2.me/theorems/588f9c21-177c-4287-9095-a406b6151964
-- title:
--   MitigationMeasurements
-- statement:
--   MitigationMeasurements
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\MitigationMeasurements.lean

import Definitions.Def_QAlgorithms_Defs_MitigationOperationBasis
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.ErrorMitigation

/-- arxiv-1712.09271v2 PDF p.3; arxiv-1712.09271v2 PDF p.14. -/
structure ObservableMeasurement (I : Type*) [Fintype I] [DecidableEq I] where
  outcomes : ℕ
  effect : Fin outcomes → Matrix I I ℂ
  valid : IsPOVM effect
  value : Fin outcomes → ℝ

/-- The observable actually measured by the valued POVM (1712.09271 pp.3,14).
arxiv-1712.09271v2 PDF p.3; arxiv-1712.09271v2 PDF p.14. -/
def ObservableMeasurement.observable {I : Type*} [Fintype I] [DecidableEq I]
    (M : ObservableMeasurement I) : Matrix I I ℂ := ∑ o, (M.value o : ℂ) • M.effect o

/-- The source's trivial +1 readout of the identity observable (1712.09271 p.14). -/
def identityMeasurement (I : Type*) [Fintype I] [DecidableEq I] : ObservableMeasurement I :=
  ⟨1,fun _ => 1,⟨fun _ => Matrix.PosSemidef.one,by simp⟩,fun _ => 1⟩

/-- Sanity check for the source model (arxiv-1712.09271v2 PDF p.3). -/
example {I : Type*} [Fintype I] [DecidableEq I] :
    (identityMeasurement I).observable = 1 := by
  change (∑ o : Fin 1, (1 : ℂ) • (1 : Matrix I I ℂ)) = 1
  simp [Fin.sum_univ_one]

end QAlgorithms.ErrorMitigation


