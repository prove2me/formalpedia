-- Prove2me | Definitions.Def_QAlgorithms_Defs_RankOneAmplitudeSequence
-- name    : QAlgorithms_Defs_RankOneAmplitudeSequence
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:32:08.721518+00:00
-- url     : https://prove2.me/theorems/b3ea5c36-f28a-4d68-8266-0e19fe9766af
-- title:
--   RankOneAmplitudeSequence
-- statement:
--   RankOneAmplitudeSequence
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\RankOneAmplitudeSequence.lean

import Definitions.Def_QAlgorithms_Defs_FixedPointSearch
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.RankOneAA

/-- Increasing-index rank-one amplification product; 2105.02859 p.5 (13).
Both phase shifts have positive sign. Domain: unit states and unitary U.
The empty product is A_phi0 U, not U. -/
def sequence {I : Type*} [Fintype I] [DecidableEq I]
    (A0 B0 : EuclideanSpace ℂ I) (_hA : IsState A0) (_hB : IsState B0)
    (U : Matrix.unitaryGroup I ℂ) (l : ℕ) (phi : Fin (2*l+1) → ℝ) : Matrix I I ℂ :=
  targetPhaseReflection A0 (phi ⟨0,by omega⟩) *
    (List.ofFn fun j : Fin l =>
      (U : Matrix I I ℂ) * targetPhaseReflection B0 (phi ⟨2*j.val+1,by omega⟩) *
        star (U : Matrix I I ℂ) * targetPhaseReflection A0 (phi ⟨2*j.val+2,by omega⟩)).prod *
    (U : Matrix I I ℂ)

example {I : Type*} [Fintype I] [DecidableEq I]
    (A0 B0 : EuclideanSpace ℂ I) (hA : IsState A0) (hB : IsState B0)
    (U : Matrix.unitaryGroup I ℂ) (phi : Fin 1 → ℝ) :
    sequence A0 B0 hA hB U 0 phi =
      targetPhaseReflection A0 (phi 0)*(U : Matrix I I ℂ) := by
  simp [sequence]

end QAlgorithms.RankOneAA


