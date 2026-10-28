-- Prove2me | Definitions.Def_D1Bound5_WeightedRowCertificate_Definitions
-- name    : D1Bound5_WeightedRowCertificate_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:32:34.976393+00:00
-- url     : https://prove2.me/theorems/66ae3b55-df8f-4b16-9917-529b08f8a3dc
-- title:
--   Weighted Row Certificate
-- statement:
--   Positive weights for the mixed first-row perturbation estimate. The named objects in this bundle include `weightedFourWeights`, `mixedFourEnvelope`.
-- source:
--   D1Bound5/WeightedRowCertificate.lean, lines 7-9, SHA-256 24e91527c5f644ec2b6289935e81e061377a21fe404f3e2ef431b87e3d5e91b5; D1Bound5/WeightedRowCertificate.lean, lines 11-13, SHA-256 24e91527c5f644ec2b6289935e81e061377a21fe404f3e2ef431b87e3d5e91b5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
namespace D1Bound5

/-- Positive weights for the mixed first-row perturbation estimate. -/
noncomputable def weightedFourWeights (i : Fin 4) : ℝ :=
  if i = 0 then 3 / 2 else 1

/-- Symmetric real entrywise envelope for the mixed root error. -/
noncomputable def mixedFourEnvelope (i j : Fin 4) : ℝ :=
  if i = j then 0 else if i = 0 ∨ j = 0 then 1 / 18 else 1 / 64











end D1Bound5

namespace D1Bound5





end D1Bound5
end


