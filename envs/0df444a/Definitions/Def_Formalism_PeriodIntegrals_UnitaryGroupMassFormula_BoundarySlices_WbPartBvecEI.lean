-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BoundarySlices_WbPartBvecEI
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BoundarySlices_WbPartBvecEI
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:53:51.092859+00:00
-- url     : https://prove2.me/theorems/b3a6fba1-cd4f-4364-a316-1cd4dc7076cd
-- title:
--   Wb Part Bvec EI
-- statement:
--   Definitions and structural lemmas for Wb Part Bvec EI, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BoundarySlices/WbPartBvecEI.lean

import Definitions.Def_Formalism_PeriodIntegrals_BordSlice
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace PI.HermitianEmbeddingSlice
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic
variable {k r : ℕ}
def emb (k r : ℕ) (y : Fin (k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := fun i =>
  if h : r ≤ i.val ∧ i.val ≤ r + k then y ⟨i.val - r, by omega⟩ else 0
def dd (k : ℕ) (j : Fin (k + 1)) : ℂ := if j = Fin.last k then -1 else 1
end PI.HermitianEmbeddingSlice


