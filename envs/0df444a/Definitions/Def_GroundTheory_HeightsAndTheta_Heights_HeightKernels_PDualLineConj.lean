-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualLineConj
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualLineConj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:49.684158+00:00
-- url     : https://prove2.me/theorems/2f73ed27-d8cf-4256-8db6-63b1a9d2dd5c
-- title:
--   PDual Line Conj
-- statement:
--   Definitions and structural lemmas for PDual Line Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualLineConj.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo Matrix NumberField NumberField.ComplexEmbedding
noncomputable section
namespace DualLineConjugation
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T] [DecidableEq T]
def conjPerm (K : Type) [Field K] : Equiv.Perm (K →+* ℂ) :=
  Function.Involutive.toPerm _ (involutive_conjugate K)
end DualLineConjugation
end
end GroundTheory.Heights₂.Heights


