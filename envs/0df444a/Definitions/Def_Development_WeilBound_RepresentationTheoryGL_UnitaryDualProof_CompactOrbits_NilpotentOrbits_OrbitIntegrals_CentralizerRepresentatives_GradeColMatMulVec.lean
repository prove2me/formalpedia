-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_GradeColMatMulVec
-- name    : Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_GradeColMatMulVec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:45.303724+00:00
-- url     : https://prove2.me/theorems/980602f6-a136-44ed-af0c-82eed2f37931
-- title:
--   Grade Col Mat Mul Vec
-- statement:
--   Definitions and structural lemmas for Grade Col Mat Mul Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/GradeColMatMulVec.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_IsChain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Submodule
namespace PositivityTheory.RgUd.T.Nil.Orb.BReps
variable {k : Type} [Field k] {n : ℕ}
def gradeColMat (b : Module.Basis (Fin n) k (Fin n → k)) : Matrix (Fin n) (Fin n) k :=
  (Pi.basisFun k (Fin n)).toMatrix b
def gradeRowMat (b : Module.Basis (Fin n) k (Fin n → k)) : Matrix (Fin n) (Fin n) k :=
  b.toMatrix (Pi.basisFun k (Fin n))
def gradeBasisGL (b : Module.Basis (Fin n) k (Fin n → k)) : GL (Fin n) k :=
  ⟨gradeColMat b, gradeRowMat b, Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩
end PositivityTheory.RgUd.T.Nil.Orb.BReps


