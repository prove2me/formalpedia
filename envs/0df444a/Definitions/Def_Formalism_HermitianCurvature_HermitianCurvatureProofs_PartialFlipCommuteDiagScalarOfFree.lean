-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:43:40.646956+00:00
-- url     : https://prove2.me/theorems/893f9b18-1780-4a29-8f45-5f523aaf5b3a
-- title:
--   Partial Flip Commute Diag Scalar Of Free
-- statement:
--   Definitions and structural lemmas for Partial Flip Commute Diag Scalar Of Free, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PartialFlipCommuteDiagScalarOfFree.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.Wd10
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
section Kap
variable {K S : Type} [Field K]
def gq (l : Letter K S) (y : K) : K :=
  if l.plus then (y - l.pt + 1) / (y - l.pt) else (l.pt - y) / (l.pt - y - 1)
def hp (l : Letter K S) (Y : K) : K :=
  if l.plus then (Y - l.pt) / (Y - l.pt - 1) else (Y - l.pt) / (Y - l.pt + 1)
def fac (l l' : Letter K S) : K :=
  if l.plus = l'.plus then 1 else 1 - ((l.pt - l'.pt + (if l.plus then 1 else -1)) ^ 2)⁻¹
end Kap
section Dual
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
end Dual
section Main
end Main
end Formalism.FourierDecayAlt.P.Wd10


