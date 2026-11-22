-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:41:50.033148+00:00
-- url     : https://prove2.me/theorems/54866b6a-dc63-4ab0-ac48-7c99cfb6cfec
-- title:
--   Transfer Matrix Factorization
-- statement:
--   Definitions and structural lemmas for Transfer Matrix Factorization, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferMatrixFactorization.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.Wd5
open Matrix Formalism.FourierDecayAlt.Wd
section Free
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
end Free
end Formalism.FourierDecayAlt.P.Wd5
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.Wd
end Formalism.FourierDecayAlt.P


