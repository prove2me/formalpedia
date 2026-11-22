-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteClassesPositiveSums
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteClassesPositiveSums
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:29:39.65604+00:00
-- url     : https://prove2.me/theorems/a141a601-1f08-4ad0-91d2-d09486ecc2cf
-- title:
--   Finite Classes Positive Sums
-- statement:
--   Definitions and structural lemmas for Finite Classes Positive Sums, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteClassesPositiveSums.lean

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
section gen
variable {α : Type}
end gen
section classes
variable {K : Type} [CommRing K] (R : Subring K)
variable {R} {F : Finset (Point K)} {Lc : Set K} {S : Finset (K ⧸ R.toAddSubgroup)}
end classes
end Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
end Formalism.FourierDecayAlt.P


