-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_TraceDiagonalBis
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_TraceDiagonalBis
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:26:51.463589+00:00
-- url     : https://prove2.me/theorems/4e834873-733d-4fe9-9300-78d012aa49ba
-- title:
--   Trace Diagonal Bis
-- statement:
--   Definitions and structural lemmas for Trace Diagonal Bis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/TraceDiagonalBis.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_GramFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_UnitaryInverseIdentity
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SquareEqDiagOfQuadraticEven
import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CharacterExistsAllEmbeddings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.C
namespace Gram
open Pts Calc Formalism.HermitianLattices.IntegralLatticeDensity
end Gram
namespace Gram
section Rat
open USideA IntegralMvPolynomialLemmas Pts
variable {K : Type} [Field K] [CharZero K]
end Rat
end Gram
end Formalism.L2.Th1.C


