-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
-- name    : Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:40:17.633823+00:00
-- url     : https://prove2.me/theorems/a160e5ae-d771-4d19-a0cd-de5e5401a471
-- title:
--   Conjugate Weight Lattice Of General
-- statement:
--   Definitions and structural lemmas for Conjugate Weight Lattice Of General, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjugateWeightLatticeOfGeneral.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.DivisionValues
open RationalHermitianForm
namespace ConjugateWeightGram
open StepBAux
section LocalW
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end LocalW
end ConjugateWeightGram
namespace ConjugateWeightGram
section Field
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Field
end ConjugateWeightGram
namespace ConjugateWeightGram
end ConjugateWeightGram
namespace ConjugateWeightGram
open StepBAux
section Restrict
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def colMat {n d : ℕ} (z : Fin d → Fin n → K) : Matrix (Fin n) (Fin d) K := Matrix.of fun i a => z a i
end Restrict
end ConjugateWeightGram
end Formalism.DivisionValues


