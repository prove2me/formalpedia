-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_ExistsUnitDiff
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_ExistsUnitDiff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:18:46.912191+00:00
-- url     : https://prove2.me/theorems/d18918a9-c112-44b9-92f1-e361310ff7e6
-- title:
--   Exists Unit Diff
-- statement:
--   Definitions and structural lemmas for Exists Unit Diff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitPrimeIntegers/ExistsUnitDiff.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_EmbMemOfIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct
noncomputable section
namespace PI.SplitIntLoc.Proof
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} (spl : E ⊗[F] (v.adicCompletion F) ≃+* (v.adicCompletion F) × (v.adicCompletion F))
def Dloc (Q : Ideal (𝓞 E)) [Q.IsPrime] : Subalgebra (𝓞 E) E :=
  Localization.subalgebra E Q.primeCompl Q.primeCompl_le_nonZeroDivisors
instance (Q : Ideal (𝓞 E)) [Q.IsPrime] : IsLocalization.AtPrime (Dloc Q) Q :=
  inferInstanceAs (IsLocalization Q.primeCompl
    (Localization.subalgebra E Q.primeCompl Q.primeCompl_le_nonZeroDivisors))
instance (Q : Ideal (𝓞 E)) [Q.IsPrime] : IsFractionRing (Dloc Q) E :=
  inferInstanceAs (IsFractionRing
    (Localization.subalgebra E Q.primeCompl Q.primeCompl_le_nonZeroDivisors) E)
end PI.SplitIntLoc.Proof


