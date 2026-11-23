-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_HermitianFormGramBlockBasis
-- name    : Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_HermitianFormGramBlockBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:21.410684+00:00
-- url     : https://prove2.me/theorems/6910f8aa-552a-4cb2-ace8-42186d7ff30e
-- title:
--   Hermitian Form Gram Block Basis
-- statement:
--   Definitions and structural lemmas for Hermitian Form Gram Block Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/HermitianFormGramBlockBasis.lean

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementS
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_FiniteDetAddSmulOneEqZero
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_LargeResidueExtensionLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.LamCM
open NumberField IsDedekindDomain IsLocalRing Matrix
open scoped nonZeroDivisors ComplexOrder
section Gram
variable {K : Type} [Field K] [NumberField K] {B : Type} {m : B → ℕ} {g : ℕ}
end Gram
end Formalism.L2.LamCM


