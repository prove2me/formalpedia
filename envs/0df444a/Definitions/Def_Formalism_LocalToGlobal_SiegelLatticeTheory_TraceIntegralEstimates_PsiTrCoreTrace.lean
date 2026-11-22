-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_PsiTrCoreTrace
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_PsiTrCoreTrace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:43:54.016544+00:00
-- url     : https://prove2.me/theorems/12bf4ed8-22ea-4f84-b5be-a58bd9bd4dcc
-- title:
--   Psi Tr Core Trace
-- statement:
--   Definitions and structural lemmas for Psi Tr Core Trace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/PsiTrCoreTrace.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
namespace Formalism.L2.S.Pv.PsiTrCore
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def embOf (φ : InfinitePlace F → (E →+* ℂ)) (p : InfinitePlace F × Bool) : E →+* ℂ :=
  if p.2 then ComplexEmbedding.conjugate (φ p.1) else φ p.1
end Formalism.L2.S.Pv.PsiTrCore


