-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CrossFactorCount
-- name    : Formalism_PadicSubsetSums_StableGradedCounts_CrossFactorCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:49.734184+00:00
-- url     : https://prove2.me/theorems/a293133c-a8c7-475d-9951-b72e56822056
-- title:
--   Cross Factor Count
-- statement:
--   Definitions and structural lemmas for Cross Factor Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CrossFactorCount.lean

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CoeffZeroNeZeroOfIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
section
variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]
end
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility


