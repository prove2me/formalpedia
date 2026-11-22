-- Prove2me | Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
-- name    : Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:53:42.058472+00:00
-- url     : https://prove2.me/theorems/594e39af-666f-4f77-a694-52d6c03c1fe9
-- title:
--   LFocks Lemmas
-- statement:
--   Definitions and structural lemmas for LFocks Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFocksLemmas.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.REAL
noncomputable section
namespace Formalism.GradedWeylDivisibility
section general
variable {σ : Type*}
end general
variable {σ : Type*} [Fintype σ]
variable [DecidableEq σ]
end Formalism.GradedWeylDivisibility


