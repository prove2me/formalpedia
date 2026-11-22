-- Prove2me | Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
-- name    : Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:03:09.253594+00:00
-- url     : https://prove2.me/theorems/0da8a1b9-ccf7-4c60-b430-35787e761ead
-- title:
--   Fock QRow Div Adj
-- statement:
--   Definitions and structural lemmas for Fock QRow Div Adj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQRowDivAdj.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockRowAdj
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
def lfockq_mat {r : ℕ} (a b : Fin r) (t : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  fun c d => (if c = d then 1 else 0) + (if c = b ∧ d = a then t else 0)
end Formalism.GradedWeylDivisibility


