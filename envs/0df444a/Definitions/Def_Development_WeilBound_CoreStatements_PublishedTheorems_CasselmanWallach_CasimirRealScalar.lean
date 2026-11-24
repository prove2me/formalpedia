-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CasimirRealScalar
-- name    : Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CasimirRealScalar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:53.87621+00:00
-- url     : https://prove2.me/theorems/b7f31514-20cf-4c0a-b0bd-8d55df4e2dd2
-- title:
--   Casimir Real Scalar
-- statement:
--   Definitions and structural lemmas for Casimir Real Scalar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/CasimirRealScalar.lean

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
namespace PositivityTheory.CW
namespace CasimirEigenvector
variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}
end CasimirEigenvector
end PositivityTheory.CW
end


