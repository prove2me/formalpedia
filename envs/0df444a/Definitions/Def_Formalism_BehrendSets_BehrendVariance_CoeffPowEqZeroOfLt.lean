-- Prove2me | Definitions.Def_Formalism_BehrendSets_BehrendVariance_CoeffPowEqZeroOfLt
-- name    : Formalism_BehrendSets_BehrendVariance_CoeffPowEqZeroOfLt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:35:23.498996+00:00
-- url     : https://prove2.me/theorems/4426dbd1-24b3-413d-be3a-5a379d8c1734
-- title:
--   Coeff Pow Eq Zero Of Lt
-- statement:
--   Definitions and structural lemmas for Coeff Pow Eq Zero Of Lt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/CoeffPowEqZeroOfLt.lean

import Definitions.Def_Formalism_BehrendSets_StatementE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Finset
noncomputable section
namespace Formalism.BehrendSets.Level3
section General
variable {R : Type*} [CommRing R]
end General
end Formalism.BehrendSets.Level3
namespace Formalism.BehrendSets.Level3
end Formalism.BehrendSets.Level3
namespace Formalism.BehrendSets.Level3
def tOne (Q : ℕ) (c : ℚ) (D : ℚ⟦X⟧) : ℚ⟦X⟧ := X * subst ((X : ℚ⟦X⟧) ^ (Q - 1)) (rescale c D)
end Formalism.BehrendSets.Level3
namespace Formalism.BehrendSets
end Formalism.BehrendSets


