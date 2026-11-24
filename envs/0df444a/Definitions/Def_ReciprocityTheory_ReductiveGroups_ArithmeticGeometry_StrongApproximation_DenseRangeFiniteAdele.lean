-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_DenseRangeFiniteAdele
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_DenseRangeFiniteAdele
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:51:41.290841+00:00
-- url     : https://prove2.me/theorems/677ca729-7304-4262-8ef7-9a467d4a5bdf
-- title:
--   Dense Range Finite Adele
-- statement:
--   Definitions and structural lemmas for Dense Range Finite Adele, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/DenseRangeFiniteAdele.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_AdeleApproximation_AdeleIntA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.SA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology WithZero Filter
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
end ReciprocityTheory.ChartRestriction.G.SA


