-- Prove2me | Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__PoincareLelong_e61d89ea90cf58ae
-- name    : P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__PoincareLelong_e61d89ea90cf58ae
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:48.020216+00:00
-- url     : https://prove2.me/theorems/17d9ea15-719f-43b6-b744-137601504929
-- title:
--   Poincare Lelong
-- statement:
--   Definitions and structural lemmas for Poincare Lelong, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/Metrics₂/PoincareLelong.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.CompanionTheory.Ar.Pub
def PoincareLelong : Prop :=
  ReciprocityTheory.ChartRestriction.G.Geo.ArithmeticPoincareLelongFormula
end GlobalTheory.CompanionTheory.Ar.Pub


