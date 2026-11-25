-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_ProdNormLe
-- name    : CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_ProdNormLe
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T07:26:40.026948+00:00
-- url     : https://prove2.me/theorems/52ff7a05-5fc4-5e1b-8968-12c6f4109b31
-- title:
--   Prod Norm Le
-- statement:
--   Definitions and structural lemmas for Prod Norm Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselOrbitBounds/BesselMapUniqueness/ProdNormLe.lean

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_ContinuousOnOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
open scoped ContDiff InnerProductSpace ComplexConjugate
noncomputable section
namespace CompanionTheory.Bmu
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end CompanionTheory.Bmu


