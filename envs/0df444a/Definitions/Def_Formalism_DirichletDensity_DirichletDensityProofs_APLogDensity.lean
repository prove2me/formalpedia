-- Prove2me | Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_APLogDensity
-- name    : Formalism_DirichletDensity_DirichletDensityProofs_APLogDensity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:40:47.700802+00:00
-- url     : https://prove2.me/theorems/510c4b6c-c4b1-4db1-a282-d67ce5d1e9b2
-- title:
--   APLog Density
-- statement:
--   Definitions and structural lemmas for APLog Density, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/APLogDensity.lean

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology ArithmeticFunction ArithmeticFunction.vonMangoldt Complex LSeries
noncomputable section
namespace Formalism.HF.P
variable {q : ℕ} [NeZero q] {a : ZMod q}
end Formalism.HF.P


