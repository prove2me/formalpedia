-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntertwiningSymplecticAndGroupLaw
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntertwiningSymplecticAndGroupLaw
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:50.769518+00:00
-- url     : https://prove2.me/theorems/b5020ea1-c4b6-4e74-8c99-448529b1fc20
-- title:
--   Intertwining Symplectic And Group Law
-- statement:
--   Definitions and structural lemmas for Intertwining Symplectic And Group Law, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntertwiningSymplecticAndGroupLaw.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.RealWeil MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace
namespace GlobalTheory.RealWeil.Intertw
variable {l : Type} [Fintype l]
end GlobalTheory.RealWeil.Intertw
namespace GlobalTheory.RealWeil
end GlobalTheory.RealWeil


