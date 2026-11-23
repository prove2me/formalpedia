-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RiemannClEqSum
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_RiemannClEqSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:01.063783+00:00
-- url     : https://prove2.me/theorems/53c13f44-7c85-42c1-a396-646a34787bf4
-- title:
--   Riemann Cl Eq Sum
-- statement:
--   Definitions and structural lemmas for Riemann Cl Eq Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RiemannClEqSum.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
namespace GlobalTheory.DualFormValues
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
end GlobalTheory.DualFormValues


