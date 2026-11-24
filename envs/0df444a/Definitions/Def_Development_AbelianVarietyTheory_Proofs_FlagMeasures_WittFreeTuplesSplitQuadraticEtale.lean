-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesSplitQuadraticEtale
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesSplitQuadraticEtale
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:03.024996+00:00
-- url     : https://prove2.me/theorems/ecb3bca0-564a-4d87-8b5e-1a41d70c9364
-- title:
--   Witt Free Tuples Split Quadratic Etale
-- statement:
--   Definitions and structural lemmas for Witt Free Tuples Split Quadratic Etale, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittFreeTuplesSplitQuadraticEtale.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SgAlg Matrix Module
noncomputable section
namespace GlobalTheory.SgAlg.WittSplit
section Lin
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
end Lin
section Mat
variable {F : Type} [Field F] {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
end Mat
section Ring
variable {E : Type} [CommRing E] (σ : E →+* E)
end Ring
end GlobalTheory.SgAlg.WittSplit


