-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRealAdd
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRealAdd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:46.204883+00:00
-- url     : https://prove2.me/theorems/e0001a18-f5d5-4bbe-95c8-e2b060322bd7
-- title:
--   Exists Real Add
-- statement:
--   Definitions and structural lemmas for Exists Real Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsRealAdd.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 TensorProduct
namespace GlobalTheory.SplitComp
variable (L : Type) [Field L] [NumberField L] [IsCMField L]
end GlobalTheory.SplitComp


