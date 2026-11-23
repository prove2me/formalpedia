-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgHomEqOrConj
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgHomEqOrConj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:28.174383+00:00
-- url     : https://prove2.me/theorems/630196d9-82b4-4ad3-9c80-d80e351d9382
-- title:
--   Alg Hom Eq Or Conj
-- statement:
--   Definitions and structural lemmas for Alg Hom Eq Or Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AlgHomEqOrConj.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
noncomputable section
namespace GlobalTheory.SplitPlaceExt
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => NumberField.maximalRealSubfield L
local notation3 "cc" => IsCMField.complexConj L
end GlobalTheory.SplitPlaceExt


