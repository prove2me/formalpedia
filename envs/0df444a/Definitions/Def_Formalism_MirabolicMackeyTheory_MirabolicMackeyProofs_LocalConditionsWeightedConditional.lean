-- Prove2me | Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsWeightedConditional
-- name    : Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsWeightedConditional
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:35:49.562111+00:00
-- url     : https://prove2.me/theorems/b1e02ba1-84c6-463f-a630-6cff1782638c
-- title:
--   Local Conditions Weighted Conditional
-- statement:
--   Definitions and structural lemmas for Local Conditions Weighted Conditional, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/LocalConditionsWeightedConditional.lean

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementLoc
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
namespace Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues Formalism.HermitianLatticesTheory
section Gen
def lenQ {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (X Y : Submodule R W) : ℕ :=
  (Module.length R (↥X ⧸ Y.comap X.subtype)).toNat
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Gen
section Instance
variable (K : Type) [Field K] [NumberField K] [StarRing K]
end Instance
end Formalism.EigenvalueLevelCeiling


