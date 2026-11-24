-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TransSIntertwines
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TransSIntertwines
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:28.375052+00:00
-- url     : https://prove2.me/theorems/6bc51275-b84a-4f61-a7e0-ca1a65b05ac3
-- title:
--   Trans SIntertwines
-- statement:
--   Definitions and structural lemmas for Trans SIntertwines, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TransSIntertwines.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeisenbergOperatorRationalPointLaws
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase GlobalTheory.SiegelAction
open scoped ComplexConjugate Real
namespace GlobalTheory.Phase.Inter
variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
def rowAct (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) (y : Matrix κ ι ℚ × Matrix κ ι ℚ) :
    Matrix κ ι ℚ × Matrix κ ι ℚ :=
  (y.2 * σ.toBlocks₁₂ + y.1 * σ.toBlocks₂₂, y.2 * σ.toBlocks₁₁ + y.1 * σ.toBlocks₂₁)
end GlobalTheory.Phase.Inter
namespace GlobalTheory.Phase
open Inter
end GlobalTheory.Phase


