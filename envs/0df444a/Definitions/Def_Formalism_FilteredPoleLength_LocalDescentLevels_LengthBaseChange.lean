-- Prove2me | Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LengthBaseChange
-- name    : Formalism_FilteredPoleLength_LocalDescentLevels_LengthBaseChange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:50:38.104895+00:00
-- url     : https://prove2.me/theorems/40834675-e0d2-49eb-821d-f1c3adb746a7
-- title:
--   Length Base Change
-- statement:
--   Definitions and structural lemmas for Length Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LengthBaseChange.lean

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_LengthBaseChangeLocal
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.LatticeBaseChangeAlt
open Module TensorProduct
namespace LengthBaseChangeAlt
end LengthBaseChangeAlt
namespace LengthBaseChangeAlt
open BQuot
section Ext
variable {O K K₁ V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [Field K₁] [Algebra K K₁] [FiniteDimensional K K₁]
  [Algebra.IsSeparable K K₁] [Algebra O K₁] [IsScalarTower O K K₁]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
end Ext
end LengthBaseChangeAlt
end Formalism.LatticeBaseChangeAlt


