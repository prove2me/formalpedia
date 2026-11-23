-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MemTorsionOfMulConj
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MemTorsionOfMulConj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:18:41.540069+00:00
-- url     : https://prove2.me/theorems/3a59d5fb-5cec-4db8-b470-a87e80ba1b54
-- title:
--   Mem Torsion Of Mul Conj
-- statement:
--   Definitions and structural lemmas for Mem Torsion Of Mul Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/MemTorsionOfMulConj.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TwoLeAbsNormPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
namespace Formalism.L2.SG.NGCut.TorsionTotientBound
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
abbrev cO (E : Type) [Field E] [NumberField E] [IsCMField E] : 𝓞 E ≃+* 𝓞 E :=
  RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv
end Formalism.L2.SG.NGCut.TorsionTotientBound


