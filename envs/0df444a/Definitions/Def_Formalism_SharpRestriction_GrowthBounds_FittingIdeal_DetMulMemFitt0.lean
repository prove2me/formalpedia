-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_FittingIdeal_DetMulMemFitt0
-- name    : Formalism_SharpRestriction_GrowthBounds_FittingIdeal_DetMulMemFitt0
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:12.16504+00:00
-- url     : https://prove2.me/theorems/5b817816-0fd1-4253-876b-50762b80cccd
-- title:
--   Det Mul Mem Fitt0
-- statement:
--   Definitions and structural lemmas for Det Mul Mem Fitt0, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/FittingIdeal/DetMulMemFitt0.lean

import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace Formalism.MainNotions.G.ValuationFitting
open ReciprocityTheory.PGsh.Up
section general
variable {R : Type} [CommRing R]
def Em (R : Type) [CommRing R] (m h : ℕ) : Matrix (Fin m) (Fin h) R :=
  Matrix.of fun j k => if (k : ℕ) = (j : ℕ) then 1 else 0
end general
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
end Formalism.MainNotions.G.ValuationFitting


