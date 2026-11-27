-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffPderivUncurry
-- name    : Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffPderivUncurry
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-27T05:00:28.573705+00:00
-- url     : https://prove2.me/theorems/151edcb5-3b82-5a2f-b7b7-368a25cb6eb4
-- title:
--   Constant Coeff Pderiv Uncurry
-- statement:
--   Definitions and structural lemmas for Constant Coeff Pderiv Uncurry, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstantCoeffPderivUncurry.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieChar
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MfactMulCoeffMvExpLinF
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace ChG
section Uniq
variable {K : Type} [Field K] [CharZero K] {τ : Type} [Fintype τ]
end Uniq
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd)
open VP
def Psi (χ : PS C 1 dd) : MvPowerSeries (Fin dd) C := MvPowerSeries.subst (e Y) (un1 χ)
end ChG
end Formalism.L2.FormalSeriesBounds


