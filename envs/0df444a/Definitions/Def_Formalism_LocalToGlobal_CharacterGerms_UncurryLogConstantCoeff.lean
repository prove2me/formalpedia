-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_UncurryLogConstantCoeff
-- name    : Formalism_LocalToGlobal_CharacterGerms_UncurryLogConstantCoeff
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T01:03:39.661271+00:00
-- url     : https://prove2.me/theorems/5bbf7245-47a9-4983-b13c-75f13803313f
-- title:
--   Uncurry Log Constant Coeff
-- statement:
--   Definitions and structural lemmas for Uncurry Log Constant Coeff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/UncurryLogConstantCoeff.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
namespace SelfConjugateGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ FormalGermZero GeneralGermZero
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
def eC (col : Fin 2) : Fin dd ↪ Fin 2 × Fin dd := ⟨fun x => (col, x), Prod.mk_right_injective col⟩
def lawS (Y : FBChart C V O dd) (x : Fin 2 × Fin dd) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C :=
  MvPowerSeries.subst (fun q : Fin 2 × Fin dd =>
    (MvPowerSeries.X (q.1, (x.1, q.2)) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) (Y.B.G.F x.2)
variable {d : ℕ} {I0 : Type} [Fintype I0]
end SelfConjugateGermZero
end Formalism.L2.FormalSeriesBounds


