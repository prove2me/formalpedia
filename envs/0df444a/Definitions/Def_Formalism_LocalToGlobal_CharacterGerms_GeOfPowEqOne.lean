-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
-- name    : Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:46.013565+00:00
-- url     : https://prove2.me/theorems/d31d1131-4031-4240-8d79-c6c88ad94b25
-- title:
--   Ge Of Pow Eq One
-- statement:
--   Definitions and structural lemmas for Ge Of Pow Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeOfPowEqOne.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
def InL (l : ℕ) (f : PowerSeries C) : Prop := ∀ m, ¬ l ∣ m → PowerSeries.coeff m f = 0
def dnL (l : ℕ) (f : PowerSeries C) : PowerSeries C := PowerSeries.mk fun n => PowerSeries.coeff (l * n) f
namespace RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
end RawChart
end Formalism.L2.FormalSeriesBounds


