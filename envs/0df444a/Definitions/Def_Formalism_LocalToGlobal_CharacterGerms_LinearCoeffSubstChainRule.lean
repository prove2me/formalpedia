-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LinearCoeffSubstChainRule
-- name    : Formalism_LocalToGlobal_CharacterGerms_LinearCoeffSubstChainRule
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T10:38:47.309266+00:00
-- url     : https://prove2.me/theorems/1892f5c2-513c-54a2-acd4-99d1813cace8
-- title:
--   Linear Coeff Subst Chain Rule
-- statement:
--   Definitions and structural lemmas for Linear Coeff Subst Chain Rule, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LinearCoeffSubstChainRule.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCr
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
namespace VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}
def lin1 {σ : Type} (f : MvPowerSeries σ C) (j : σ) : C := MvPowerSeries.constantCoeff (MvPowerSeries.pderiv C j f)
end VP
end Formalism.L2.FormalSeriesBounds


