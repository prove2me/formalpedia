-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FrobSerSt
-- name    : Formalism_LocalToGlobal_CharacterGerms_FrobSerSt
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:23:32.773734+00:00
-- url     : https://prove2.me/theorems/68aa727b-92b0-4516-bcaa-7b50ef5244b8
-- title:
--   Frob Ser St
-- statement:
--   Definitions and structural lemmas for Frob Ser St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/FrobSerSt.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.FormalSeriesBounds
def FrobSerSt : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (σ : Type) (f : MvPowerSeries σ C),
    (∀ i (μ : σ →₀ ℕ), V.MM (MvPowerSeries.coeff μ (MvPowerSeries.pderiv C i f))) →
    ∀ μ : σ →₀ ℕ, (∃ i, ¬ V.l ∣ μ i) → V.MM (MvPowerSeries.coeff μ f)
def FrobPowSt : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (f : PowerSeries C), (∀ n, V.Ge 0 (PowerSeries.coeff n f)) →
    (∀ n, V.MM (PowerSeries.coeff (V.l * n) (f ^ V.l) - PowerSeries.coeff n f ^ V.l)) ∧
    ∀ m, ¬ V.l ∣ m → V.MM (PowerSeries.coeff m (f ^ V.l))
end Formalism.L2.FormalSeriesBounds


