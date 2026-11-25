-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BoundedSums
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BoundedSums
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:14:13.812777+00:00
-- url     : https://prove2.me/theorems/c96b1c93-a515-4f83-9eeb-516aa6d4c500
-- title:
--   Bounded Sums
-- statement:
--   Definitions and structural lemmas for Bounded Sums, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/BoundedSums.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.BoundedSums.Bdd :
    {C : Type} → [inst : Field C] → Formalism.L2.FormalSeriesBounds.VF C → (ℕ → C) → Prop :=
    fun {C : Type} [Field C] (V : Formalism.L2.FormalSeriesBounds.VF C) (s : ℕ → C) ↦ ∃ (K : ℝ), ∀ (n : ℕ), V.Ge K (s n)
noncomputable def UpperTheory.Reformulated.B.BoundedSums.BddS :
    {C : Type} → [inst : Field C] → {σ : Type} → Formalism.L2.FormalSeriesBounds.VF C → (ℕ → MvPowerSeries σ C) → Prop :=
    fun {C : Type} [Field C] {σ : Type} (V : Formalism.L2.FormalSeriesBounds.VF C) (f : ℕ → MvPowerSeries σ C) ↦
      ∀ (μ : σ →₀ ℕ), UpperTheory.Reformulated.B.BoundedSums.Bdd V fun (n : ℕ) ↦ (MvPowerSeries.coeff μ : MvPowerSeries σ C → C) (f n)


