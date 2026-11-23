-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralPolynomialFourth
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralPolynomialFourth
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:49.745443+00:00
-- url     : https://prove2.me/theorems/95b2f466-64a7-4836-abd3-8bc7b4a94675
-- title:
--   Integral Polynomial Fourth
-- statement:
--   Definitions and structural lemmas for Integral Polynomial Fourth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntegralPolynomialFourth.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialFourth.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)
noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialFourth.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : ℕ} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
    fun {σ : Type u_1} {p : ℕ} [Fact (Nat.Prime p)] (F : MvPowerSeries σ ℂ_[p]) ↦
      ∀ (n : σ →₀ ℕ), UpperTheory.Reformulated.B.IntegralPolynomialFourth.IsIntP ((MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F)


