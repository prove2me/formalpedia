-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralPolynomialSixth
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralPolynomialSixth
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:11:05.043588+00:00
-- url     : https://prove2.me/theorems/2304b557-0485-40eb-8b4f-013371205257
-- title:
--   Integral Polynomial Sixth
-- statement:
--   Definitions and structural lemmas for Integral Polynomial Sixth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntegralPolynomialSixth.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.IntegralMvPowerSeriesOverPadicComplex.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)
noncomputable def UpperTheory.Reformulated.B.IntegralMvPowerSeriesOverPadicComplex.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : ℕ} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
    fun {σ : Type u_1} {p : ℕ} [Fact (Nat.Prime p)] (F : MvPowerSeries σ ℂ_[p]) ↦
      ∀ (n : σ →₀ ℕ), UpperTheory.Reformulated.B.IntegralMvPowerSeriesOverPadicComplex.IsIntP ((MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F)


