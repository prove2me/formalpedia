-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WtGeProd
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WtGeProd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:47.03704+00:00
-- url     : https://prove2.me/theorems/52742a5d-f39e-4270-bbfb-8d18541554d9
-- title:
--   Wt Ge Prod
-- statement:
--   Definitions and structural lemmas for Wt Ge Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/WtGeProd.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Qk29.dot.{v} :
    {ι : Type v} → (ι →₀ ℕ) → (ι → ℝ) → ℝ :=
    fun {ι : Type v} (n : ι →₀ ℕ) (r : ι → ℝ) ↦ n.sum fun (i : ι) (k : ℕ) ↦ (↑k : ℝ) * r i
noncomputable def UpperTheory.Reformulated.B.Qk29.MonoWtGe.{u, v} :
    {K : Type u} → [NormedField K] → {ι : Type v} → ℝ → (ι → ℝ) → ℝ → (ι →₀ ℕ) → K → Prop :=
    fun {K : Type u} [NormedField K] {ι : Type v} (pi : ℝ) (r : ι → ℝ) (w : ℝ) (n : ι →₀ ℕ) (c : K) ↦
      ‖c‖ ≤ pi ^ (w - UpperTheory.Reformulated.B.Qk29.dot n r)
noncomputable def UpperTheory.Reformulated.B.Qk29.WtGe.{u, v} :
    {K : Type u} → [NormedField K] → {ι : Type v} → ℝ → (ι → ℝ) → ℝ → MvPowerSeries ι K → Prop :=
    fun {K : Type u} [NormedField K] {ι : Type v} (pi : ℝ) (r : ι → ℝ) (w : ℝ) (f : MvPowerSeries ι K) ↦
      ∀ (n : ι →₀ ℕ), UpperTheory.Reformulated.B.Qk29.MonoWtGe pi r w n ((MvPowerSeries.coeff n : MvPowerSeries ι K → K) f)


