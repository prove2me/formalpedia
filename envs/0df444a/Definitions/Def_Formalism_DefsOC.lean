-- Prove2me | Definitions.Def_Formalism_DefsOC
-- name    : Formalism_DefsOC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:51:39.550187+00:00
-- url     : https://prove2.me/theorems/1ca0cceb-9b89-491e-9ea6-ed1f78ba51da
-- title:
--   Defs OC
-- statement:
--   Definitions and structural lemmas for Defs OC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DefsOC.lean

import Definitions.Def_Formalism_StatementOC
import Definitions.Def_Formalism_ZetaRealNonvanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace Formalism
def Sa (a : ℕ → ℝ) (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * (x / n - 1)
def MellinSgen : Prop :=
  ∀ (a : ℕ → ℝ) (K : ℝ), (∀ n : ℕ, |a n| ≤ K * ArithmeticFunction.vonMangoldt n) →
    Measurable (Sa a) ∧
    (∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => |Sa a x| * x ^ (-σ - 1)) (Ioi 1)) ∧
    ∀ s : ℂ, 1 < s.re →
      ∫ x in Ioi (1:ℝ), (Sa a x : ℂ) * (x : ℂ) ^ (-s - 1) =
        LSeries (fun n => (a n : ℂ)) s / (s * (s - 1))
def LSeriesTwistRe : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), (∀ n : ℕ, (χ n).im = 0) →
    ∀ s : ℂ, 1 < s.re →
      LSeries (fun n => ((ArithmeticFunction.vonMangoldt n * (χ n).re : ℝ) : ℂ)) s =
        -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s
def LandauEq : Prop :=
  ∀ (H : ℝ → ℝ) (a b : ℝ), a < b → AEStronglyMeasurable H (volume.restrict (Ioi 1)) →
    (∀ x : ℝ, 1 < x → 0 ≤ H x) →
    (∀ σ : ℝ, b < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1)) →
    ∀ Φ : ℂ → ℂ, (∀ s : ℂ, b < s.re → AnalyticAt ℂ Φ s) →
    (∀ σ : ℝ, a < σ → σ ≤ b → AnalyticAt ℂ Φ σ) →
    (∀ s : ℂ, b < s.re → Φ s = ∫ x in Ioi (1:ℝ), (H x : ℂ) * (x : ℂ) ^ (-s - 1)) →
    ∀ σ : ℝ, a < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1) ∧
      Φ σ = ∫ x in Ioi (1:ℝ), (H x : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 1)
def LogDerivResidue : Prop :=
  ∀ (f : ℂ → ℂ) (ρ : ℂ), Differentiable ℂ f → (∃ z, f z ≠ 0) →
    Tendsto (fun s => (s - ρ) * (deriv f s / f s)) (𝓝[≠] ρ) (𝓝 (analyticOrderNatAt f ρ : ℂ))
def OrderLogDeriv : Prop :=
  ∀ (ι : Type) [Fintype ι] (P0 : ℂ → ℂ) (P : ι → ℂ → ℂ) (W : ℝ) (w : ι → ℝ) (q : ℂ → ℂ)
    (U : Set ℂ), IsOpen U → Differentiable ℂ P0 → (∀ i, Differentiable ℂ (P i)) →
    (∃ z, P0 z ≠ 0) → (∀ i, ∃ z, P i z ≠ 0) → DifferentiableOn ℂ q U →
    (∀ s ∈ U, P0 s ≠ 0 → (∀ i, P i s ≠ 0) →
        (W : ℂ) * (deriv P0 s / P0 s) - ∑ i, (w i : ℂ) * (deriv (P i) s / P i s) = q s) →
    ∀ s ∈ U, W * (analyticOrderNatAt P0 s : ℝ) = ∑ i, w i * (analyticOrderNatAt (P i) s : ℝ)
end Formalism


