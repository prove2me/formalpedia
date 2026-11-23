-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinSt
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:09.456035+00:00
-- url     : https://prove2.me/theorems/e7340874-8973-433f-9948-7e8e94185196
-- title:
--   Phi CMin St
-- statement:
--   Definitions and structural lemmas for Phi CMin St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PhiCMinSt.lean

import Mathlib
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
open Matrix
def WhitenStatement : Prop :=
  ∀ (d : ℕ) (L : Matrix (Fin d) (Fin d) ℝ), L.PosDef →
    ∃ R : Matrix (Fin d) (Fin d) ℝ, IsUnit R.det ∧ L = Rᵀ * R
def HalfTraceStatement : Prop :=
  ∀ (d : ℕ) (L G K R : Matrix (Fin d) (Fin d) ℝ), L = Rᵀ * R → IsUnit R.det → G.PosSemidef →
    Kᵀ * G = -(G * K) → K * L = -(L * Kᵀ) → IsUnit K.det →
    ∀ x : Fin d → ℝ, x ⬝ᵥ (G *ᵥ x) ≤
      (1 / 2) * trace (L * G) * (((R⁻¹)ᵀ *ᵥ x) ⬝ᵥ ((R⁻¹)ᵀ *ᵥ x))
def ShortDualStatement : Prop :=
  ∀ (d : ℕ) (L R : Matrix (Fin d) (Fin d) ℝ) (μ : ℝ), 0 < d → L = Rᵀ * R → IsUnit R.det → 0 < μ →
    (∀ t : Fin d → ℤ, t ≠ 0 → μ ^ 2 ≤ (fun i => (t i : ℝ)) ⬝ᵥ (L *ᵥ fun i => (t i : ℝ))) →
    ∀ δ : ℝ, 0 < δ → ∃ c : Fin d → Fin d → ℤ, LinearIndependent ℤ c ∧
      ∀ j, ((R⁻¹)ᵀ *ᵥ fun i => (c j i : ℝ)) ⬝ᵥ ((R⁻¹)ᵀ *ᵥ fun i => (c j i : ℝ)) ≤
        ((d : ℝ) / μ + δ) ^ 2
def FiniteShortStatement : Prop :=
  ∀ (d : ℕ) (G : Matrix (Fin d) (Fin d) ℝ), G.PosDef → ∀ B : ℝ,
    {c : Fin d → ℤ | (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ)) ≤ B}.Finite
end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin


