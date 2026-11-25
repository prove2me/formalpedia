-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_VacEntire
-- name    : Formalism_PeriodIntegrals_VacEntire
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T10:34:21.128065+00:00
-- url     : https://prove2.me/theorems/8a915942-0729-4066-a97f-ba349af107c4
-- title:
--   Vac Entire
-- statement:
--   Definitions and structural lemmas for Vac Entire, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/VacEntire.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VacEntire
variable {ι : Type} [Fintype ι] {N N' : ℕ}
def Hf (A : ℝ) (z w : ι → Fin N' → Fin N → ℂ) : ℂ :=
  (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)) / (A : ℂ)
def al (d : ℕ) (A : ℝ) (x : ι → Fin N' → Fin N → ℂ) : ℂ :=
  (-1 : ℂ) ^ (round (Real.sqrt d / 2 * (Hf A x x).re))
def U (A : ℝ) (x : ι → Fin N' → Fin N → ℂ) (G : (ι → Fin N' → Fin N → ℂ) → ℂ) : (ι → Fin N' → Fin N → ℂ) → ℂ :=
  fun z => G (z + x) * Complex.exp (-(Real.pi : ℂ) * Hf A z x - (Real.pi : ℂ) * Hf A x x / 2)
def Iop (d : ℕ) (A : ℝ) (La₁ La₂ : AddSubgroup (ι → Fin N' → Fin N → ℂ))
    (G : (ι → Fin N' → Fin N → ℂ) → ℂ) : (ι → Fin N' → Fin N → ℂ) → ℂ :=
  fun z => ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) *
    ∑ᶠ q : La₂ ⧸ La₁.addSubgroupOf La₂,
      al d A ((Quotient.out q : La₂) : ι → Fin N' → Fin N → ℂ) * U A ((Quotient.out q : La₂) : ι → Fin N' → Fin N → ℂ) G z
def tensPow {n : Type} [Fintype n] (θ : (n → ℂ) → ℂ) (N N' : ℕ) (z : n → Fin N' → Fin N → ℂ) : ℂ :=
  ∏ i : Fin N', ∏ j : Fin N, θ fun τ => z τ i j
def IopEntire : Prop :=
  ∀ (ι : Type) [Fintype ι] (N N' d : ℕ) (A : ℝ) (La₁ La₂ : AddSubgroup (ι → Fin N' → Fin N → ℂ))
    (G : (ι → Fin N' → Fin N → ℂ) → ℂ), AnalyticOnNhd ℂ G Set.univ → AnalyticOnNhd ℂ (Iop d A La₁ La₂ G) Set.univ
def TensEntire : Prop :=
  ∀ (n : Type) [Fintype n] (θ : (n → ℂ) → ℂ) (N N' : ℕ), AnalyticOnNhd ℂ θ Set.univ →
    AnalyticOnNhd ℂ (tensPow θ N N') Set.univ
def Target : Prop := IopEntire ∧ TensEntire
end PI.VacEntire


