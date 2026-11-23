-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:49.298483+00:00
-- url     : https://prove2.me/theorems/af8025ea-efd1-44a4-ab49-c2fe1590ec68
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/Development.lean

import Definitions.Def_Formalism_PeriodIntegrals_SqfRootShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
namespace PI.SqfRootShift.W
open PI.SqfLab
def ppSum (N : ℕ) : ℕ := ∑ p ∈ N.primeFactors, p ^ N.factorization p
def CountP : Prop :=
  ∀ (g r : ℕ) [Fact g.Prime], 3 ≤ g → 1 ≤ r → ∀ (c : (ZMod g)ˣ) (T : Finset (ZMod g)[X]),
    (∀ f ∈ T, Eiii g r c f) →
    (T.card : ℝ) ≤ ∑ k ∈ Finset.Icc 1 r, ((ppSum (g ^ k - 1) : ℝ) / k) * (g : ℝ) ^ (r - k)
def ArithP : Prop :=
  ∀ (g r q d e : ℕ), g.Prime → q.Prime → d.Prime → q % 8 = 3 → d % 16 = 7 → 2 ≤ e →
    16 ≤ q → 16 ≤ d → g % (4 * 2 ^ e * q * d) = 1 → 100 ≤ r → 2 ^ 12 ≤ g →
    ∑ k ∈ Finset.Icc 1 r, ((ppSum (g ^ k - 1) : ℝ) / k) * (g : ℝ) ^ (r - k) ≤
      (1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log r) / ((g : ℝ) - 1)) * (g : ℝ) ^ r
end PI.SqfRootShift.W


