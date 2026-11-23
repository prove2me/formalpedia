-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_BigPrimes
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_BigPrimes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:48.177339+00:00
-- url     : https://prove2.me/theorems/f1809ca7-4ee5-4152-be79-b954d161b6d6
-- title:
--   Big Primes
-- statement:
--   Definitions and structural lemmas for Big Primes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/BigPrimes.lean

import Definitions.Def_Formalism_PeriodIntegrals_SqfPrimeFactor
import Definitions.Def_Formalism_PeriodIntegrals_PrimesDyadicRS
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
namespace PI.SqfPrimeFactor.W
open PI.SqfLab
def monicDeg (g d : ℕ) [Fact g.Prime] : Finset (ZMod g)[X] :=
  Finset.univ.image (fun c : Fin d → ZMod g => X ^ d + ∑ i, C (c i) * X ^ (i : ℕ))
open Classical in

def irrDeg (g d : ℕ) [Fact g.Prime] : Finset (ZMod g)[X] :=
  (monicDeg g d).filter Irreducible
def bigPrimes (r : ℕ) : Finset ℕ :=
  (Finset.range (r + 1)).filter (fun p => p.Prime ∧ r < 2 * p ∧ p + 3 ≤ r)
def CountA : Prop :=
  ∀ (g r : ℕ) [Fact g.Prime], ∀ T : Finset (ZMod g)[X], (∀ f ∈ T, Ev g r f) →
    (T.card : ℝ) ≤ (g : ℝ) ^ r - ∑ p ∈ bigPrimes r, ((irrDeg g p).card : ℝ) * (g : ℝ) ^ (r - p)
def IrrLower : Prop :=
  ∀ (g p : ℕ) [Fact g.Prime], p.Prime → (g : ℝ) ^ p - g ≤ p * ((irrDeg g p).card : ℝ)
def Analytic : Prop :=
  ∀ g r : ℕ, 100 ≤ r → 2 ^ 12 ≤ g →
    (g : ℝ) ^ r - ∑ p ∈ bigPrimes r, ((g : ℝ) ^ p - g) / p * (g : ℝ) ^ (r - p)
      ≤ (1 - 1 / (5 * Real.log r)) * (g : ℝ) ^ r
end PI.SqfPrimeFactor.W


