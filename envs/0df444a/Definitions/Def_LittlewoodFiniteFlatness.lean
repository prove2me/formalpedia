-- Prove2me | Definitions.Def_LittlewoodFiniteFlatness
-- name    : LittlewoodFiniteFlatness
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:17.610364+00:00
-- url     : https://prove2.me/theorems/b940f959-9d87-4a9c-a8fd-759289ac9c8c
-- statement:
--   For a real coefficient family ε indexed by k=0,…,N−1, littlewoodValue(ε,z) is the degree N−1 polynomial Σ_k ε_k z^k with consecutive powers, with coefficients viewed as complex numbers. IsRealSigning(ε) means every coefficient equals −1 or 1. MainStatement is a defined proposition, not an established theorem. It asserts that there exists, for each N, a real signing ε_N of length N such that for every real p>0 the following integral tends to 0 as N→∞: the integral over the unit circle, with Haar probability measure and points parametrized as the character z=fourier(1,t), of |‖littlewoodValue(ε_N,z)‖/√N − 1|^p. In other words, a single sequence of ±1 polynomials has modulus on the circle that, after normalizing by √N, converges to 1 in every L^p norm with p>0, a finite-flatness (asymptotically flat) condition in the sense of Littlewood.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/LittlewoodFiniteFlatness.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/LittlewoodFiniteFlatness.lean; bytes 16..962
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter Complex
open scoped BigOperators Topology ComplexConjugate

namespace AsymptoticallyMinimalLittlewoodFiniteFlatness

/-- The consecutive-degree polynomial of a real coefficient family. -/
def littlewoodValue {N : ℕ} (ε : Fin N → ℝ) (z : ℂ) : ℂ :=
  ∑ k : Fin N, (ε k : ℂ) * z ^ (k : ℕ)

/-- Every coefficient is a real sign. -/
def IsRealSigning {N : ℕ} (ε : Fin N → ℝ) : Prop :=
  ∀ k, ε k = -1 ∨ ε k = 1

def MainStatement : Prop :=
  ∃ ε : (N : ℕ) → Fin N → ℝ,
    (∀ N : ℕ, IsRealSigning (ε N)) ∧
    ∀ p : ℝ, 0 < p →
      Filter.Tendsto
        (fun N : ℕ =>
          ∫ t : UnitAddCircle,
            Real.rpow
              |‖littlewoodValue (ε N) (fourier (1 : ℤ) t)‖ /
                  Real.sqrt (N : ℝ) - 1|
              p
            ∂AddCircle.haarAddCircle)
        Filter.atTop (𝓝 (0 : ℝ))



end AsymptoticallyMinimalLittlewoodFiniteFlatness
end
end OAI


