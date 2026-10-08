-- Prove2me | Definitions.Def_Rokhlin
-- name    : Rokhlin
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:16.612097+00:00
-- url     : https://prove2.me/theorems/4bca9a0f-7fd2-4a09-ae50-4d6a9a35697b
-- statement:
--   For a measurable space with measure μ and a bijection T whose forward and inverse maps are measurable, timeMap(T,n) is the nth integer iterate of T: zero gives the identity, and negative integers use inverse iterates. IsMixing(μ,T) means that, for any measurable sets A and B, the measure of A intersected with the inverse image of B under timeMap(T,n) tends to μ(A)μ(B) as |n| tends to infinity. Given positive integer gaps between k consecutive observation times, layoutTime assigns index i the sum of the gaps preceding i, starting at time zero. MixingOfOrder(μ,T,k) means that, for every family of k measurable sets, the measure of the intersection of their inverse images under T at these observation times tends to the product of their measures as all gaps tend to infinity. These definitions do not themselves require T to preserve μ or μ to be a probability measure.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Rokhlin.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/Rokhlin.lean; bytes 16..941
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Rokhlin

variable {Ω : Type*} [MeasurableSpace Ω]

def timeMap (T : Ω ≃ᵐ Ω) (n : ℤ) : Ω → Ω :=
  ⇑((T.toEquiv : Equiv.Perm Ω) ^ n)

def IsMixing (μ : Measure Ω) (T : Ω ≃ᵐ Ω) : Prop :=
  ∀ A B : Set Ω, MeasurableSet A → MeasurableSet B →
    Tendsto (fun n : ℤ => μ (A ∩ timeMap T n ⁻¹' B))
      (comap Int.natAbs atTop) (𝓝 (μ A * μ B))

def layoutTime {k : ℕ} (gaps : Fin (k - 1) → ℕ+) (i : Fin k) : ℕ :=
  ∑ j : Fin (k - 1), if j.val < i.val then (gaps j : ℕ) else 0

def MixingOfOrder (μ : Measure Ω) (T : Ω ≃ᵐ Ω) (k : ℕ) : Prop :=
  ∀ A : Fin k → Set Ω, (∀ i, MeasurableSet (A i)) →
    Tendsto
      (fun gaps : Fin (k - 1) → ℕ+ =>
        μ (⋂ i : Fin k, timeMap T (layoutTime gaps i : ℤ) ⁻¹' A i))
      atTop (𝓝 (∏ i : Fin k, μ (A i)))



end Rokhlin
end OAI


