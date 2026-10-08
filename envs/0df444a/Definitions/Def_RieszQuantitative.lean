-- Prove2me | Definitions.Def_RieszQuantitative
-- name    : RieszQuantitative
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:16.414346+00:00
-- url     : https://prove2.me/theorems/8a091678-c301-4cd9-aa1f-d50fe6b7c139
-- statement:
--   Ambient(d) is d-dimensional real Euclidean space. For a measure μ on it, a radius r is admissible if r>0 and r is at most the extended diameter of the support of μ. The kernel K_n(x,y) is the vector (x−y)/‖x−y‖^(n+1). The truncated transform T_ε f(x) is the vector-valued integral, over the points y with dist(x,y)>ε, of f(y)K_n(x,y) with respect to μ. ADRegularWithConstant(n,C,μ) means C≥1 and, for every x in the support of μ and every admissible r, the ball B(x,r) has measure between r^n/C and C·r^n. RieszL2BoundedWithConstant(n,C,μ) means that for every ε>0 and every real function f in L²(μ), T_ε f is also in L²(μ) and its L² norm is at most C times that of f, with C a nonnegative real constant. BallImageConclusion(n,μ,θ,M) means that for every x in the support of μ and every admissible r there is an M-Lipschitz map g from the open ball of radius r about 0 in n-dimensional Euclidean space into Ambient(d) such that μ(B(x,r)∩range g)≥θ r^n. QuantitativeFullStatement is a defined proposition, not an established theorem. It says that for all natural numbers d and n with d≥4, n≥2 and n+2≤d, every C_AD≥1 and every nonnegative real C_R, there exist θ>0 and M≥0, depending only on these parameters, such that every regular measure μ on Ambient(d) that is AD-regular with constant C_AD and has L² Riesz bound C_R satisfies BallImageConclusion(n,μ,θ,M).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/RieszQuantitative.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/RieszQuantitative.lean; bytes 16..2076
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace RieszRectifiability
noncomputable section
open MeasureTheory Set Metric
open scoped NNReal ENNReal

abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)

def AdmissibleRadius {d : ℕ} (μ : Measure (Ambient d)) (r : ℝ) : Prop :=
  0 < r ∧ ENNReal.ofReal r ≤ Metric.ediam μ.support

def kernel {d : ℕ} (n : ℕ) (x y : Ambient d) : Ambient d :=
  (‖x - y‖ ^ (n + 1))⁻¹ • (x - y)

def truncated {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (ε : ℝ) (f : Ambient d → ℝ) (x : Ambient d) : Ambient d :=
  ∫ y in {y | ε < dist x y}, f y • kernel n x y ∂μ

def ADRegularWithConstant {d : ℕ} (n : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) : Prop :=
  1 ≤ C ∧ ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
    ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r) ∧
    μ (ball x r) ≤ ENNReal.ofReal (C * r ^ n)

def RieszL2BoundedWithConstant {d : ℕ} (n : ℕ) (C : ℝ≥0)
    (μ : Measure (Ambient d)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ,
    MemLp f 2 μ → MemLp (truncated n μ ε f) 2 μ ∧
      eLpNorm (truncated n μ ε f) 2 μ ≤ (C : ℝ≥0∞) * eLpNorm f 2 μ

def BallImageConclusion {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (θ : ℝ) (M : ℝ≥0) : Prop :=
  ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
    ∃ g : (ball (0 : Ambient n) r) → Ambient d,
      LipschitzWith M g ∧
      ENNReal.ofReal (θ * r ^ n) ≤ μ (ball x r ∩ range g)

/-- A single mass fraction and Lipschitz bound work for all measures with fixed AD and Riesz bounds. -/
def QuantitativeFullStatement : Prop :=
  ∀ d n : ℕ, 4 ≤ d → 2 ≤ n → n + 2 ≤ d →
    ∀ C_AD : ℝ, 1 ≤ C_AD → ∀ C_R : ℝ≥0,
      ∃ θ : ℝ, 0 < θ ∧ ∃ M : ℝ≥0,
        ∀ μ : Measure (Ambient d), μ.Regular →
          ADRegularWithConstant n C_AD μ →
          RieszL2BoundedWithConstant n C_R μ →
          BallImageConclusion n μ θ M

end
end RieszRectifiability

namespace RieszRectifiability



end RieszRectifiability
end OAI


