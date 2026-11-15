-- Prove2me | Definitions.Def_LG2021_CanonicalBandit
-- name    : LG2021_CanonicalBandit
-- status  : Definition
-- author  : @sim2000dg
-- created : 2026-11-14T15:08:01.412233+00:00
-- url     : https://prove2.me/theorems/2731af0d-310a-4110-b47c-eb54f5ab8bee
-- title:
--   Normalized stochastic convex-bandit model
-- statement:
--   These predicates specify the normalized stochastic convex-bandit observation model and its canonical geometric problem.
--
--   For a known set $K$ and loss $L$, the normalized noise condition requires every legal finite-history observation law at $x\in K$ to be a probability measure, to have mean $L(x)$, and to satisfy
--   $$\mathbb E[\exp((Y-L(x))^2)]\le2.$$
--   The mean and exponential moment are integrable. The observation law may depend measurably on all previous queries and observations.
--
--   The canonical problem in dimension $d$ and with constant $C$ requires, for every $n\ge2$ and every known compact convex body $B_1\subseteq K\subseteq B_{dn}$, a legal measurable query policy and probability seed chosen before the loss and noise law. For every globally convex, nonnegative, $1$-Lipschitz loss with values in $[0,1]$ on $K$ and every admissible observation kernel, the expected cumulative regret is at most $C\sqrt n\log^2n$.
--
--   These are definitions, not asserted guarantees. The normalized body condition is the source-shaped intermediate problem produced by John normalization and the horizon-dependent erosion; the existence theorem is proved separately.
-- source:
--   Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, Proceedings of the 34th Conference on Learning Theory (COLT 2021), Proceedings of Machine Learning Research 134:2938–2964, 2021, observation model on printed p. 4 and non-Lipschitz reduction in Appendix F, printed p. 27. The explicit quantifier and measurable-kernel interfaces are formal adapters.

import Definitions.Def_BilateralProfitMHR_ConvexBandit

/-! The normalized stochastic convex-bandit problem. The known body and horizon
precede the algorithm; the unknown loss and every admissible adaptive observation
kernel follow it. This is a predicate, whose existence theorem is proved separately. -/

namespace BilateralProfitMHR.CorollaryTransport
open MeasureTheory
def UnitNoiseCond {X : Type} (K : Set X) (L : X → ℝ) (ν : ObsKernel X) : Prop :=
  ∀ (τ : ℕ) (xs : Fin τ → X) (ys : Fin τ → ℝ) (x : X),
    (∀ i, xs i ∈ K) → x ∈ K →
      IsProbabilityMeasure (ν τ xs ys x) ∧
      Integrable (fun z : ℝ => z) (ν τ xs ys x) ∧
      (∫ z, z ∂(ν τ xs ys x)) = L x ∧
      Integrable (fun z : ℝ => Real.exp ((z - L x) ^ 2)) (ν τ xs ys x) ∧
      (∫ z, Real.exp ((z - L x) ^ 2) ∂(ν τ xs ys x)) ≤ 2

end BilateralProfitMHR.CorollaryTransport

namespace LG2021
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
def CanonicalLipschitzBandit (d : ℕ) (C : ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ K : Set (EuclideanSpace ℝ (Fin d)),
    IsCompact K → Convex ℝ K → closedBall 0 1 ⊆ K →
    K ⊆ closedBall 0 ((d : ℝ) * n) →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
      ∃ A : QueryAlg (EuclideanSpace ℝ (Fin d)) Ω, A.IsOn K ∧
        ∀ L : EuclideanSpace ℝ (Fin d) → ℝ,
          ConvexOn ℝ univ L → LipschitzWith 1 L → (∀ x, 0 ≤ L x) →
          (∀ x ∈ K, L x ∈ Icc 0 1) →
          ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin d)), ν.IsMeasurable → UnitNoiseCond K L ν →
            expectedCumLoss A P ν (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n ≤
              ENNReal.ofReal (C * Real.sqrt n * Real.log n ^ 2)

end LG2021


