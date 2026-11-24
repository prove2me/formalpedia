-- Prove2me | Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_PathLimits
-- name    : KellyLossNetworks_RevisedDual_Supplement_PathLimits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:56:14.610819+00:00
-- url     : https://prove2.me/theorems/0365665e-421e-452e-b901-a47955cae728
-- title:
--   Simplex, weak J1 path convergence and cumulative fluid equations
-- statement:
--   For link capacity $C$, write $\Delta=\{x\in\mathbb R_+^{C+1}:\sum_nx_n=1\}$. The module specifies weak convergence of initial laws and full path laws on $D_\Delta[0,\infty)$, and the integral form of the cumulative fluid equations:
--   $$\sum_{m=0}^n x_m(t)=\sum_{m=0}^n x_m(0)+\int_0^t[(n+1)x_{n+1}(u)-b_n(x(u))x_n(u)]\,du.$$
--   Here $n=0,\ldots,C-1$, and $b_n$ is the appropriate star, alternative-routing or trunk-reservation birth rate. For trunk reservation, $q=\sum_{m<C-s}x_m$ and the overflow term is $2\nu x_C q\sum_{i=0}^{v-1}(1-q^2)^i$, the polynomial extension of the source expression at $q=0$.
--
--   The published càdlàg space and finite-state rate-chain law are reused. J1 convergence uses increasing time changes on every compact interval ending at a continuity point of the limit. Weak path convergence is its bounded continuous test-function characterization, not a collection of one-time limits. These interfaces support all three functional laws.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, pp.343–344,350,353, §§4.1,4.3–4.4

import Mathlib
import Definitions.Def_RBMSensitivity_Cadlag
import Definitions.Def_LambdaCoalescent_Rates_FiniteChain

open scoped NNReal ENNReal

open MeasureTheory Filter Topology

namespace KellyLossNetworks.RevisedDual.Supplement

/-- The simplex Δ of §4.1 (Kelly 1991, p. 343). -/
def simplex (C : ℕ) : Set (Fin (C + 1) → ℝ) :=
  {x | (∀ n, 0 ≤ x n) ∧ ∑ n, x n = 1}

/-- J1 convergence on [0,∞), using time changes on every compact interval whose right
endpoint is a continuity point of the limit. Kelly (1991), p. 343, D_Δ[0,∞).
**Formalization Note.** Order isomorphisms of compact real intervals are precisely the
increasing homeomorphisms fixing their endpoints. No restriction to integer horizons. -/
def J1Converges {V : Type} [MetricSpace V]
    (x : ℕ → RBMSensitivity.Cadlag V) (y : RBMSensitivity.Cadlag V) : Prop :=
  ∀ T : ℝ≥0, 0 < T → ContinuousAt y.1 T → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ k in atTop, ∃ a : Set.Icc (0 : ℝ≥0) T ≃o Set.Icc (0 : ℝ≥0) T,
      ∀ t : Set.Icc (0 : ℝ≥0) T,
        |((a t).1 : ℝ) - (t.1 : ℝ)| < ε ∧ dist ((x k).1 t.1) (y.1 (a t).1) < ε

/-- Test-function definition of weak J1 convergence, on the evaluation σ-algebra of the
published càdlàg space (the J1 Borel σ-algebra). Kelly (1991), Theorems 4.1, 4.22, 4.30.
**Formalization Note.** Laws are represented on the ambient function space to allow direct
push-forward of empirical coordinates. Tests are bounded measurable functions whose
restriction to càdlàg paths is J1 continuous. Both source and limit laws are supported on
càdlàg paths; this is the usual bounded-continuous-test characterization, not convergence
of finite-dimensional marginals. -/
def WeakJ1 {V : Type} [MetricSpace V] [MeasurableSpace V]
    (μ : ℕ → Measure (ℝ≥0 → V)) (ρ : Measure (ℝ≥0 → V)) : Prop :=
  ∀ f : (ℝ≥0 → V) → ℝ, Measurable f → (∃ b : ℝ, ∀ x, |f x| ≤ b) →
    (∀ (xs : ℕ → RBMSensitivity.Cadlag V) (x : RBMSensitivity.Cadlag V),
      J1Converges xs x → Tendsto (fun k => f (xs k).1) atTop (𝓝 (f x.1))) →
    Tendsto (fun k => ∫ x, f x ∂μ k) atTop (𝓝 (∫ x, f x ∂ρ))

/-- Weak convergence of initial occupancy vectors. Kelly (1991), p. 344. -/
def WeakInitial {C : ℕ} (μ : ℕ → Measure (Fin (C+1) → ℝ))
    (ρ : Measure (Fin (C+1) → ℝ)) : Prop :=
  ∀ f : (Fin (C+1) → ℝ) → ℝ, Continuous f → (∃ b : ℝ, ∀ x, |f x| ≤ b) →
    Tendsto (fun k => ∫ x, f x ∂μ k) atTop (𝓝 (∫ x, f x ∂ρ))

/-- An arbitrary-initial-law finite-state rate chain, by conditioning on each initial state
of positive probability and using the published deterministic-start rate-chain law.
Kelly (1991), §§4.1, 4.3–4.4; independent Poisson input and exponential unit holding.
**Formalization Note.** This is a property of the law of the actual chain, not an assumption
about its drift or its limiting behavior. -/
def RandomRateChain {S : Type} [Fintype S] [DecidableEq S]
    [TopologicalSpace S] [MeasurableSpace S]
    (P : Measure (RBMSensitivity.Cadlag S)) (Q : Matrix S S ℝ) : Prop :=
  IsProbabilityMeasure P ∧ ∀ s : S, P {x | x.1 0 = s} ≠ 0 →
    LambdaCoalescent.Rates.IsRateChain
      ((P {x | x.1 0 = s})⁻¹ • P.restrict {x | x.1 0 = s}) Q s (fun t x => x.1 t)

/-- Integral form of the complete cumulative-coordinate ODE, including continuity and
simplex invariance. Kelly (1991), (4.2), (4.23), Theorem 4.30.
**Formalization Note.** No equation at n=C; n ranges over 0,…,C−1. -/
def FluidSolution {C : ℕ} (birth : (Fin (C+1) → ℝ) → Fin C → ℝ)
    (z : Fin (C+1) → ℝ) (x : ℝ≥0 → (Fin (C+1) → ℝ)) : Prop :=
  Continuous x ∧ x 0 = z ∧ (∀ t, x t ∈ simplex C) ∧
  ∀ n : Fin C, ∀ t : ℝ≥0,
    (∑ m ∈ Finset.univ.filter (fun m : Fin (C+1) => m.val ≤ n.val), x t m) =
      (∑ m ∈ Finset.univ.filter (fun m : Fin (C+1) => m.val ≤ n.val), z m) +
      ∫ u in (0 : ℝ)..(t : ℝ),
        ((n.val + 1 : ℕ) : ℝ) * x (Real.toNNReal u) n.succ -
          birth (x (Real.toNNReal u)) n * x (Real.toNNReal u) n.castSucc

/-- The birth rates in (4.2), (4.23) and Theorem 4.30. At q=0 the overflow is its polynomial
extension 2νx_C q Σ_{i<v}(1−q²)^i, equal to zero. Kelly (1991), pp.344,350,353. -/
def starBirth (C w : ℕ) (lam : ℝ) (x : Fin (C+1) → ℝ) (_ : Fin C) : ℝ :=
  lam * (1 - x (Fin.last C)) ^ (w-1)

def trunkBirth (C s v : ℕ) (ν : ℝ) (x : Fin (C+1) → ℝ) (n : Fin C) : ℝ :=
  let q := ∑ m ∈ Finset.univ.filter (fun m : Fin (C+1) => m.val < C-s), x m
  ν + if n.val < C-s then
    2 * ν * x (Fin.last C) * q * ∑ i ∈ Finset.range v, (1-q^2)^i else 0

end KellyLossNetworks.RevisedDual.Supplement


