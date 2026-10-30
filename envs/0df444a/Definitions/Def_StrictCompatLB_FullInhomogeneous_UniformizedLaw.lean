-- Prove2me | Definitions.Def_StrictCompatLB_FullInhomogeneous_UniformizedLaw
-- name    : StrictCompatLB_FullInhomogeneous_UniformizedLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:38:02.40037+00:00
-- url     : https://prove2.me/theorems/0c421d21-d203-4c76-949a-1f5d95ab6e3d
-- title:
--   Operational uniformization with arbitrary initial law and attraction to stationarity
-- statement:
--   Let $S$ be a countable state space with its discrete sigma algebra, $K$ a stochastic transition kernel, $r>0$ a clock rate, and $\mu$ an arbitrary initial probability vector. A sample consists of an entire chain $Y_0,Y_1,\ldots$ and independent exponential gaps $\tau_0,\tau_1,\ldots$. Its law satisfies
--
--   $$
--   P(Y_0=z_0,\ldots,Y_n=z_n)=\mu(z_0)\prod_{j=0}^{n-1}K(z_j,z_{j+1}).
--   $$
--
--   The gaps are iid exponential of rate $r$, independent of the entire chain; almost surely they are positive and their partial sums tend to infinity. The tagged process is $Y_{n(t)}$, where $n(t)$ counts completed clock epochs. This extends the published deterministic-initial-state uniformization interface without adding a moment condition.
--
--   The attraction predicate says that, for every initial state and every operational law with that initial state, the tagged law converges to the stated probability vector in total variation as time tends to infinity. It does not assert that a stationary vector exists. Operational-law existence, stationarity, uniqueness, and attraction are separate conclusions of the goal. Only countable discrete state spaces, stochastic kernels, and positive clock rates are used there; this definition is total on other arguments as well.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, https://arxiv.org/abs/2008.07562v2, §2 pp. 8–9, Appendix H p. 46 (uniformized Markov chain), Theorems 3.4 p. 12 and 4.8(i) p. 20 (ergodicity).

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_CountableChain

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StrictCompatLB.FullInhomogeneous

/-- Canonical sample space of a discrete chain and its independent exponential clock.
The state space is countable with its discrete sigma algebra in the queueing application. -/
abbrev ChainSample (S : Type*) := (ℕ → S) × (ℕ → ℝ)

/-- A law-valued version of `MeanField.IsUniformizedProcess` (arXiv:2008.07562v2,
§2 pp. 8–9 and Appendix H p. 46). The initial probability vector is arbitrary.
Finite cylinders specify the Markov chain operationally, independently of the iid
exponential gaps. Positive gaps with divergent partial sums express nonexplosion;
they are automatic almost surely for a positive-rate exponential clock.
No convergence, stationary law, or moment condition occurs in this definition. -/
def IsUniformizedLaw {S : Type*} [MeasurableSpace S]
    (P : Measure (ChainSample S)) (K : S → S → ℝ) (rate : ℝ) (μ : S → ℝ) : Prop :=
  IsProbabilityMeasure P ∧ MeanField.IsProbVec μ ∧
  (∀ (n : ℕ) (zs : ℕ → S),
    P {ω | ∀ j ≤ n, ω.1 j = zs j} =
      ENNReal.ofReal (μ (zs 0) * ∏ j ∈ Finset.range n, K (zs j) (zs (j + 1)))) ∧
  iIndepFun (fun k (ω : ChainSample S) => ω.2 k) P ∧
  (∀ k, P.map (fun ω => ω.2 k) = expMeasure rate) ∧
  IndepFun (fun ω : ChainSample S => ω.1) (fun ω : ChainSample S => ω.2) P ∧
  ∀ᵐ ω ∂P, (∀ k, 0 < ω.2 k) ∧
    Tendsto (fun n => ∑ k ∈ Finset.range n, ω.2 k) atTop atTop

/-- Tagged state at time `t`, including time zero. On regular clocks the epoch count is
finite on every bounded time interval. Null irregular clocks use the published total extension. -/
noncomputable def taggedState {S : Type*} (ω : ChainSample S) (t : ℝ) : S :=
  MeanField.jumpPath ω.1 ω.2 t

/-- Attraction of the stationary probability vector from every state, in total variation
(twice TV distance is the displayed sum). The law is the operational uniformized chain,
not a process defined by its asymptotic behavior. Existence of these laws is a separate
conclusion of the full theorem. This includes the absorbing no-arrivals case. -/
def AttractsAllStates {S : Type*} [DecidableEq S] [MeasurableSpace S]
    (K : S → S → ℝ) (rate : ℝ) (π : S → ℝ) : Prop :=
  ∀ z : S, ∀ P : Measure (ChainSample S),
    IsUniformizedLaw P K rate (fun z' => if z' = z then 1 else 0) →
    Tendsto (fun t : ℝ => ∑' z', |(P {ω | taggedState ω t = z'}).toReal - π z'|)
      atTop (𝓝 0)

end StrictCompatLB.FullInhomogeneous


